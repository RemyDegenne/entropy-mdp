/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.EV2026.AnalysisCommon

/-!
# Analysis of Entropic-BPI for `β < 0` on the good event

The mirror image of `EV2026/AnalysisPos.lean` (Essakine, Vernade 2026, Appendix B.2): for
`β < 0` the values lie in `[e^{β j}, 1]`, the optimal exponential value is a minimum, the
greedy policy minimizes the pessimistic backup and the ring value `Z̊` is an upper bound on `Z̃`
and on the value of the greedy policy.

The lemmas are first proved at a history `hist` satisfying the concentration inequalities of the
good event (`HistConcentration`), then on the good event of a run:

* **Lemma 12** (concentration): `abs_vecExp_sub_le_bonus_add_of_neg`,
  `abs_vecExp_sub_le_bonusAt_add_of_neg`;
* **Lemma 13** (optimism): `optExpValue_mem_Icc_optZ_of_neg`, `optExpQ_mem_Icc_stepUAt_of_neg`,
  `optExpValue_mem_Icc_ZlowerAt_ZtildeAt_of_neg`, `optExpQ_mem_Icc_UlowerAt_UtildeAt_of_neg`;
* the ring value is at most one: `ringZ_le_one_of_neg`, `ringU_le_one_of_neg`;
* **Lemma 15** (the ring value is an upper bound, no event needed):
  `optZ_fst_le_ringZ_and_expValue_le_of_neg`, `stepUAt_fst_le_ringU_and_expQ_le_of_neg` and
  their run versions;
* **Lemma 16** (one-step certificate bound): `ringU_sub_stepUAt_snd_le_of_neg`,
  `ringUAt_sub_UlowerAt_le_of_neg`;
* the certificate dominates the ring–pessimistic gap: `ringZ_sub_optZ_snd_le_cert_of_neg`,
  `ringZAt_sub_ZlowerAt_le_certAt_of_neg`;
* **Lemma 14** (the certificate dominates the suboptimality gap):
  `expValue_sub_optExpValue_le_cert_of_neg`, `expValue_sub_optExpValue_le_certAt_of_neg`;
* soundness of the stopping rule: `optEntropicValue_sub_entropicValue_le_of_stopCond_of_neg`,
  `optEntropicValue_sub_entropicValue_greedyAt_le_of_neg`;
* the certificate recursion under the true kernel, with the additive rate term outside the
  factor `e^{β r}`: `cert_le_of_neg`, `certAt_le_of_neg`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP.Episodic Learning.MDP
  InformationTheory
open scoped ENNReal

namespace Essakine2026Tight

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]
  {H : ℕ} {M : EpisodicMDP S A} {r : ℕ → S → A → ℝ} {β δ : ℝ} {t : ℕ}
  {hist : Hist Unit (Policy S A H) (Traj S H) t}

/-! ### Ranges -/

section Ranges

omit [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] in
/-- Range of the optimal exponential values for `β < 0`: `[e^{β (H - h)}, 1]`. -/
lemma optExpValue_mem_Icc_of_neg [Finite S] [Finite A] (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hβ : β < 0) (h : Fin (H + 1)) (s : S) :
    optExpValue M H β h s ∈ Set.Icc (Real.exp (β * (H - h : ℕ))) 1 :=
  mem_Icc_exp_one_of_neg hβ (Nat.cast_nonneg _)
    (optExpValue_mem_Icc M H β (rewardsIn_Icc_of_hasRewardFn hM hr) hβ.ne h s)

omit [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] in
/-- Range of the exponential values for `β < 0`: `[e^{β (H - h)}, 1]`. -/
lemma expValue_mem_Icc_of_neg [Finite S] (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hβ : β < 0) (π : Policy S A H) (h : Fin (H + 1)) (s : S) :
    expValue M H β π.extend h s ∈ Set.Icc (Real.exp (β * (H - h : ℕ))) 1 :=
  mem_Icc_exp_one_of_neg hβ (Nat.cast_nonneg _)
    (expValue_mem_Icc M H β (rewardsIn_Icc_of_hasRewardFn hM hr) π.measurable_extend h s)

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- Ranges of the optimistic and pessimistic values for `β < 0`. -/
lemma optZ_mem_of_neg (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (j : ℕ) (hj : j ≤ H) (s : S) :
    (optZ r β δ hist j).2 s ≤ (optZ r β δ hist j).1 s ∧ Real.exp (β * j) ≤ (optZ r β δ hist j).2 s
      ∧ (optZ r β δ hist j).1 s ≤ 1 := by
  have h := optZ_mem hist r β δ hr hδ hδ1 j hj s
  exact ⟨h.1, (mem_Icc_exp_one_of_neg hβ j.cast_nonneg h.2.2).1,
    (mem_Icc_exp_one_of_neg hβ j.cast_nonneg h.2.1).2⟩

/-- `e^{β k} ≤ 1` for `β < 0`. -/
lemma exp_mul_le_one_of_neg (hβ : β < 0) (k : ℕ) : Real.exp (β * k) ≤ 1 :=
  Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hβ.le k.cast_nonneg)

end Ranges

/-! ### Concentration and optimism -/

section Optimism

/-- **Lemma 12** (concentration of the optimal exponential value, `β < 0`), at a history
satisfying the concentration inequalities: for a visited pair,
`|(p̂ - p) Z*_{h+1}| ≤ b + (1/H) p̂|Z*_{h+1} - Z̲_{h+1}|`. -/
lemma abs_vecExp_sub_le_bonus_add_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (h : Fin H) (s : S) (a : A)
    (hn : 0 < visitCount hist h s a) :
    |vecExp (empTrans hist h s a) (optExpValue M H β (h + 1))
        - vecExp (M.transVec h s a) (optExpValue M H β (h + 1))|
      ≤ bonus (Fintype.card S) (Fintype.card A) H β δ (H - 1 - h) (visitCount hist h s a)
          (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1 (optZ r β δ hist (H - 1 - h)).2
        + 1 / H * vecExp (empTrans hist h s a)
          (fun s' ↦ |optExpValue M H β (h + 1) s' - (optZ r β δ hist (H - 1 - h)).2 s'|) := by
  set k := H - 1 - (h : ℕ) with hk
  have hB : 0 ≤ 1 - Real.exp (β * k) := sub_nonneg.2 (exp_mul_le_one_of_neg hβ k)
  have hf : ∀ s', optExpValue M H β (h + 1) s'
      ∈ Set.Icc (Real.exp (β * k)) (Real.exp (β * k) + (1 - Real.exp (β * k))) := fun s' ↦ by
    have := optExpValue_mem_Icc_of_neg hM hr hβ h.succ s'
    rw [sub_succ_eq, Fin.val_succ] at this
    exact ⟨this.1, by linarith [this.2]⟩
  have hg : ∀ s', (optZ r β δ hist k).2 s'
      ∈ Set.Icc (Real.exp (β * k)) (Real.exp (β * k) + (1 - Real.exp (β * k))) := fun s' ↦ by
    have := optZ_mem_of_neg (hist := hist) hr hβ hδ hδ1 k (by omega) s'
    exact ⟨this.2.1, by linarith [this.1, this.2.2]⟩
  have hbern := hc.bern h s a hn
  simp only [bernRange, hβ.not_gt, ↓reduceIte] at hbern
  have := abs_vecExp_sub_le_bonus_add (empTrans_nonneg hist h s a) (sum_empTrans hist h s a)
    (measureReal_trans_singleton M h s a)
    (div_nonneg (alphaStar_nonneg _ _ _ hδ hδ1 _) (Nat.cast_nonneg _))
    (alphaStar_div_le_alphaKL_div _ _ _ (one_le_card_of_elem s) _ _) hB (one_le_cast_of_fin h)
    hf hg (hc.klDiv_le_ofReal h s a hn) hbern
  have e : (fun s' ↦ |optExpValue M H β (h + 1) s' - (optZ r β δ hist k).2 s'|)
      = fun s' ↦ |(optZ r β δ hist k).2 s' - optExpValue M H β (h + 1) s'| :=
    funext fun _ ↦ abs_sub_comm _ _
  rw [bonus_of_not_pos (hβ := hβ.not_gt), e]
  exact this

/-- The optimistic backup dominates `U*` at a step whose next-step values bracket `Z*`
(**Lemma 13**, upper bound, `β < 0`). -/
lemma optExpQ_le_stepUAt_fst_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (h : Fin H)
    (hZ : ∀ s', optExpValue M H β (h + 1) s'
      ∈ Set.Icc ((optZ r β δ hist (H - 1 - h)).2 s') ((optZ r β δ hist (H - 1 - h)).1 s'))
    (s : S) (a : A) : optExpQ M H β h s a ≤ (stepUAt r β δ hist h s a).1 := by
  have hQ := optExpQ_mem_Icc M H β (rewardsIn_Icc_of_hasRewardFn hM hr) hβ.ne h.is_lt s a
  rw [cast_sub_castSucc_eq] at hQ
  have hQ' := mem_Icc_exp_one_of_neg hβ (by positivity) hQ
  simp only [stepUAt, stepU, hβ.not_gt, ↓reduceIte]
  split_ifs with hn
  · exact hQ'.2
  refine le_min hQ'.2 ?_
  have h12 := abs_vecExp_sub_le_bonus_add_of_neg hM hr hβ hδ hδ1 hc h s a (Nat.pos_of_ne_zero hn)
  have hp := empTrans_nonneg hist h s a
  rw [vecExp_abs_sub_eq_of_le _ fun s' ↦ (hZ s').1] at h12
  rw [optExpQ_of_hasRewardFn_eq_vecExp M H β hM]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  set u := (1 / H : ℝ)
  have hu0 : 0 ≤ u := by positivity
  have e1 := vecExp_mono hp fun s' ↦ (hZ s').1
  have e2 := vecExp_mono hp fun s' ↦ (hZ s').2
  rw [vecExp_sub]
  have e3 : u * (vecExp (empTrans hist h s a) (optExpValue M H β (h + 1))
      - vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).2)
      ≤ u * (vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1
      - vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).2) :=
    mul_le_mul_of_nonneg_left (by linarith) hu0
  have := (abs_le.1 h12).1
  linarith

/-- The pessimistic backup is dominated by `U*` at a step whose next-step values bracket `Z*`
(**Lemma 13**, lower bound, `β < 0`). -/
lemma stepUAt_snd_le_optExpQ_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (h : Fin H)
    (hZ : ∀ s', optExpValue M H β (h + 1) s'
      ∈ Set.Icc ((optZ r β δ hist (H - 1 - h)).2 s') ((optZ r β δ hist (H - 1 - h)).1 s'))
    (s : S) (a : A) : (stepUAt r β δ hist h s a).2 ≤ optExpQ M H β h s a := by
  have hQ := optExpQ_mem_Icc M H β (rewardsIn_Icc_of_hasRewardFn hM hr) hβ.ne h.is_lt s a
  rw [cast_sub_castSucc_eq] at hQ
  have hQ' := mem_Icc_exp_one_of_neg hβ (by positivity) hQ
  simp only [stepUAt, stepU, hβ.not_gt, ↓reduceIte]
  split_ifs with hn
  · exact hQ'.1
  refine max_le hQ'.1 ?_
  have h12 := abs_vecExp_sub_le_bonus_add_of_neg hM hr hβ hδ hδ1 hc h s a (Nat.pos_of_ne_zero hn)
  have hp := empTrans_nonneg hist h s a
  rw [vecExp_abs_sub_eq_of_le _ fun s' ↦ (hZ s').1] at h12
  rw [optExpQ_of_hasRewardFn_eq_vecExp M H β hM]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  set u := (1 / H : ℝ)
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 := by
    rw [div_le_one (by linarith [one_le_cast_of_fin h])]; exact one_le_cast_of_fin h
  have e1 := vecExp_mono hp fun s' ↦ (hZ s').1
  have e2 := vecExp_mono hp fun s' ↦ (hZ s').2
  rw [vecExp_sub]
  have e3 : u * (vecExp (empTrans hist h s a) (optExpValue M H β (h + 1))
      - vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).2)
      ≤ vecExp (empTrans hist h s a) (optExpValue M H β (h + 1))
      - vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).2 :=
    mul_le_of_le_one_left (by linarith) hu1
  have e4 : 0 ≤ u * (vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1
      - vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).2) :=
    mul_nonneg hu0 (by linarith)
  have := (abs_le.1 h12).2
  linarith

/-- **Lemma 13** (optimism and pessimism, `β < 0`), at a history satisfying the concentration
inequalities: `Z̲_h ≤ Z*_h ≤ Z̃_h` at every step. -/
lemma optExpValue_mem_Icc_optZ_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (h : Fin (H + 1)) (s : S) :
    optExpValue M H β h s
      ∈ Set.Icc ((optZ r β δ hist (H - h)).2 s) ((optZ r β δ hist (H - h)).1 s) := by
  have hR := rewardsIn_Icc_of_hasRewardFn hM hr
  induction h using Fin.reverseInduction generalizing s with
  | last => simp [Fin.val_last, optExpValue_of_le M H β hR hβ.ne le_rfl, optZ_zero]
  | cast i ih =>
    have ih' : ∀ s', optExpValue M H β (i + 1) s'
        ∈ Set.Icc ((optZ r β δ hist (H - 1 - i)).2 s') ((optZ r β δ hist (H - 1 - i)).1 s') := by
      intro s'; rw [← sub_succ_eq]; exact ih s'
    rw [Fin.val_castSucc, optZ_eq]
    simp only [hβ.not_gt, ↓reduceIte]
    constructor
    · rw [optExpValue_succ_eq M H β hR hβ.ne i.is_lt]
      exact (Function.min_le (fun a ↦ (stepUAt r β δ hist i s a).2) _).trans
        (stepUAt_snd_le_optExpQ_of_neg hM hr hβ hδ hδ1 hc i ih' s _)
    · rw [← argmin_spec]
      exact (optExpValue_le_optExpQ M H β hR hβ i.is_lt s _).trans
        (optExpQ_le_stepUAt_fst_of_neg hM hr hβ hδ hδ1 hc i ih' s _)

/-- **Lemma 13** for the backups (`β < 0`): `U̲_h ≤ U*_h ≤ Ũ_h`. -/
lemma optExpQ_mem_Icc_stepUAt_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (h : Fin H) (s : S) (a : A) :
    optExpQ M H β h s a ∈ Set.Icc (stepUAt r β δ hist h s a).2 (stepUAt r β δ hist h s a).1 := by
  have hZ : ∀ s', optExpValue M H β (h + 1) s'
      ∈ Set.Icc ((optZ r β δ hist (H - 1 - h)).2 s') ((optZ r β δ hist (H - 1 - h)).1 s') := by
    intro s'; rw [← sub_succ_eq]
    exact optExpValue_mem_Icc_optZ_of_neg hM hr hβ hδ hδ1 hc h.succ s'
  exact ⟨stepUAt_snd_le_optExpQ_of_neg hM hr hβ hδ hδ1 hc h hZ s a,
    optExpQ_le_stepUAt_fst_of_neg hM hr hβ hδ hδ1 hc h hZ s a⟩

end Optimism

/-! ### The ring value -/

section Ring

omit [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- The ring backup of values at most one is at most one (`β < 0`). -/
lemma ringUAux_le_one_of_neg {nS nA k n : ℕ} {rr : ℝ} (hrr : 0 ≤ rr) (hβ : β < 0)
    {p phat Zr Zt Zl : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) (hZr : ∀ s, Zr s ≤ 1) :
    ringUAux nS nA H β δ k n rr p phat Zr Zt Zl ≤ 1 := by
  have h1 : vecExp p Zr ≤ 1 := by
    have := vecExp_mono hp (g := fun _ ↦ (1 : ℝ)) hZr
    rwa [vecExp_const, hp1, one_mul] at this
  have he1 : Real.exp (β * rr) ≤ 1 :=
    Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hβ.le hrr)
  have he0 := Real.exp_pos (β * rr)
  have hQ : Real.exp (β * rr) * vecExp p Zr ≤ 1 := by
    rcases le_total 0 (vecExp p Zr) with hx | hx
    · exact (mul_le_of_le_one_left hx he1).trans h1
    · exact (mul_nonpos_of_nonneg_of_nonpos he0.le hx).trans zero_le_one
  simp only [ringUAux, hβ.not_gt, ↓reduceIte]
  split_ifs
  · exact max_le hQ le_rfl
  · exact max_le hQ (min_le_left _ _)

omit [MeasurableSingletonClass A] in
/-- **The ring value is at most one** (`β < 0`), at every number of steps to go. -/
lemma ringZ_le_one_of_neg (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (j : ℕ) (s : S) :
    ringZ M r β δ hist j s ≤ 1 := by
  induction j generalizing s with
  | zero => exact le_rfl
  | succ k ih =>
    change ringZStep M r β δ hist k (ringZ M r β δ hist k) s ≤ 1
    simp only [ringZStep]
    split_ifs with hk
    · exact ringUAux_le_one_of_neg (hr _ _ _).1 hβ (M.transVec_nonneg _ _ _)
        (M.sum_transVec _ _ _) ih
    · exact ih s

omit [MeasurableSingletonClass A] in
/-- **The ring backup is at most one** (`β < 0`). -/
lemma ringU_le_one_of_neg (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (h : Fin H) (s : S)
    (a : A) : ringU M r β δ hist h s a ≤ 1 :=
  ringUAux_le_one_of_neg (hr h s a).1 hβ (M.transVec_nonneg h s a) (M.sum_transVec h s a)
    (ringZ_le_one_of_neg hr hβ _)

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- `Ũ_h ≤ Ů_h` when `Z̃_{h+1} ≤ Z̊_{h+1}` (`β < 0`). -/
lemma stepUAt_fst_le_ringU_of_neg (hβ : β < 0) (h : Fin H)
    (hZ : ∀ s', (optZ r β δ hist (H - 1 - h)).1 s' ≤ ringZ M r β δ hist (H - 1 - h) s')
    (s : S) (a : A) : (stepUAt r β δ hist h s a).1 ≤ ringU M r β δ hist h s a := by
  have hp := empTrans_nonneg hist h s a
  simp only [ringU, ringUAux, stepUAt, stepU, hβ.not_gt, ↓reduceIte]
  split_ifs with hn
  · exact le_max_right _ _
  · refine (min_le_min le_rfl ?_).trans (le_max_right _ _)
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have e1 := vecExp_mono hp hZ
    rw [vecExp_sub, vecExp_sub]
    have hu0 : (0 : ℝ) ≤ 1 / H := by positivity
    have := mul_le_mul_of_nonneg_left e1 hu0
    linarith

omit [MeasurableSingletonClass A] in
/-- `U^π_h ≤ Ů_h` when `Z^π_{h+1} ≤ Z̊_{h+1}` (`β < 0`). -/
lemma expQ_le_ringU_of_neg (hM : M.HasRewardFn r) (hβ : β < 0) (π : Policy S A H) (h : Fin H)
    (hZ : ∀ s', expValue M H β π.extend (h + 1) s' ≤ ringZ M r β δ hist (H - 1 - h) s') (s : S)
    (a : A) :
    expQ M H β π.extend h s a ≤ ringU M r β δ hist h s a := by
  rw [expQ_of_hasRewardFn_eq_vecExp M H β hM]
  refine le_trans (mul_le_mul_of_nonneg_left (vecExp_mono (M.transVec_nonneg h s a) hZ)
    (Real.exp_pos _).le) ?_
  simp only [ringU, ringUAux, hβ.not_gt, ↓reduceIte]
  split_ifs <;> exact le_max_left _ _

/-- **Lemma 15** (the ring value is an upper bound, `β < 0`; no event is needed):
`Z̃_h ≤ Z̊_h` and `Z^π_h ≤ Z̊_h` for the greedy policy `π` of the history. -/
lemma optZ_fst_le_ringZ_and_expValue_le_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (h : Fin (H + 1)) (s : S) :
    (optZ r β δ hist (H - h)).1 s ≤ ringZ M r β δ hist (H - h) s
      ∧ expValue M H β (greedy r β δ hist).extend h s ≤ ringZ M r β δ hist (H - h) s := by
  have hR := rewardsIn_Icc_of_hasRewardFn hM hr
  induction h using Fin.reverseInduction generalizing s with
  | last =>
    simp [Fin.val_last, optZ_zero, ringZ_zero,
      expValue_of_le M H β (greedy r β δ hist).measurable_extend le_rfl]
  | cast i ih =>
    have ih1 : ∀ s', (optZ r β δ hist (H - 1 - i)).1 s' ≤ ringZ M r β δ hist (H - 1 - i) s' :=
      fun s' ↦ by rw [← sub_succ_eq]; exact (ih s').1
    have ih2 : ∀ s', expValue M H β (greedy r β δ hist).extend (i + 1) s'
        ≤ ringZ M r β δ hist (H - 1 - i) s' :=
      fun s' ↦ by rw [← sub_succ_eq]; exact (ih s').2
    rw [Fin.val_castSucc, ringZ_sub_eq, optZ_eq,
      expValue_succ M H β hR (greedy r β δ hist).measurable_extend i.is_lt, Policy.extend_fin]
    simp only [hβ.not_gt, ↓reduceIte]
    exact ⟨(Function.min_le (fun a ↦ (stepUAt r β δ hist i s a).1) _).trans
        (stepUAt_fst_le_ringU_of_neg hβ i ih1 s _),
      expQ_le_ringU_of_neg hM hβ (greedy r β δ hist) i ih2 s (greedy r β δ hist i s)⟩

/-- **Lemma 15** for the backups (`β < 0`): `Ũ_h ≤ Ů_h` and `U^π_h ≤ Ů_h`. -/
lemma stepUAt_fst_le_ringU_and_expQ_le_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (h : Fin H) (s : S) (a : A) :
    (stepUAt r β δ hist h s a).1 ≤ ringU M r β δ hist h s a
      ∧ expQ M H β (greedy r β δ hist).extend h s a ≤ ringU M r β δ hist h s a :=
  ⟨stepUAt_fst_le_ringU_of_neg hβ h (fun s' ↦ by
      rw [← sub_succ_eq]
      exact (optZ_fst_le_ringZ_and_expValue_le_of_neg hM hr hβ h.succ s').1) s a,
    expQ_le_ringU_of_neg hM hβ (greedy r β δ hist) h (fun s' ↦ by
      rw [← sub_succ_eq]
      exact (optZ_fst_le_ringZ_and_expValue_le_of_neg hM hr hβ h.succ s').2) s a⟩

end Ring

/-! ### The certificate -/

section Certificate

/-- **Lemma 16** (one-step certificate bound, `β < 0`), at a history satisfying the concentration
inequalities: for a visited pair,
`Ů_h - U̲_h ≤ e^{β r_h} (3 b + (1 + 3/H) p̂(Z̊_{h+1} - Z̲_{h+1}))`. -/
lemma ringU_sub_stepUAt_snd_le_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (h : Fin H) (s : S) (a : A)
    (hn : 0 < visitCount hist h s a) :
    ringU M r β δ hist h s a - (stepUAt r β δ hist h s a).2
      ≤ Real.exp (β * r h s a) *
        (3 * bonus (Fintype.card S) (Fintype.card A) H β δ (H - 1 - h) (visitCount hist h s a)
            (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1 (optZ r β δ hist (H - 1 - h)).2
          + (1 + 3 / H) * vecExp (empTrans hist h s a)
            (ringZ M r β δ hist (H - 1 - h) - (optZ r β δ hist (H - 1 - h)).2)) := by
  have hZ : ∀ s', optExpValue M H β (h + 1) s'
      ∈ Set.Icc ((optZ r β δ hist (H - 1 - h)).2 s') ((optZ r β δ hist (H - 1 - h)).1 s') := by
    intro s'; rw [← sub_succ_eq]
    exact optExpValue_mem_Icc_optZ_of_neg hM hr hβ hδ hδ1 hc h.succ s'
  have hRt : ∀ s', (optZ r β δ hist (H - 1 - h)).1 s' ≤ ringZ M r β δ hist (H - 1 - h) s' := by
    intro s'; rw [← sub_succ_eq]
    exact (optZ_fst_le_ringZ_and_expValue_le_of_neg hM hr hβ h.succ s').1
  have hR1 : ∀ s', ringZ M r β δ hist (H - 1 - h) s' ≤ 1 := ringZ_le_one_of_neg hr hβ _
  have hZs : ∀ s', Real.exp (β * (H - 1 - h : ℕ)) ≤ optExpValue M H β (h + 1) s' := by
    intro s'
    have := (optExpValue_mem_Icc_of_neg hM hr hβ h.succ s').1
    rwa [sub_succ_eq, Fin.val_succ] at this
  have hH := one_le_cast_of_fin h
  have hp := empTrans_nonneg hist h s a
  have hαn : 0 ≤ alphaKL (Fintype.card S) (Fintype.card A) H δ (visitCount hist h s a)
      / visitCount hist h s a := div_nonneg (alphaKL_nonneg _ _ _ hδ hδ1 _) (Nat.cast_nonneg _)
  have hB : 0 ≤ 1 - Real.exp (β * (H - 1 - h : ℕ)) :=
    sub_nonneg.2 (exp_mul_le_one_of_neg hβ _)
  have h12 := abs_vecExp_sub_le_bonus_add_of_neg hM hr hβ hδ hδ1 hc h s a hn
  rw [vecExp_abs_sub_eq_of_le _ fun s' ↦ (hZ s').1] at h12
  have h3 := vecExp_sub_vecExp_le_of_klDiv_le hp (sum_empTrans hist h s a)
    (measureReal_trans_singleton M h s a) hαn hB hH
    (f := ringZ M r β δ hist (H - 1 - h) - optExpValue M H β (h + 1))
    (fun s' ↦ ⟨sub_nonneg.2 ((hZ s').2.trans (hRt s')), by
      simp only [Pi.sub_apply]; linarith [hZs s', hR1 s']⟩) (hc.klDiv_le_ofReal h s a hn)
  have hbB : (5 + 4 * (H : ℝ)) * (1 - Real.exp (β * (H - 1 - h : ℕ)))
      * (alphaKL (Fintype.card S) (Fintype.card A) H δ (visitCount hist h s a)
        / visitCount hist h s a)
      ≤ bonus (Fintype.card S) (Fintype.card A) H β δ (H - 1 - h) (visitCount hist h s a)
          (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1
          (optZ r β δ hist (H - 1 - h)).2 := by
    rw [bonus_of_not_pos (hβ := hβ.not_gt)]
    have : 0 ≤ 2 * √2 * √(vecVar (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).2
        * (alphaStar (Fintype.card S) (Fintype.card A) H δ (visitCount hist h s a)
          / visitCount hist h s a)) := by positivity
    linarith
  have hb0 := bonus_nonneg (Fintype.card S) (Fintype.card A) H β hδ hδ1 (H - 1 - h)
    (visitCount hist h s a) (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1
    (optZ r β δ hist (H - 1 - h)).2
  have m1 := vecExp_mono hp fun s' ↦ (hZ s').1
  have m2 := vecExp_mono hp fun s' ↦ (hZ s').2
  have m3 := vecExp_mono hp hRt
  rw [vecExp_sub, vecExp_sub] at h3
  have hUl : Real.exp (β * r h s a) *
      (vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).2
        - bonus (Fintype.card S) (Fintype.card A) H β δ (H - 1 - h) (visitCount hist h s a)
          (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1 (optZ r β δ hist (H - 1 - h)).2
        - 1 / H * (vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1
          - vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).2))
      ≤ (stepUAt r β δ hist h s a).2 := by
    simp only [stepUAt, stepU, hβ.not_gt, hn.ne', ↓reduceIte, vecExp_sub]
    exact le_max_right _ _
  have hUr : ringU M r β δ hist h s a
      = max (Real.exp (β * r h s a) * vecExp (M.transVec h s a) (ringZ M r β δ hist (H - 1 - h)))
        (min 1 (Real.exp (β * r h s a) *
          (vecExp (empTrans hist h s a) (ringZ M r β δ hist (H - 1 - h))
            + bonus (Fintype.card S) (Fintype.card A) H β δ (H - 1 - h) (visitCount hist h s a)
              (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1
              (optZ r β δ hist (H - 1 - h)).2
            + 1 / H * (vecExp (empTrans hist h s a) (ringZ M r β δ hist (H - 1 - h))
              - vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).2)))) := by
    simp only [ringU, ringUAux, hβ.not_gt, hn.ne', ↓reduceIte, vecExp_sub]
  rw [hUr, vecExp_sub]
  set e := Real.exp (β * r h s a) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  set b := bonus (Fintype.card S) (Fintype.card A) H β δ (H - 1 - h) (visitCount hist h s a)
    (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1 (optZ r β δ hist (H - 1 - h)).2
  set xt := vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1
  set xl := vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).2
  set xs := vecExp (empTrans hist h s a) (optExpValue M H β (h + 1))
  set xr := vecExp (empTrans hist h s a) (ringZ M r β δ hist (H - 1 - h))
  set ys := vecExp (M.transVec h s a) (optExpValue M H β (h + 1))
  set yr := vecExp (M.transVec h s a) (ringZ M r β δ hist (H - 1 - h))
  set u := (1 / H : ℝ) with hu
  have hu0 : 0 ≤ u := by positivity
  have h3H : 3 / (H : ℝ) = 3 * u := by rw [hu]; ring
  rw [h3H]
  have h12' := (abs_le.1 h12).1
  have hΔ : 0 ≤ u * (xr - xl) := mul_nonneg hu0 (by linarith)
  have e1 : u * (xt - xl) ≤ u * (xr - xl) := mul_le_mul_of_nonneg_left (by linarith) hu0
  rcases max_choice (e * yr) (min 1 (e * (xr + b + u * (xr - xl)))) with hm | hm <;> rw [hm]
  · have key : yr - (xl - b - u * (xt - xl)) ≤ 3 * b + (1 + 3 * u) * (xr - xl) := by
      linarith
    have := mul_le_mul_of_nonneg_left key he0
    linarith
  · have hR := min_le_right 1 (e * (xr + b + u * (xr - xl)))
    have key : xr + b + u * (xr - xl) - (xl - b - u * (xt - xl))
        ≤ 3 * b + (1 + 3 * u) * (xr - xl) := by linarith
    have := mul_le_mul_of_nonneg_left key he0
    linarith

/-- **The certificate dominates the ring–pessimistic gap** (`β < 0`), at a history satisfying
the concentration inequalities: `Z̊_h - Z̲_h ≤ π_h G_h`. -/
lemma ringZ_sub_optZ_snd_le_cert_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (h : Fin (H + 1)) (s : S) :
    ringZ M r β δ hist (H - h) s - (optZ r β δ hist (H - h)).2 s ≤ cert r β δ hist (H - h) s := by
  induction h using Fin.reverseInduction generalizing s with
  | last => simp [optZ_zero, ringZ_zero, cert_zero]
  | cast i ih =>
    have ih' : ∀ s', (ringZ M r β δ hist (H - 1 - i) - (optZ r β δ hist (H - 1 - i)).2) s'
        ≤ cert r β δ hist (H - 1 - i) s' := fun s' ↦ by rw [← sub_succ_eq]; exact ih s'
    rw [Fin.val_castSucc, optZ_snd_eq_stepUAt_greedy hist r β δ hβ.not_gt i s, ringZ_sub_eq,
      cert_sub_eq]
    simp only [hβ.not_gt, ↓reduceIte]
    have hUl := (stepUAt_mem hist r β δ hr hδ hδ1 i s (greedy r β δ hist i s)).2.2
    rw [cast_sub_castSucc_eq] at hUl
    have hUl' := (mem_Icc_exp_one_of_neg hβ (by positivity) hUl).1
    have hR1 := ringU_le_one_of_neg (M := M) (hist := hist) (δ := δ) hr hβ i s
      (greedy r β δ hist i s)
    have hclip : ringU M r β δ hist i s (greedy r β δ hist i s)
        - (stepUAt r β δ hist i s (greedy r β δ hist i s)).2 ≤ 1 := by
      linarith [Real.exp_pos (β * ((H - 1 - i : ℕ) + 1))]
    split_ifs with hn
    · exact hclip
    · refine le_min hclip ?_
      refine (ringU_sub_stepUAt_snd_le_of_neg hM hr hβ hδ hδ1 hc i s _
        (Nat.pos_of_ne_zero hn)).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
      push_cast
      have hH : (0 : ℝ) ≤ 1 + 3 / H := by positivity
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (vecExp_mono (empTrans_nonneg hist i s _) ih') hH)

/-- **Lemma 14** (the certificate dominates the suboptimality gap, `β < 0`), at a history
satisfying the concentration inequalities: `Z^π_h - Z*_h ≤ π_h G_h` for the greedy policy `π`. -/
lemma expValue_sub_optExpValue_le_cert_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (h : Fin (H + 1)) (s : S) :
    expValue M H β (greedy r β δ hist).extend h s - optExpValue M H β h s
      ≤ cert r β δ hist (H - h) s := by
  have h1 := (optExpValue_mem_Icc_optZ_of_neg hM hr hβ hδ hδ1 hc h s).1
  have h2 := (optZ_fst_le_ringZ_and_expValue_le_of_neg (δ := δ) (hist := hist) hM hr hβ h s).2
  have h3 := ringZ_sub_optZ_snd_le_cert_of_neg hM hr hβ hδ hδ1 hc h s
  linarith

/-- **Soundness of the stopping rule** (`β < 0`), at a history satisfying the concentration
inequalities: if the stopping condition holds, the greedy policy is `ε`-optimal. -/
lemma optEntropicValue_sub_entropicValue_le_of_stopCond_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) {ε : ℝ} (hε : 0 ≤ ε) {s₁ : S}
    (hstop : stopCond r β δ ε s₁ hist) :
    optEntropicValue M H β 0 s₁ - entropicValue M H β (greedy r β δ hist).extend 0 s₁
      ≤ ε := by
  have hR := rewardsIn_Icc_of_hasRewardFn hM hr
  simp only [stopCond, hβ.not_gt, ↓reduceIte] at hstop
  have h1 : (optZ r β δ hist H).2 s₁ ≤ optExpValue M H β 0 s₁ := by
    simpa only [Fin.val_zero, Nat.sub_zero] using
      (optExpValue_mem_Icc_optZ_of_neg hM hr hβ hδ hδ1 hc 0 s₁).1
  have h3 : expValue M H β (greedy r β δ hist).extend 0 s₁ - optExpValue M H β 0 s₁
      ≤ cert r β δ hist H s₁ := by
    simpa only [Fin.val_zero, Nat.sub_zero] using
      expValue_sub_optExpValue_le_cert_of_neg hM hr hβ hδ hδ1 hc 0 s₁
  have hZπ := expValue_pos M H β hR (greedy r β δ hist).measurable_extend 0 s₁
  have hZsπ := optExpValue_le_expValue M H β hR hβ (greedy r β δ hist).measurable_extend 0 s₁
  refine optEntropicValue_sub_entropicValue_le_of_neg M H β hβ hZπ ?_
  set E := Real.exp (β * ε)
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hβ.le hε)
  have e1 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hE1)
  have e2 := mul_le_mul_of_nonneg_left hZsπ (sub_nonneg.2 hE1)
  linarith

end Certificate

/-! ### The certificate under the true kernel -/

section TrueKernel

/-- **Certificate recursion under the true kernel** (`β < 0`), at a history satisfying the
concentration inequalities: with `a = π_h(s)` for the greedy policy `π`,
`π_h G_h(s) ≤ e^{β r_h(s, a)} (36 √(Var_{p_h}(Z^π_{h+1}) ρ*) + (1 + 13/H) p_h(π_{h+1} G_{h+1}))
+ 84 H ρ`; the additive rate term is outside the factor `e^{β r_h(s, a)} ≤ 1`. -/
lemma cert_le_of_neg (hM : M.HasRewardFn r) (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc : HistConcentration M β δ hist) (h : Fin H) (s : S) :
    cert r β δ hist (H - h) s ≤ Real.exp (β * r h s (greedy r β δ hist h s)) *
      (36 * √(vecVar (M.transVec h s (greedy r β δ hist h s))
          (expValue M H β (greedy r β δ hist).extend (h + 1))
          * rateMin (alphaStar (Fintype.card S) (Fintype.card A) H δ)
            (visitCount hist h s (greedy r β δ hist h s)))
        + (1 + 13 / H) * vecExp (M.transVec h s (greedy r β δ hist h s))
          (cert r β δ hist (H - 1 - h)))
      + 84 * H * rateMin (alphaKL (Fintype.card S) (Fintype.card A) H δ)
            (visitCount hist h s (greedy r β δ hist h s)) := by
  set a := greedy r β δ hist h s with ha
  set n := visitCount hist h s a with hn_def
  set π := greedy r β δ hist
  have hH := one_le_cast_of_fin h
  have hq0 := M.transVec_nonneg h s a
  have hp := empTrans_nonneg hist h s a
  have hp1 := sum_empTrans hist h s a
  set k := H - 1 - (h : ℕ) with hk
  set B := 1 - Real.exp (β * k) with hB
  have hB0 : 0 ≤ B := sub_nonneg.2 (exp_mul_le_one_of_neg hβ k)
  have hB1 : B ≤ 1 := by have := Real.exp_pos (β * k); linarith
  have he0 : 0 < Real.exp (β * r h s a) := Real.exp_pos _
  have he1 : Real.exp (β * r h s a) ≤ 1 :=
    Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hβ.le (hr h s a).1)
  -- the certificate at the next step
  have hg : ∀ s', cert r β δ hist k s' ∈ Set.Icc 0 1 := by
    intro s'
    have := cert_mem hist r β δ hδ hδ1 k (by omega) s'
    simp only [hβ.not_gt, ↓reduceIte] at this
    refine ⟨this.1, this.2.trans ?_⟩
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  have hΔp : 0 ≤ vecExp (M.transVec h s a) (cert r β δ hist k) :=
    vecExp_nonneg hq0 fun s' ↦ (hg s').1
  have hcert1 : cert r β δ hist (H - h) s ≤ 1 := by
    have := (cert_mem hist r β δ hδ hδ1 (H - h) (by omega) s).2
    simp only [show H - (h : ℕ) ≠ 0 by omega, hβ.not_gt, ↓reduceIte] at this
    exact this
  by_cases htriv : n = 0 ∨ 1 ≤ alphaKL (Fintype.card S) (Fintype.card A) H δ n / n
  · -- trivial case: the rate term is `1`
    rw [rateMin_eq_one htriv, mul_one]
    have : 0 ≤ Real.exp (β * r h s a) * (36 * √(vecVar (M.transVec h s a)
        (expValue M H β π.extend (h + 1))
        * rateMin (alphaStar (Fintype.card S) (Fintype.card A) H δ) n)
        + (1 + 13 / H) * vecExp (M.transVec h s a) (cert r β δ hist k)) := by positivity
    calc cert r β δ hist (H - h) s ≤ 1 := hcert1
      _ ≤ 84 * H := by linarith
      _ ≤ _ := le_add_of_nonneg_left this
  · -- main case
    push Not at htriv
    obtain ⟨hn0, hαlt⟩ := htriv
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    set αn := alphaKL (Fintype.card S) (Fintype.card A) H δ n / n with hαn_def
    set αs := alphaStar (Fintype.card S) (Fintype.card A) H δ n / n with hαs_def
    have hαn0 : 0 ≤ αn := div_nonneg (alphaKL_nonneg _ _ _ hδ hδ1 _) (Nat.cast_nonneg _)
    have hαs0 : 0 ≤ αs := div_nonneg (alphaStar_nonneg _ _ _ hδ hδ1 _) (Nat.cast_nonneg _)
    have hαsn : αs ≤ αn := alphaStar_div_le_alphaKL_div _ _ _ (one_le_card_of_elem s) _ _
    have hρ : rateMin (alphaKL (Fintype.card S) (Fintype.card A) H δ) n = αn :=
      rateMin_eq_div hn0 hαlt
    have hρs : rateMin (alphaStar (Fintype.card S) (Fintype.card A) H δ) n = αs :=
      rateMin_eq_div hn0 (hαsn.trans_lt hαlt)
    rw [hρ, hρs]
    have hσ : 0 ≤ √(vecVar (M.transVec h s a) (expValue M H β π.extend (h + 1)) * αs) :=
      Real.sqrt_nonneg _
    have hkl := hc.klDiv_le_ofReal h s a hnpos
    -- drop the clip
    have hcert : cert r β δ hist (H - h) s ≤ Real.exp (β * r h s a) *
        (3 * bonus (Fintype.card S) (Fintype.card A) H β δ k n (empTrans hist h s a)
            (optZ r β δ hist k).1 (optZ r β δ hist k).2
          + (1 + 3 / H) * vecExp (empTrans hist h s a) (cert r β δ hist k)) := by
      rw [cert_sub_eq]
      simp only [hβ.not_gt, ↓reduceIte]
      split_ifs with h0
      · exact absurd h0 hn0
      · push_cast
        exact min_le_right _ _
    -- step (i), with the range `1` of the certificate
    have hi := vecExp_le_one_add_mul_vecExp_add hp hp1 (measureReal_trans_singleton M h s a)
      hαn0 zero_le_one hH hg hkl
    -- facts at the next step
    have hZ : ∀ s', optExpValue M H β (h + 1) s'
        ∈ Set.Icc ((optZ r β δ hist k).2 s') ((optZ r β δ hist k).1 s') := by
      intro s'; rw [hk, ← sub_succ_eq]
      exact optExpValue_mem_Icc_optZ_of_neg hM hr hβ hδ hδ1 hc h.succ s'
    have hRπ : ∀ s', expValue M H β π.extend (h + 1) s' ≤ ringZ M r β δ hist k s' := by
      intro s'; rw [hk, ← sub_succ_eq]
      exact (optZ_fst_le_ringZ_and_expValue_le_of_neg hM hr hβ h.succ s').2
    have hGap : ∀ s', ringZ M r β δ hist k s' - (optZ r β δ hist k).2 s'
        ≤ cert r β δ hist k s' := by
      intro s'; rw [hk, ← sub_succ_eq]
      exact ringZ_sub_optZ_snd_le_cert_of_neg hM hr hβ hδ hδ1 hc h.succ s'
    have hR := rewardsIn_Icc_of_hasRewardFn hM hr
    have hπZ : ∀ s', optExpValue M H β (h + 1) s' ≤ expValue M H β π.extend (h + 1) s' := fun s' ↦
      optExpValue_le_expValue M H β hR hβ π.measurable_extend _ _
    have hZl : ∀ s', (optZ r β δ hist k).2 s'
        ∈ Set.Icc (Real.exp (β * k)) (Real.exp (β * k) + B) := fun s' ↦ by
        have := optZ_mem_of_neg (hist := hist) hr hβ hδ hδ1 k (by omega) s'
        exact ⟨this.2.1, by rw [hB]; linarith [this.1, this.2.2]⟩
    have hZπ : ∀ s', expValue M H β π.extend (h + 1) s'
        ∈ Set.Icc (Real.exp (β * k)) (Real.exp (β * k) + B) := fun s' ↦ by
        have := expValue_mem_Icc_of_neg hM hr hβ π h.succ s'
        rw [sub_succ_eq, Fin.val_succ] at this
        exact ⟨this.1, by rw [hB]; linarith [this.2]⟩
    have hΔ : vecExp (M.transVec h s a)
        (fun s' ↦ |(optZ r β δ hist k).2 s' - expValue M H β π.extend (h + 1) s'|)
        ≤ vecExp (M.transVec h s a) (cert r β δ hist k) := by
      refine vecExp_mono hq0 fun s' ↦ ?_
      rw [abs_of_nonpos (sub_nonpos.2 ((hZ s').1.trans (hπZ s')))]
      linarith [hRπ s', hGap s']
    -- step (ii)
    have hii := bonusTerm_le_of_klDiv_le hp hp1 (measureReal_trans_singleton M h s a) hαs0 hαsn
      hB0 hH hZl hZπ hΔ hkl
    rw [← bonus_of_not_pos (Zt := (optZ r β δ hist k).1) (hβ := hβ.not_gt)] at hii
    -- step (iii)
    have hiii := three_mul_add_le hH hσ hΔp hαn0 zero_le_one hB1 le_rfl hii hi
    have e84 : Real.exp (β * r h s a) * (84 * H * 1 * αn) ≤ 84 * H * αn := by
      rw [mul_one]
      exact mul_le_of_le_one_left (by positivity) he1
    calc cert r β δ hist (H - h) s ≤ _ := hcert
      _ ≤ _ := mul_le_mul_of_nonneg_left hiii he0.le
      _ ≤ _ := by rw [mul_add]; exact add_le_add le_rfl e84

end TrueKernel

/-! ### On the good event of a run -/

section Run

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℕ → Ω → Policy S A H} {Y : ℕ → Ω → Traj S H}
  {s₁ : S} {ω : Ω}

/-- **Lemma 12** (concentration of the optimal exponential value, `β < 0`): on the good event,
for every episode `t` and every visited pair,
`|(p̂_h^t - p_h) Z*_{h+1}| ≤ b_h^t + (1/H) p̂_h^t|Z*_{h+1} - Z̲^t_{h+1}|`. -/
lemma abs_vecExp_sub_le_bonusAt_add_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hω : ω ∈ goodEvent X Y M s₁ β δ) (t : ℕ) (h : Fin H) (s : S) (a : A)
    (hn : 0 < visitCountAt X Y h s a t ω) :
    |vecExp (empTransAt X Y h s a t ω) (optExpValue M H β (h + 1))
        - vecExp (M.transVec h s a) (optExpValue M H β (h + 1))|
      ≤ bonusAt X Y r β δ t ω h s a + 1 / H * vecExp (empTransAt X Y h s a t ω)
          (fun s' ↦ |optExpValue M H β (h + 1) s' - ZlowerAt X Y r β δ t ω h.succ s'|) := by
  have := abs_vecExp_sub_le_bonus_add_of_neg hM hr hβ hδ hδ1 (histConcentration_histAt hω t) h s
    a hn
  simp only [bonusAt, ZtildeAt, ZlowerAt, sub_succ_eq]
  exact this

/-- **Lemma 13** (optimism and pessimism, `β < 0`): on the good event,
`Z̲_h^t ≤ Z*_h ≤ Z̃_h^t`. -/
lemma optExpValue_mem_Icc_ZlowerAt_ZtildeAt_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hω : ω ∈ goodEvent X Y M s₁ β δ) (t : ℕ) (h : Fin (H + 1)) (s : S) :
    optExpValue M H β h s ∈ Set.Icc (ZlowerAt X Y r β δ t ω h s) (ZtildeAt X Y r β δ t ω h s) :=
  optExpValue_mem_Icc_optZ_of_neg hM hr hβ hδ hδ1 (histConcentration_histAt hω t) h s

/-- **Lemma 13** for the backups (`β < 0`): on the good event, `U̲_h^t ≤ U*_h ≤ Ũ_h^t`. -/
lemma optExpQ_mem_Icc_UlowerAt_UtildeAt_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hω : ω ∈ goodEvent X Y M s₁ β δ) (t : ℕ) (h : Fin H) (s : S) (a : A) :
    optExpQ M H β h s a ∈ Set.Icc (UlowerAt X Y r β δ t ω h s a) (UtildeAt X Y r β δ t ω h s a) :=
  optExpQ_mem_Icc_stepUAt_of_neg hM hr hβ hδ hδ1 (histConcentration_histAt hω t) h s a

omit [MeasurableSingletonClass A] in
/-- **The ring value is at most one** (`β < 0`): `Z̊_h^t ≤ 1` and `Ů_h^t ≤ 1`. -/
lemma ringZAt_le_one_of_neg (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (t : ℕ) (ω : Ω)
    (h : Fin (H + 1)) (s : S) : ringZAt X Y M r β δ t ω h s ≤ 1 :=
  ringZ_le_one_of_neg hr hβ _ s

omit [MeasurableSingletonClass A] in
/-- The ring backup of a run is at most one (`β < 0`). -/
lemma ringUAt_le_one_of_neg (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (t : ℕ) (ω : Ω)
    (h : Fin H) (s : S) (a : A) : ringUAt X Y M r β δ t ω h s a ≤ 1 :=
  ringU_le_one_of_neg hr hβ h s a

/-- **Lemma 15** (the ring value is an upper bound, `β < 0`; no event is needed):
`Z̃_h^t ≤ Z̊_h^t` and `Z^π_h ≤ Z̊_h^t` for `π = π^{t+1}`. -/
lemma ZtildeAt_le_ringZAt_and_expValue_le_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (t : ℕ) (ω : Ω) (h : Fin (H + 1))
    (s : S) :
    ZtildeAt X Y r β δ t ω h s ≤ ringZAt X Y M r β δ t ω h s
      ∧ expValue M H β (greedyAt X Y r β δ t ω).extend h s ≤ ringZAt X Y M r β δ t ω h s :=
  optZ_fst_le_ringZ_and_expValue_le_of_neg hM hr hβ h s

/-- **Lemma 15** for the backups (`β < 0`): `Ũ_h^t ≤ Ů_h^t` and `U^π_h ≤ Ů_h^t`. -/
lemma UtildeAt_le_ringUAt_and_expQ_le_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (t : ℕ) (ω : Ω) (h : Fin H) (s : S)
    (a : A) :
    UtildeAt X Y r β δ t ω h s a ≤ ringUAt X Y M r β δ t ω h s a
      ∧ expQ M H β (greedyAt X Y r β δ t ω).extend h s a ≤ ringUAt X Y M r β δ t ω h s a :=
  stepUAt_fst_le_ringU_and_expQ_le_of_neg hM hr hβ h s a

/-- **Lemma 16** (one-step certificate bound, `β < 0`): on the good event, for a visited pair,
`Ů_h^t - U̲_h^t ≤ e^{β r_h} (3 b_h^t + (1 + 3/H) p̂_h^t(Z̊^t_{h+1} - Z̲^t_{h+1}))`. -/
lemma ringUAt_sub_UlowerAt_le_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hω : ω ∈ goodEvent X Y M s₁ β δ) (t : ℕ) (h : Fin H) (s : S) (a : A)
    (hn : 0 < visitCountAt X Y h s a t ω) :
    ringUAt X Y M r β δ t ω h s a - UlowerAt X Y r β δ t ω h s a
      ≤ Real.exp (β * r h s a) * (3 * bonusAt X Y r β δ t ω h s a
        + (1 + 3 / H) * vecExp (empTransAt X Y h s a t ω)
          (ringZAt X Y M r β δ t ω h.succ - ZlowerAt X Y r β δ t ω h.succ)) := by
  have := ringU_sub_stepUAt_snd_le_of_neg hM hr hβ hδ hδ1 (histConcentration_histAt hω t) h s a
    hn
  simp only [bonusAt, ZtildeAt, ZlowerAt, ringZAt, sub_succ_eq]
  exact this

/-- **The certificate dominates the ring–pessimistic gap** (`β < 0`): on the good event,
`Z̊_h^t - Z̲_h^t ≤ π_h G_h^t`. -/
lemma ringZAt_sub_ZlowerAt_le_certAt_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hω : ω ∈ goodEvent X Y M s₁ β δ) (t : ℕ) (h : Fin (H + 1)) (s : S) :
    ringZAt X Y M r β δ t ω h s - ZlowerAt X Y r β δ t ω h s ≤ certAt X Y r β δ t ω h s :=
  ringZ_sub_optZ_snd_le_cert_of_neg hM hr hβ hδ hδ1 (histConcentration_histAt hω t) h s

/-- **Lemma 14** (the certificate dominates the suboptimality gap, `β < 0`): on the good event,
`Z^π_h - Z*_h ≤ π_h G_h^t` for `π = π^{t+1}`. -/
lemma expValue_sub_optExpValue_le_certAt_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hω : ω ∈ goodEvent X Y M s₁ β δ) (t : ℕ) (h : Fin (H + 1)) (s : S) :
    expValue M H β (greedyAt X Y r β δ t ω).extend h s - optExpValue M H β h s
      ≤ certAt X Y r β δ t ω h s :=
  expValue_sub_optExpValue_le_cert_of_neg hM hr hβ hδ hδ1 (histConcentration_histAt hω t) h s

/-- **Soundness of the stopping rule** (`β < 0`): on the good event, if the stopping condition
holds after `t` episodes, the greedy policy `π^{t+1}` is `ε`-optimal from `s₁`. -/
lemma optEntropicValue_sub_entropicValue_greedyAt_le_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hω : ω ∈ goodEvent X Y M s₁ β δ) {ε : ℝ} (hε : 0 ≤ ε) {t : ℕ}
    (hstop : stopCond r β δ ε s₁ (histAt X Y t ω)) :
    optEntropicValue M H β 0 s₁
      - entropicValue M H β (greedyAt X Y r β δ t ω).extend 0 s₁ ≤ ε :=
  optEntropicValue_sub_entropicValue_le_of_stopCond_of_neg hM hr hβ hδ hδ1
    (histConcentration_histAt hω t) hε hstop

/-- **Certificate recursion under the true kernel** (`β < 0`): on the good event, with
`π = π^{t+1}` and `a = π_h(s)`,
`π_h G_h^t(s) ≤ e^{β r_h(s, a)} (36 √(Var_{p_h}(Z^π_{h+1})(s, a) ρ*)
+ (1 + 13/H) p_h(π_{h+1} G^t_{h+1})) + 84 H ρ` with the rate terms `ρ = min {α(n)/n, 1}`,
`ρ* = min {α*(n)/n, 1}`. -/
lemma certAt_le_of_neg (hM : M.HasRewardFn r) (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hω : ω ∈ goodEvent X Y M s₁ β δ) (t : ℕ) (h : Fin H)
    (s : S) :
    certAt X Y r β δ t ω h.castSucc s ≤ Real.exp (β * r h s (greedyAt X Y r β δ t ω h s)) *
      (36 * √(vecVar (M.transVec h s (greedyAt X Y r β δ t ω h s))
          (expValue M H β (greedyAt X Y r β δ t ω).extend (h + 1))
          * starRateMinAt X Y δ h s (greedyAt X Y r β δ t ω h s) t ω)
        + (1 + 13 / H) * vecExp (M.transVec h s (greedyAt X Y r β δ t ω h s))
          (certAt X Y r β δ t ω h.succ))
      + 84 * H * klRateMinAt X Y δ h s (greedyAt X Y r β δ t ω h s) t ω := by
  have := cert_le_of_neg hM hr hβ hδ hδ1 (histConcentration_histAt hω t) h s
  simp only [certAt, sub_succ_eq, Fin.val_castSucc]
  exact this

end Run

end Essakine2026Tight
