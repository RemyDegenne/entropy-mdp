/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.EV2026.AnalysisCommon

/-!
# Analysis of Entropic-BPI for `β > 0` on the good event

Essakine, Vernade (2026), Appendix B.1, Lemmas 7–11 and the certificate recursion under the true
kernel (blueprint chapter "Analysis of Entropic-BPI for β > 0"). For `β > 0` the values lie in
`[1, e^{β j}]`, the optimal exponential value is a maximum, the greedy policy maximizes the
optimistic backup and the ring value `Z̊` is a lower bound on `Z̲` and on the value of the greedy
policy.

The lemmas are first proved at a history `hist` satisfying the concentration inequalities of the
good event (`HistConcentration`), then on the good event of a run (the quantities of a run are
functions of its history, so no run hypothesis is needed):

* **Lemma 7** (concentration): `abs_vecExp_sub_le_bonus_add_of_pos`,
  `abs_vecExp_sub_le_bonusAt_add_of_pos`;
* **Lemma 8** (optimism): `optExpValue_mem_Icc_optZ_of_pos`, `optExpQ_mem_Icc_stepUAt_of_pos`,
  `optExpValue_mem_Icc_ZlowerAt_ZtildeAt_of_pos`, `optExpQ_mem_Icc_UlowerAt_UtildeAt_of_pos`;
* the ring value is at least one: `one_le_ringZ_of_pos`, `one_le_ringU_of_pos`;
* **Lemma 10** (the ring value is a lower bound, no event needed):
  `ringZ_le_optZ_snd_and_expValue_of_pos`, `ringU_le_stepUAt_snd_and_expQ_of_pos` and their run
  versions;
* **Lemma 11** (one-step certificate bound): `stepUAt_fst_sub_ringU_le_of_pos`,
  `UtildeAt_sub_ringUAt_le_of_pos`;
* the certificate dominates the optimistic–ring gap: `optZ_fst_sub_ringZ_le_cert_of_pos`,
  `ZtildeAt_sub_ringZAt_le_certAt_of_pos`;
* **Lemma 9** (the certificate dominates the suboptimality gap):
  `optExpValue_sub_expValue_le_cert_of_pos`, `optExpValue_sub_expValue_le_certAt_of_pos`;
* soundness of the stopping rule: `optEntropicValue_sub_entropicValue_le_of_stopCond_of_pos`,
  `optEntropicValue_sub_entropicValue_greedyAt_le_of_pos`;
* the certificate recursion under the true kernel: `cert_le_of_pos`, `certAt_le_of_pos`.
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
/-- Range of the optimal exponential values for `β > 0`: `[1, e^{β (H - h)}]`. -/
lemma optExpValue_mem_Icc_of_pos [Finite S] [Finite A] (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hβ : 0 < β) (h : Fin (H + 1)) (s : S) :
    optExpValue M H β h s ∈ Set.Icc 1 (Real.exp (β * (H - h : ℕ))) :=
  mem_Icc_one_exp_of_pos hβ (Nat.cast_nonneg _)
    (optExpValue_mem_Icc M H β (rewardsIn_Icc_of_hasRewardFn hM hr) hβ.ne' h s)

omit [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] in
/-- Range of the exponential values for `β > 0`: `[1, e^{β (H - h)}]`. -/
lemma expValue_mem_Icc_of_pos [Finite S] (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hβ : 0 < β) (π : Policy S A H) (h : Fin (H + 1)) (s : S) :
    expValue M H β π.extend h s ∈ Set.Icc 1 (Real.exp (β * (H - h : ℕ))) :=
  mem_Icc_one_exp_of_pos hβ (Nat.cast_nonneg _)
    (expValue_mem_Icc M H β (rewardsIn_Icc_of_hasRewardFn hM hr) π.measurable_extend h s)

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- Ranges of the optimistic and pessimistic values for `β > 0`. -/
lemma optZ_mem_of_pos (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (j : ℕ) (hj : j ≤ H) (s : S) :
    (optZ r β δ hist j).2 s ≤ (optZ r β δ hist j).1 s ∧ 1 ≤ (optZ r β δ hist j).2 s
      ∧ (optZ r β δ hist j).1 s ≤ Real.exp (β * j) := by
  have h := optZ_mem hist r β δ hr hδ hδ1 j hj s
  exact ⟨h.1, (mem_Icc_one_exp_of_pos hβ j.cast_nonneg h.2.2).1,
    (mem_Icc_one_exp_of_pos hβ j.cast_nonneg h.2.1).2⟩

end Ranges

/-! ### Concentration and optimism -/

section Optimism

/-- **Lemma 7** (concentration of the optimal exponential value, `β > 0`), at a history
satisfying the concentration inequalities: for a visited pair,
`|(p̂ - p) Z*_{h+1}| ≤ b + (1/H) p̂|Z̃_{h+1} - Z*_{h+1}|`. -/
lemma abs_vecExp_sub_le_bonus_add_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (h : Fin H) (s : S) (a : A)
    (hn : 0 < visitCount hist h s a) :
    |vecExp (empTrans hist h s a) (optExpValue M H β (h + 1))
        - vecExp (M.transVec h s a) (optExpValue M H β (h + 1))|
      ≤ bonus (Fintype.card S) (Fintype.card A) H β δ (H - 1 - h) (visitCount hist h s a)
          (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1 (optZ r β δ hist (H - 1 - h)).2
        + 1 / H * vecExp (empTrans hist h s a)
          (fun s' ↦ |(optZ r β δ hist (H - 1 - h)).1 s' - optExpValue M H β (h + 1) s'|) := by
  set k := H - 1 - (h : ℕ) with hk
  have hB : 0 ≤ Real.exp (β * k) := (Real.exp_pos _).le
  have hf : ∀ s', optExpValue M H β (h + 1) s' ∈ Set.Icc 1 (1 + Real.exp (β * k)) := fun s' ↦ by
    have := optExpValue_mem_Icc_of_pos hM hr hβ h.succ s'
    rw [sub_succ_eq, Fin.val_succ] at this
    exact ⟨this.1, by linarith [this.2]⟩
  have hg : ∀ s', (optZ r β δ hist k).1 s' ∈ Set.Icc 1 (1 + Real.exp (β * k)) := fun s' ↦ by
    have := optZ_mem_of_pos (hist := hist) hr hβ hδ hδ1 k (by omega) s'
    exact ⟨this.2.1.trans this.1, by linarith [this.2.2]⟩
  have hbern := hc.bern h s a hn
  simp only [bernRange, hβ, ↓reduceIte] at hbern
  have := abs_vecExp_sub_le_bonus_add (empTrans_nonneg hist h s a) (sum_empTrans hist h s a)
    (measureReal_trans_singleton M h s a)
    (div_nonneg (alphaStar_nonneg _ _ _ hδ hδ1 _) (Nat.cast_nonneg _))
    (alphaStar_div_le_alphaKL_div _ _ _ (one_le_card_of_elem s) _ _) hB (one_le_cast_of_fin h)
    hf hg (hc.klDiv_le_ofReal h s a hn) hbern
  rwa [bonus_of_pos (hβ := hβ)]

/-- The optimistic backup dominates `U*` at a step whose next-step values bracket `Z*`
(**Lemma 8**, upper bound, `β > 0`). -/
lemma optExpQ_le_stepUAt_fst_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (h : Fin H)
    (hZ : ∀ s', optExpValue M H β (h + 1) s'
      ∈ Set.Icc ((optZ r β δ hist (H - 1 - h)).2 s') ((optZ r β δ hist (H - 1 - h)).1 s'))
    (s : S) (a : A) : optExpQ M H β h s a ≤ (stepUAt r β δ hist h s a).1 := by
  have hQ := optExpQ_mem_Icc M H β (rewardsIn_Icc_of_hasRewardFn hM hr) hβ.ne' h.is_lt s a
  rw [cast_sub_castSucc_eq] at hQ
  have hQ' := mem_Icc_one_exp_of_pos hβ (by positivity) hQ
  simp only [stepUAt, stepU, hβ, ↓reduceIte]
  split_ifs with hn
  · exact hQ'.2
  refine le_min hQ'.2 ?_
  have h7 := abs_vecExp_sub_le_bonus_add_of_pos hM hr hβ hδ hδ1 hc h s a (Nat.pos_of_ne_zero hn)
  have hp := empTrans_nonneg hist h s a
  rw [vecExp_abs_sub_eq_of_le _ fun s' ↦ (hZ s').2] at h7
  rw [optExpQ_of_hasRewardFn_eq_vecExp M H β hM]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  set u := (1 / H : ℝ)
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1 := by
    rw [div_le_one (by linarith [one_le_cast_of_fin h])]; exact one_le_cast_of_fin h
  have e1 := vecExp_mono hp fun s' ↦ (hZ s').1
  have e2 := vecExp_mono hp fun s' ↦ (hZ s').2
  rw [vecExp_sub]
  have e3 : u * (vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1
      - vecExp (empTrans hist h s a) (optExpValue M H β (h + 1)))
      ≤ vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1
      - vecExp (empTrans hist h s a) (optExpValue M H β (h + 1)) :=
    mul_le_of_le_one_left (by linarith) hu1
  have e4 : 0 ≤ u * (vecExp (empTrans hist h s a) (optExpValue M H β (h + 1))
      - vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).2) :=
    mul_nonneg hu0 (by linarith)
  have := (abs_le.1 h7).1
  nlinarith

/-- The pessimistic backup is dominated by `U*` at a step whose next-step values bracket `Z*`
(**Lemma 8**, lower bound, `β > 0`). -/
lemma stepUAt_snd_le_optExpQ_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (h : Fin H)
    (hZ : ∀ s', optExpValue M H β (h + 1) s'
      ∈ Set.Icc ((optZ r β δ hist (H - 1 - h)).2 s') ((optZ r β δ hist (H - 1 - h)).1 s'))
    (s : S) (a : A) : (stepUAt r β δ hist h s a).2 ≤ optExpQ M H β h s a := by
  have hQ := optExpQ_mem_Icc M H β (rewardsIn_Icc_of_hasRewardFn hM hr) hβ.ne' h.is_lt s a
  rw [cast_sub_castSucc_eq] at hQ
  have hQ' := mem_Icc_one_exp_of_pos hβ (by positivity) hQ
  simp only [stepUAt, stepU, hβ, ↓reduceIte]
  split_ifs with hn
  · exact hQ'.1
  refine max_le hQ'.1 ?_
  have h7 := abs_vecExp_sub_le_bonus_add_of_pos hM hr hβ hδ hδ1 hc h s a (Nat.pos_of_ne_zero hn)
  have hp := empTrans_nonneg hist h s a
  rw [vecExp_abs_sub_eq_of_le _ fun s' ↦ (hZ s').2] at h7
  rw [optExpQ_of_hasRewardFn_eq_vecExp M H β hM]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  set u := (1 / H : ℝ)
  have hu0 : 0 ≤ u := by positivity
  have e1 := vecExp_mono hp fun s' ↦ (hZ s').1
  have e2 := vecExp_mono hp fun s' ↦ (hZ s').2
  rw [vecExp_sub]
  have e4 : 0 ≤ u * (vecExp (empTrans hist h s a) (optExpValue M H β (h + 1))
      - vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).2) :=
    mul_nonneg hu0 (by linarith)
  have := (abs_le.1 h7).2
  nlinarith

/-- **Lemma 8** (optimism and pessimism, `β > 0`), at a history satisfying the concentration
inequalities: `Z̲_h ≤ Z*_h ≤ Z̃_h` at every step. -/
lemma optExpValue_mem_Icc_optZ_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (h : Fin (H + 1)) (s : S) :
    optExpValue M H β h s
      ∈ Set.Icc ((optZ r β δ hist (H - h)).2 s) ((optZ r β δ hist (H - h)).1 s) := by
  have hR := rewardsIn_Icc_of_hasRewardFn hM hr
  induction h using Fin.reverseInduction generalizing s with
  | last => simp [Fin.val_last, optExpValue_of_le M H β hR hβ.ne' le_rfl, optZ_zero]
  | cast i ih =>
    have ih' : ∀ s', optExpValue M H β (i + 1) s'
        ∈ Set.Icc ((optZ r β δ hist (H - 1 - i)).2 s') ((optZ r β δ hist (H - 1 - i)).1 s') := by
      intro s'; rw [← sub_succ_eq]; exact ih s'
    rw [Fin.val_castSucc, optZ_eq]
    simp only [hβ, ↓reduceIte]
    constructor
    · rw [← argmax_spec]
      exact (stepUAt_snd_le_optExpQ_of_pos hM hr hβ hδ hδ1 hc i ih' s _).trans
        (optExpQ_le_optExpValue M H β hR hβ i.is_lt s _)
    · rw [optExpValue_succ_eq M H β hR hβ.ne' i.is_lt]
      exact (optExpQ_le_stepUAt_fst_of_pos hM hr hβ hδ hδ1 hc i ih' s _).trans
        (Function.le_max (fun a ↦ (stepUAt r β δ hist i s a).1) _)

/-- **Lemma 8** for the backups (`β > 0`): `U̲_h ≤ U*_h ≤ Ũ_h`. -/
lemma optExpQ_mem_Icc_stepUAt_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (h : Fin H) (s : S) (a : A) :
    optExpQ M H β h s a ∈ Set.Icc (stepUAt r β δ hist h s a).2 (stepUAt r β δ hist h s a).1 := by
  have hZ : ∀ s', optExpValue M H β (h + 1) s'
      ∈ Set.Icc ((optZ r β δ hist (H - 1 - h)).2 s') ((optZ r β δ hist (H - 1 - h)).1 s') := by
    intro s'; rw [← sub_succ_eq]
    exact optExpValue_mem_Icc_optZ_of_pos hM hr hβ hδ hδ1 hc h.succ s'
  exact ⟨stepUAt_snd_le_optExpQ_of_pos hM hr hβ hδ hδ1 hc h hZ s a,
    optExpQ_le_stepUAt_fst_of_pos hM hr hβ hδ hδ1 hc h hZ s a⟩

end Optimism

/-! ### The ring value -/

section Ring

omit [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- The ring backup of values at least one is at least one (`β > 0`). -/
lemma one_le_ringUAux_of_pos {nS nA k n : ℕ} {rr : ℝ} (hrr : 0 ≤ rr) (hβ : 0 < β)
    {p phat Zr Zt Zl : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) (hZr : ∀ s, 1 ≤ Zr s) :
    1 ≤ ringUAux nS nA H β δ k n rr p phat Zr Zt Zl := by
  have h1 : 1 ≤ vecExp p Zr := by
    have := vecExp_mono hp (f := fun _ ↦ (1 : ℝ)) hZr
    rwa [vecExp_const, hp1, one_mul] at this
  have he : 1 ≤ Real.exp (β * rr) := Real.one_le_exp (mul_nonneg hβ.le hrr)
  have hQ : 1 ≤ Real.exp (β * rr) * vecExp p Zr := one_le_mul_of_one_le_of_one_le he h1
  simp only [ringUAux, hβ, ↓reduceIte]
  split_ifs
  · exact le_min hQ le_rfl
  · exact le_min hQ (le_max_left _ _)

omit [MeasurableSingletonClass A] in
/-- **The ring value is at least one** (`β > 0`), at every number of steps to go. -/
lemma one_le_ringZ_of_pos (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (j : ℕ) (s : S) :
    1 ≤ ringZ M r β δ hist j s := by
  induction j generalizing s with
  | zero => exact le_rfl
  | succ k ih =>
    change 1 ≤ ringZStep M r β δ hist k (ringZ M r β δ hist k) s
    simp only [ringZStep]
    split_ifs with hk
    · exact one_le_ringUAux_of_pos (hr _ _ _).1 hβ (M.transVec_nonneg _ _ _)
        (M.sum_transVec _ _ _) ih
    · exact ih s

omit [MeasurableSingletonClass A] in
/-- **The ring backup is at least one** (`β > 0`). -/
lemma one_le_ringU_of_pos (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (h : Fin H) (s : S)
    (a : A) : 1 ≤ ringU M r β δ hist h s a :=
  one_le_ringUAux_of_pos (hr h s a).1 hβ (M.transVec_nonneg h s a) (M.sum_transVec h s a)
    (one_le_ringZ_of_pos hr hβ _)

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- `Ů_h ≤ U̲_h` when `Z̊_{h+1} ≤ Z̲_{h+1}` (`β > 0`). -/
lemma ringU_le_stepUAt_snd_of_pos (hβ : 0 < β) (h : Fin H)
    (hZ : ∀ s', ringZ M r β δ hist (H - 1 - h) s' ≤ (optZ r β δ hist (H - 1 - h)).2 s')
    (s : S) (a : A) : ringU M r β δ hist h s a ≤ (stepUAt r β δ hist h s a).2 := by
  have hp := empTrans_nonneg hist h s a
  simp only [ringU, ringUAux, stepUAt, stepU, hβ, ↓reduceIte]
  split_ifs with hn
  · exact min_le_right _ _
  · refine (min_le_right _ _).trans (max_le_max le_rfl ?_)
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have e1 := vecExp_mono hp hZ
    rw [vecExp_sub, vecExp_sub]
    have hu0 : (0 : ℝ) ≤ 1 / H := by positivity
    have := mul_nonneg hu0 (sub_nonneg.2 e1)
    linarith

omit [MeasurableSingletonClass A] in
/-- `Ů_h ≤ U^π_h` when `Z̊_{h+1} ≤ Z^π_{h+1}` (`β > 0`). -/
lemma ringU_le_expQ_of_pos (hM : M.HasRewardFn r) (hβ : 0 < β) (π : Policy S A H) (h : Fin H)
    (hZ : ∀ s', ringZ M r β δ hist (H - 1 - h) s' ≤ expValue M H β π.extend (h + 1) s') (s : S)
    (a : A) :
    ringU M r β δ hist h s a ≤ expQ M H β π.extend h s a := by
  rw [expQ_of_hasRewardFn_eq_vecExp M H β hM]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (vecExp_mono (M.transVec_nonneg h s a) hZ)
    (Real.exp_pos _).le)
  simp only [ringU, ringUAux, hβ, ↓reduceIte]
  split_ifs <;> exact min_le_left _ _

/-- **Lemma 10** (the ring value is a lower bound, `β > 0`; no event is needed):
`Z̊_h ≤ Z̲_h` and `Z̊_h ≤ Z^π_h` for the greedy policy `π` of the history. -/
lemma ringZ_le_optZ_snd_and_expValue_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (h : Fin (H + 1)) (s : S) :
    ringZ M r β δ hist (H - h) s ≤ (optZ r β δ hist (H - h)).2 s
      ∧ ringZ M r β δ hist (H - h) s ≤ expValue M H β (greedy r β δ hist).extend h s := by
  have hR := rewardsIn_Icc_of_hasRewardFn hM hr
  induction h using Fin.reverseInduction generalizing s with
  | last =>
    simp [Fin.val_last, optZ_zero, ringZ_zero,
      expValue_of_le M H β (greedy r β δ hist).measurable_extend le_rfl]
  | cast i ih =>
    have ih1 : ∀ s', ringZ M r β δ hist (H - 1 - i) s' ≤ (optZ r β δ hist (H - 1 - i)).2 s' :=
      fun s' ↦ by rw [← sub_succ_eq]; exact (ih s').1
    have ih2 : ∀ s', ringZ M r β δ hist (H - 1 - i) s'
        ≤ expValue M H β (greedy r β δ hist).extend (i + 1) s' :=
      fun s' ↦ by rw [← sub_succ_eq]; exact (ih s').2
    rw [Fin.val_castSucc, ringZ_sub_eq, optZ_eq,
      expValue_succ M H β hR (greedy r β δ hist).measurable_extend i.is_lt, Policy.extend_fin]
    simp only [hβ, ↓reduceIte]
    exact ⟨(ringU_le_stepUAt_snd_of_pos hβ i ih1 s _).trans
        (Function.le_max (fun a ↦ (stepUAt r β δ hist i s a).2) _),
      ringU_le_expQ_of_pos hM hβ (greedy r β δ hist) i ih2 s (greedy r β δ hist i s)⟩

/-- **Lemma 10** for the backups (`β > 0`): `Ů_h ≤ U̲_h` and `Ů_h ≤ U^π_h`. -/
lemma ringU_le_stepUAt_snd_and_expQ_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (h : Fin H) (s : S) (a : A) :
    ringU M r β δ hist h s a ≤ (stepUAt r β δ hist h s a).2
      ∧ ringU M r β δ hist h s a ≤ expQ M H β (greedy r β δ hist).extend h s a :=
  ⟨ringU_le_stepUAt_snd_of_pos hβ h
      (fun s' ↦ by
        rw [← sub_succ_eq]; exact (ringZ_le_optZ_snd_and_expValue_of_pos hM hr hβ _ s').1) s a,
    ringU_le_expQ_of_pos hM hβ _ h
      (fun s' ↦ by
        rw [← sub_succ_eq]; exact (ringZ_le_optZ_snd_and_expValue_of_pos hM hr hβ _ s').2) s a⟩

end Ring

/-! ### The certificate -/

section Certificate

/-- **Lemma 11** (one-step certificate bound, `β > 0`), at a history satisfying the concentration
inequalities: for a visited pair,
`Ũ_h - Ů_h ≤ e^{β r_h} (3 b + (1 + 3/H) p̂(Z̃_{h+1} - Z̊_{h+1}))`. -/
lemma stepUAt_fst_sub_ringU_le_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (h : Fin H) (s : S) (a : A)
    (hn : 0 < visitCount hist h s a) :
    (stepUAt r β δ hist h s a).1 - ringU M r β δ hist h s a
      ≤ Real.exp (β * r h s a) *
        (3 * bonus (Fintype.card S) (Fintype.card A) H β δ (H - 1 - h) (visitCount hist h s a)
            (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1 (optZ r β δ hist (H - 1 - h)).2
          + (1 + 3 / H) * vecExp (empTrans hist h s a)
            ((optZ r β δ hist (H - 1 - h)).1 - ringZ M r β δ hist (H - 1 - h))) := by
  have hZ : ∀ s', optExpValue M H β (h + 1) s'
      ∈ Set.Icc ((optZ r β δ hist (H - 1 - h)).2 s') ((optZ r β δ hist (H - 1 - h)).1 s') := by
    intro s'; rw [← sub_succ_eq]
    exact optExpValue_mem_Icc_optZ_of_pos hM hr hβ hδ hδ1 hc h.succ s'
  have hRl : ∀ s', ringZ M r β δ hist (H - 1 - h) s' ≤ (optZ r β δ hist (H - 1 - h)).2 s' := by
    intro s'; rw [← sub_succ_eq]
    exact (ringZ_le_optZ_snd_and_expValue_of_pos hM hr hβ h.succ s').1
  have hR1 : ∀ s', 1 ≤ ringZ M r β δ hist (H - 1 - h) s' := one_le_ringZ_of_pos hr hβ _
  have hZs : ∀ s', optExpValue M H β (h + 1) s' ≤ Real.exp (β * (H - 1 - h : ℕ)) := by
    intro s'
    have := (optExpValue_mem_Icc_of_pos hM hr hβ h.succ s').2
    rwa [sub_succ_eq, Fin.val_succ] at this
  have hH := one_le_cast_of_fin h
  have hHpos : (0 : ℝ) < H := by linarith
  have hp := empTrans_nonneg hist h s a
  have hαn : 0 ≤ alphaKL (Fintype.card S) (Fintype.card A) H δ (visitCount hist h s a)
      / visitCount hist h s a := div_nonneg (alphaKL_nonneg _ _ _ hδ hδ1 _) (Nat.cast_nonneg _)
  have h7 := abs_vecExp_sub_le_bonus_add_of_pos hM hr hβ hδ hδ1 hc h s a hn
  rw [vecExp_abs_sub_eq_of_le _ fun s' ↦ (hZ s').2] at h7
  have h3 := vecExp_sub_vecExp_le_of_klDiv_le hp (sum_empTrans hist h s a)
    (measureReal_trans_singleton M h s a) hαn (Real.exp_pos _).le hH
    (f := optExpValue M H β (h + 1) - ringZ M r β δ hist (H - 1 - h))
    (fun s' ↦ ⟨sub_nonneg.2 ((hRl s').trans (hZ s').1), by
      simp only [Pi.sub_apply]; linarith [hZs s', hR1 s']⟩) (hc.klDiv_le_ofReal h s a hn)
  have hbB : (5 + 4 * (H : ℝ)) * Real.exp (β * (H - 1 - h : ℕ))
      * (alphaKL (Fintype.card S) (Fintype.card A) H δ (visitCount hist h s a)
        / visitCount hist h s a)
      ≤ bonus (Fintype.card S) (Fintype.card A) H β δ (H - 1 - h) (visitCount hist h s a)
          (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1
          (optZ r β δ hist (H - 1 - h)).2 := by
    rw [bonus_of_pos (hβ := hβ)]
    have : 0 ≤ 2 * √2 * √(vecVar (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1
        * (alphaStar (Fintype.card S) (Fintype.card A) H δ (visitCount hist h s a)
          / visitCount hist h s a)) := by positivity
    linarith
  have hb0 := bonus_nonneg (Fintype.card S) (Fintype.card A) H β hδ hδ1 (H - 1 - h)
    (visitCount hist h s a) (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1
    (optZ r β δ hist (H - 1 - h)).2
  have m1 := vecExp_mono hp hRl
  have m2 := vecExp_mono hp fun s' ↦ (hZ s').1
  have m3 := vecExp_mono hp fun s' ↦ (hZ s').2
  rw [vecExp_sub, vecExp_sub] at h3
  have hUt : (stepUAt r β δ hist h s a).1
      ≤ Real.exp (β * r h s a) * (vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1
        + bonus (Fintype.card S) (Fintype.card A) H β δ (H - 1 - h) (visitCount hist h s a)
          (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1 (optZ r β δ hist (H - 1 - h)).2
        + 1 / H * (vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1
          - vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).2)) := by
    simp only [stepUAt, stepU, hβ, hn.ne', ↓reduceIte, vecExp_sub]
    exact min_le_right _ _
  have hUr : ringU M r β δ hist h s a
      = min (Real.exp (β * r h s a) * vecExp (M.transVec h s a) (ringZ M r β δ hist (H - 1 - h)))
        (max 1 (Real.exp (β * r h s a) *
          (vecExp (empTrans hist h s a) (ringZ M r β δ hist (H - 1 - h))
            - bonus (Fintype.card S) (Fintype.card A) H β δ (H - 1 - h) (visitCount hist h s a)
              (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1
              (optZ r β δ hist (H - 1 - h)).2
            - 1 / H * (vecExp (empTrans hist h s a) (optZ r β δ hist (H - 1 - h)).1
              - vecExp (empTrans hist h s a) (ringZ M r β δ hist (H - 1 - h)))))) := by
    simp only [ringU, ringUAux, hβ, hn.ne', ↓reduceIte, vecExp_sub]
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
  have h7' := (abs_le.1 h7).2
  have hΔ : 0 ≤ u * (xt - xr) := mul_nonneg hu0 (by linarith)
  have e1 : u * (xt - xl) ≤ u * (xt - xr) := mul_le_mul_of_nonneg_left (by linarith) hu0
  rcases min_choice (e * yr) (max 1 (e * (xr - b - u * (xt - xr)))) with hm | hm <;> rw [hm]
  · have key : xt + b + u * (xt - xl) - yr ≤ 3 * b + (1 + 3 * u) * (xt - xr) := by
      linarith
    have := mul_le_mul_of_nonneg_left key he0
    linarith
  · have hR := le_max_right 1 (e * (xr - b - u * (xt - xr)))
    have key : xt + b + u * (xt - xl) - (xr - b - u * (xt - xr))
        ≤ 3 * b + (1 + 3 * u) * (xt - xr) := by linarith
    have := mul_le_mul_of_nonneg_left key he0
    linarith

/-- **The certificate dominates the optimistic–ring gap** (`β > 0`), at a history satisfying the
concentration inequalities: `Z̃_h - Z̊_h ≤ π_h G_h`. -/
lemma optZ_fst_sub_ringZ_le_cert_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (h : Fin (H + 1)) (s : S) :
    (optZ r β δ hist (H - h)).1 s - ringZ M r β δ hist (H - h) s ≤ cert r β δ hist (H - h) s := by
  induction h using Fin.reverseInduction generalizing s with
  | last => simp [optZ_zero, ringZ_zero, cert_zero]
  | cast i ih =>
    have ih' : ∀ s', ((optZ r β δ hist (H - 1 - i)).1 - ringZ M r β δ hist (H - 1 - i)) s'
        ≤ cert r β δ hist (H - 1 - i) s' := fun s' ↦ by rw [← sub_succ_eq]; exact ih s'
    rw [Fin.val_castSucc, optZ_fst_eq_stepUAt_greedy hist r β δ hβ i s, ringZ_sub_eq,
      cert_sub_eq]
    simp only [hβ, ↓reduceIte]
    have hUt := (stepUAt_mem hist r β δ hr hδ hδ1 i s (greedy r β δ hist i s)).2.1
    rw [cast_sub_castSucc_eq] at hUt
    have hUt' := (mem_Icc_one_exp_of_pos hβ (by positivity) hUt).2
    have hR1 := one_le_ringU_of_pos (M := M) (hist := hist) (δ := δ) hr hβ i s
      (greedy r β δ hist i s)
    have hclip : (stepUAt r β δ hist i s (greedy r β δ hist i s)).1
        - ringU M r β δ hist i s (greedy r β δ hist i s)
        ≤ Real.exp (β * ((H - 1 - i : ℕ) + 1)) := by linarith
    split_ifs with hn
    · exact hclip
    · refine le_min hclip ?_
      refine (stepUAt_fst_sub_ringU_le_of_pos hM hr hβ hδ hδ1 hc i s _
        (Nat.pos_of_ne_zero hn)).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
      push_cast
      have hH : (0 : ℝ) ≤ 1 + 3 / H := by positivity
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (vecExp_mono (empTrans_nonneg hist i s _) ih') hH)

/-- **Lemma 9** (the certificate dominates the suboptimality gap, `β > 0`), at a history
satisfying the concentration inequalities: `Z*_h - Z^π_h ≤ π_h G_h` for the greedy policy `π`. -/
lemma optExpValue_sub_expValue_le_cert_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (h : Fin (H + 1)) (s : S) :
    optExpValue M H β h s - expValue M H β (greedy r β δ hist).extend h s
      ≤ cert r β δ hist (H - h) s := by
  have h1 := (optExpValue_mem_Icc_optZ_of_pos hM hr hβ hδ hδ1 hc h s).2
  have h2 := (ringZ_le_optZ_snd_and_expValue_of_pos (δ := δ) (hist := hist) hM hr hβ h s).2
  have h3 := optZ_fst_sub_ringZ_le_cert_of_pos hM hr hβ hδ hδ1 hc h s
  linarith

/-- **Soundness of the stopping rule** (`β > 0`), at a history satisfying the concentration
inequalities: if the stopping condition holds, the greedy policy is `ε`-optimal. -/
lemma optEntropicValue_sub_entropicValue_le_of_stopCond_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) {ε : ℝ} (hε : 0 ≤ ε) {s₁ : S}
    (hstop : stopCond r β δ ε s₁ hist) :
    optEntropicValue M H β 0 s₁ - entropicValue M H β (greedy r β δ hist).extend 0 s₁
      ≤ ε := by
  have hR := rewardsIn_Icc_of_hasRewardFn hM hr
  simp only [stopCond, hβ, ↓reduceIte] at hstop
  have hg0 : 0 ≤ cert r β δ hist H s₁ := (cert_mem hist r β δ hδ hδ1 H le_rfl s₁).1
  have h1 : (optZ r β δ hist H).1 s₁ - ringZ M r β δ hist H s₁ ≤ cert r β δ hist H s₁ := by
    simpa only [Fin.val_zero, Nat.sub_zero] using
      optZ_fst_sub_ringZ_le_cert_of_pos hM hr hβ hδ hδ1 hc 0 s₁
  have h2 : ringZ M r β δ hist H s₁ ≤ expValue M H β (greedy r β δ hist).extend 0 s₁ := by
    simpa only [Fin.val_zero, Nat.sub_zero] using
      (ringZ_le_optZ_snd_and_expValue_of_pos hM hr hβ 0 s₁).2
  have h3 : optExpValue M H β 0 s₁ - expValue M H β (greedy r β δ hist).extend 0 s₁
      ≤ cert r β δ hist H s₁ := by
    simpa only [Fin.val_zero, Nat.sub_zero] using
      optExpValue_sub_expValue_le_cert_of_pos hM hr hβ hδ hδ1 hc 0 s₁
  refine optEntropicValue_sub_entropicValue_le_of_pos M H β hβ
    (expValue_pos M H β hR (greedy r β δ hist).measurable_extend 0 s₁) ?_
  set E := Real.exp (β * ε)
  have hE1 : 1 ≤ E := Real.one_le_exp (mul_nonneg hβ.le hε)
  have hEpos : 0 < E := Real.exp_pos _
  have hs' : E * cert r β δ hist H s₁ ≤ (E - 1) * (optZ r β δ hist H).1 s₁ := by
    have := mul_le_mul_of_nonneg_left hstop hEpos.le
    rwa [← mul_assoc, mul_div_cancel₀ _ hEpos.ne'] at this
  have hZ : (optZ r β δ hist H).1 s₁ - cert r β δ hist H s₁
      ≤ expValue M H β (greedy r β δ hist).extend 0 s₁ := by linarith
  have := mul_le_mul_of_nonneg_left hZ (by linarith : 0 ≤ E - 1)
  nlinarith

end Certificate

/-! ### The certificate under the true kernel -/

section TrueKernel

/-- **Certificate recursion under the true kernel** (`β > 0`), at a history satisfying the
concentration inequalities: with `a = π_h(s)` for the greedy policy `π`,
`π_h G_h(s) ≤ e^{β r_h(s, a)} (36 √(Var_{p_h}(Z^π_{h+1}) ρ*) + (1 + 13/H) p_h(π_{h+1} G_{h+1})
+ 84 H e^{β (H - h)} ρ)`. -/
lemma cert_le_of_pos (hM : M.HasRewardFn r) (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc : HistConcentration M β δ hist) (h : Fin H) (s : S) :
    cert r β δ hist (H - h) s ≤ Real.exp (β * r h s (greedy r β δ hist h s)) *
      (36 * √(vecVar (M.transVec h s (greedy r β δ hist h s))
          (expValue M H β (greedy r β δ hist).extend (h + 1))
          * rateMin (alphaStar (Fintype.card S) (Fintype.card A) H δ)
            (visitCount hist h s (greedy r β δ hist h s)))
        + (1 + 13 / H) * vecExp (M.transVec h s (greedy r β δ hist h s))
          (cert r β δ hist (H - 1 - h))
        + 84 * H * Real.exp (β * (H - h : ℕ))
          * rateMin (alphaKL (Fintype.card S) (Fintype.card A) H δ)
            (visitCount hist h s (greedy r β δ hist h s))) := by
  set a := greedy r β δ hist h s with ha
  set n := visitCount hist h s a with hn_def
  set π := greedy r β δ hist
  have hH := one_le_cast_of_fin h
  have hHpos : (0 : ℝ) < H := by linarith
  have hq0 := M.transVec_nonneg h s a
  have hq1 := M.sum_transVec h s a
  have hp := empTrans_nonneg hist h s a
  have hp1 := sum_empTrans hist h s a
  set k := H - 1 - (h : ℕ) with hk
  set B := Real.exp (β * k) with hB
  set C := Real.exp (β * (H - h : ℕ)) with hC
  have hBpos : 0 < B := Real.exp_pos _
  have hBC : B ≤ C := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
    (by exact_mod_cast (by omega : k ≤ H - (h : ℕ))) hβ.le)
  have hC1 : 1 ≤ C := Real.one_le_exp (mul_nonneg hβ.le (Nat.cast_nonneg _))
  have he1 : 1 ≤ Real.exp (β * r h s a) := Real.one_le_exp (mul_nonneg hβ.le (hr h s a).1)
  -- the certificate at the next step
  have hg : ∀ s', cert r β δ hist k s' ∈ Set.Icc 0 B := by
    intro s'
    have := cert_mem hist r β δ hδ hδ1 k (by omega) s'
    refine ⟨this.1, this.2.trans ?_⟩
    split_ifs
    · exact hBpos.le
    · exact le_rfl
  have hΔp : 0 ≤ vecExp (M.transVec h s a) (cert r β δ hist k) :=
    vecExp_nonneg hq0 fun s' ↦ (hg s').1
  have hρ0 : 0 ≤ rateMin (alphaKL (Fintype.card S) (Fintype.card A) H δ) n :=
    rateMin_nonneg (alphaKL_nonneg _ _ _ hδ hδ1) n
  have hρs0 : 0 ≤ rateMin (alphaStar (Fintype.card S) (Fintype.card A) H δ) n :=
    rateMin_nonneg (alphaStar_nonneg _ _ _ hδ hδ1) n
  have hcertC : cert r β δ hist (H - h) s ≤ C := by
    have := (cert_mem hist r β δ hδ hδ1 (H - h) (by omega) s).2
    simp only [show H - (h : ℕ) ≠ 0 by omega, hβ, ↓reduceIte] at this
    exact this
  by_cases htriv : n = 0 ∨ 1 ≤ alphaKL (Fintype.card S) (Fintype.card A) H δ n / n
  · -- trivial case: the rate term is `1`
    rw [rateMin_eq_one htriv, mul_one]
    have h84 : C ≤ 84 * H * C := by nlinarith
    have hσ : 0 ≤ √(vecVar (M.transVec h s a) (expValue M H β π.extend (h + 1))
      * rateMin (alphaStar (Fintype.card S) (Fintype.card A) H δ) n) := Real.sqrt_nonneg _
    have hbr : C ≤ 36 * √(vecVar (M.transVec h s a) (expValue M H β π.extend (h + 1))
          * rateMin (alphaStar (Fintype.card S) (Fintype.card A) H δ) n)
        + (1 + 13 / H) * vecExp (M.transVec h s a) (cert r β δ hist k) + 84 * H * C := by
      have : 0 ≤ (1 + 13 / (H : ℝ)) * vecExp (M.transVec h s a) (cert r β δ hist k) := by
        positivity
      linarith
    have hbr0 : 0 ≤ 36 * √(vecVar (M.transVec h s a) (expValue M H β π.extend (h + 1))
          * rateMin (alphaStar (Fintype.card S) (Fintype.card A) H δ) n)
        + (1 + 13 / H) * vecExp (M.transVec h s a) (cert r β δ hist k) + 84 * H * C := by
      linarith
    calc cert r β δ hist (H - h) s ≤ C := hcertC
      _ ≤ _ := hbr
      _ ≤ _ := le_mul_of_one_le_left hbr0 he1
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
      simp only [hβ, ↓reduceIte]
      split_ifs with h0
      · exact absurd h0 hn0
      · push_cast
        exact min_le_right _ _
    -- step (i)
    have hi := vecExp_le_one_add_mul_vecExp_add hp hp1 (measureReal_trans_singleton M h s a)
      hαn0 hBpos.le hH hg hkl
    -- facts at the next step
    have hZ : ∀ s', optExpValue M H β (h + 1) s'
        ∈ Set.Icc ((optZ r β δ hist k).2 s') ((optZ r β δ hist k).1 s') := by
      intro s'; rw [hk, ← sub_succ_eq]
      exact optExpValue_mem_Icc_optZ_of_pos hM hr hβ hδ hδ1 hc h.succ s'
    have hRπ : ∀ s', ringZ M r β δ hist k s' ≤ expValue M H β π.extend (h + 1) s' := by
      intro s'; rw [hk, ← sub_succ_eq]
      exact (ringZ_le_optZ_snd_and_expValue_of_pos hM hr hβ h.succ s').2
    have hGap : ∀ s', (optZ r β δ hist k).1 s' - ringZ M r β δ hist k s'
        ≤ cert r β δ hist k s' := by
      intro s'; rw [hk, ← sub_succ_eq]
      exact optZ_fst_sub_ringZ_le_cert_of_pos hM hr hβ hδ hδ1 hc h.succ s'
    have hR := rewardsIn_Icc_of_hasRewardFn hM hr
    have hπZ : ∀ s', expValue M H β π.extend (h + 1) s' ≤ optExpValue M H β (h + 1) s' := fun s' ↦
      expValue_le_optExpValue M H β hR hβ π.measurable_extend _ _
    have hZt : ∀ s', (optZ r β δ hist k).1 s' ∈ Set.Icc 1 (1 + B) := fun s' ↦ by
      have := optZ_mem_of_pos (hist := hist) hr hβ hδ hδ1 k (by omega) s'
      exact ⟨this.2.1.trans this.1, by linarith [this.2.2]⟩
    have hZπ : ∀ s', expValue M H β π.extend (h + 1) s' ∈ Set.Icc 1 (1 + B) := fun s' ↦ by
      have := expValue_mem_Icc_of_pos hM hr hβ π h.succ s'
      rw [sub_succ_eq, Fin.val_succ] at this
      exact ⟨this.1, by linarith [this.2]⟩
    have hΔ : vecExp (M.transVec h s a)
        (fun s' ↦ |(optZ r β δ hist k).1 s' - expValue M H β π.extend (h + 1) s'|)
        ≤ vecExp (M.transVec h s a) (cert r β δ hist k) := by
      refine vecExp_mono hq0 fun s' ↦ ?_
      rw [abs_of_nonneg (sub_nonneg.2 ((hπZ s').trans (hZ s').2))]
      linarith [hRπ s', hGap s']
    -- step (ii)
    have hii := bonusTerm_le_of_klDiv_le hp hp1 (measureReal_trans_singleton M h s a) hαs0 hαsn
      hBpos.le hH hZt hZπ hΔ hkl
    rw [← bonus_of_pos (Zl := (optZ r β δ hist k).2) (hβ := hβ)] at hii
    -- step (iii)
    have hiii := three_mul_add_le hH hσ hΔp hαn0 hBpos.le hBC hBC hii hi
    calc cert r β δ hist (H - h) s ≤ _ := hcert
      _ ≤ _ := mul_le_mul_of_nonneg_left hiii (Real.exp_pos _).le

end TrueKernel

/-! ### On the good event of a run -/

section Run

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℕ → Ω → Policy S A H} {Y : ℕ → Ω → Traj S H}
  {s₁ : S} {ω : Ω}

/-- **Lemma 7** (concentration of the optimal exponential value, `β > 0`): on the good event, for
every episode `t` and every visited pair,
`|(p̂_h^t - p_h) Z*_{h+1}| ≤ b_h^t + (1/H) p̂_h^t|Z̃^t_{h+1} - Z*_{h+1}|`. -/
lemma abs_vecExp_sub_le_bonusAt_add_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hω : ω ∈ goodEvent X Y M s₁ β δ) (t : ℕ) (h : Fin H) (s : S) (a : A)
    (hn : 0 < visitCountAt X Y h s a t ω) :
    |vecExp (empTransAt X Y h s a t ω) (optExpValue M H β (h + 1))
        - vecExp (M.transVec h s a) (optExpValue M H β (h + 1))|
      ≤ bonusAt X Y r β δ t ω h s a + 1 / H * vecExp (empTransAt X Y h s a t ω)
          (fun s' ↦ |ZtildeAt X Y r β δ t ω h.succ s' - optExpValue M H β (h + 1) s'|) := by
  have := abs_vecExp_sub_le_bonus_add_of_pos hM hr hβ hδ hδ1 (histConcentration_histAt hω t) h s
    a hn
  simp only [bonusAt, ZtildeAt, ZlowerAt, sub_succ_eq]
  exact this

/-- **Lemma 8** (optimism and pessimism, `β > 0`): on the good event, `Z̲_h^t ≤ Z*_h ≤ Z̃_h^t`. -/
lemma optExpValue_mem_Icc_ZlowerAt_ZtildeAt_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hω : ω ∈ goodEvent X Y M s₁ β δ) (t : ℕ) (h : Fin (H + 1)) (s : S) :
    optExpValue M H β h s ∈ Set.Icc (ZlowerAt X Y r β δ t ω h s) (ZtildeAt X Y r β δ t ω h s) :=
  optExpValue_mem_Icc_optZ_of_pos hM hr hβ hδ hδ1 (histConcentration_histAt hω t) h s

/-- **Lemma 8** for the backups (`β > 0`): on the good event, `U̲_h^t ≤ U*_h ≤ Ũ_h^t`. -/
lemma optExpQ_mem_Icc_UlowerAt_UtildeAt_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hω : ω ∈ goodEvent X Y M s₁ β δ) (t : ℕ) (h : Fin H) (s : S) (a : A) :
    optExpQ M H β h s a ∈ Set.Icc (UlowerAt X Y r β δ t ω h s a) (UtildeAt X Y r β δ t ω h s a) :=
  optExpQ_mem_Icc_stepUAt_of_pos hM hr hβ hδ hδ1 (histConcentration_histAt hω t) h s a

omit [MeasurableSingletonClass A] in
/-- **The ring value is at least one** (`β > 0`): `Z̊_h^t ≥ 1` and `Ů_h^t ≥ 1`. -/
lemma one_le_ringZAt_of_pos (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (t : ℕ) (ω : Ω)
    (h : Fin (H + 1)) (s : S) : 1 ≤ ringZAt X Y M r β δ t ω h s :=
  one_le_ringZ_of_pos hr hβ _ s

omit [MeasurableSingletonClass A] in
/-- The ring backup of a run is at least one (`β > 0`). -/
lemma one_le_ringUAt_of_pos (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (t : ℕ) (ω : Ω)
    (h : Fin H) (s : S) (a : A) : 1 ≤ ringUAt X Y M r β δ t ω h s a :=
  one_le_ringU_of_pos hr hβ h s a

/-- **Lemma 10** (the ring value is a lower bound, `β > 0`; no event is needed):
`Z̊_h^t ≤ Z̲_h^t` and `Z̊_h^t ≤ Z^π_h` for `π = π^{t+1}`. -/
lemma ringZAt_le_ZlowerAt_and_expValue_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (t : ℕ) (ω : Ω) (h : Fin (H + 1))
    (s : S) :
    ringZAt X Y M r β δ t ω h s ≤ ZlowerAt X Y r β δ t ω h s
      ∧ ringZAt X Y M r β δ t ω h s ≤ expValue M H β (greedyAt X Y r β δ t ω).extend h s :=
  ringZ_le_optZ_snd_and_expValue_of_pos hM hr hβ h s

/-- **Lemma 10** for the backups (`β > 0`): `Ů_h^t ≤ U̲_h^t` and `Ů_h^t ≤ U^π_h`. -/
lemma ringUAt_le_UlowerAt_and_expQ_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (t : ℕ) (ω : Ω) (h : Fin H) (s : S)
    (a : A) :
    ringUAt X Y M r β δ t ω h s a ≤ UlowerAt X Y r β δ t ω h s a
      ∧ ringUAt X Y M r β δ t ω h s a ≤ expQ M H β (greedyAt X Y r β δ t ω).extend h s a :=
  ringU_le_stepUAt_snd_and_expQ_of_pos hM hr hβ h s a

/-- **Lemma 11** (one-step certificate bound, `β > 0`): on the good event, for a visited pair,
`Ũ_h^t - Ů_h^t ≤ e^{β r_h} (3 b_h^t + (1 + 3/H) p̂_h^t(Z̃^t_{h+1} - Z̊^t_{h+1}))`. -/
lemma UtildeAt_sub_ringUAt_le_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hω : ω ∈ goodEvent X Y M s₁ β δ) (t : ℕ) (h : Fin H) (s : S) (a : A)
    (hn : 0 < visitCountAt X Y h s a t ω) :
    UtildeAt X Y r β δ t ω h s a - ringUAt X Y M r β δ t ω h s a
      ≤ Real.exp (β * r h s a) * (3 * bonusAt X Y r β δ t ω h s a
        + (1 + 3 / H) * vecExp (empTransAt X Y h s a t ω)
          (ZtildeAt X Y r β δ t ω h.succ - ringZAt X Y M r β δ t ω h.succ)) := by
  have := stepUAt_fst_sub_ringU_le_of_pos hM hr hβ hδ hδ1 (histConcentration_histAt hω t) h s a
    hn
  simp only [bonusAt, ZtildeAt, ZlowerAt, ringZAt, sub_succ_eq]
  exact this

/-- **The certificate dominates the optimistic–ring gap** (`β > 0`): on the good event,
`Z̃_h^t - Z̊_h^t ≤ π_h G_h^t`. -/
lemma ZtildeAt_sub_ringZAt_le_certAt_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hω : ω ∈ goodEvent X Y M s₁ β δ) (t : ℕ) (h : Fin (H + 1)) (s : S) :
    ZtildeAt X Y r β δ t ω h s - ringZAt X Y M r β δ t ω h s ≤ certAt X Y r β δ t ω h s :=
  optZ_fst_sub_ringZ_le_cert_of_pos hM hr hβ hδ hδ1 (histConcentration_histAt hω t) h s

/-- **Lemma 9** (the certificate dominates the suboptimality gap, `β > 0`): on the good event,
`Z*_h - Z^π_h ≤ π_h G_h^t` for `π = π^{t+1}`. -/
lemma optExpValue_sub_expValue_le_certAt_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hω : ω ∈ goodEvent X Y M s₁ β δ) (t : ℕ) (h : Fin (H + 1)) (s : S) :
    optExpValue M H β h s - expValue M H β (greedyAt X Y r β δ t ω).extend h s
      ≤ certAt X Y r β δ t ω h s :=
  optExpValue_sub_expValue_le_cert_of_pos hM hr hβ hδ hδ1 (histConcentration_histAt hω t) h s

/-- **Soundness of the stopping rule** (`β > 0`): on the good event, if the stopping condition
holds after `t` episodes, the greedy policy `π^{t+1}` is `ε`-optimal from `s₁`. -/
lemma optEntropicValue_sub_entropicValue_greedyAt_le_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hω : ω ∈ goodEvent X Y M s₁ β δ) {ε : ℝ} (hε : 0 ≤ ε) {t : ℕ}
    (hstop : stopCond r β δ ε s₁ (histAt X Y t ω)) :
    optEntropicValue M H β 0 s₁
      - entropicValue M H β (greedyAt X Y r β δ t ω).extend 0 s₁ ≤ ε :=
  optEntropicValue_sub_entropicValue_le_of_stopCond_of_pos hM hr hβ hδ hδ1
    (histConcentration_histAt hω t) hε hstop

/-- **Certificate recursion under the true kernel** (`β > 0`): on the good event, with
`π = π^{t+1}` and `a = π_h(s)`,
`π_h G_h^t(s) ≤ e^{β r_h(s, a)} (36 √(Var_{p_h}(Z^π_{h+1})(s, a) ρ*)
+ (1 + 13/H) p_h(π_{h+1} G^t_{h+1}) + 84 H e^{β (H - h)} ρ)` with the rate terms
`ρ = min {α(n)/n, 1}`, `ρ* = min {α*(n)/n, 1}`. -/
lemma certAt_le_of_pos (hM : M.HasRewardFn r) (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hω : ω ∈ goodEvent X Y M s₁ β δ) (t : ℕ) (h : Fin H)
    (s : S) :
    certAt X Y r β δ t ω h.castSucc s ≤ Real.exp (β * r h s (greedyAt X Y r β δ t ω h s)) *
      (36 * √(vecVar (M.transVec h s (greedyAt X Y r β δ t ω h s))
          (expValue M H β (greedyAt X Y r β δ t ω).extend (h + 1))
          * starRateMinAt X Y δ h s (greedyAt X Y r β δ t ω h s) t ω)
        + (1 + 13 / H) * vecExp (M.transVec h s (greedyAt X Y r β δ t ω h s))
          (certAt X Y r β δ t ω h.succ)
        + 84 * H * Real.exp (β * (H - h : ℕ))
          * klRateMinAt X Y δ h s (greedyAt X Y r β δ t ω h s) t ω) := by
  have := cert_le_of_pos hM hr hβ hδ hδ1 (histConcentration_histAt hω t) h s
  simp only [certAt, sub_succ_eq, Fin.val_castSucc]
  exact this

end Run

end Essakine2026Tight
