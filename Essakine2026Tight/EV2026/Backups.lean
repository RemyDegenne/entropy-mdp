/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.EV2026.Algorithm
public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.EmpiricalCounts
public import Essakine2026Tight.Mathlib.Probability.Moments.Variance

/-!
# Ranges of the quantities computed by Entropic-BPI

* The empirical transitions of a history form a probability vector (`empTrans_nonneg`,
  `sum_empTrans`), the rates are nonnegative (`alphaKL_nonneg`, `alphaStar_nonneg`) and so is the
  bonus (`bonus_nonneg`).
* **Ranges of the backups** (`stepU_mem`, `optZ_mem`): for rewards in `[0, 1]` and `δ ∈ (0, 1]`,
  `Z̲ ≤ Z̃` and both lie between `1` and `e^{β j}` at the step with `j ≤ H` steps to go.
* The optimistic values are the maxima (`β > 0`) or minima (`β ≤ 0`) of the backups over the
  actions, attained at the greedy action (`optZ_eq`, `optZ_fst_eq_stepUAt_greedy`, …).
* **Range of the certificate** (`cert_mem`): between `0` and its clip.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP.Episodic Learning.MDP

namespace Essakine2026Tight

/-! ### Rates and bonus -/

lemma log_three_mul_div_nonneg (S A H : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ Real.log ((3 * S * A * H : ℕ) / δ) := by
  rcases Nat.eq_zero_or_pos (3 * S * A * H) with h | h
  · simp [h]
  · refine Real.log_nonneg ?_
    rw [le_div_iff₀ hδ, one_mul]
    exact hδ1.trans (by exact_mod_cast h)

lemma log_eight_exp_one_mul_nonneg (n : ℕ) : 0 ≤ Real.log ((8 : ℕ) * Real.exp 1 * (n + 1 : ℕ)) := by
  refine Real.log_nonneg ?_
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have h8 : (1 : ℝ) ≤ (8 : ℕ) := by norm_num
  have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
    _ ≤ _ := by gcongr

lemma alphaKL_nonneg (S A H : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (n : ℕ) :
    0 ≤ alphaKL S A H δ n :=
  add_nonneg (log_three_mul_div_nonneg S A H hδ hδ1)
    (mul_nonneg (Nat.cast_nonneg _) (log_eight_exp_one_mul_nonneg n))

lemma alphaStar_nonneg (S A H : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (n : ℕ) :
    0 ≤ alphaStar S A H δ n :=
  add_nonneg (log_three_mul_div_nonneg S A H hδ hδ1) (log_eight_exp_one_mul_nonneg n)

lemma bonus_nonneg {S : Type*} [Fintype S] (nS nA H : ℕ) (β : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (k n : ℕ) (phat Zt Zl : S → ℝ) : 0 ≤ bonus nS nA H β δ k n phat Zt Zl := by
  have hα : 0 ≤ alphaKL nS nA H δ n / n := div_nonneg (alphaKL_nonneg _ _ _ hδ hδ1 n) n.cast_nonneg
  unfold bonus
  split_ifs with hβ
  · positivity
  · have h1 : 0 ≤ 1 - Real.exp (β * k) := by
      rw [sub_nonneg, Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hβ) k.cast_nonneg
    positivity

/-! ### One step of the backups -/

section Step

variable {S : Type*} [Fintype S]

lemma exp_mul_mem_Icc_of_mem_Icc {β r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp (β * r) ∈ Set.Icc (min 1 (Real.exp β)) (max 1 (Real.exp β)) := by
  have := ProbabilityTheory.exp_mul_mem_Icc_min_max (β := β) hr
  simpa using this

/-- **Ranges of the backups of one pair**: for a reward in `[0, 1]`, a probability vector `phat`
and next-step values `Z̲ ≤ Z̃` between `1` and `e^{β k}`, the backups satisfy `U̲ ≤ Ũ` and lie
between `1` and `e^{β (k + 1)}`. -/
lemma stepU_mem (nS nA H : ℕ) (β : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (k n : ℕ) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) 1) {phat Zt Zl : S → ℝ} (hp : ∀ s, 0 ≤ phat s)
    (hp1 : ∑ s, phat s = 1) (hZ : ∀ s, Zl s ≤ Zt s)
    (hZt : ∀ s, Zt s ∈ Set.Icc (min 1 (Real.exp (β * k))) (max 1 (Real.exp (β * k))))
    (hZl : ∀ s, Zl s ∈ Set.Icc (min 1 (Real.exp (β * k))) (max 1 (Real.exp (β * k)))) :
    (stepU nS nA H β δ k n r phat Zt Zl).2 ≤ (stepU nS nA H β δ k n r phat Zt Zl).1
      ∧ (stepU nS nA H β δ k n r phat Zt Zl).1
          ∈ Set.Icc (min 1 (Real.exp (β * (k + 1)))) (max 1 (Real.exp (β * (k + 1))))
      ∧ (stepU nS nA H β δ k n r phat Zt Zl).2
          ∈ Set.Icc (min 1 (Real.exp (β * (k + 1)))) (max 1 (Real.exp (β * (k + 1)))) := by
  have hb := bonus_nonneg nS nA H β hδ hδ1 k n phat Zt Zl
  have hw : 0 ≤ (1 / H : ℝ) * vecExp phat (Zt - Zl) :=
    mul_nonneg (by positivity) (vecExp_nonneg hp fun s ↦ sub_nonneg.2 (hZ s))
  have hpZ : vecExp phat Zl ≤ vecExp phat Zt := vecExp_mono hp hZ
  have hpZt := vecExp_mem_Icc hp hp1 hZt
  have hpZl := vecExp_mem_Icc hp hp1 hZl
  have her := exp_mul_mem_Icc_of_mem_Icc (β := β) hr
  have hepos := Real.exp_pos (β * r)
  have hsplit : Real.exp (β * (k + 1)) = Real.exp β * Real.exp (β * k) := by
    rw [← Real.exp_add]; ring_nf
  set b := bonus nS nA H β δ k n phat Zt Zl
  set w := (1 / H : ℝ) * vecExp phat (Zt - Zl)
  unfold stepU
  simp only []
  rcases lt_or_ge 0 β with hβ | hβ
  · have h1k : 1 ≤ Real.exp (β * k) := Real.one_le_exp (mul_nonneg hβ.le k.cast_nonneg)
    have h1β : 1 ≤ Real.exp β := Real.one_le_exp hβ.le
    have hc : 1 ≤ Real.exp (β * (k + 1)) := by rw [hsplit]; nlinarith
    rw [min_eq_left h1k, max_eq_right h1k] at hpZt hpZl
    rw [min_eq_left h1β, max_eq_right h1β] at her
    rw [min_eq_left hc, max_eq_right hc]
    simp only [hβ, ↓reduceIte]
    split_ifs with hn
    · exact ⟨hc, ⟨hc, le_rfl⟩, ⟨le_rfl, hc⟩⟩
    · have hX : 1 ≤ Real.exp (β * r) * (vecExp phat Zt + b + w) :=
        one_le_mul_of_one_le_of_one_le her.1 (by linarith [hpZt.1])
      have hYc : Real.exp (β * r) * (vecExp phat Zl - b - w) ≤ Real.exp (β * (k + 1)) := by
        rw [hsplit]
        calc Real.exp (β * r) * (vecExp phat Zl - b - w) ≤ Real.exp (β * r) * vecExp phat Zl :=
              mul_le_mul_of_nonneg_left (by linarith) hepos.le
          _ ≤ Real.exp β * Real.exp (β * k) :=
              mul_le_mul her.2 hpZl.2 (by linarith [hpZl.1]) (by linarith)
      have hYX : Real.exp (β * r) * (vecExp phat Zl - b - w)
          ≤ Real.exp (β * r) * (vecExp phat Zt + b + w) :=
        mul_le_mul_of_nonneg_left (by linarith) hepos.le
      refine ⟨max_le (le_min hc hX) (le_min hYc hYX), ⟨le_min hc hX, min_le_left _ _⟩,
        ⟨le_max_left _ _, max_le hc hYc⟩⟩
  · have hk1 : Real.exp (β * k) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hβ k.cast_nonneg)
    have hβ1 : Real.exp β ≤ 1 := Real.exp_le_one_iff.2 hβ
    have hc : Real.exp (β * (k + 1)) ≤ 1 := by
      rw [hsplit]; nlinarith [Real.exp_pos β, Real.exp_pos (β * k)]
    rw [min_eq_right hk1, max_eq_left hk1] at hpZt hpZl
    rw [min_eq_right hβ1, max_eq_left hβ1] at her
    rw [min_eq_right hc, max_eq_left hc]
    simp only [not_lt.2 hβ, ↓reduceIte]
    split_ifs with hn
    · exact ⟨hc, ⟨hc, le_rfl⟩, ⟨le_rfl, hc⟩⟩
    · have hkpos := Real.exp_pos (β * k)
      have hX : Real.exp (β * (k + 1)) ≤ Real.exp (β * r) * (vecExp phat Zt + b + w) := by
        rw [hsplit]
        exact mul_le_mul her.1 (by linarith [hpZt.1]) hkpos.le hepos.le
      have hY : Real.exp (β * r) * (vecExp phat Zl - b - w) ≤ 1 := by
        rcases le_or_gt (vecExp phat Zl - b - w) 0 with hneg | hpos
        · nlinarith
        · calc Real.exp (β * r) * (vecExp phat Zl - b - w) ≤ 1 * 1 :=
                mul_le_mul her.2 (by linarith [hpZl.2]) hpos.le zero_le_one
            _ = 1 := one_mul 1
      have hYX : Real.exp (β * r) * (vecExp phat Zl - b - w)
          ≤ Real.exp (β * r) * (vecExp phat Zt + b + w) :=
        mul_le_mul_of_nonneg_left (by linarith) hepos.le
      refine ⟨max_le (le_min hc hX) (le_min hY hYX), ⟨le_min hc hX, min_le_left _ _⟩,
        ⟨le_max_left _ _, max_le hc hY⟩⟩

end Step

/-! ### Empirical transitions of a history -/

section History

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A]
  {H : ℕ} {t : ℕ} (hist : Hist Unit (Policy S A H) (Traj S H) t)

omit [Fintype A] [Nonempty A] in
lemma isConsistent_stepModel (h : Fin H) : (stepModel hist h).IsConsistent :=
  EmpiricalModel.isConsistent_sum _ fun _ _ ↦ EmpiricalModel.isConsistent_ofEpisodeAt _ _ _ _

omit [Fintype A] [Nonempty A] in
lemma empTrans_nonneg (h : Fin H) (s : S) (a : A) (s' : S) : 0 ≤ empTrans hist h s a s' := by
  unfold empTrans
  split_ifs
  · positivity
  · exact EmpiricalModel.empTrans_nonneg _ _ _

omit [Fintype A] [Nonempty A] in
/-- The empirical transitions of a history form a probability vector. -/
lemma sum_empTrans (h : Fin H) (s : S) (a : A) : ∑ s', empTrans hist h s a s' = 1 := by
  unfold empTrans
  split_ifs with hn
  · have : Nonempty S := ⟨s⟩
    rw [sum_const, card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)]
  · exact (isConsistent_stepModel hist h).sum_empTrans hn

end History

/-! ### The backward recursion of the backups -/

section Recursion

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A]
  {H : ℕ} {t : ℕ} (hist : Hist Unit (Policy S A H) (Traj S H) t) (r : ℕ → S → A → ℝ)
  (β δ : ℝ)

omit [Nonempty A] in
lemma stepOf_sub_one_sub (h : Fin H) : stepOf H (H - 1 - h) (sub_one_sub_lt h.is_lt) = h :=
  Fin.ext (by simp only [stepOf]; omega)

omit [Nonempty A] in
lemma sub_val_eq (h : Fin H) : H - (h : ℕ) = (H - 1 - h) + 1 := by omega

/-- The optimistic and pessimistic values at the step `h` are the extrema over the actions of
the backups at `h`. -/
lemma optZ_eq (h : Fin H) :
    optZ r β δ hist (H - h)
      = (fun s ↦ if 0 < β then (fun a ↦ (stepUAt r β δ hist h s a).1).max
          else (fun a ↦ (stepUAt r β δ hist h s a).1).min,
        fun s ↦ if 0 < β then (fun a ↦ (stepUAt r β δ hist h s a).2).max
          else (fun a ↦ (stepUAt r β δ hist h s a).2).min) := by
  rw [sub_val_eq h, optZ_succ, optZStep]
  simp only [sub_one_sub_lt h.is_lt, ↓reduceDIte, stepOf_sub_one_sub]
  rfl

lemma stepUAt_fst_le_optZ (hβ : 0 < β) (h : Fin H) (s : S) (a : A) :
    (stepUAt r β δ hist h s a).1 ≤ (optZ r β δ hist (H - h)).1 s := by
  simp only [optZ_eq, hβ, ↓reduceIte]
  exact Function.le_max (fun a ↦ (stepUAt r β δ hist h s a).1) a

lemma optZ_fst_eq_stepUAt_greedy (hβ : 0 < β) (h : Fin H) (s : S) :
    (optZ r β δ hist (H - h)).1 s = (stepUAt r β δ hist h s (greedy r β δ hist h s)).1 := by
  simp only [optZ_eq, greedy, hβ, ↓reduceIte]
  exact (argmax_spec _).symm

lemma optZ_snd_le_stepUAt (hβ : ¬ 0 < β) (h : Fin H) (s : S) (a : A) :
    (optZ r β δ hist (H - h)).2 s ≤ (stepUAt r β δ hist h s a).2 := by
  simp only [optZ_eq, hβ, ↓reduceIte]
  exact Function.min_le (fun a ↦ (stepUAt r β δ hist h s a).2) a

lemma optZ_snd_eq_stepUAt_greedy (hβ : ¬ 0 < β) (h : Fin H) (s : S) :
    (optZ r β δ hist (H - h)).2 s = (stepUAt r β δ hist h s (greedy r β δ hist h s)).2 := by
  simp only [optZ_eq, greedy, hβ, ↓reduceIte]
  exact (argmin_spec _).symm

omit [Nonempty A] in
lemma max_mem_Icc {ι : Type*} [Fintype ι] [Nonempty ι] {f : ι → ℝ} {a b : ℝ}
    (hf : ∀ i, f i ∈ Set.Icc a b) : f.max ∈ Set.Icc a b := by
  rw [← argmax_spec f]
  exact hf _

omit [Nonempty A] in
lemma min_mem_Icc {ι : Type*} [Fintype ι] [Nonempty ι] {f : ι → ℝ} {a b : ℝ}
    (hf : ∀ i, f i ∈ Set.Icc a b) : f.min ∈ Set.Icc a b := by
  rw [← argmin_spec f]
  exact hf _

omit [Nonempty A] in
lemma max_le_max_of_le {ι : Type*} [Fintype ι] [Nonempty ι] {f g : ι → ℝ} (hfg : ∀ i, f i ≤ g i) :
    f.max ≤ g.max := by
  rw [← argmax_spec f]
  exact (hfg _).trans (Function.le_max _ _)

omit [Nonempty A] in
lemma min_le_min_of_le {ι : Type*} [Fintype ι] [Nonempty ι] {f g : ι → ℝ} (hfg : ∀ i, f i ≤ g i) :
    f.min ≤ g.min := by
  rw [← argmin_spec g]
  exact (Function.min_le _ _).trans (hfg _)

/-- **Ranges of the optimistic and pessimistic values**: for rewards in `[0, 1]` and
`δ ∈ (0, 1]`, at the step with `j ≤ H` steps to go, `Z̲ ≤ Z̃` and both lie between `1` and
`e^{β j}`. -/
lemma optZ_mem (hr : ∀ h s a, r h s a ∈ Set.Icc (0 : ℝ) 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (j : ℕ) (hj : j ≤ H) (s : S) :
    (optZ r β δ hist j).2 s ≤ (optZ r β δ hist j).1 s
      ∧ (optZ r β δ hist j).1 s ∈ Set.Icc (min 1 (Real.exp (β * j))) (max 1 (Real.exp (β * j)))
      ∧ (optZ r β δ hist j).2 s
          ∈ Set.Icc (min 1 (Real.exp (β * j))) (max 1 (Real.exp (β * j))) := by
  induction j generalizing s with
  | zero => simp [optZ_zero]
  | succ k ih =>
    have hk : k < H := by omega
    have ih' := fun s ↦ ih (by omega) s
    have hU := fun (s : S) (a : A) ↦ stepU_mem (S := S) (Fintype.card S) (Fintype.card A) H β
      hδ hδ1 k (visitCount hist (stepOf H k hk) s a) (hr (stepOf H k hk) s a)
      (empTrans_nonneg hist (stepOf H k hk) s a) (sum_empTrans hist (stepOf H k hk) s a)
      (fun s' ↦ (ih' s').1) (fun s' ↦ (ih' s').2.1) (fun s' ↦ (ih' s').2.2)
    rw [optZ_succ, optZStep]
    simp only [hk, ↓reduceDIte, Nat.cast_add, Nat.cast_one]
    split_ifs with hβ
    · exact ⟨max_le_max_of_le fun a ↦ (hU s a).1, max_mem_Icc fun a ↦ (hU s a).2.1,
        max_mem_Icc fun a ↦ (hU s a).2.2⟩
    · exact ⟨min_le_min_of_le fun a ↦ (hU s a).1, min_mem_Icc fun a ↦ (hU s a).2.1,
        min_mem_Icc fun a ↦ (hU s a).2.2⟩

/-- **Range of the certificate**: at the step with `j ≤ H` steps to go, the certificate lies
between `0` and its clip (`0` at the terminal step, `e^{β j}` if `β > 0`, `1` otherwise). -/
lemma cert_mem (hδ : 0 < δ) (hδ1 : δ ≤ 1) (j : ℕ) (hj : j ≤ H) (s : S) :
    cert r β δ hist j s
      ∈ Set.Icc 0 (if j = 0 then 0 else if 0 < β then Real.exp (β * j) else 1) := by
  induction j generalizing s with
  | zero => simp [cert_zero]
  | succ k ih =>
    have hk : k < H := by omega
    have ih0 : ∀ s', 0 ≤ cert r β δ hist k s' := fun s' ↦ (ih (by omega) s').1
    rw [cert_succ, certStep]
    simp only [hk, ↓reduceDIte, Nat.add_one_ne_zero, ↓reduceIte, Nat.cast_add, Nat.cast_one]
    split_ifs with hβ hn hn
    · exact ⟨(Real.exp_pos _).le, le_rfl⟩
    · refine ⟨le_min (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le ?_), min_le_left _ _⟩
      exact add_nonneg (mul_nonneg (by positivity) (bonus_nonneg _ _ _ _ hδ hδ1 _ _ _ _ _))
        (mul_nonneg (by positivity) (vecExp_nonneg (empTrans_nonneg hist _ s _) ih0))
    · exact ⟨zero_le_one, le_rfl⟩
    · refine ⟨le_min zero_le_one (mul_nonneg (Real.exp_pos _).le ?_), min_le_left _ _⟩
      exact add_nonneg (mul_nonneg (by positivity) (bonus_nonneg _ _ _ _ hδ hδ1 _ _ _ _ _))
        (mul_nonneg (by positivity) (vecExp_nonneg (empTrans_nonneg hist _ s _) ih0))

/-- Ranges of the backups at the step `h`. -/
lemma stepUAt_mem (hr : ∀ h s a, r h s a ∈ Set.Icc (0 : ℝ) 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : Fin H) (s : S) (a : A) :
    (stepUAt r β δ hist h s a).2 ≤ (stepUAt r β δ hist h s a).1
      ∧ (stepUAt r β δ hist h s a).1
          ∈ Set.Icc (min 1 (Real.exp (β * (H - h : ℕ)))) (max 1 (Real.exp (β * (H - h : ℕ))))
      ∧ (stepUAt r β δ hist h s a).2
          ∈ Set.Icc (min 1 (Real.exp (β * (H - h : ℕ)))) (max 1 (Real.exp (β * (H - h : ℕ)))) := by
  have hZ := optZ_mem hist r β δ hr hδ hδ1 (H - 1 - h) (by omega)
  have hU := stepU_mem (S := S) (Fintype.card S) (Fintype.card A) H β hδ hδ1 (H - 1 - h)
    (visitCount hist h s a) (hr h s a) (empTrans_nonneg hist h s a) (sum_empTrans hist h s a)
    (fun s' ↦ (hZ s').1) (fun s' ↦ (hZ s').2.1) (fun s' ↦ (hZ s').2.2)
  have hcast : ((H - (h : ℕ) : ℕ) : ℝ) = ((H - 1 - h : ℕ) : ℝ) + 1 := by
    rw [sub_val_eq h]; push_cast; ring
  rw [hcast]
  exact hU

end Recursion

end Essakine2026Tight
