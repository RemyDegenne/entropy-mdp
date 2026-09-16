/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.StepLaw
public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Entropic
public import Essakine2026Tight.Mathlib.Probability.Moments.Variance

/-!
# Bellman equations and ranges of the exponential and entropic values

For a finite-horizon MDP `M`, a risk parameter `β` and a policy `π`:

* the **exponential Bellman equation** `Z^π_h(s) = U^π_h(s, π_h(s))` (`expValue_castSucc`) and
  `Z^π_{H+1} = 1` (`expValue_last`), under the hypothesis that the rewards have a finite
  exponential moment of order `β` (true for bounded rewards, `integrable_exp_mul_of_rewardsIn`);
  its Lebesgue-integral form `lexpValue_castSucc` holds without any hypothesis;
* for rewards in `[0, 1]`, the **ranges** of `Z^π_h`, `U^π_h`, `Z*_h`, `U*_h` between `1` and
  `e^{β (H - h)}` (`expValue_mem_Icc`, …) and of the return (`ae_episodeReturn_mem_Icc`), and the
  bounds `0 ≤ G_max ≤ H` on the maximal return (`maxReturn_nonneg`, `maxReturn_le`);
* the **optimal values**: `Z*_h(s)` is the largest (`β > 0`) or smallest (`β < 0`) value of a
  policy (`expValue_le_optExpValue`, `optExpValue_le_expValue`), the greedy policy `optPolicy`
  with respect to `U*` is optimal from every state at every step (`expValue_optPolicy`), and the
  **optimal Bellman equation** `Z*_h(s) = max_a U*_h(s, a)` (resp. `min`) holds
  (`optExpValue_castSucc_eq`, `optExpQ_le_optExpValue`, `optExpValue_le_optExpQ`);
* the value gap `V*_h(s) - V^π_h(s) = β⁻¹ log (Z*_h(s) / Z^π_h(s))` and its consequences
  (`optEntropicValue_sub_entropicValue`, `optEntropicValue_sub_entropicValue_le_of_pos`,
  `optEntropicValue_sub_entropicValue_le_of_neg`).

Steps are `0`-indexed: the state value at `h : Fin (H + 1)` has `H - h` steps to go, so the paper's
range `e^{β (H + 1 - h)}` is `e^{β (H - h)}` here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP
open scoped ENNReal

namespace Learning.MDP.Episodic

variable {S A : Type*} [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] {H : ℕ} (M : EpisodicMDP S A H)
  (β : ℝ)

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A]
  [Nonempty A] in
lemma measurable_exp_mul_episodeReturn :
    Measurable fun x : ℕ → Round (LayerState S H) A ℝ ↦ Real.exp (β * episodeReturn H x) :=
  Real.measurable_exp.comp (measurable_episodeReturn.const_mul β)

/-! ### Lebesgue integrals of the exponential return -/

/-- The Lebesgue integral `∫⁻ exp (β R_h)` of the exponential return of `π` from the state `s` at
the step `h`. -/
noncomputable def lexpValue (π : Policy S A H) (h : Fin (H + 1)) (s : S) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (β * episodeReturn H x)) ∂stepLaw M π (s, h)

lemma expValue_eq_toReal_lexpValue (π : Policy S A H) (h : Fin (H + 1)) (s : S) :
    expValue M β π h s = (lexpValue M β π h s).toReal :=
  integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)
    (measurable_exp_mul_episodeReturn β).aestronglyMeasurable

lemma lexpValue_last (π : Policy S A H) (s : S) : lexpValue M β π (Fin.last H) s = 1 := by
  rw [lexpValue, lintegral_congr_ae (g := fun _ ↦ 1)]
  · simp
  · filter_upwards [ae_episodeReturn_eq_zero_stepLaw_last M π s] with x hx
    simp [hx]

/-- The exponential Bellman equation for the Lebesgue integrals of the exponential return. -/
lemma lexpValue_castSucc (π : Policy S A H) (h : Fin H) (s : S) :
    lexpValue M β π h.castSucc s
      = (∫⁻ r, ENNReal.ofReal (Real.exp (β * r)) ∂M.reward h (s, π h s))
        * ∫⁻ s', lexpValue M β π h.succ s' ∂M.trans h (s, π h s) := by
  have hmeas : Measurable fun z : (ℝ × S) × (ℕ → Round (LayerState S H) A ℝ) ↦
      ENNReal.ofReal (Real.exp (β * z.1.1))
        * ENNReal.ofReal (Real.exp (β * episodeReturn H z.2)) :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_fst.fst.const_mul β))).mul
      (ENNReal.measurable_ofReal.comp ((measurable_exp_mul_episodeReturn β).comp measurable_snd))
  calc lexpValue M β π h.castSucc s
      = ∫⁻ x, ENNReal.ofReal (Real.exp (β * IT.feedback 0 x))
          * ENNReal.ofReal (Real.exp (β * episodeReturn H (shiftRound x)))
          ∂stepLaw M π (s, h.castSucc) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_episodeReturn_eq_add_shiftRound M π h.castSucc s] with x hx
        rw [hx, mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ = ∫⁻ q, ∫⁻ y, ENNReal.ofReal (Real.exp (β * q.1))
          * ENNReal.ofReal (Real.exp (β * episodeReturn H y)) ∂stepLaw M π (q.2, h.succ)
          ∂((M.reward h (s, π h s)).prod (M.trans h (s, π h s))) :=
        lintegral_stepLaw_castSucc M π h s hmeas
    _ = ∫⁻ q, ENNReal.ofReal (Real.exp (β * q.1)) * lexpValue M β π h.succ q.2
          ∂((M.reward h (s, π h s)).prod (M.trans h (s, π h s))) := by
        refine lintegral_congr fun q ↦ ?_
        exact lintegral_const_mul _
          (ENNReal.measurable_ofReal.comp (measurable_exp_mul_episodeReturn β))
    _ = _ := lintegral_prod_mul (f := fun r ↦ ENNReal.ofReal (Real.exp (β * r)))
        (g := fun s' ↦ lexpValue M β π h.succ s')
        (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          (measurable_id.const_mul β))).aemeasurable
        (measurable_of_countable _).aemeasurable

/-! ### The exponential Bellman equation -/

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A]
  [Nonempty A] in
/-- Bounded rewards have finite exponential moments. -/
lemma integrable_exp_mul_of_rewardsIn {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) (h : Fin H)
    (s : S) (a' : A) : Integrable (fun x ↦ Real.exp (β * x)) (M.reward h (s, a')) := by
  refine Integrable.of_bound
    (Real.measurable_exp.comp (measurable_id.const_mul β)).aestronglyMeasurable
    (Real.exp (|β| * max |a| |b|)) ?_
  filter_upwards [hM h s a'] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  calc β * x ≤ |β * x| := le_abs_self _
    _ = |β| * |x| := abs_mul _ _
    _ ≤ |β| * max |a| |b| := by
        gcongr
        exact abs_le_max_abs_abs hx.1 hx.2

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A]
  [Nonempty A] in
lemma rewardsIn_of_hasRewardFn {r : Fin H → S → A → ℝ} (hM : M.HasRewardFn r) {I : Set ℝ}
    (hI : MeasurableSet I) (hr : ∀ h s a, r h s a ∈ I) : M.RewardsIn I := by
  intro h s a
  rw [hM h s a]
  exact (ae_dirac_iff (p := (· ∈ I)) hI).2 (hr h s a)

lemma lexpValue_lt_top (hR : ∀ h s a, Integrable (fun x ↦ Real.exp (β * x)) (M.reward h (s, a)))
    (π : Policy S A H) (h : Fin (H + 1)) (s : S) : lexpValue M β π h s < ∞ := by
  induction h using Fin.reverseInduction generalizing s with
  | last => simp [lexpValue_last]
  | cast i ih =>
    rw [lexpValue_castSucc]
    refine ENNReal.mul_lt_top (hR i s (π i s)).lintegral_lt_top ?_
    rw [lintegral_fintype]
    exact ENNReal.sum_lt_top.2 fun s' _ ↦ ENNReal.mul_lt_top (ih s') (measure_lt_top _ _)

lemma expValue_last (π : Policy S A H) (s : S) : expValue M β π (Fin.last H) s = 1 := by
  rw [expValue_eq_toReal_lexpValue, lexpValue_last, ENNReal.toReal_one]

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A]
  [Nonempty A] in
lemma integral_exp_mul_eq_toReal (μ : Measure ℝ) :
    ∫ x, Real.exp (β * x) ∂μ = (∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂μ).toReal :=
  integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)
    (Real.measurable_exp.comp (measurable_id.const_mul β)).aestronglyMeasurable

/-- **Exponential Bellman equation**: `Z^π_h(s) = U^π_h(s, π_h(s))`. -/
lemma expValue_castSucc
    (hR : ∀ h s a, Integrable (fun x ↦ Real.exp (β * x)) (M.reward h (s, a)))
    (π : Policy S A H) (h : Fin H) (s : S) :
    expValue M β π h.castSucc s = expQ M β π h s (π h s) := by
  rw [expValue_eq_toReal_lexpValue, lexpValue_castSucc, ENNReal.toReal_mul, expQ,
    integral_exp_mul_eq_toReal]
  congr 1
  simp_rw [expValue_eq_toReal_lexpValue]
  exact (integral_toReal (measurable_of_countable _).aemeasurable
    (Filter.Eventually.of_forall fun s' ↦ lexpValue_lt_top M β hR π h.succ s')).symm

omit [Fintype A] [MeasurableSingletonClass A] [Nonempty A] in
lemma integral_eq_vecExp_transVec (h : Fin H) (s : S) (a : A) (f : S → ℝ) :
    ∫ s', f s' ∂M.trans h (s, a) = vecExp (M.transVec h s a) f := by
  rw [integral_fintype Integrable.of_finite]
  rfl

/-- The exponential Bellman operator for an MDP with a reward function. -/
lemma expQ_of_hasRewardFn {r : Fin H → S → A → ℝ} (hM : M.HasRewardFn r) (π : Policy S A H)
    (h : Fin H) (s : S) (a : A) :
    expQ M β π h s a
      = Real.exp (β * r h s a) * vecExp (M.transVec h s a) (expValue M β π h.succ) := by
  rw [expQ, hM h s a, integral_dirac, integral_eq_vecExp_transVec]

/-- The optimal exponential Bellman operator for an MDP with a reward function. -/
lemma optExpQ_of_hasRewardFn {r : Fin H → S → A → ℝ} (hM : M.HasRewardFn r) (h : Fin H) (s : S)
    (a : A) :
    optExpQ M β h s a
      = Real.exp (β * r h s a) * vecExp (M.transVec h s a) (optExpValue M β h.succ) := by
  rw [optExpQ, hM h s a, integral_dirac, integral_eq_vecExp_transVec]

lemma expValue_pos (hR : ∀ h s a, Integrable (fun x ↦ Real.exp (β * x)) (M.reward h (s, a)))
    (π : Policy S A H) (h : Fin (H + 1)) (s : S) : 0 < expValue M β π h s := by
  induction h using Fin.reverseInduction generalizing s with
  | last => simp [expValue_last]
  | cast i ih =>
    rw [expValue_castSucc M β hR, expQ]
    refine mul_pos (integral_exp_pos (hR i s (π i s))) ?_
    rw [integral_pos_iff_support_of_nonneg (fun s' ↦ (ih s').le) Integrable.of_finite]
    rw [Function.support_eq_univ fun s' ↦ (ih s').ne', measure_univ]
    exact zero_lt_one

/-! ### Ranges for rewards in `[0, 1]` -/

omit [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Nonempty A] in
lemma mul_mem_Icc_min_max_exp {u v x y : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hx : x ∈ Set.Icc (min 1 (Real.exp (β * u))) (max 1 (Real.exp (β * u))))
    (hy : y ∈ Set.Icc (min 1 (Real.exp (β * v))) (max 1 (Real.exp (β * v)))) :
    x * y ∈ Set.Icc (min 1 (Real.exp (β * (u + v)))) (max 1 (Real.exp (β * (u + v)))) := by
  rw [mul_add, Real.exp_add]
  rcases le_or_gt 0 β with hβ | hβ
  · have h1 : 1 ≤ Real.exp (β * u) := Real.one_le_exp (mul_nonneg hβ hu)
    have h2 : 1 ≤ Real.exp (β * v) := Real.one_le_exp (mul_nonneg hβ hv)
    rw [min_eq_left h1, max_eq_right h1] at hx
    rw [min_eq_left h2, max_eq_right h2] at hy
    rw [min_eq_left (one_le_mul_of_one_le_of_one_le h1 h2),
      max_eq_right (one_le_mul_of_one_le_of_one_le h1 h2)]
    exact ⟨one_le_mul_of_one_le_of_one_le hx.1 hy.1,
      mul_le_mul hx.2 hy.2 (by linarith [hy.1]) (by linarith)⟩
  · have h1 : Real.exp (β * u) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hβ.le hu)
    have h2 : Real.exp (β * v) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hβ.le hv)
    have h1' := Real.exp_pos (β * u)
    have h2' := Real.exp_pos (β * v)
    rw [min_eq_right h1, max_eq_left h1] at hx
    rw [min_eq_right h2, max_eq_left h2] at hy
    have h12 : Real.exp (β * u) * Real.exp (β * v) ≤ 1 := by nlinarith
    rw [min_eq_right h12, max_eq_left h12]
    exact ⟨mul_le_mul hx.1 hy.1 h2'.le (by linarith [hx.1]),
      (mul_le_mul hx.2 hy.2 (by linarith [hy.1]) zero_le_one).trans_eq (one_mul 1)⟩

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A]
  [Nonempty A] in
lemma integral_exp_mul_reward_mem_Icc (hM : M.RewardsIn (Set.Icc 0 1)) (h : Fin H) (s : S)
    (a : A) :
    ∫ x, Real.exp (β * x) ∂M.reward h (s, a)
      ∈ Set.Icc (min 1 (Real.exp (β * 1))) (max 1 (Real.exp (β * 1))) :=
  integral_mem_Icc_of_ae_mem_Icc ((hM h s a).mono fun _ hx ↦ exp_mul_mem_Icc_min_max hx)
    (Real.measurable_exp.comp (measurable_id.const_mul β)).aestronglyMeasurable

omit [Fintype S] [Fintype A] [MeasurableSingletonClass A] [Nonempty A] in
lemma integral_trans_mem_Icc [Finite S] {a b : ℝ} {f : S → ℝ} (hf : ∀ s', f s' ∈ Set.Icc a b)
    (h : Fin H) (s : S) (a' : A) : ∫ s', f s' ∂M.trans h (s, a') ∈ Set.Icc a b :=
  integral_mem_Icc_of_ae_mem_Icc (Filter.Eventually.of_forall hf)
    (measurable_of_countable _).aestronglyMeasurable

lemma cast_sub_castSucc (h : Fin H) :
    ((H - (h.castSucc : ℕ) : ℕ) : ℝ) = 1 + ((H - (h.succ : ℕ) : ℕ) : ℝ) := by
  rw [Fin.val_succ, Fin.val_castSucc, show H - (h : ℕ) = (H - ((h : ℕ) + 1)) + 1 by omega]
  push_cast
  ring

/-- Range of the exponential values for rewards in `[0, 1]`. -/
lemma expValue_mem_Icc (hM : M.RewardsIn (Set.Icc 0 1)) (π : Policy S A H) (h : Fin (H + 1))
    (s : S) :
    expValue M β π h s
      ∈ Set.Icc (min 1 (Real.exp (β * (H - h : ℕ)))) (max 1 (Real.exp (β * (H - h : ℕ)))) := by
  induction h using Fin.reverseInduction generalizing s with
  | last => simp [expValue_last]
  | cast i ih =>
    rw [expValue_castSucc M β (integrable_exp_mul_of_rewardsIn M β hM), expQ, cast_sub_castSucc]
    exact mul_mem_Icc_min_max_exp β zero_le_one (Nat.cast_nonneg _)
      (integral_exp_mul_reward_mem_Icc M β hM i s _) (integral_trans_mem_Icc M ih i s _)

/-- Range of the exponential state-action values for rewards in `[0, 1]`. -/
lemma expQ_mem_Icc (hM : M.RewardsIn (Set.Icc 0 1)) (π : Policy S A H) (h : Fin H) (s : S)
    (a : A) :
    expQ M β π h s a
      ∈ Set.Icc (min 1 (Real.exp (β * (H - h : ℕ)))) (max 1 (Real.exp (β * (H - h : ℕ)))) := by
  rw [expQ, show ((H - (h : ℕ) : ℕ) : ℝ) = ((H - (h.castSucc : ℕ) : ℕ) : ℝ) from rfl,
    cast_sub_castSucc]
  exact mul_mem_Icc_min_max_exp β zero_le_one (Nat.cast_nonneg _)
    (integral_exp_mul_reward_mem_Icc M β hM h s a)
    (integral_trans_mem_Icc M (fun s' ↦ expValue_mem_Icc M β hM π h.succ s') h s a)

/-- The return from the step `h` lies in `[0, H - h]` for rewards in `[0, 1]`. -/
lemma ae_episodeReturn_mem_Icc (hM : M.RewardsIn (Set.Icc 0 1)) (π : Policy S A H)
    (h : Fin (H + 1)) (s : S) :
    ∀ᵐ x ∂stepLaw M π (s, h), episodeReturn H x ∈ Set.Icc 0 ((H - h : ℕ) : ℝ) := by
  induction h using Fin.reverseInduction generalizing s with
  | last =>
    filter_upwards [ae_episodeReturn_eq_zero_stepLaw_last M π s] with x hx
    simp [hx]
  | cast i ih =>
    have h0 : ∀ᵐ x ∂stepLaw M π (s, i.castSucc), IT.feedback 0 x ∈ Set.Icc (0 : ℝ) 1 := by
      have hl := hasLaw_feedback_zero_stepLaw_castSucc M π i s
      exact ae_of_ae_map (p := fun r ↦ r ∈ Set.Icc (0 : ℝ) 1) hl.aemeasurable
        (by rw [hl.map_eq]; exact hM i s (π i s))
    have h1 : ∀ᵐ x ∂stepLaw M π (s, i.castSucc),
        episodeReturn H (shiftRound x) ∈ Set.Icc 0 ((H - (i.succ : ℕ) : ℕ) : ℝ) :=
      ae_stepLaw_castSucc_of_ae M π
        (P := fun _ _ y ↦ episodeReturn H y ∈ Set.Icc 0 ((H - (i.succ : ℕ) : ℕ) : ℝ))
        (measurableSet_Icc.preimage (measurable_episodeReturn.comp measurable_snd))
        (Filter.Eventually.of_forall fun _ s' ↦ ih s')
    filter_upwards [ae_episodeReturn_eq_add_shiftRound M π i.castSucc s, h0, h1] with x hx h0 h1
    rw [hx, cast_sub_castSucc]
    exact ⟨add_nonneg h0.1 h1.1, add_le_add h0.2 h1.2⟩

/-! ### The maximal return -/

lemma essSup_episodeReturn_mem_Icc (hM : M.RewardsIn (Set.Icc 0 1)) (π : Policy S A H) (s₁ : S) :
    essSup (episodeReturn H) (stepLaw M π (s₁, startStep H)) ∈ Set.Icc 0 (H : ℝ) := by
  have hae := ae_episodeReturn_mem_Icc M hM π (startStep H) s₁
  have hle : ∀ᵐ x ∂stepLaw M π (s₁, startStep H), episodeReturn H x ≤ H := hae.mono fun _ hx ↦ hx.2
  have hge : ∀ᵐ x ∂stepLaw M π (s₁, startStep H), 0 ≤ episodeReturn H x := hae.mono fun _ hx ↦ hx.1
  constructor
  · obtain ⟨x, hx1, hx2⟩ :=
      ((ae_le_essSup (Filter.isBoundedUnder_of_eventually_le hle)).and hge).exists
    exact hx2.trans hx1
  · exact essSup_le_of_ae_le _ hle (Filter.isCoboundedUnder_le_of_eventually_le _ hge)

/-- The return of an episode is at most the maximal return, for rewards in `[0, 1]`. -/
lemma ae_episodeReturn_le_maxReturn (hM : M.RewardsIn (Set.Icc 0 1)) (π : Policy S A H)
    (s₁ : S) :
    ∀ᵐ x ∂stepLaw M π (s₁, startStep H), episodeReturn H x ≤ maxReturn M s₁ := by
  have hle : ∀ᵐ x ∂stepLaw M π (s₁, startStep H), episodeReturn H x ≤ H :=
    (ae_episodeReturn_mem_Icc M hM π (startStep H) s₁).mono fun _ hx ↦ hx.2
  filter_upwards [ae_le_essSup (Filter.isBoundedUnder_of_eventually_le hle)] with x hx
  exact hx.trans (le_ciSup (f := fun π ↦ essSup (episodeReturn H) (stepLaw M π (s₁, startStep H)))
    (Finite.bddAbove_range _) π)

lemma maxReturn_nonneg (hM : M.RewardsIn (Set.Icc 0 1)) (s₁ : S) : 0 ≤ maxReturn M s₁ :=
  (essSup_episodeReturn_mem_Icc M hM (Classical.arbitrary _) s₁).1.trans
    (le_ciSup (f := fun π ↦ essSup (episodeReturn H) (stepLaw M π (s₁, startStep H)))
      (Finite.bddAbove_range _) (Classical.arbitrary _))

lemma maxReturn_le (hM : M.RewardsIn (Set.Icc 0 1)) (s₁ : S) : maxReturn M s₁ ≤ H :=
  ciSup_le (f := fun π ↦ essSup (episodeReturn H) (stepLaw M π (s₁, startStep H)))
    fun π ↦ (essSup_episodeReturn_mem_Icc M hM π s₁).2

/-! ### Optimal values -/

lemma entropicValue_le_optEntropicValue (π : Policy S A H) (h : Fin (H + 1)) (s : S) :
    entropicValue M β π h s ≤ optEntropicValue M β h s :=
  le_ciSup (f := fun π ↦ entropicValue M β π h s) (Finite.bddAbove_range _) π

lemma exists_entropicValue_eq_optEntropicValue (h : Fin (H + 1)) (s : S) :
    ∃ π, entropicValue M β π h s = optEntropicValue M β h s :=
  exists_eq_ciSup_of_finite (f := fun π ↦ entropicValue M β π h s)

lemma expValue_eq_exp_mul_entropicValue (hβ : β ≠ 0) {π : Policy S A H} {h : Fin (H + 1)} {s : S}
    (hZ : 0 < expValue M β π h s) :
    expValue M β π h s = Real.exp (β * entropicValue M β π h s) := by
  rw [entropicValue, ← mul_assoc, mul_inv_cancel₀ hβ, one_mul, Real.exp_log hZ]

lemma optExpValue_pos (h : Fin (H + 1)) (s : S) : 0 < optExpValue M β h s := Real.exp_pos _

lemma optEntropicValue_eq_inv_mul_log (hβ : β ≠ 0) (h : Fin (H + 1)) (s : S) :
    optEntropicValue M β h s = β⁻¹ * Real.log (optExpValue M β h s) := by
  rw [optExpValue, Real.log_exp, ← mul_assoc, inv_mul_cancel₀ hβ, one_mul]

/-- For `β > 0`, the optimal exponential value dominates the exponential value of every policy. -/
lemma expValue_le_optExpValue (hβ : 0 < β) {π : Policy S A H} {h : Fin (H + 1)} {s : S}
    (hZ : 0 < expValue M β π h s) : expValue M β π h s ≤ optExpValue M β h s := by
  rw [expValue_eq_exp_mul_entropicValue M β hβ.ne' hZ, optExpValue]
  exact Real.exp_le_exp.2
    (mul_le_mul_of_nonneg_left (entropicValue_le_optEntropicValue M β π h s) hβ.le)

/-- For `β < 0`, the optimal exponential value is dominated by the exponential value of every
policy. -/
lemma optExpValue_le_expValue (hβ : β < 0) {π : Policy S A H} {h : Fin (H + 1)} {s : S}
    (hZ : 0 < expValue M β π h s) : optExpValue M β h s ≤ expValue M β π h s := by
  rw [expValue_eq_exp_mul_entropicValue M β hβ.ne hZ, optExpValue]
  exact Real.exp_le_exp.2
    (mul_le_mul_of_nonpos_left (entropicValue_le_optEntropicValue M β π h s) hβ.le)

lemma exists_expValue_eq_optExpValue (hβ : β ≠ 0) {h : Fin (H + 1)} {s : S}
    (hZ : ∀ π, 0 < expValue M β π h s) : ∃ π, expValue M β π h s = optExpValue M β h s := by
  obtain ⟨π, hπ⟩ := exists_entropicValue_eq_optEntropicValue M β h s
  exact ⟨π, by rw [expValue_eq_exp_mul_entropicValue M β hβ (hZ π), hπ, optExpValue]⟩

lemma optExpValue_last (s : S) : optExpValue M β (Fin.last H) s = 1 := by
  simp [optExpValue, optEntropicValue, entropicValue, expValue_last]

/-- A greedy policy with respect to the optimal exponential state-action values: it maximizes
`U*_h(s, ·)` if `β > 0` and minimizes it otherwise. -/
noncomputable def optPolicy : Policy S A H := fun h s ↦
  if 0 < β then (Finite.exists_max (optExpQ M β h s)).choose
  else (Finite.exists_min (optExpQ M β h s)).choose

lemma optExpQ_le_optExpQ_optPolicy (hβ : 0 < β) (h : Fin H) (s : S) (a : A) :
    optExpQ M β h s a ≤ optExpQ M β h s (optPolicy M β h s) := by
  simp only [optPolicy, hβ, ↓reduceIte]
  exact (Finite.exists_max _).choose_spec a

lemma optExpQ_optPolicy_le_optExpQ (hβ : β < 0) (h : Fin H) (s : S) (a : A) :
    optExpQ M β h s (optPolicy M β h s) ≤ optExpQ M β h s a := by
  simp only [optPolicy, hβ.not_gt, ↓reduceIte]
  exact (Finite.exists_min _).choose_spec a

lemma expQ_le_optExpQ (hβ : 0 < β)
    (hR : ∀ h s a, Integrable (fun x ↦ Real.exp (β * x)) (M.reward h (s, a)))
    (π : Policy S A H) (h : Fin H) (s : S) (a : A) : expQ M β π h s a ≤ optExpQ M β h s a := by
  rw [expQ, optExpQ]
  exact mul_le_mul_of_nonneg_left (integral_mono Integrable.of_finite Integrable.of_finite
    fun s' ↦ expValue_le_optExpValue M β hβ (expValue_pos M β hR π _ _))
    (integral_nonneg fun _ ↦ (Real.exp_pos _).le)

lemma optExpQ_le_expQ (hβ : β < 0)
    (hR : ∀ h s a, Integrable (fun x ↦ Real.exp (β * x)) (M.reward h (s, a)))
    (π : Policy S A H) (h : Fin H) (s : S) (a : A) : optExpQ M β h s a ≤ expQ M β π h s a := by
  rw [expQ, optExpQ]
  exact mul_le_mul_of_nonneg_left (integral_mono Integrable.of_finite Integrable.of_finite
    fun s' ↦ optExpValue_le_expValue M β hβ (expValue_pos M β hR π _ _))
    (integral_nonneg fun _ ↦ (Real.exp_pos _).le)

/-- The greedy policy with respect to `U*` is optimal from every state at every step. -/
lemma expValue_optPolicy (hβ : β ≠ 0)
    (hR : ∀ h s a, Integrable (fun x ↦ Real.exp (β * x)) (M.reward h (s, a)))
    (h : Fin (H + 1)) (s : S) :
    expValue M β (optPolicy M β) h s = optExpValue M β h s := by
  induction h using Fin.reverseInduction generalizing s with
  | last => rw [expValue_last, optExpValue_last]
  | cast i ih =>
    have hQ : expValue M β (optPolicy M β) i.castSucc s
        = optExpQ M β i s (optPolicy M β i s) := by
      rw [expValue_castSucc M β hR, expQ, optExpQ]
      simp_rw [ih]
    obtain ⟨π, hπ⟩ := exists_expValue_eq_optExpValue M β hβ
      (fun π ↦ expValue_pos M β hR π i.castSucc s)
    rcases hβ.lt_or_gt with hβ' | hβ'
    · refine le_antisymm ?_ (optExpValue_le_expValue M β hβ' (expValue_pos M β hR _ _ _))
      rw [hQ, ← hπ, expValue_castSucc M β hR]
      exact (optExpQ_optPolicy_le_optExpQ M β hβ' i s _).trans
        (optExpQ_le_expQ M β hβ' hR π i s (π i s))
    · refine le_antisymm (expValue_le_optExpValue M β hβ' (expValue_pos M β hR _ _ _)) ?_
      rw [hQ, ← hπ, expValue_castSucc M β hR]
      exact (expQ_le_optExpQ M β hβ' hR π i s (π i s)).trans
        (optExpQ_le_optExpQ_optPolicy M β hβ' i s _)

/-- **Optimal exponential Bellman equation**: `Z*_h(s) = U*_h(s, π*_h(s))` for the greedy
policy `π*`. -/
lemma optExpValue_castSucc_eq (hβ : β ≠ 0)
    (hR : ∀ h s a, Integrable (fun x ↦ Real.exp (β * x)) (M.reward h (s, a)))
    (h : Fin H) (s : S) :
    optExpValue M β h.castSucc s = optExpQ M β h s (optPolicy M β h s) := by
  rw [← expValue_optPolicy M β hβ hR, expValue_castSucc M β hR, expQ, optExpQ]
  simp_rw [expValue_optPolicy M β hβ hR]

/-- For `β > 0`, `Z*_h(s) = max_a U*_h(s, a)`. -/
lemma optExpQ_le_optExpValue (hβ : 0 < β)
    (hR : ∀ h s a, Integrable (fun x ↦ Real.exp (β * x)) (M.reward h (s, a)))
    (h : Fin H) (s : S) (a : A) : optExpQ M β h s a ≤ optExpValue M β h.castSucc s := by
  rw [optExpValue_castSucc_eq M β hβ.ne' hR]
  exact optExpQ_le_optExpQ_optPolicy M β hβ h s a

/-- For `β < 0`, `Z*_h(s) = min_a U*_h(s, a)`. -/
lemma optExpValue_le_optExpQ (hβ : β < 0)
    (hR : ∀ h s a, Integrable (fun x ↦ Real.exp (β * x)) (M.reward h (s, a)))
    (h : Fin H) (s : S) (a : A) : optExpValue M β h.castSucc s ≤ optExpQ M β h s a := by
  rw [optExpValue_castSucc_eq M β hβ.ne hR]
  exact optExpQ_optPolicy_le_optExpQ M β hβ h s a

/-- Range of the optimal exponential values for rewards in `[0, 1]`. -/
lemma optExpValue_mem_Icc (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β ≠ 0) (h : Fin (H + 1))
    (s : S) :
    optExpValue M β h s
      ∈ Set.Icc (min 1 (Real.exp (β * (H - h : ℕ)))) (max 1 (Real.exp (β * (H - h : ℕ)))) := by
  obtain ⟨π, hπ⟩ := exists_expValue_eq_optExpValue M β hβ
    (fun π ↦ expValue_pos M β (integrable_exp_mul_of_rewardsIn M β hM) π h s)
  rw [← hπ]
  exact expValue_mem_Icc M β hM π h s

/-- Range of the optimal exponential state-action values for rewards in `[0, 1]`. -/
lemma optExpQ_mem_Icc (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β ≠ 0) (h : Fin H) (s : S)
    (a : A) :
    optExpQ M β h s a
      ∈ Set.Icc (min 1 (Real.exp (β * (H - h : ℕ)))) (max 1 (Real.exp (β * (H - h : ℕ)))) := by
  rw [optExpQ, show ((H - (h : ℕ) : ℕ) : ℝ) = ((H - (h.castSucc : ℕ) : ℕ) : ℝ) from rfl,
    cast_sub_castSucc]
  exact mul_mem_Icc_min_max_exp β zero_le_one (Nat.cast_nonneg _)
    (integral_exp_mul_reward_mem_Icc M β hM h s a)
    (integral_trans_mem_Icc M (fun s' ↦ optExpValue_mem_Icc M β hM hβ h.succ s') h s a)

/-! ### The value gap -/

/-- The value gap in the exponential space: `V*_h(s) - V^π_h(s) = β⁻¹ log (Z*_h(s) / Z^π_h(s))`. -/
lemma optEntropicValue_sub_entropicValue (hβ : β ≠ 0) {π : Policy S A H} {h : Fin (H + 1)}
    {s : S} (hZ : 0 < expValue M β π h s) :
    optEntropicValue M β h s - entropicValue M β π h s
      = β⁻¹ * Real.log (optExpValue M β h s / expValue M β π h s) := by
  rw [optEntropicValue_eq_inv_mul_log M β hβ, entropicValue,
    Real.log_div (optExpValue_pos M β h s).ne' hZ.ne', mul_sub]

/-- For `β > 0`, `Z*_h(s) ≤ e^{β ε} Z^π_h(s)` implies `V*_h(s) - V^π_h(s) ≤ ε`. -/
lemma optEntropicValue_sub_entropicValue_le_of_pos (hβ : 0 < β) {ε : ℝ} {π : Policy S A H}
    {h : Fin (H + 1)} {s : S} (hZ : 0 < expValue M β π h s)
    (hle : optExpValue M β h s ≤ Real.exp (β * ε) * expValue M β π h s) :
    optEntropicValue M β h s - entropicValue M β π h s ≤ ε := by
  rw [optEntropicValue_sub_entropicValue M β hβ.ne' hZ]
  have h1 : optExpValue M β h s / expValue M β π h s ≤ Real.exp (β * ε) := (div_le_iff₀ hZ).2 hle
  have h2 : Real.log (optExpValue M β h s / expValue M β π h s) ≤ β * ε :=
    (Real.log_le_log (div_pos (optExpValue_pos M β h s) hZ) h1).trans_eq (Real.log_exp _)
  calc β⁻¹ * Real.log (optExpValue M β h s / expValue M β π h s) ≤ β⁻¹ * (β * ε) :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hβ.le)
    _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ hβ.ne', one_mul]

/-- For `β < 0`, `e^{β ε} Z^π_h(s) ≤ Z*_h(s)` implies `V*_h(s) - V^π_h(s) ≤ ε`. -/
lemma optEntropicValue_sub_entropicValue_le_of_neg (hβ : β < 0) {ε : ℝ} {π : Policy S A H}
    {h : Fin (H + 1)} {s : S} (hZ : 0 < expValue M β π h s)
    (hle : Real.exp (β * ε) * expValue M β π h s ≤ optExpValue M β h s) :
    optEntropicValue M β h s - entropicValue M β π h s ≤ ε := by
  rw [optEntropicValue_sub_entropicValue M β hβ.ne hZ]
  have h1 : Real.exp (β * ε) ≤ optExpValue M β h s / expValue M β π h s := (le_div_iff₀ hZ).2 hle
  have h2 : β * ε ≤ Real.log (optExpValue M β h s / expValue M β π h s) :=
    (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) h1)
  calc β⁻¹ * Real.log (optExpValue M β h s / expValue M β π h s) ≤ β⁻¹ * (β * ε) :=
        mul_le_mul_of_nonpos_left h2 (inv_nonpos.2 hβ.le)
    _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ hβ.ne, one_mul]

end Learning.MDP.Episodic
