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

For a finite-horizon MDP `M` with horizon `H`, a risk parameter `β` and a policy
`π : ℕ → S → A` measurable at every step:

* the **exponential Bellman equation** `Z^π_h(s) = U^π_h(s, π_h(s))` for `h < H`
  (`expValue_succ`) and `Z^π_h = 1` for `h ≥ H` (`expValue_of_le`), for bounded rewards; its
  Lebesgue-integral form `lexpValue_succ` holds without any hypothesis;
* the return of `n` steps of a trajectory lies in `[n a, n b]` for rewards in `[a, b]`
  (`ae_episodeReturn_mem_Icc`), so that the exponential return is integrable
  (`integrable_exp_mul_episodeReturn`) and the exponential values are positive (`expValue_pos`)
  and measurable in the state (`measurable_expValue`);
* for rewards in `[0, 1]`, the **ranges** of `Z^π_h`, `U^π_h`, `Z*_h`, `U*_h` between `1` and
  `e^{β (H - h)}` (`expValue_mem_Icc`, …), and the bounds `0 ≤ G_max ≤ H` on the maximal return
  (`maxReturn_nonneg`, `maxReturn_le`);
* the **optimal values**, for a countable discrete state space, a finite action space and rewards
  in `[0, 1]`: the Bellman-recursive value `optExpValueRec` is the exponential value of the greedy
  policy `optPolicy` (`expValue_optPolicy`), which is optimal from every state at every step, so
  that the supremum `V*_h(s)` over all measurable policies is attained (`optEntropicValue_eq`,
  `exists_entropicValue_eq_optEntropicValue`), `Z*_h(s)` is the largest (`β > 0`) or smallest
  (`β < 0`) value of a policy (`expValue_le_optExpValue`, `optExpValue_le_expValue`), and the
  **optimal Bellman equation** `Z*_h(s) = max_a U*_h(s, a)` (resp. `min`) holds
  (`optExpValue_succ_eq`, `optExpQ_le_optExpValue`, `optExpValue_le_optExpQ`);
* the value gap `V*_h(s) - V^π_h(s) = β⁻¹ log (Z*_h(s) / Z^π_h(s))` and its consequences
  (`optEntropicValue_sub_entropicValue`, `optEntropicValue_sub_entropicValue_le_of_pos`,
  `optEntropicValue_sub_entropicValue_le_of_neg`).

Steps are `0`-indexed: the state value at the step `h` has `H - h` steps to go, so the paper's
range `e^{β (H + 1 - h)}` is `e^{β (H - h)}` here. Statements about all steps are proved by
induction on the number of steps to go (`horizon_induction`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP
open scoped ENNReal

namespace Learning.MDP.Episodic

/-- Induction on the number `H - h` of steps to go: a property which holds from the step `H` on
and propagates from a step to the previous one holds at every step. -/
lemma horizon_induction {P : ℕ → Prop} (H : ℕ) (h0 : ∀ h, H ≤ h → P h)
    (hstep : ∀ h, h < H → P (h + 1) → P h) (h : ℕ) : P h := by
  obtain ⟨n, hn⟩ : ∃ n, H - h = n := ⟨_, rfl⟩
  induction n generalizing h with
  | zero => exact h0 h (by omega)
  | succ n ih => exact hstep h (by omega) (ih (h + 1) (by omega))

lemma cast_sub_eq_one_add {H h : ℕ} (hh : h < H) :
    ((H - h : ℕ) : ℝ) = 1 + ((H - (h + 1) : ℕ) : ℝ) := by
  rw [show H - h = (H - (h + 1)) + 1 by omega]
  push_cast
  ring

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : EpisodicMDP S A) (H : ℕ)
  (β : ℝ)

lemma measurable_exp_mul_episodeReturn (n : ℕ) :
    Measurable fun x : ℕ → Round (S × ℕ) A ℝ ↦ Real.exp (β * episodeReturn n x) :=
  Real.measurable_exp.comp ((measurable_episodeReturn n).const_mul β)

/-! ### Lebesgue integrals of the exponential return -/

/-- The Lebesgue integral `∫⁻ exp (β R_h)` of the exponential return of `π` from the state `s` at
the step `h`, with the horizon `H`. -/
noncomputable def lexpValue (π : ℕ → S → A) (h : ℕ) (s : S) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (β * episodeReturn (H - h) x)) ∂stepLaw M π (s, h)

lemma expValue_eq_toReal_lexpValue (π : ℕ → S → A) (h : ℕ) (s : S) :
    expValue M H β π h s = (lexpValue M H β π h s).toReal :=
  integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)
    (measurable_exp_mul_episodeReturn β _).aestronglyMeasurable

lemma measurable_lexpValue (π : ℕ → S → A) (h : ℕ) : Measurable (lexpValue M H β π h) := by
  have := Measurable.lintegral_kernel_prod_right' (κ := stepLawKernel M π h)
    (f := fun p : S × (ℕ → Round (S × ℕ) A ℝ) ↦
      ENNReal.ofReal (Real.exp (β * episodeReturn (H - h) p.2)))
    (ENNReal.measurable_ofReal.comp ((measurable_exp_mul_episodeReturn β _).comp measurable_snd))
  unfold lexpValue
  simpa only [stepLawKernel_apply] using this

lemma measurable_expValue (π : ℕ → S → A) (h : ℕ) : Measurable (expValue M H β π h) := by
  have := ENNReal.measurable_toReal.comp (measurable_lexpValue M H β π h)
  simp only [Function.comp_def] at this
  simpa only [← expValue_eq_toReal_lexpValue] using this

lemma lexpValue_of_le {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) {h : ℕ} (hh : H ≤ h) (s : S) :
    lexpValue M H β π h s = 1 := by
  simp [lexpValue, Nat.sub_eq_zero_of_le hh, stepLaw_univ M hπ]

lemma expValue_of_le {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) {h : ℕ} (hh : H ≤ h) (s : S) :
    expValue M H β π h s = 1 := by
  rw [expValue_eq_toReal_lexpValue, lexpValue_of_le M H β hπ hh, ENNReal.toReal_one]

variable [MeasurableSingletonClass S] [MeasurableSingletonClass A]

/-- The exponential Bellman equation for the Lebesgue integrals of the exponential return. -/
lemma lexpValue_succ {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) {h : ℕ} (hh : h < H) (s : S) :
    lexpValue M H β π h s
      = (∫⁻ r, ENNReal.ofReal (Real.exp (β * r)) ∂M.reward h (s, π h s))
        * ∫⁻ s', lexpValue M H β π (h + 1) s' ∂M.trans h (s, π h s) := by
  have hn : H - h = (H - (h + 1)) + 1 := by omega
  have hmeas : Measurable fun z : (ℝ × S) × (ℕ → Round (S × ℕ) A ℝ) ↦
      ENNReal.ofReal (Real.exp (β * z.1.1))
        * ENNReal.ofReal (Real.exp (β * episodeReturn (H - (h + 1)) z.2)) :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_fst.fst.const_mul β))).mul
      (ENNReal.measurable_ofReal.comp ((measurable_exp_mul_episodeReturn β _).comp measurable_snd))
  calc lexpValue M H β π h s
      = ∫⁻ x, ENNReal.ofReal (Real.exp (β * IT.feedback 0 x))
          * ENNReal.ofReal (Real.exp (β * episodeReturn (H - (h + 1)) (shiftRound x)))
          ∂stepLaw M π (s, h) := by
        refine lintegral_congr fun x ↦ ?_
        rw [hn, episodeReturn_succ_eq_add_shiftRound, mul_add, Real.exp_add,
          ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ = ∫⁻ q, ∫⁻ y, ENNReal.ofReal (Real.exp (β * q.1))
          * ENNReal.ofReal (Real.exp (β * episodeReturn (H - (h + 1)) y))
          ∂stepLaw M π (q.2, h + 1) ∂((M.reward h (s, π h s)).prod (M.trans h (s, π h s))) :=
        lintegral_stepLaw_succ M hπ s h hmeas
    _ = ∫⁻ q, ENNReal.ofReal (Real.exp (β * q.1)) * lexpValue M H β π (h + 1) q.2
          ∂((M.reward h (s, π h s)).prod (M.trans h (s, π h s))) := by
        refine lintegral_congr fun q ↦ ?_
        exact lintegral_const_mul _
          (ENNReal.measurable_ofReal.comp (measurable_exp_mul_episodeReturn β _))
    _ = _ := lintegral_prod_mul (f := fun r ↦ ENNReal.ofReal (Real.exp (β * r)))
        (g := fun s' ↦ lexpValue M H β π (h + 1) s')
        (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          (measurable_id.const_mul β))).aemeasurable
        (measurable_lexpValue M H β π (h + 1)).aemeasurable

/-! ### Bounded rewards -/

/-- The return of `n` steps lies in `[n a, n b]` for rewards in `[a, b]`. -/
lemma ae_episodeReturn_mem_Icc {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) {π : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h)) (n : ℕ) :
    ∀ h s, ∀ᵐ x ∂stepLaw M π (s, h), episodeReturn n x ∈ Set.Icc (n * a) (n * b) := by
  induction n with
  | zero => intro h s; simp
  | succ n ih =>
    intro h s
    have h0 : ∀ᵐ x ∂stepLaw M π (s, h), IT.feedback 0 x ∈ Set.Icc a b := by
      have hl := hasLaw_feedback_zero_stepLaw M hπ s h
      exact ae_of_ae_map (p := fun r ↦ r ∈ Set.Icc a b) hl.aemeasurable
        (by rw [hl.map_eq]; exact hM h s (π h s))
    have h1 : ∀ᵐ x ∂stepLaw M π (s, h),
        episodeReturn n (shiftRound x) ∈ Set.Icc (n * a) (n * b) :=
      ae_stepLaw_succ_of_ae M hπ (P := fun _ _ y ↦ episodeReturn n y ∈ Set.Icc (n * a) (n * b))
        (measurableSet_Icc.preimage ((measurable_episodeReturn n).comp measurable_snd))
        (Filter.Eventually.of_forall fun _ s' ↦ ih (h + 1) s')
    filter_upwards [h0, h1] with x h0 h1
    rw [episodeReturn_succ_eq_add_shiftRound]
    push_cast
    constructor <;> nlinarith [h0.1, h0.2, h1.1, h1.2]

/-- The exponential return of `n` steps is bounded by `exp (|β| n max (|a|, |b|))` for rewards in
`[a, b]`. -/
lemma ae_exp_mul_episodeReturn_le {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b))
    {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) (n h : ℕ) (s : S) :
    ∀ᵐ x ∂stepLaw M π (s, h),
      Real.exp (β * episodeReturn n x) ≤ Real.exp (|β| * (n * max |a| |b|)) := by
  filter_upwards [ae_episodeReturn_mem_Icc M hM hπ n h s] with x hx
  rw [Real.exp_le_exp]
  calc β * episodeReturn n x ≤ |β * episodeReturn n x| := le_abs_self _
    _ = |β| * |episodeReturn n x| := abs_mul _ _
    _ ≤ |β| * (n * max |a| |b|) := by
        gcongr
        rw [abs_le]
        have h1 : |a| ≤ max |a| |b| := le_max_left _ _
        have h2 : |b| ≤ max |a| |b| := le_max_right _ _
        have ha := abs_le.1 (le_refl |a|)
        have hb := abs_le.1 (le_refl |b|)
        constructor <;> nlinarith [hx.1, hx.2, n.cast_nonneg (α := ℝ), abs_nonneg a, abs_nonneg b]

lemma integrable_exp_mul_episodeReturn {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b))
    {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) (n h : ℕ) (s : S) :
    Integrable (fun x ↦ Real.exp (β * episodeReturn n x)) (stepLaw M π (s, h)) := by
  refine Integrable.of_bound (measurable_exp_mul_episodeReturn β n).aestronglyMeasurable
    (Real.exp (|β| * (n * max |a| |b|))) ?_
  filter_upwards [ae_exp_mul_episodeReturn_le M β hM hπ n h s] with x hx
  rwa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma lexpValue_le_ofReal {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) {π : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h)) (h : ℕ) (s : S) :
    lexpValue M H β π h s ≤ ENNReal.ofReal (Real.exp (|β| * ((H - h : ℕ) * max |a| |b|))) := by
  calc lexpValue M H β π h s
      ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (|β| * ((H - h : ℕ) * max |a| |b|)))
          ∂stepLaw M π (s, h) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_exp_mul_episodeReturn_le M β hM hπ (H - h) h s] with x hx
        exact ENNReal.ofReal_le_ofReal hx
    _ = _ := by rw [lintegral_const, stepLaw_univ M hπ, mul_one]

lemma lexpValue_lt_top {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) {π : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h)) (h : ℕ) (s : S) : lexpValue M H β π h s < ∞ :=
  (lexpValue_le_ofReal M H β hM hπ h s).trans_lt ENNReal.ofReal_lt_top

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- Bounded rewards have finite exponential moments. -/
lemma integrable_exp_mul_of_rewardsIn {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) (h : ℕ) (s : S)
    (a' : A) : Integrable (fun x ↦ Real.exp (β * x)) (M.reward h (s, a')) := by
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

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
lemma rewardsIn_of_hasRewardFn {r : ℕ → S → A → ℝ} (hM : M.HasRewardFn r) {I : Set ℝ}
    (hI : MeasurableSet I) (hr : ∀ h s a, r h s a ∈ I) : M.RewardsIn I := by
  intro h s a
  rw [hM h s a]
  exact (ae_dirac_iff (p := (· ∈ I)) hI).2 (hr h s a)

/-! ### The exponential Bellman equation -/

lemma integral_exp_mul_eq_toReal (μ : Measure ℝ) :
    ∫ x, Real.exp (β * x) ∂μ = (∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂μ).toReal :=
  integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)
    (Real.measurable_exp.comp (measurable_id.const_mul β)).aestronglyMeasurable

/-- **Exponential Bellman equation**: `Z^π_h(s) = U^π_h(s, π_h(s))` for `h < H` and bounded
rewards. -/
lemma expValue_succ {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) {π : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h)) {h : ℕ}
    (hh : h < H) (s : S) : expValue M H β π h s = expQ M H β π h s (π h s) := by
  rw [expValue_eq_toReal_lexpValue, lexpValue_succ M H β hπ hh, ENNReal.toReal_mul, expQ,
    integral_exp_mul_eq_toReal]
  congr 1
  simp_rw [expValue_eq_toReal_lexpValue]
  exact (integral_toReal (measurable_lexpValue M H β π (h + 1)).aemeasurable
    (Filter.Eventually.of_forall fun s' ↦ lexpValue_lt_top M H β hM hπ (h + 1) s')).symm

/-- The exponential value only depends on the policy at the steps before the horizon. -/
lemma expValue_congr {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) {π π' : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h)) (hπ' : ∀ h, Measurable (π' h)) (heq : ∀ k < H, π k = π' k)
    (h : ℕ) (s : S) :
    expValue M H β π h s = expValue M H β π' h s := by
  induction h using horizon_induction H generalizing s with
  | h0 h hh => rw [expValue_of_le M H β hπ hh, expValue_of_le M H β hπ' hh]
  | hstep h hh ih =>
    rw [expValue_succ M H β hM hπ hh, expValue_succ M H β hM hπ' hh, expQ, expQ, heq h hh]
    exact congrArg (fun z ↦ (∫ x, Real.exp (β * x) ∂M.reward h (s, π' h s)) * z)
      (integral_congr_ae (Filter.Eventually.of_forall fun s' ↦ ih s'))

/-- The entropic value only depends on the policy at the steps before the horizon. -/
lemma entropicValue_congr {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) {π π' : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h)) (hπ' : ∀ h, Measurable (π' h)) (heq : ∀ k < H, π k = π' k)
    (h : ℕ) (s : S) :
    entropicValue M H β π h s = entropicValue M H β π' h s := by
  rw [entropicValue, entropicValue, expValue_congr M H β hM hπ hπ' heq]

lemma expValue_pos {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) {π : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h)) (h : ℕ) (s : S) : 0 < expValue M H β π h s := by
  rw [expValue, integral_pos_iff_support_of_nonneg (fun _ ↦ (Real.exp_pos _).le)
    (integrable_exp_mul_episodeReturn M β hM hπ _ h s),
    Function.support_eq_univ fun _ ↦ (Real.exp_pos _).ne', stepLaw_univ M hπ]
  exact zero_lt_one

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- The exponential Bellman operator for an MDP with a reward function. -/
lemma expQ_of_hasRewardFn {r : ℕ → S → A → ℝ} (hM : M.HasRewardFn r) (π : ℕ → S → A)
    (h : ℕ) (s : S) (a : A) :
    expQ M H β π h s a
      = Real.exp (β * r h s a) * ∫ s', expValue M H β π (h + 1) s' ∂M.trans h (s, a) := by
  rw [expQ, hM h s a, integral_dirac]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- The optimal exponential Bellman operator for an MDP with a reward function. -/
lemma optExpQ_of_hasRewardFn {r : ℕ → S → A → ℝ} (hM : M.HasRewardFn r) (h : ℕ) (s : S) (a : A) :
    optExpQ M H β h s a
      = Real.exp (β * r h s a) * ∫ s', optExpValue M H β (h + 1) s' ∂M.trans h (s, a) := by
  rw [optExpQ, hM h s a, integral_dirac]

omit [MeasurableSingletonClass A] in
/-- On a finite state space, the integral against a transition kernel is the expectation under
the transition vector. -/
lemma integral_eq_vecExp_transVec [Fintype S] (h : ℕ) (s : S) (a : A) (f : S → ℝ) :
    ∫ s', f s' ∂M.trans h (s, a) = vecExp (M.transVec h s a) f := by
  rw [integral_fintype Integrable.of_finite]
  simp only [smul_eq_mul]
  rfl

omit [MeasurableSingletonClass A] in
lemma expQ_of_hasRewardFn_eq_vecExp [Fintype S] {r : ℕ → S → A → ℝ} (hM : M.HasRewardFn r)
    (π : ℕ → S → A) (h : ℕ) (s : S) (a : A) :
    expQ M H β π h s a
      = Real.exp (β * r h s a) * vecExp (M.transVec h s a) (expValue M H β π (h + 1)) := by
  rw [expQ, hM h s a, integral_dirac, integral_eq_vecExp_transVec]

omit [MeasurableSingletonClass A] in
lemma optExpQ_of_hasRewardFn_eq_vecExp [Fintype S] {r : ℕ → S → A → ℝ} (hM : M.HasRewardFn r)
    (h : ℕ) (s : S) (a : A) :
    optExpQ M H β h s a
      = Real.exp (β * r h s a) * vecExp (M.transVec h s a) (optExpValue M H β (h + 1)) := by
  rw [optExpQ, hM h s a, integral_dirac, integral_eq_vecExp_transVec]

/-! ### Ranges for rewards in `[0, 1]` -/

omit [MeasurableSpace S] [MeasurableSpace A] [MeasurableSingletonClass S]
  [MeasurableSingletonClass A] in
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

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
lemma integral_exp_mul_reward_mem_Icc (hM : M.RewardsIn (Set.Icc 0 1)) (h : ℕ) (s : S) (a : A) :
    ∫ x, Real.exp (β * x) ∂M.reward h (s, a)
      ∈ Set.Icc (min 1 (Real.exp (β * 1))) (max 1 (Real.exp (β * 1))) :=
  integral_mem_Icc_of_ae_mem_Icc ((hM h s a).mono fun _ hx ↦ exp_mul_mem_Icc_min_max hx)
    (Real.measurable_exp.comp (measurable_id.const_mul β)).aestronglyMeasurable

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
lemma integral_trans_mem_Icc {a b : ℝ} {f : S → ℝ} (hf : Measurable f)
    (hfab : ∀ s', f s' ∈ Set.Icc a b) (h : ℕ) (s : S) (a' : A) :
    ∫ s', f s' ∂M.trans h (s, a') ∈ Set.Icc a b :=
  integral_mem_Icc_of_ae_mem_Icc (Filter.Eventually.of_forall hfab) hf.aestronglyMeasurable

/-- Range of the exponential values for rewards in `[0, 1]`. -/
lemma expValue_mem_Icc (hM : M.RewardsIn (Set.Icc 0 1)) {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h))
    (h : ℕ) (s : S) :
    expValue M H β π h s
      ∈ Set.Icc (min 1 (Real.exp (β * (H - h : ℕ)))) (max 1 (Real.exp (β * (H - h : ℕ)))) := by
  induction h using horizon_induction H generalizing s with
  | h0 h hh => simp [expValue_of_le M H β hπ hh, Nat.sub_eq_zero_of_le hh]
  | hstep h hh ih =>
    rw [expValue_succ M H β hM hπ hh, expQ, cast_sub_eq_one_add hh]
    exact mul_mem_Icc_min_max_exp β zero_le_one (Nat.cast_nonneg _)
      (integral_exp_mul_reward_mem_Icc M β hM h s _)
      (integral_trans_mem_Icc M (measurable_expValue M H β π (h + 1)) ih h s _)

/-- Range of the exponential state-action values for rewards in `[0, 1]`. -/
lemma expQ_mem_Icc (hM : M.RewardsIn (Set.Icc 0 1)) {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h))
    {h : ℕ} (hh : h < H) (s : S) (a : A) :
    expQ M H β π h s a
      ∈ Set.Icc (min 1 (Real.exp (β * (H - h : ℕ)))) (max 1 (Real.exp (β * (H - h : ℕ)))) := by
  rw [expQ, cast_sub_eq_one_add hh]
  exact mul_mem_Icc_min_max_exp β zero_le_one (Nat.cast_nonneg _)
    (integral_exp_mul_reward_mem_Icc M β hM h s a)
    (integral_trans_mem_Icc M (measurable_expValue M H β π (h + 1))
      (fun s' ↦ expValue_mem_Icc M H β hM hπ (h + 1) s') h s a)

/-- The return of `n` steps lies in `[0, n]` for rewards in `[0, 1]`. -/
lemma ae_episodeReturn_mem_Icc_of_unit (hM : M.RewardsIn (Set.Icc 0 1)) {π : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h))
    (n h : ℕ) (s : S) : ∀ᵐ x ∂stepLaw M π (s, h), episodeReturn n x ∈ Set.Icc 0 (n : ℝ) := by
  simpa using ae_episodeReturn_mem_Icc M hM hπ n h s

/-! ### The maximal return -/

lemma essSup_episodeReturn_mem_Icc (hM : M.RewardsIn (Set.Icc 0 1)) {π : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h))
    (s₁ : S) : essSup (episodeReturn H) (stepLaw M π (s₁, 0)) ∈ Set.Icc 0 (H : ℝ) := by
  have := isProbabilityMeasure_stepLaw M hπ (s₁, 0)
  have hae := ae_episodeReturn_mem_Icc_of_unit M hM hπ H 0 s₁
  have hle : ∀ᵐ x ∂stepLaw M π (s₁, 0), episodeReturn H x ≤ H := hae.mono fun _ hx ↦ hx.2
  have hge : ∀ᵐ x ∂stepLaw M π (s₁, 0), 0 ≤ episodeReturn H x := hae.mono fun _ hx ↦ hx.1
  constructor
  · obtain ⟨x, hx1, hx2⟩ :=
      ((ae_le_essSup (Filter.isBoundedUnder_of_eventually_le hle)).and hge).exists
    exact hx2.trans hx1
  · exact essSup_le_of_ae_le _ hle (Filter.isCoboundedUnder_le_of_eventually_le _ hge)

lemma bddAbove_essSup_episodeReturn (hM : M.RewardsIn (Set.Icc 0 1)) (s₁ : S) :
    BddAbove (Set.range fun π : {π : ℕ → S → A // ∀ h, Measurable (π h)} ↦
      essSup (episodeReturn H) (stepLaw M π (s₁, 0))) :=
  ⟨H, by
    rintro _ ⟨π, rfl⟩
    exact (essSup_episodeReturn_mem_Icc M H hM π.2 s₁).2⟩

/-- The return of an episode is at most the maximal return, for rewards in `[0, 1]`. -/
lemma ae_episodeReturn_le_maxReturn (hM : M.RewardsIn (Set.Icc 0 1)) {π : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h))
    (s₁ : S) : ∀ᵐ x ∂stepLaw M π (s₁, 0), episodeReturn H x ≤ maxReturn M H s₁ := by
  have hle : ∀ᵐ x ∂stepLaw M π (s₁, 0), episodeReturn H x ≤ H :=
    (ae_episodeReturn_mem_Icc_of_unit M hM hπ H 0 s₁).mono fun _ hx ↦ hx.2
  filter_upwards [ae_le_essSup (Filter.isBoundedUnder_of_eventually_le hle)] with x hx
  exact hx.trans (le_ciSup (f := fun π : {π : ℕ → S → A // ∀ h, Measurable (π h)} ↦
    essSup (episodeReturn H) (stepLaw M π (s₁, 0))) (bddAbove_essSup_episodeReturn M H hM s₁)
      ⟨π, hπ⟩)

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
lemma measurable_const_policy (a : A) (h : ℕ) : Measurable ((fun _ _ ↦ a : ℕ → S → A) h) :=
  measurable_const

lemma maxReturn_nonneg [Nonempty A] (hM : M.RewardsIn (Set.Icc 0 1)) (s₁ : S) :
    0 ≤ maxReturn M H s₁ :=
  (essSup_episodeReturn_mem_Icc M H hM (measurable_const_policy (Classical.arbitrary A))
    s₁).1.trans (le_ciSup (f := fun π : {π : ℕ → S → A // ∀ h, Measurable (π h)} ↦
      essSup (episodeReturn H) (stepLaw M π (s₁, 0))) (bddAbove_essSup_episodeReturn M H hM s₁)
      ⟨_, measurable_const_policy (Classical.arbitrary A)⟩)

lemma maxReturn_le [Nonempty A] (hM : M.RewardsIn (Set.Icc 0 1)) (s₁ : S) :
    maxReturn M H s₁ ≤ H :=
  ciSup_le (f := fun π : {π : ℕ → S → A // ∀ h, Measurable (π h)} ↦
    essSup (episodeReturn H) (stepLaw M π (s₁, 0)))
    fun π ↦ (essSup_episodeReturn_mem_Icc M H hM π.2 s₁).2

/-! ### Entropic values and their optimum -/

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
lemma expValue_eq_exp_mul_entropicValue (hβ : β ≠ 0) {π : ℕ → S → A} {h : ℕ} {s : S}
    (hZ : 0 < expValue M H β π h s) :
    expValue M H β π h s = Real.exp (β * entropicValue M H β π h s) := by
  rw [entropicValue, ← mul_assoc, mul_inv_cancel₀ hβ, one_mul, Real.exp_log hZ]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
lemma optExpValue_pos (h : ℕ) (s : S) : 0 < optExpValue M H β h s := Real.exp_pos _

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
lemma optEntropicValue_eq_inv_mul_log (hβ : β ≠ 0) (h : ℕ) (s : S) :
    optEntropicValue M H β h s = β⁻¹ * Real.log (optExpValue M H β h s) := by
  rw [optExpValue, Real.log_exp, ← mul_assoc, inv_mul_cancel₀ hβ, one_mul]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- The entropic value of a policy is at most `β⁻¹ log` of the bound on the exponential value. -/
lemma entropicValue_le_of_pos (hβ : 0 < β) {π : ℕ → S → A} {h : ℕ} {s : S} {C : ℝ}
    (hZ : 0 < expValue M H β π h s) (hC : expValue M H β π h s ≤ C) :
    entropicValue M H β π h s ≤ β⁻¹ * Real.log C :=
  mul_le_mul_of_nonneg_left (Real.log_le_log hZ hC) (inv_nonneg.2 hβ.le)

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
lemma entropicValue_le_of_neg (hβ : β < 0) {π : ℕ → S → A} {h : ℕ} {s : S} {c : ℝ}
    (hc : 0 < c) (hC : c ≤ expValue M H β π h s) :
    entropicValue M H β π h s ≤ β⁻¹ * Real.log c :=
  mul_le_mul_of_nonpos_left (Real.log_le_log hc hC) (inv_nonpos.2 hβ.le)

lemma bddAbove_entropicValue (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β ≠ 0) (h : ℕ) (s : S) :
    BddAbove (Set.range fun π : {π : ℕ → S → A // ∀ h, Measurable (π h)} ↦
      entropicValue M H β π h s) := by
  rcases hβ.lt_or_gt with hβ' | hβ'
  · refine ⟨β⁻¹ * Real.log (min 1 (Real.exp (β * (H - h : ℕ)))), ?_⟩
    rintro _ ⟨π, rfl⟩
    exact entropicValue_le_of_neg M H β hβ' (lt_min zero_lt_one (Real.exp_pos _))
      (expValue_mem_Icc M H β hM π.2 h s).1
  · refine ⟨β⁻¹ * Real.log (max 1 (Real.exp (β * (H - h : ℕ)))), ?_⟩
    rintro _ ⟨π, rfl⟩
    exact entropicValue_le_of_pos M H β hβ' (expValue_pos M H β hM π.2 h s)
      (expValue_mem_Icc M H β hM π.2 h s).2

lemma entropicValue_le_optEntropicValue (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β ≠ 0)
    {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) (h : ℕ) (s : S) :
    entropicValue M H β π h s ≤ optEntropicValue M H β h s :=
  le_ciSup (f := fun π : {π : ℕ → S → A // ∀ h, Measurable (π h)} ↦ entropicValue M H β π h s)
    (bddAbove_entropicValue M H β hM hβ h s) ⟨π, hπ⟩

/-- For `β > 0`, the optimal exponential value dominates the exponential value of every policy. -/
lemma expValue_le_optExpValue (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : 0 < β) {π : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h))
    (h : ℕ) (s : S) : expValue M H β π h s ≤ optExpValue M H β h s := by
  rw [expValue_eq_exp_mul_entropicValue M H β hβ.ne' (expValue_pos M H β hM hπ h s), optExpValue]
  exact Real.exp_le_exp.2
    (mul_le_mul_of_nonneg_left (entropicValue_le_optEntropicValue M H β hM hβ.ne' hπ h s) hβ.le)

/-- For `β < 0`, the optimal exponential value is dominated by the exponential value of every
policy. -/
lemma optExpValue_le_expValue (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β < 0) {π : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h))
    (h : ℕ) (s : S) : optExpValue M H β h s ≤ expValue M H β π h s := by
  rw [expValue_eq_exp_mul_entropicValue M H β hβ.ne (expValue_pos M H β hM hπ h s), optExpValue]
  exact Real.exp_le_exp.2
    (mul_le_mul_of_nonpos_left (entropicValue_le_optEntropicValue M H β hM hβ.ne hπ h s) hβ.le)

/-! ### The Bellman recursion of the optimal values -/

section Optimal

/-- The optimal exponential value by backward recursion: `1` from the step `H` on, and the
maximum (`β > 0`) or minimum (`β < 0`) over the actions of the exponential Bellman backup of the
value at the next step. -/
noncomputable def optExpValueRec (h : ℕ) (s : S) : ℝ :=
  if _hh : h < H then
    if 0 < β then
      ⨆ a : A, (∫ x, Real.exp (β * x) ∂M.reward h (s, a))
        * ∫ s', optExpValueRec (h + 1) s' ∂M.trans h (s, a)
    else
      ⨅ a : A, (∫ x, Real.exp (β * x) ∂M.reward h (s, a))
        * ∫ s', optExpValueRec (h + 1) s' ∂M.trans h (s, a)
  else 1
termination_by H - h
decreasing_by all_goals omega

/-- The exponential Bellman backup of the recursive optimal value. -/
noncomputable def optExpQRec (h : ℕ) (s : S) (a : A) : ℝ :=
  (∫ x, Real.exp (β * x) ∂M.reward h (s, a))
    * ∫ s', optExpValueRec M H β (h + 1) s' ∂M.trans h (s, a)

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
lemma optExpValueRec_of_le {h : ℕ} (hh : H ≤ h) (s : S) : optExpValueRec M H β h s = 1 := by
  rw [optExpValueRec]
  simp only [not_lt.2 hh, ↓reduceDIte]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
lemma optExpValueRec_of_lt {h : ℕ} (hh : h < H) (s : S) :
    optExpValueRec M H β h s
      = if 0 < β then ⨆ a, optExpQRec M H β h s a else ⨅ a, optExpQRec M H β h s a := by
  rw [optExpValueRec]
  simp only [hh, ↓reduceDIte]
  rfl

variable [Countable S] [Finite A] [Nonempty A]

/-- The greedy policy of the Bellman recursion: it maximizes `U*_h(s, ·)` if `β > 0` and
minimizes it otherwise. -/
noncomputable def optPolicy (h : ℕ) (s : S) : A :=
  if 0 < β then (Finite.exists_max (optExpQRec M H β h s)).choose
  else (Finite.exists_min (optExpQRec M H β h s)).choose

omit [MeasurableSingletonClass A] in
lemma measurable_optPolicy (h : ℕ) : Measurable (optPolicy M H β h) :=
  measurable_of_countable _

omit [MeasurableSingletonClass S] [Countable S] [MeasurableSingletonClass A] in
lemma optExpQRec_le_optExpQRec_optPolicy (hβ : 0 < β) (h : ℕ) (s : S) (a : A) :
    optExpQRec M H β h s a ≤ optExpQRec M H β h s (optPolicy M H β h s) := by
  simp only [optPolicy, hβ, ↓reduceIte]
  exact (Finite.exists_max _).choose_spec a

omit [MeasurableSingletonClass S] [Countable S] [MeasurableSingletonClass A] in
lemma optExpQRec_optPolicy_le_optExpQRec (hβ : β < 0) (h : ℕ) (s : S) (a : A) :
    optExpQRec M H β h s (optPolicy M H β h s) ≤ optExpQRec M H β h s a := by
  simp only [optPolicy, hβ.not_gt, ↓reduceIte]
  exact (Finite.exists_min _).choose_spec a

omit [MeasurableSingletonClass S] [Countable S] [MeasurableSingletonClass A] in
/-- The recursive optimal value is the backup of the greedy action. -/
lemma optExpValueRec_eq_optExpQRec_optPolicy (hβ : β ≠ 0) {h : ℕ} (hh : h < H) (s : S) :
    optExpValueRec M H β h s = optExpQRec M H β h s (optPolicy M H β h s) := by
  rw [optExpValueRec_of_lt M H β hh]
  rcases hβ.lt_or_gt with hβ' | hβ'
  · simp only [hβ'.not_gt, ↓reduceIte]
    exact le_antisymm (ciInf_le (Finite.bddBelow_range _) _)
      (le_ciInf fun a ↦ optExpQRec_optPolicy_le_optExpQRec M H β hβ' h s a)
  · simp only [hβ', ↓reduceIte]
    exact le_antisymm (ciSup_le fun a ↦ optExpQRec_le_optExpQRec_optPolicy M H β hβ' h s a)
      (le_ciSup (Finite.bddAbove_range _) _)

omit [MeasurableSingletonClass S] [Countable S] [MeasurableSingletonClass A] in
lemma optExpQRec_le_optExpValueRec (hβ : 0 < β) {h : ℕ} (hh : h < H) (s : S) (a : A) :
    optExpQRec M H β h s a ≤ optExpValueRec M H β h s := by
  rw [optExpValueRec_eq_optExpQRec_optPolicy M H β hβ.ne' hh]
  exact optExpQRec_le_optExpQRec_optPolicy M H β hβ h s a

omit [MeasurableSingletonClass S] [Countable S] [MeasurableSingletonClass A] in
lemma optExpValueRec_le_optExpQRec (hβ : β < 0) {h : ℕ} (hh : h < H) (s : S) (a : A) :
    optExpValueRec M H β h s ≤ optExpQRec M H β h s a := by
  rw [optExpValueRec_eq_optExpQRec_optPolicy M H β hβ.ne hh]
  exact optExpQRec_optPolicy_le_optExpQRec M H β hβ h s a

omit [MeasurableSingletonClass A] in
/-- Range of the recursive optimal values for rewards in `[0, 1]`. -/
lemma optExpValueRec_mem_Icc (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β ≠ 0) (h : ℕ) (s : S) :
    optExpValueRec M H β h s
      ∈ Set.Icc (min 1 (Real.exp (β * (H - h : ℕ)))) (max 1 (Real.exp (β * (H - h : ℕ)))) := by
  induction h using horizon_induction H generalizing s with
  | h0 h hh => simp [optExpValueRec_of_le M H β hh, Nat.sub_eq_zero_of_le hh]
  | hstep h hh ih =>
    rw [optExpValueRec_eq_optExpQRec_optPolicy M H β hβ hh, optExpQRec, cast_sub_eq_one_add hh]
    exact mul_mem_Icc_min_max_exp β zero_le_one (Nat.cast_nonneg _)
      (integral_exp_mul_reward_mem_Icc M β hM h s _)
      (integral_trans_mem_Icc M (measurable_of_countable _) ih h s _)

/-- The greedy policy attains the recursive optimal value from every state at every step. -/
lemma expValue_optPolicy (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β ≠ 0) (h : ℕ) (s : S) :
    expValue M H β (optPolicy M H β) h s = optExpValueRec M H β h s := by
  induction h using horizon_induction H generalizing s with
  | h0 h hh =>
    rw [expValue_of_le M H β (measurable_optPolicy M H β) hh, optExpValueRec_of_le M H β hh]
  | hstep h hh ih =>
    rw [expValue_succ M H β hM (measurable_optPolicy M H β) hh,
      optExpValueRec_eq_optExpQRec_optPolicy M H β hβ hh, expQ, optExpQRec]
    simp_rw [ih]

/-- For `β > 0`, the recursive optimal value dominates the exponential value of every policy. -/
lemma expValue_le_optExpValueRec (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : 0 < β)
    {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) (h : ℕ) (s : S) :
    expValue M H β π h s ≤ optExpValueRec M H β h s := by
  induction h using horizon_induction H generalizing s with
  | h0 h hh => rw [expValue_of_le M H β hπ hh, optExpValueRec_of_le M H β hh]
  | hstep h hh ih =>
    rw [expValue_succ M H β hM hπ hh, expQ]
    refine (mul_le_mul_of_nonneg_left (integral_mono ?_ ?_ ih)
      (integral_nonneg fun _ ↦ (Real.exp_pos _).le)).trans
      (optExpQRec_le_optExpValueRec M H β hβ hh s _)
    · exact (integrable_const _).mono' (measurable_expValue M H β π (h + 1)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun s' ↦ by
          rw [Real.norm_eq_abs, abs_of_pos (expValue_pos M H β hM hπ _ s')]
          exact (expValue_mem_Icc M H β hM hπ (h + 1) s').2)
    · exact (integrable_const _).mono' (measurable_of_countable _).aestronglyMeasurable
        (Filter.Eventually.of_forall fun s' ↦ by
          rw [Real.norm_eq_abs, abs_of_pos]
          · exact (optExpValueRec_mem_Icc M H β hM hβ.ne' (h + 1) s').2
          · exact lt_of_lt_of_le (lt_min zero_lt_one (Real.exp_pos _))
              (optExpValueRec_mem_Icc M H β hM hβ.ne' (h + 1) s').1)

/-- For `β < 0`, the recursive optimal value is dominated by the exponential value of every
policy. -/
lemma optExpValueRec_le_expValue (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β < 0)
    {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) (h : ℕ) (s : S) :
    optExpValueRec M H β h s ≤ expValue M H β π h s := by
  induction h using horizon_induction H generalizing s with
  | h0 h hh => rw [expValue_of_le M H β hπ hh, optExpValueRec_of_le M H β hh]
  | hstep h hh ih =>
    rw [expValue_succ M H β hM hπ hh, expQ]
    refine (optExpValueRec_le_optExpQRec M H β hβ hh s _).trans
      (mul_le_mul_of_nonneg_left (integral_mono ?_ ?_ ih)
        (integral_nonneg fun _ ↦ (Real.exp_pos _).le))
    · exact (integrable_const _).mono' (measurable_of_countable _).aestronglyMeasurable
        (Filter.Eventually.of_forall fun s' ↦ by
          rw [Real.norm_eq_abs, abs_of_pos]
          · exact (optExpValueRec_mem_Icc M H β hM hβ.ne (h + 1) s').2
          · exact lt_of_lt_of_le (lt_min zero_lt_one (Real.exp_pos _))
              (optExpValueRec_mem_Icc M H β hM hβ.ne (h + 1) s').1)
    · exact (integrable_const _).mono' (measurable_expValue M H β π (h + 1)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun s' ↦ by
          rw [Real.norm_eq_abs, abs_of_pos (expValue_pos M H β hM hπ _ s')]
          exact (expValue_mem_Icc M H β hM hπ (h + 1) s').2)

/-- The greedy policy is optimal for the entropic criterion. -/
lemma entropicValue_le_entropicValue_optPolicy (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β ≠ 0)
    {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) (h : ℕ) (s : S) :
    entropicValue M H β π h s ≤ entropicValue M H β (optPolicy M H β) h s := by
  rcases hβ.lt_or_gt with hβ' | hβ'
  · refine entropicValue_le_of_neg M H β hβ'
      (expValue_pos M H β hM (measurable_optPolicy M H β) h s) ?_
    rw [expValue_optPolicy M H β hM hβ]
    exact optExpValueRec_le_expValue M H β hM hβ' hπ h s
  · refine entropicValue_le_of_pos M H β hβ' (expValue_pos M H β hM hπ h s) ?_
    rw [expValue_optPolicy M H β hM hβ]
    exact expValue_le_optExpValueRec M H β hM hβ' hπ h s

/-- **The optimal entropic value is attained** by the greedy policy of the Bellman recursion. -/
lemma optEntropicValue_eq (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β ≠ 0) (h : ℕ) (s : S) :
    optEntropicValue M H β h s = entropicValue M H β (optPolicy M H β) h s :=
  le_antisymm (ciSup_le fun π ↦ entropicValue_le_entropicValue_optPolicy M H β hM hβ π.2 h s)
    (entropicValue_le_optEntropicValue M H β hM hβ (measurable_optPolicy M H β) h s)

lemma exists_entropicValue_eq_optEntropicValue (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β ≠ 0)
    (h : ℕ) (s : S) :
    ∃ π : ℕ → S → A, (∀ k, Measurable (π k))
      ∧ entropicValue M H β π h s = optEntropicValue M H β h s :=
  ⟨optPolicy M H β, measurable_optPolicy M H β, (optEntropicValue_eq M H β hM hβ h s).symm⟩

/-- The optimal exponential value is the recursive one. -/
lemma optExpValue_eq_optExpValueRec (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β ≠ 0) (h : ℕ)
    (s : S) : optExpValue M H β h s = optExpValueRec M H β h s := by
  rw [optExpValue, optEntropicValue_eq M H β hM hβ, ← expValue_eq_exp_mul_entropicValue M H β hβ
    (expValue_pos M H β hM (measurable_optPolicy M H β) h s), expValue_optPolicy M H β hM hβ]

lemma optExpValue_eq_expValue_optPolicy (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β ≠ 0) (h : ℕ)
    (s : S) : optExpValue M H β h s = expValue M H β (optPolicy M H β) h s := by
  rw [optExpValue_eq_optExpValueRec M H β hM hβ, expValue_optPolicy M H β hM hβ]

lemma exists_expValue_eq_optExpValue (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β ≠ 0) (h : ℕ) (s : S) :
    ∃ π : ℕ → S → A, (∀ k, Measurable (π k)) ∧ expValue M H β π h s = optExpValue M H β h s :=
  ⟨optPolicy M H β, measurable_optPolicy M H β,
    (optExpValue_eq_expValue_optPolicy M H β hM hβ h s).symm⟩

lemma optExpValue_of_le (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β ≠ 0) {h : ℕ} (hh : H ≤ h)
    (s : S) : optExpValue M H β h s = 1 := by
  rw [optExpValue_eq_optExpValueRec M H β hM hβ, optExpValueRec_of_le M H β hh]

lemma optExpQ_eq_optExpQRec (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β ≠ 0) (h : ℕ) (s : S)
    (a : A) : optExpQ M H β h s a = optExpQRec M H β h s a := by
  rw [optExpQ, optExpQRec]
  simp_rw [optExpValue_eq_optExpValueRec M H β hM hβ]

/-- **Optimal exponential Bellman equation**: `Z*_h(s) = U*_h(s, π*_h(s))` for the greedy
policy `π*`. -/
lemma optExpValue_succ_eq (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β ≠ 0) {h : ℕ} (hh : h < H)
    (s : S) : optExpValue M H β h s = optExpQ M H β h s (optPolicy M H β h s) := by
  rw [optExpValue_eq_optExpValueRec M H β hM hβ, optExpQ_eq_optExpQRec M H β hM hβ,
    optExpValueRec_eq_optExpQRec_optPolicy M H β hβ hh]

/-- For `β > 0`, `Z*_h(s) = max_a U*_h(s, a)`. -/
lemma optExpQ_le_optExpValue (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : 0 < β) {h : ℕ} (hh : h < H)
    (s : S) (a : A) : optExpQ M H β h s a ≤ optExpValue M H β h s := by
  rw [optExpValue_succ_eq M H β hM hβ.ne' hh, optExpQ_eq_optExpQRec M H β hM hβ.ne',
    optExpQ_eq_optExpQRec M H β hM hβ.ne']
  exact optExpQRec_le_optExpQRec_optPolicy M H β hβ h s a

/-- For `β < 0`, `Z*_h(s) = min_a U*_h(s, a)`. -/
lemma optExpValue_le_optExpQ (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β < 0) {h : ℕ} (hh : h < H)
    (s : S) (a : A) : optExpValue M H β h s ≤ optExpQ M H β h s a := by
  rw [optExpValue_succ_eq M H β hM hβ.ne hh, optExpQ_eq_optExpQRec M H β hM hβ.ne,
    optExpQ_eq_optExpQRec M H β hM hβ.ne]
  exact optExpQRec_optPolicy_le_optExpQRec M H β hβ h s a

lemma expQ_le_optExpQ (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : 0 < β) {π : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h))
    (h : ℕ) (s : S) (a : A) : expQ M H β π h s a ≤ optExpQ M H β h s a := by
  rw [expQ, optExpQ]
  refine mul_le_mul_of_nonneg_left (integral_mono ?_ ?_ fun s' ↦
    expValue_le_optExpValue M H β hM hβ hπ _ s') (integral_nonneg fun _ ↦ (Real.exp_pos _).le)
  · exact (integrable_const _).mono' (measurable_expValue M H β π (h + 1)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s' ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (expValue_pos M H β hM hπ _ s')]
        exact (expValue_mem_Icc M H β hM hπ (h + 1) s').2)
  · exact (integrable_const _).mono' (measurable_of_countable _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s' ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (optExpValue_pos M H β _ s'),
          optExpValue_eq_optExpValueRec M H β hM hβ.ne']
        exact (optExpValueRec_mem_Icc M H β hM hβ.ne' (h + 1) s').2)

lemma optExpQ_le_expQ (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β < 0) {π : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h))
    (h : ℕ) (s : S) (a : A) : optExpQ M H β h s a ≤ expQ M H β π h s a := by
  rw [expQ, optExpQ]
  refine mul_le_mul_of_nonneg_left (integral_mono ?_ ?_ fun s' ↦
    optExpValue_le_expValue M H β hM hβ hπ _ s') (integral_nonneg fun _ ↦ (Real.exp_pos _).le)
  · exact (integrable_const _).mono' (measurable_of_countable _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s' ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (optExpValue_pos M H β _ s'),
          optExpValue_eq_optExpValueRec M H β hM hβ.ne]
        exact (optExpValueRec_mem_Icc M H β hM hβ.ne (h + 1) s').2)
  · exact (integrable_const _).mono' (measurable_expValue M H β π (h + 1)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s' ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (expValue_pos M H β hM hπ _ s')]
        exact (expValue_mem_Icc M H β hM hπ (h + 1) s').2)

/-- Range of the optimal exponential values for rewards in `[0, 1]`. -/
lemma optExpValue_mem_Icc (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β ≠ 0) (h : ℕ) (s : S) :
    optExpValue M H β h s
      ∈ Set.Icc (min 1 (Real.exp (β * (H - h : ℕ)))) (max 1 (Real.exp (β * (H - h : ℕ)))) := by
  rw [optExpValue_eq_optExpValueRec M H β hM hβ]
  exact optExpValueRec_mem_Icc M H β hM hβ h s

/-- Range of the optimal exponential state-action values for rewards in `[0, 1]`. -/
lemma optExpQ_mem_Icc (hM : M.RewardsIn (Set.Icc 0 1)) (hβ : β ≠ 0) {h : ℕ} (hh : h < H) (s : S)
    (a : A) :
    optExpQ M H β h s a
      ∈ Set.Icc (min 1 (Real.exp (β * (H - h : ℕ)))) (max 1 (Real.exp (β * (H - h : ℕ)))) := by
  rw [optExpQ, cast_sub_eq_one_add hh]
  exact mul_mem_Icc_min_max_exp β zero_le_one (Nat.cast_nonneg _)
    (integral_exp_mul_reward_mem_Icc M β hM h s a)
    (integral_trans_mem_Icc M (measurable_of_countable _)
      (fun s' ↦ optExpValue_mem_Icc M H β hM hβ (h + 1) s') h s a)

end Optimal

/-! ### The value gap -/

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- The value gap in the exponential space: `V*_h(s) - V^π_h(s) = β⁻¹ log (Z*_h(s) / Z^π_h(s))`. -/
lemma optEntropicValue_sub_entropicValue (hβ : β ≠ 0) {π : ℕ → S → A} {h : ℕ} {s : S}
    (hZ : 0 < expValue M H β π h s) :
    optEntropicValue M H β h s - entropicValue M H β π h s
      = β⁻¹ * Real.log (optExpValue M H β h s / expValue M H β π h s) := by
  rw [optEntropicValue_eq_inv_mul_log M H β hβ, entropicValue,
    Real.log_div (optExpValue_pos M H β h s).ne' hZ.ne', mul_sub]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- For `β > 0`, `Z*_h(s) ≤ e^{β ε} Z^π_h(s)` implies `V*_h(s) - V^π_h(s) ≤ ε`. -/
lemma optEntropicValue_sub_entropicValue_le_of_pos (hβ : 0 < β) {ε : ℝ} {π : ℕ → S → A}
    {h : ℕ} {s : S} (hZ : 0 < expValue M H β π h s)
    (hle : optExpValue M H β h s ≤ Real.exp (β * ε) * expValue M H β π h s) :
    optEntropicValue M H β h s - entropicValue M H β π h s ≤ ε := by
  rw [optEntropicValue_sub_entropicValue M H β hβ.ne' hZ]
  have h1 : optExpValue M H β h s / expValue M H β π h s ≤ Real.exp (β * ε) :=
    (div_le_iff₀ hZ).2 hle
  have h2 : Real.log (optExpValue M H β h s / expValue M H β π h s) ≤ β * ε :=
    (Real.log_le_log (div_pos (optExpValue_pos M H β h s) hZ) h1).trans_eq (Real.log_exp _)
  calc β⁻¹ * Real.log (optExpValue M H β h s / expValue M H β π h s) ≤ β⁻¹ * (β * ε) :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hβ.le)
    _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ hβ.ne', one_mul]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- For `β < 0`, `e^{β ε} Z^π_h(s) ≤ Z*_h(s)` implies `V*_h(s) - V^π_h(s) ≤ ε`. -/
lemma optEntropicValue_sub_entropicValue_le_of_neg (hβ : β < 0) {ε : ℝ} {π : ℕ → S → A}
    {h : ℕ} {s : S} (hZ : 0 < expValue M H β π h s)
    (hle : Real.exp (β * ε) * expValue M H β π h s ≤ optExpValue M H β h s) :
    optEntropicValue M H β h s - entropicValue M H β π h s ≤ ε := by
  rw [optEntropicValue_sub_entropicValue M H β hβ.ne hZ]
  have h1 : Real.exp (β * ε) ≤ optExpValue M H β h s / expValue M H β π h s :=
    (le_div_iff₀ hZ).2 hle
  have h2 : β * ε ≤ Real.log (optExpValue M H β h s / expValue M H β π h s) :=
    (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) h1)
  calc β⁻¹ * Real.log (optExpValue M H β h s / expValue M H β π h s) ≤ β⁻¹ * (β * ε) :=
        mul_le_mul_of_nonpos_left h2 (inv_nonpos.2 hβ.le)
    _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ hβ.ne, one_mul]

end Learning.MDP.Episodic
