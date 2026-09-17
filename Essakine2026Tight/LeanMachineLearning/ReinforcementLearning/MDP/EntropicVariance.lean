/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Unroll
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Entropic variances of a finite-horizon MDP

For a finite-horizon MDP `M` with the horizon `H`, a risk parameter `β` and a policy `π`,
the entropic variances `entropicVarQ M H β π h s a` (`σQ^π_h(s, a)`) and `entropicVarV M H β π h s`
(`σV^π_h(s)`) are defined in `MDP/Entropic.lean` as nested integrals. This file proves, for
bounded rewards:

* `σV^π_h(s)` is the variance of `e^{β R_h}` under the trajectory law from `(s, h)`
  (`entropicVarV_eq_integral`, `entropicVarV_eq_variance`), and it is bounded and measurable
  (`entropicVarV_mem_Icc`, `measurable_entropicVarV`);
* the **Bellman recursion** of the entropic variances for an MDP with a reward function `r`
  (`entropicVarQ_eq_of_hasRewardFn`, the paper's Lemma 23):
  `σQ^π_h(s, a) = e^{2β r_h(s, a)} (Var_{p_h}(Z^π_{h+1})(s, a) + (p_h σV^π_{h+1})(s, a))`,
  in integral form and, for a finite state space, with the transition vectors
  (`entropicVarQ_eq_of_hasRewardFn_vec`);
* the **telescoping** of the entropic variances along the trajectory
  (`sum_integral_exp_mul_variance_eq_variance`, `sum_integral_exp_mul_vecVar_eq_variance`):
  `∑_h E^π[e^{2β ∑_{i ≤ h} r_i(S_i, A_i)} Var_{p_h}(Z^π_{h+1})(S_h, A_h)] = Var_{P^π}(e^{β R_0})`;
* the **normalized variance** of the exponentiated return
  (`variance_exp_episodeReturn_div_sq_le`, the paper's Lemma 24 applied to the return).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP
open scoped ENNReal

namespace Learning.MDP.Episodic

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : EpisodicMDP S A) (H : ℕ)
  (β : ℝ)

/-! ### The entropic variance of a state -/

omit [MeasurableSpace S] [MeasurableSpace A] in
lemma exp_two_mul_eq_sq (x : ℝ) : Real.exp (2 * β * x) = Real.exp (β * x) ^ 2 := by
  rw [← Real.exp_nat_mul]
  ring_nf

/-- The entropic variance at a step `h < H` is the entropic variance of the pair `(s, π_h(s))`. -/
lemma entropicVarV_of_lt (π : ℕ → S → A) {h : ℕ} (hh : h < H) (s : S) :
    entropicVarV M H β π h s = entropicVarQ M H β π h s (π h s) := by
  simp only [entropicVarV, hh, ↓reduceIte]

/-- The entropic variance is `0` from the step `H` on. -/
lemma entropicVarV_of_le (π : ℕ → S → A) {h : ℕ} (hh : H ≤ h) (s : S) :
    entropicVarV M H β π h s = 0 := by
  simp only [entropicVarV, not_lt.2 hh, ↓reduceIte]

/-- The exponential state-action value is a measurable function of the pair. -/
lemma measurable_expQ (π : ℕ → S → A) (h : ℕ) :
    Measurable fun p : S × A ↦ expQ M H β π h p.1 p.2 := by
  have h1 : StronglyMeasurable fun p : S × A ↦ ∫ x, Real.exp (β * x) ∂M.reward h p :=
    StronglyMeasurable.integral_kernel_prod_right' (κ := M.reward h)
      (f := fun z : (S × A) × ℝ ↦ Real.exp (β * z.2))
      (Real.measurable_exp.comp (measurable_snd.const_mul β)).stronglyMeasurable
  have h2 : StronglyMeasurable fun p : S × A ↦ ∫ s', expValue M H β π (h + 1) s' ∂M.trans h p :=
    StronglyMeasurable.integral_kernel_prod_right' (κ := M.trans h)
      (f := fun z : (S × A) × S ↦ expValue M H β π (h + 1) z.2)
      ((measurable_expValue M H β π (h + 1)).comp measurable_snd).stronglyMeasurable
  exact (h1.mul h2).measurable

/-- The entropic variance of a pair is a measurable function of the pair. -/
lemma measurable_entropicVarQ (π : ℕ → S → A) (h : ℕ) :
    Measurable fun p : S × A ↦ entropicVarQ M H β π h p.1 p.2 := by
  set n := H - (h + 1)
  have h1 : StronglyMeasurable fun q : ((S × A) × ℝ) × S ↦
      ∫ traj, (Real.exp (β * (q.1.2 + episodeReturn n traj)) - expQ M H β π h q.1.1.1 q.1.1.2) ^ 2
        ∂stepLaw M π (q.2, h + 1) := by
    have := StronglyMeasurable.integral_kernel_prod_right'
      (κ := Kernel.prodMkLeft ((S × A) × ℝ) (stepLawKernel M π (h + 1)))
      (f := fun z : (((S × A) × ℝ) × S) × (ℕ → Round (S × ℕ) A ℝ) ↦
        (Real.exp (β * (z.1.1.2 + episodeReturn n z.2)) - expQ M H β π h z.1.1.1.1 z.1.1.1.2) ^ 2)
      (Measurable.stronglyMeasurable (by
        refine ((Real.measurable_exp.comp ((measurable_fst.fst.snd.add
          ((measurable_episodeReturn n).comp measurable_snd)).const_mul β)).sub ?_).pow_const 2
        exact (measurable_expQ M H β π h).comp measurable_fst.fst.fst))
    simpa only [Kernel.prodMkLeft_apply, stepLawKernel_apply] using this
  have h2 : StronglyMeasurable fun q : (S × A) × ℝ ↦ ∫ s', ∫ traj,
      (Real.exp (β * (q.2 + episodeReturn n traj)) - expQ M H β π h q.1.1 q.1.2) ^ 2
        ∂stepLaw M π (s', h + 1) ∂M.trans h q.1 := by
    have := StronglyMeasurable.integral_kernel_prod_right'
      (κ := Kernel.prodMkRight ℝ (M.trans h)) h1
    simpa only [Kernel.prodMkRight_apply] using this
  have h3 : StronglyMeasurable fun p : S × A ↦ ∫ x, ∫ s', ∫ traj,
      (Real.exp (β * (x + episodeReturn n traj)) - expQ M H β π h p.1 p.2) ^ 2
        ∂stepLaw M π (s', h + 1) ∂M.trans h p ∂M.reward h p :=
    StronglyMeasurable.integral_kernel_prod_right' (κ := M.reward h) h2
  exact h3.measurable

/-- The entropic variance of a state is a measurable function of the state. -/
lemma measurable_entropicVarV {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) (h : ℕ) :
    Measurable (entropicVarV M H β π h) := by
  unfold entropicVarV
  split_ifs
  · exact (measurable_entropicVarQ M H β π h).comp (measurable_id.prodMk (hπ h))
  · exact measurable_const

variable [MeasurableSingletonClass S] [MeasurableSingletonClass A]

/-- For bounded rewards, `(e^{β R} - c)²` is integrable under every trajectory law. -/
lemma integrable_exp_episodeReturn_sub_sq {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b))
    {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) (n h : ℕ) (s : S) (c : ℝ) :
    Integrable (fun x ↦ (Real.exp (β * episodeReturn n x) - c) ^ 2) (stepLaw M π (s, h)) := by
  refine Integrable.mono'
    (((integrable_exp_mul_episodeReturn M (2 * β) hM hπ n h s).const_mul 2).add
    (integrable_const (2 * c ^ 2)))
    ((((measurable_exp_mul_episodeReturn β n).sub_const c).pow_const 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [Pi.add_apply, exp_two_mul_eq_sq]
  nlinarith [sq_nonneg (Real.exp (β * episodeReturn n x) + c)]

/-- For rewards in `[a, b]`, the exponential value is at most `e^{|β| (H - h) max(|a|, |b|)}`. -/
lemma expValue_le_exp {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) {π : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h)) (h : ℕ)
    (s : S) : expValue M H β π h s ≤ Real.exp (|β| * ((H - h : ℕ) * max |a| |b|)) := by
  have := isProbabilityMeasure_stepLaw M hπ (s, h)
  rw [expValue]
  calc ∫ x, Real.exp (β * episodeReturn (H - h) x) ∂stepLaw M π (s, h)
      ≤ ∫ _, Real.exp (|β| * ((H - h : ℕ) * max |a| |b|)) ∂stepLaw M π (s, h) :=
        integral_mono_ae (integrable_exp_mul_episodeReturn M β hM hπ _ h s) (integrable_const _)
          (ae_exp_mul_episodeReturn_le M β hM hπ _ h s)
    _ = _ := by simp

/-- For bounded rewards, the exponential value is integrable under every finite measure. -/
lemma integrable_expValue {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) {π : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h))
    (h : ℕ) (μ : Measure S) [IsFiniteMeasure μ] : Integrable (expValue M H β π h) μ := by
  refine Integrable.of_bound (measurable_expValue M H β π h).aestronglyMeasurable
    (Real.exp (|β| * ((H - h : ℕ) * max |a| |b|))) (Filter.Eventually.of_forall fun s ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_pos (expValue_pos M H β hM hπ h s)]
  exact expValue_le_exp M H β hM hπ h s

/-- The entropic variance `σV^π_h(s)` is the mean square deviation of `e^{β R_h}` from its mean
`Z^π_h(s)` under the trajectory law from `(s, h)`, for bounded rewards. -/
lemma entropicVarV_eq_integral {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) {π : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h)) (h : ℕ) (s : S) :
    entropicVarV M H β π h s
      = ∫ x, (Real.exp (β * episodeReturn (H - h) x) - expValue M H β π h s) ^ 2
          ∂stepLaw M π (s, h) := by
  rcases le_or_gt H h with hh | hh
  · rw [entropicVarV_of_le M H β π hh, Nat.sub_eq_zero_of_le hh, expValue_of_le M H β hπ hh]
    simp
  set Z := expValue M H β π h s with hZ
  set n := H - (h + 1) with hn
  have hHh : H - h = n + 1 := by omega
  set G : (ℝ × S) × (ℕ → Round (S × ℕ) A ℝ) → ℝ :=
    fun z ↦ (Real.exp (β * (z.1.1 + episodeReturn n z.2)) - Z) ^ 2 with hG
  have hGm : Measurable G :=
    ((Real.measurable_exp.comp ((measurable_fst.fst.add
      ((measurable_episodeReturn n).comp measurable_snd)).const_mul β)).sub_const Z).pow_const 2
  have hΦ : Measurable fun x : ℕ → Round (S × ℕ) A ℝ ↦
      ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x) :=
    ((IT.measurable_feedback 0).prodMk (measurable_fst.comp (IT.measurable_obs 1))).prodMk
      measurable_shiftRound
  have hlaw := hasLaw_stepLaw_succ M hπ s h
  have heq : (fun x ↦ G ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x))
      = fun x ↦ (Real.exp (β * episodeReturn (H - h) x) - Z) ^ 2 := by
    funext x
    simp only [hG, hHh, episodeReturn_succ_eq_add_shiftRound]
  -- integrability of `G` under the law of (first reward, next state, shifted trajectory)
  have hGint : Integrable G ((M.reward h (s, π h s)).prod (M.trans h (s, π h s))
      ⊗ₘ Kernel.prodMkLeft ℝ (stepLawKernel M π (h + 1))) := by
    rw [← hlaw.map_eq, integrable_map_measure hGm.aestronglyMeasurable hΦ.aemeasurable]
    change Integrable (fun x ↦ G ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x)) _
    rw [heq]
    exact integrable_exp_episodeReturn_sub_sq M β hM hπ (H - h) h s Z
  have hGint' := ((Measure.integrable_compProd_iff hGm.aestronglyMeasurable).1 hGint).2
  have hGnorm : (fun q : ℝ × S ↦ ∫ y, ‖G (q, y)‖ ∂(Kernel.prodMkLeft ℝ
      (stepLawKernel M π (h + 1))) q) = fun q ↦ ∫ y, G (q, y) ∂stepLaw M π (q.2, h + 1) := by
    funext q
    rw [Kernel.prodMkLeft_apply, stepLawKernel_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    exact Real.norm_of_nonneg (sq_nonneg _)
  rw [hGnorm] at hGint'
  rw [entropicVarV_of_lt M H β π hh, entropicVarQ, ← expValue_succ M H β hM hπ hh s, ← hZ, ← hn]
  symm
  calc ∫ x, (Real.exp (β * episodeReturn (H - h) x) - Z) ^ 2 ∂stepLaw M π (s, h)
      = ∫ x, G ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x) ∂stepLaw M π (s, h) := by
        rw [heq]
    _ = ∫ q, ∫ y, G (q, y) ∂stepLaw M π (q.2, h + 1)
          ∂((M.reward h (s, π h s)).prod (M.trans h (s, π h s))) :=
        integral_stepLaw_succ M hπ s h hGint
    _ = _ := integral_prod (fun q ↦ ∫ y, G (q, y) ∂stepLaw M π (q.2, h + 1)) hGint'

/-- The entropic variance `σV^π_h(s)` is the variance of `e^{β R_h}` under the trajectory law
from `(s, h)`, for bounded rewards. -/
lemma entropicVarV_eq_variance {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) {π : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h)) (h : ℕ) (s : S) :
    entropicVarV M H β π h s
      = variance (fun x ↦ Real.exp (β * episodeReturn (H - h) x)) (stepLaw M π (s, h)) := by
  rw [entropicVarV_eq_integral M H β hM hπ, variance_eq_integral
    (measurable_exp_mul_episodeReturn β _).aemeasurable]
  rfl

/-- For rewards in `[a, b]`, the entropic variance lies in `[0, e^{2 |β| (H - h) max(|a|, |b|)}]`.
-/
lemma entropicVarV_mem_Icc {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) {π : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h)) (h : ℕ) (s : S) :
    entropicVarV M H β π h s
      ∈ Set.Icc 0 (Real.exp (|β| * ((H - h : ℕ) * max |a| |b|)) ^ 2) := by
  have := isProbabilityMeasure_stepLaw M hπ (s, h)
  rw [entropicVarV_eq_integral M H β hM hπ]
  refine ⟨integral_nonneg fun _ ↦ sq_nonneg _, ?_⟩
  set E := Real.exp (|β| * ((H - h : ℕ) * max |a| |b|)) with hE
  calc ∫ x, (Real.exp (β * episodeReturn (H - h) x) - expValue M H β π h s) ^ 2
        ∂stepLaw M π (s, h)
      ≤ ∫ _, E ^ 2 ∂stepLaw M π (s, h) := by
        refine integral_mono_ae (integrable_exp_episodeReturn_sub_sq M β hM hπ _ h s _)
          (integrable_const _) ?_
        filter_upwards [ae_exp_mul_episodeReturn_le M β hM hπ (H - h) h s] with x hx
        have h1 := expValue_pos M H β hM hπ h s
        have h2 := expValue_le_exp M H β hM hπ h s
        have h3 := Real.exp_pos (β * episodeReturn (H - h) x)
        exact sq_le_sq' (by linarith) (by linarith)
    _ = _ := by simp

/-- For bounded rewards, the entropic variance is integrable under every finite measure. -/
lemma integrable_entropicVarV {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) {π : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h))
    (h : ℕ) (μ : Measure S) [IsFiniteMeasure μ] : Integrable (entropicVarV M H β π h) μ := by
  refine Integrable.of_bound (measurable_entropicVarV M H β hπ h).aestronglyMeasurable
    (Real.exp (|β| * ((H - h : ℕ) * max |a| |b|)) ^ 2) (Filter.Eventually.of_forall fun s ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (entropicVarV_mem_Icc M H β hM hπ h s).1]
  exact (entropicVarV_mem_Icc M H β hM hπ h s).2

/-! ### The Bellman recursion of the entropic variances -/

/-- **Bellman recursion of the entropic variances** (Lemma 23 of Essakine, Vernade (2026)): for
an MDP with a bounded reward function `r`,
`σQ^π_h(s, a) = e^{2β r_h(s, a)} (Var_{p_h}(Z^π_{h+1})(s, a) + (p_h σV^π_{h+1})(s, a))`. -/
lemma entropicVarQ_eq_of_hasRewardFn {r : ℕ → S → A → ℝ} (hM : M.HasRewardFn r) {a b : ℝ}
    (hr : ∀ h s a', r h s a' ∈ Set.Icc a b) {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) (h : ℕ)
    (s : S) (a' : A) :
    entropicVarQ M H β π h s a'
      = Real.exp (2 * β * r h s a')
        * (variance (expValue M H β π (h + 1)) (M.trans h (s, a'))
          + ∫ s', entropicVarV M H β π (h + 1) s' ∂M.trans h (s, a')) := by
  have hR := rewardsIn_of_hasRewardFn M hM measurableSet_Icc hr
  set m := ∫ s', expValue M H β π (h + 1) s' ∂M.trans h (s, a') with hm
  have hinner (s' : S) :
      ∫ y, (Real.exp (β * (r h s a' + episodeReturn (H - (h + 1)) y)) - expQ M H β π h s a') ^ 2
          ∂stepLaw M π (s', h + 1)
        = Real.exp (2 * β * r h s a')
          * (entropicVarV M H β π (h + 1) s' + (expValue M H β π (h + 1) s' - m) ^ 2) := by
    set Z := expValue M H β π (h + 1) s' with hZ
    have hXi := integrable_exp_mul_episodeReturn M β hR hπ (H - (h + 1)) (h + 1) s'
    have hsq := integrable_exp_episodeReturn_sub_sq M β hR hπ (H - (h + 1)) (h + 1) s' Z
    calc ∫ y, (Real.exp (β * (r h s a' + episodeReturn (H - (h + 1)) y)) - expQ M H β π h s a') ^ 2
          ∂stepLaw M π (s', h + 1)
        = ∫ y, Real.exp (2 * β * r h s a')
            * ((Real.exp (β * episodeReturn (H - (h + 1)) y) - Z) ^ 2
            + (2 * (Z - m) * Real.exp (β * episodeReturn (H - (h + 1)) y) - 2 * (Z - m) * Z)
            + (Z - m) ^ 2) ∂stepLaw M π (s', h + 1) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
          simp only
          rw [expQ_of_hasRewardFn M H β hM, mul_add, Real.exp_add, ← hm, exp_two_mul_eq_sq]
          ring
      _ = Real.exp (2 * β * r h s a')
            * (∫ y, (Real.exp (β * episodeReturn (H - (h + 1)) y) - Z) ^ 2
              ∂stepLaw M π (s', h + 1) + (2 * (Z - m) * Z - 2 * (Z - m) * Z) + (Z - m) ^ 2) := by
          have := isProbabilityMeasure_stepLaw M hπ (s', h + 1)
          rw [integral_const_mul, integral_add, integral_add, integral_sub, integral_const_mul]
          · simp [hZ, expValue]
          · exact hXi.const_mul _
          · exact integrable_const _
          · exact hsq
          · exact (hXi.const_mul _).sub (integrable_const _)
          · exact hsq.add ((hXi.const_mul _).sub (integrable_const _))
          · exact integrable_const _
      _ = _ := by
          rw [← entropicVarV_eq_integral M H β hR hπ]
          ring
  have hsq : Integrable (fun s' ↦ (expValue M H β π (h + 1) s' - m) ^ 2) (M.trans h (s, a')) := by
    refine Integrable.of_bound (((measurable_expValue M H β π (h + 1)).sub_const m).pow_const
      2).aestronglyMeasurable ((Real.exp (|β| * ((H - (h + 1) : ℕ) * max |a| |b|)) + |m|) ^ 2)
      (Filter.Eventually.of_forall fun s' ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add ?_ le_rfl)) 2
    rw [abs_of_pos (expValue_pos M H β hR hπ (h + 1) s')]
    exact expValue_le_exp M H β hR hπ (h + 1) s'
  rw [entropicVarQ, hM h s a', integral_dirac]
  simp_rw [hinner]
  rw [integral_const_mul, integral_add (integrable_entropicVarV M H β hR hπ (h + 1) _) hsq,
    variance_eq_integral (measurable_expValue M H β π (h + 1)).aemeasurable, ← hm, add_comm]

omit [MeasurableSingletonClass A] in
/-- On a finite state space, the variance under a transition kernel is the variance under the
transition vector. -/
lemma variance_eq_vecVar_transVec [Fintype S] (h : ℕ) (s : S) (a : A) (f : S → ℝ) :
    variance f (M.trans h (s, a)) = vecVar (M.transVec h s a) f := by
  rw [variance_eq_integral (measurable_of_countable f).aemeasurable, integral_eq_vecExp_transVec,
    integral_eq_vecExp_transVec, vecVar_eq_sum_sq (M.sum_transVec h s a)]
  rfl

/-- **Bellman recursion of the entropic variances** on a finite state space, with the
transition vectors. -/
lemma entropicVarQ_eq_of_hasRewardFn_vec [Fintype S] {r : ℕ → S → A → ℝ} (hM : M.HasRewardFn r)
    {a b : ℝ} (hr : ∀ h s a', r h s a' ∈ Set.Icc a b) {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h))
    (h : ℕ) (s : S) (a' : A) :
    entropicVarQ M H β π h s a'
      = Real.exp (2 * β * r h s a') * vecVar (M.transVec h s a') (expValue M H β π (h + 1))
        + Real.exp (2 * β * r h s a')
          * vecExp (M.transVec h s a') (entropicVarV M H β π (h + 1)) := by
  rw [entropicVarQ_eq_of_hasRewardFn M H β hM hr hπ, variance_eq_vecVar_transVec,
    integral_eq_vecExp_transVec, mul_add]

/-! ### Telescoping along the trajectory -/

section Telescoping

variable [Finite S] [Finite A] {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) (s₁ : S)

include hπ

/-- **Telescoping of the entropic variances**: for an MDP with a bounded reward function `r`,
`∑_{h < H} E^π[e^{2β ∑_{i ≤ h} r_i(S_i, A_i)} Var_{p_h}(Z^π_{h+1})(S_h, A_h)] = σV^π_0(s₁)`. -/
lemma sum_integral_exp_mul_variance_eq_entropicVarV {r : ℕ → S → A → ℝ} (hM : M.HasRewardFn r)
    {a b : ℝ} (hr : ∀ h s a', r h s a' ∈ Set.Icc a b) :
    ∑ h ∈ range H, ∫ x, Real.exp (2 * β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
        * variance (expValue M H β π (h + 1)) (M.trans h ((IT.obs h x).1, IT.action h x))
        ∂stepLaw M π (s₁, 0)
      = entropicVarV M H β π 0 s₁ := by
  have := isProbabilityMeasure_stepLaw M hπ (s₁, 0)
  set P := stepLaw M π (s₁, 0) with hP
  set D : ℕ → ℝ := fun h ↦ ∫ x, Real.exp (2 * β * ∑ i ∈ range h, r i (IT.obs i x).1 (IT.action i x))
    * entropicVarV M H β π h (IT.obs h x).1 ∂P with hD
  have hstep (h : ℕ) (hh : h < H) :
      ∫ x, Real.exp (2 * β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
        * variance (expValue M H β π (h + 1)) (M.trans h ((IT.obs h x).1, IT.action h x)) ∂P
      = D h - D (h + 1) := by
    have hae : ∀ᵐ x ∂P, IT.action h x = π h (IT.obs h x).1 := by
      simpa only [Nat.zero_add] using ae_action_eq_stepLaw M hπ s₁ 0 h
    have h1 : D h = ∫ x,
        (Real.exp (2 * β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
          * variance (expValue M H β π (h + 1)) (M.trans h ((IT.obs h x).1, IT.action h x))
        + Real.exp (2 * β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
          * ∫ s', entropicVarV M H β π (h + 1) s'
              ∂M.trans h ((IT.obs h x).1, IT.action h x)) ∂P := by
      simp only [hD]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [entropicVarV_of_lt M H β π hh, ← hx, entropicVarQ_eq_of_hasRewardFn M H β hM hr hπ,
        sum_range_succ, mul_add (2 * β), Real.exp_add]
      ring
    have h2 : D (h + 1) = ∫ x,
        Real.exp (2 * β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
          * ∫ s', entropicVarV M H β π (h + 1) s'
              ∂M.trans h ((IT.obs h x).1, IT.action h x) ∂P := by
      simp only [hD]
      rw [hP, integral_exp_sum_mul_obs_succ M hπ s₁ (2 * β) r h (entropicVarV M H β π (h + 1))]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hx]
    rw [h1, h2, integral_add (integrable_exp_sum_mul P (2 * β) r (range (h + 1))
      (fun s a ↦ variance (expValue M H β π (h + 1)) (M.trans h (s, a))) h)
      (integrable_exp_sum_mul P (2 * β) r (range (h + 1))
        (fun s a ↦ ∫ s', entropicVarV M H β π (h + 1) s' ∂M.trans h (s, a)) h)]
    ring
  have hlast : D H = 0 := by
    simp [hD, entropicVarV_of_le M H β π le_rfl]
  have hfirst : D 0 = entropicVarV M H β π 0 s₁ := by
    simp only [hD, range_zero, sum_empty, mul_zero, Real.exp_zero, one_mul]
    rw [integral_congr_ae (g := fun _ ↦ entropicVarV M H β π 0 s₁)]
    · simp
    · filter_upwards [ae_obs_zero_stepLaw M hπ (s₁, 0)] with x hx
      rw [hx]
  rw [sum_congr rfl fun h hh ↦ hstep h (mem_range.1 hh), sum_range_sub', hlast, hfirst, sub_zero]

/-- **Telescoping of the entropic variances**: for an MDP with a bounded reward function `r`,
`∑_{h < H} E^π[e^{2β ∑_{i ≤ h} r_i(S_i, A_i)} Var_{p_h}(Z^π_{h+1})(S_h, A_h)]
  = Var_{P^π}(e^{β R_0})`. -/
lemma sum_integral_exp_mul_variance_eq_variance {r : ℕ → S → A → ℝ} (hM : M.HasRewardFn r)
    {a b : ℝ} (hr : ∀ h s a', r h s a' ∈ Set.Icc a b) :
    ∑ h ∈ range H, ∫ x, Real.exp (2 * β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
        * variance (expValue M H β π (h + 1)) (M.trans h ((IT.obs h x).1, IT.action h x))
        ∂stepLaw M π (s₁, 0)
      = variance (fun x ↦ Real.exp (β * episodeReturn H x)) (stepLaw M π (s₁, 0)) := by
  rw [sum_integral_exp_mul_variance_eq_entropicVarV M H β hπ s₁ hM hr,
    entropicVarV_eq_variance M H β (rewardsIn_of_hasRewardFn M hM measurableSet_Icc hr) hπ,
    Nat.sub_zero]

/-- **Telescoping of the entropic variances** on a finite state space, with the transition
vectors. -/
lemma sum_integral_exp_mul_vecVar_eq_variance [Fintype S] {r : ℕ → S → A → ℝ}
    (hM : M.HasRewardFn r) {a b : ℝ} (hr : ∀ h s a', r h s a' ∈ Set.Icc a b) :
    ∑ h ∈ range H, ∫ x, Real.exp (2 * β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
        * vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M H β π (h + 1))
        ∂stepLaw M π (s₁, 0)
      = variance (fun x ↦ Real.exp (β * episodeReturn H x)) (stepLaw M π (s₁, 0)) := by
  simp_rw [← variance_eq_vecVar_transVec]
  exact sum_integral_exp_mul_variance_eq_variance M H β hπ s₁ hM hr

end Telescoping

/-! ### The normalized variance of the exponentiated return -/

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- If the return lies almost surely in `[0, G]`, then the exponential value is positive. -/
lemma expValue_pos_of_ae_mem_Icc {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) (h : ℕ) (s : S)
    {G : ℝ} (hret : ∀ᵐ x ∂stepLaw M π (s, h), episodeReturn (H - h) x ∈ Set.Icc 0 G) :
    0 < expValue M H β π h s := by
  have := isProbabilityMeasure_stepLaw M hπ (s, h)
  exact (lt_min one_pos (Real.exp_pos _)).trans_le (integral_mem_Icc_of_ae_mem_Icc
    (hret.mono fun _ hx ↦ exp_mul_mem_Icc_min_max (β := β) hx)
    (measurable_exp_mul_episodeReturn β _).aestronglyMeasurable).1

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- **Normalized variance of the exponentiated return** (Lemma 24 of Essakine, Vernade (2026)
applied to the return): if the return lies almost surely in `[0, G]`, then
`Var(e^{β R_h}) / (Z^π_h)² ≤ (e^{|β| G} - 1)² / (4 e^{|β| G})`. -/
lemma variance_exp_episodeReturn_div_sq_le {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) (h : ℕ)
    (s : S) {G : ℝ}
    (hG : 0 ≤ G) (hret : ∀ᵐ x ∂stepLaw M π (s, h), episodeReturn (H - h) x ∈ Set.Icc 0 G) :
    variance (fun x ↦ Real.exp (β * episodeReturn (H - h) x)) (stepLaw M π (s, h))
        / expValue M H β π h s ^ 2
      ≤ (Real.exp (|β| * G) - 1) ^ 2 / (4 * Real.exp (|β| * G)) := by
  have := isProbabilityMeasure_stepLaw M hπ (s, h)
  exact variance_exp_div_sq_integral_le hG hret (measurable_episodeReturn _).aemeasurable

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- **Normalized variance of the exponentiated return**, with the constant
`V_G = (e^{|β| G} - 1)² / e^{|β| G}` of the paper. -/
lemma variance_exp_episodeReturn_div_sq_le' {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) (h : ℕ)
    (s : S) {G : ℝ}
    (hG : 0 ≤ G) (hret : ∀ᵐ x ∂stepLaw M π (s, h), episodeReturn (H - h) x ∈ Set.Icc 0 G) :
    variance (fun x ↦ Real.exp (β * episodeReturn (H - h) x)) (stepLaw M π (s, h))
        / expValue M H β π h s ^ 2
      ≤ (Real.exp (|β| * G) - 1) ^ 2 / Real.exp (|β| * G) := by
  refine (variance_exp_episodeReturn_div_sq_le M H β hπ h s hG hret).trans ?_
  have he := Real.exp_pos (|β| * G)
  exact div_le_div_of_nonneg_left (sq_nonneg _) he (by linarith)

/-- **Normalized variance of the exponentiated return** for rewards in `[0, 1]`, with the maximal
return `G_max(M)`: `Var_{P^π}(e^{β R_0}) / Z^π_0(s₁)² ≤ (e^{|β| G_max} - 1)² / e^{|β| G_max}`. -/
lemma variance_exp_episodeReturn_div_sq_le_maxReturn [Nonempty A]
    (hM : M.RewardsIn (Set.Icc 0 1)) {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) (s₁ : S) :
    variance (fun x ↦ Real.exp (β * episodeReturn H x)) (stepLaw M π (s₁, 0))
        / expValue M H β π 0 s₁ ^ 2
      ≤ (Real.exp (|β| * maxReturn M H s₁) - 1) ^ 2 / Real.exp (|β| * maxReturn M H s₁) := by
  refine variance_exp_episodeReturn_div_sq_le' M H β hπ 0 s₁ (maxReturn_nonneg M H hM s₁) ?_
  filter_upwards [ae_episodeReturn_mem_Icc_of_unit M hM hπ H 0 s₁,
    ae_episodeReturn_le_maxReturn M H hM hπ s₁] with x hx hx'
  exact ⟨hx.1, hx'⟩

end Learning.MDP.Episodic
