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

For a finite-horizon MDP `M`, a risk parameter `β` and a policy `π`, the entropic variances
`entropicVarQ M β π h s a` (`σQ^π_h(s, a)`) and `entropicVarV M β π h s` (`σV^π_h(s)`) are defined
in `MDP/Entropic.lean` as nested integrals. This file proves:

* `σV^π_h(s)` is the variance of `e^{β R_h}` under the trajectory law from `(s, h)`
  (`entropicVarV_eq_integral`, `entropicVarV_eq_variance`), for rewards with a finite exponential
  moment of order `2β`;
* the **Bellman recursion** of the entropic variances for an MDP with a reward function `r`
  (`entropicVarQ_eq_of_hasRewardFn`, the paper's Lemma 23):
  `σQ^π_h(s, a) = e^{2β r_h(s, a)} (Var_{p_h}(Z^π_{h+1})(s, a) + (p_h σV^π_{h+1})(s, a))`;
* the **telescoping** of the entropic variances along the trajectory
  (`sum_integral_exp_mul_vecVar_eq_variance`):
  `∑_h E^π[e^{2β ∑_{i ≤ h} r_i(S_i, A_i)} Var_{p_h}(Z^π_{h+1})(S_h, A_h)] = Var_{P^π}(e^{β R_1})`;
* the **normalized variance** of the exponentiated return
  (`variance_exp_episodeReturn_div_sq_le`, the paper's Lemma 24 applied to the return).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP
open scoped ENNReal

namespace Learning.MDP.Episodic

variable {S A : Type*} [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] {H : ℕ} (M : EpisodicMDP S A H)
  (β : ℝ)

/-! ### Integrability of the exponential return -/

omit [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Nonempty A] in
/-- `e^{β x} ≤ 1 + e^{2 β x}`. -/
lemma exp_mul_le_one_add_exp_two_mul (x : ℝ) : Real.exp (β * x) ≤ 1 + Real.exp (2 * β * x) := by
  rcases le_or_gt (β * x) 0 with hx | hx
  · linarith [Real.exp_le_one_iff.2 hx, Real.exp_pos (2 * β * x)]
  · have : Real.exp (β * x) ≤ Real.exp (2 * β * x) := Real.exp_le_exp.2 (by linarith)
    linarith

omit [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Nonempty A] in
/-- A finite exponential moment of order `2 β` gives a finite exponential moment of order `β`. -/
lemma integrable_exp_mul_of_integrable_exp_two_mul {μ : Measure ℝ} [IsFiniteMeasure μ]
    (h : Integrable (fun x ↦ Real.exp (2 * β * x)) μ) :
    Integrable (fun x ↦ Real.exp (β * x)) μ := by
  refine Integrable.mono' ((integrable_const 1).add h)
    (Real.measurable_exp.comp (measurable_id.const_mul β)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_mul_le_one_add_exp_two_mul β x

variable {M β}

/-- For rewards with a finite exponential moment of order `2 β`, the exponential return
`e^{2 β R_h}` is integrable under every trajectory law. -/
lemma integrable_exp_two_mul_episodeReturn
    (hR : ∀ h s a, Integrable (fun x ↦ Real.exp (2 * β * x)) (M.reward h (s, a)))
    (π : Policy S A H) (h : Fin (H + 1)) (s : S) :
    Integrable (fun x ↦ Real.exp (2 * β * episodeReturn H x)) (stepLaw M π (s, h)) := by
  have hfin := lexpValue_lt_top M (2 * β) hR π h s
  have := integrable_toReal_of_lintegral_ne_top
    (ENNReal.measurable_ofReal.comp (measurable_exp_mul_episodeReturn (2 * β))).aemeasurable
    hfin.ne
  simpa [ENNReal.toReal_ofReal (Real.exp_pos _).le] using this

/-- For rewards with a finite exponential moment of order `2 β`, `(e^{β R_h} - c)²` is integrable
under every trajectory law. -/
lemma integrable_exp_episodeReturn_sub_sq
    (hR : ∀ h s a, Integrable (fun x ↦ Real.exp (2 * β * x)) (M.reward h (s, a)))
    (π : Policy S A H) (h : Fin (H + 1)) (s : S) (c : ℝ) :
    Integrable (fun x ↦ (Real.exp (β * episodeReturn H x) - c) ^ 2) (stepLaw M π (s, h)) := by
  refine Integrable.mono' (((integrable_exp_two_mul_episodeReturn hR π h s).const_mul 2).add
    (integrable_const (2 * c ^ 2)))
    ((((measurable_exp_mul_episodeReturn β).sub_const c).pow_const 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h2 : Real.exp (2 * β * episodeReturn H x) = Real.exp (β * episodeReturn H x) ^ 2 := by
    rw [← Real.exp_nat_mul]
    ring_nf
  simp only [Pi.add_apply, h2]
  nlinarith [sq_nonneg (Real.exp (β * episodeReturn H x) + c)]

/-- For rewards with a finite exponential moment of order `2 β`, the exponential return
`e^{β R_h}` is integrable under every trajectory law. -/
lemma integrable_exp_episodeReturn
    (hR : ∀ h s a, Integrable (fun x ↦ Real.exp (2 * β * x)) (M.reward h (s, a)))
    (π : Policy S A H) (h : Fin (H + 1)) (s : S) :
    Integrable (fun x ↦ Real.exp (β * episodeReturn H x)) (stepLaw M π (s, h)) := by
  refine Integrable.mono' ((integrable_const 1).add (integrable_exp_two_mul_episodeReturn hR π h s))
    (measurable_exp_mul_episodeReturn β).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have := exp_mul_le_one_add_exp_two_mul β (episodeReturn H x)
  simpa [mul_assoc] using this

/-! ### The entropic variance of a state is a variance -/

/-- The entropic variance at a non-terminal step is the entropic variance of the pair
`(s, π_h(s))`. -/
lemma entropicVarV_castSucc (π : Policy S A H) (h : Fin H) (s : S) :
    entropicVarV M β π h.castSucc s = entropicVarQ M β π h s (π h s) := by
  rw [entropicVarV, dite_eq_left (by simp)]
  rfl

/-- The entropic variance at the terminal step is `0`. -/
lemma entropicVarV_last (π : Policy S A H) (s : S) : entropicVarV M β π (Fin.last H) s = 0 := by
  rw [entropicVarV, dite_eq_right (by simp)]

/-- The entropic variance `σV^π_h(s)` is the mean square deviation of `e^{β R_h}` from its mean
`Z^π_h(s)` under the trajectory law from `(s, h)`. -/
lemma entropicVarV_eq_integral
    (hR : ∀ h s a, Integrable (fun x ↦ Real.exp (2 * β * x)) (M.reward h (s, a)))
    (π : Policy S A H) (h : Fin (H + 1)) (s : S) :
    entropicVarV M β π h s
      = ∫ x, (Real.exp (β * episodeReturn H x) - expValue M β π h s) ^ 2 ∂stepLaw M π (s, h) := by
  have hR1 : ∀ h s a, Integrable (fun x ↦ Real.exp (β * x)) (M.reward h (s, a)) :=
    fun h s a ↦ integrable_exp_mul_of_integrable_exp_two_mul β (hR h s a)
  induction h using Fin.lastCases with
  | last =>
    rw [entropicVarV_last, expValue_last]
    symm
    refine (integral_congr_ae (g := fun _ ↦ (0 : ℝ)) ?_).trans (by simp)
    filter_upwards [ae_episodeReturn_eq_zero_stepLaw_last M π s] with x hx
    simp [hx]
  | cast i =>
    have hU : expQ M β π i s (π i s) = expValue M β π i.castSucc s :=
      (expValue_castSucc M β hR1 π i s).symm
    set Z := expValue M β π i.castSucc s with hZ
    set G : (ℝ × S) × (ℕ → Round (LayerState S H) A ℝ) → ℝ :=
      fun z ↦ (Real.exp (β * (z.1.1 + episodeReturn H z.2)) - Z) ^ 2 with hG
    have hGm : Measurable G :=
      ((Real.measurable_exp.comp ((measurable_fst.fst.add
        (measurable_episodeReturn.comp measurable_snd)).const_mul β)).sub_const Z).pow_const 2
    have hΦ : Measurable fun x : ℕ → Round (LayerState S H) A ℝ ↦
        ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x) :=
      ((IT.measurable_feedback 0).prodMk (measurable_fst.comp (IT.measurable_obs 1))).prodMk
        measurable_shiftRound
    have hlaw := hasLaw_stepLaw_castSucc M π i s
    have hae : (fun x ↦ G ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x))
        =ᵐ[stepLaw M π (s, i.castSucc)]
          fun x ↦ (Real.exp (β * episodeReturn H x) - Z) ^ 2 := by
      filter_upwards [ae_episodeReturn_eq_add_shiftRound M π i.castSucc s] with x hx
      simp only [hG, hx]
    -- integrability of `G` under the law of (first reward, next state, shifted trajectory)
    have hGint : Integrable G ((M.reward i (s, π i s)).prod (M.trans i (s, π i s))
        ⊗ₘ Kernel.prodMkLeft ℝ (stepLawKernel M π i.succ)) := by
      rw [← hlaw.map_eq, integrable_map_measure hGm.aestronglyMeasurable hΦ.aemeasurable]
      exact (integrable_exp_episodeReturn_sub_sq hR π i.castSucc s Z).congr hae.symm
    have hGint' := ((Measure.integrable_compProd_iff hGm.aestronglyMeasurable).1 hGint).2
    have hGnorm : (fun q : ℝ × S ↦ ∫ y, ‖G (q, y)‖ ∂(Kernel.prodMkLeft ℝ
        (stepLawKernel M π i.succ)) q) = fun q ↦ ∫ y, G (q, y) ∂stepLaw M π (q.2, i.succ) := by
      funext q
      refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
      exact Real.norm_of_nonneg (sq_nonneg _)
    rw [hGnorm] at hGint'
    rw [entropicVarV_castSucc, entropicVarQ, hU]
    symm
    calc ∫ x, (Real.exp (β * episodeReturn H x) - Z) ^ 2 ∂stepLaw M π (s, i.castSucc)
        = ∫ x, G ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x)
            ∂stepLaw M π (s, i.castSucc) := (integral_congr_ae hae).symm
      _ = ∫ z, G z ∂((M.reward i (s, π i s)).prod (M.trans i (s, π i s))
            ⊗ₘ Kernel.prodMkLeft ℝ (stepLawKernel M π i.succ)) :=
          hlaw.integral_comp hGm.aestronglyMeasurable
      _ = ∫ q, ∫ y, G (q, y) ∂stepLaw M π (q.2, i.succ)
            ∂((M.reward i (s, π i s)).prod (M.trans i (s, π i s))) :=
          Measure.integral_compProd hGint
      _ = _ := integral_prod (fun q ↦ ∫ y, G (q, y) ∂stepLaw M π (q.2, i.succ)) hGint'

/-- The entropic variance `σV^π_h(s)` is the variance of `e^{β R_h}` under the trajectory law
from `(s, h)`. -/
lemma entropicVarV_eq_variance
    (hR : ∀ h s a, Integrable (fun x ↦ Real.exp (2 * β * x)) (M.reward h (s, a)))
    (π : Policy S A H) (h : Fin (H + 1)) (s : S) :
    entropicVarV M β π h s
      = variance (fun x ↦ Real.exp (β * episodeReturn H x)) (stepLaw M π (s, h)) := by
  rw [entropicVarV_eq_integral hR, variance_eq_integral
    (measurable_exp_mul_episodeReturn β).aemeasurable]
  rfl

/-! ### The Bellman recursion of the entropic variances -/

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A]
  [Nonempty A] in
/-- With a reward function, the rewards have exponential moments of every order. -/
lemma integrable_exp_two_mul_of_hasRewardFn {r : Fin H → S → A → ℝ} (hM : M.HasRewardFn r)
    (h : Fin H) (s : S) (a : A) :
    Integrable (fun x ↦ Real.exp (2 * β * x)) (M.reward h (s, a)) := by
  rw [hM h s a]
  exact integrable_dirac (by simp)

/-- **Bellman recursion of the entropic variances** (Lemma 23 of Essakine, Vernade (2026)): for
an MDP with the reward function `r`, `σQ^π_h(s, a)` is
`e^{2β r_h(s, a)} Var_{p_h}(Z^π_{h+1})(s, a) + e^{2β r_h(s, a)} (p_h σV^π_{h+1})(s, a)`. -/
lemma entropicVarQ_eq_of_hasRewardFn {r : Fin H → S → A → ℝ} (hM : M.HasRewardFn r)
    (π : Policy S A H) (h : Fin H) (s : S) (a : A) :
    entropicVarQ M β π h s a
      = Real.exp (2 * β * r h s a) * vecVar (M.transVec h s a) (expValue M β π h.succ)
        + Real.exp (2 * β * r h s a) * vecExp (M.transVec h s a) (entropicVarV M β π h.succ) := by
  have hR := integrable_exp_two_mul_of_hasRewardFn (β := β) hM
  set m := vecExp (M.transVec h s a) (expValue M β π h.succ) with hm
  have hinner (s' : S) :
      ∫ y, (Real.exp (β * (r h s a + episodeReturn H y)) - expQ M β π h s a) ^ 2
          ∂stepLaw M π (s', h.succ)
        = Real.exp (2 * β * r h s a)
          * (entropicVarV M β π h.succ s' + (expValue M β π h.succ s' - m) ^ 2) := by
    set Z := expValue M β π h.succ s' with hZ
    have hXi := integrable_exp_episodeReturn hR π h.succ s'
    have hsq := integrable_exp_episodeReturn_sub_sq hR π h.succ s' Z
    have he : Real.exp (2 * β * r h s a) = Real.exp (β * r h s a) ^ 2 := by
      rw [← Real.exp_nat_mul]
      ring_nf
    calc ∫ y, (Real.exp (β * (r h s a + episodeReturn H y)) - expQ M β π h s a) ^ 2
          ∂stepLaw M π (s', h.succ)
        = ∫ y, Real.exp (2 * β * r h s a) * ((Real.exp (β * episodeReturn H y) - Z) ^ 2
            + (2 * (Z - m) * Real.exp (β * episodeReturn H y) - 2 * (Z - m) * Z)
            + (Z - m) ^ 2) ∂stepLaw M π (s', h.succ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
          simp only
          rw [expQ_of_hasRewardFn M β hM, mul_add, Real.exp_add, ← hm, he]
          ring
      _ = Real.exp (2 * β * r h s a) * (∫ y, (Real.exp (β * episodeReturn H y) - Z) ^ 2
            ∂stepLaw M π (s', h.succ) + (2 * (Z - m) * Z - 2 * (Z - m) * Z) + (Z - m) ^ 2) := by
          rw [integral_const_mul, integral_add, integral_add, integral_sub, integral_const_mul]
          · simp [hZ, expValue]
          · exact hXi.const_mul _
          · exact integrable_const _
          · exact hsq
          · exact (hXi.const_mul _).sub (integrable_const _)
          · exact hsq.add ((hXi.const_mul _).sub (integrable_const _))
          · exact integrable_const _
      _ = _ := by
          rw [← entropicVarV_eq_integral hR]
          ring
  rw [entropicVarQ, hM h s a, integral_dirac, integral_eq_vecExp_transVec]
  simp_rw [hinner]
  rw [vecExp_const_mul, ← mul_add]
  congr 1
  rw [vecVar_eq_sum_sq (EpisodicMDP.sum_transVec M h s a), ← hm]
  simp only [vecExp, mul_add, sum_add_distrib]
  ring

/-! ### Telescoping along the trajectory -/

/-- **Telescoping of the entropic variances**: for an MDP with the reward function `r`,
`∑_h E^π[e^{2β ∑_{i ≤ h} r_i(S_i, A_i)} Var_{p_h}(Z^π_{h+1})(S_h, A_h)] = σV^π_0(s₁)`. -/
lemma sum_integral_exp_mul_vecVar_eq_entropicVarV {r : Fin H → S → A → ℝ} (hM : M.HasRewardFn r)
    (π : Policy S A H) (s₁ : S) :
    ∑ h : Fin H, ∫ x, Real.exp (2 * β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x))
        * vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M β π h.succ)
        ∂stepLaw M π (s₁, startStep H)
      = entropicVarV M β π (startStep H) s₁ := by
  set P := stepLaw M π (s₁, startStep H) with hP
  set D : Fin (H + 1) → ℝ := fun h ↦ ∫ x, Real.exp (2 * β * ∑ i ∈ univ.filter
    (fun i : Fin H ↦ i.castSucc < h), r i (IT.obs i x).1 (IT.action i x))
      * entropicVarV M β π h (IT.obs h x).1 ∂P with hD
  have hstep (i : Fin H) :
      ∫ x, Real.exp (2 * β * ∑ j ∈ Iic i, r j (IT.obs j x).1 (IT.action j x))
        * vecVar (M.transVec i (IT.obs i x).1 (IT.action i x)) (expValue M β π i.succ) ∂P
      = D i.castSucc - D i.succ := by
    have hae := ae_action_eq_stepLaw M π s₁ (h₀ := startStep H) (h := i) (k := i) (by simp)
    have h1 : D i.castSucc = ∫ x,
        (Real.exp (2 * β * ∑ j ∈ Iic i, r j (IT.obs j x).1 (IT.action j x))
          * vecVar (M.transVec i (IT.obs i x).1 (IT.action i x)) (expValue M β π i.succ)
        + Real.exp (2 * β * ∑ j ∈ Iic i, r j (IT.obs j x).1 (IT.action j x))
          * vecExp (M.transVec i (IT.obs i x).1 (π i (IT.obs i x).1))
            (entropicVarV M β π i.succ)) ∂P := by
      simp only [hD, filter_castSucc_lt_castSucc]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      simp only [Fin.val_castSucc]
      rw [entropicVarV_castSucc, entropicVarQ_eq_of_hasRewardFn hM, Iic_eq_cons_Iio, sum_cons, hx,
        mul_add (2 * β), Real.exp_add]
      ring
    have h2 : D i.succ = ∫ x, Real.exp (2 * β * ∑ j ∈ Iic i, r j (IT.obs j x).1 (IT.action j x))
        * entropicVarV M β π i.succ (IT.obs (i + 1) x).1 ∂P := by
      simp only [hD, filter_castSucc_lt_succ]
      rfl
    rw [h1, h2, integral_add (integrable_exp_sum_mul P (2 * β) r (Iic i)
      (fun s a ↦ vecVar (M.transVec i s a) (expValue M β π i.succ)) i)
      (integrable_exp_sum_mul P (2 * β) r (Iic i)
        (fun s _ ↦ vecExp (M.transVec i s (π i s)) (entropicVarV M β π i.succ)) i),
      hP, integral_exp_sum_mul_obs_succ]
    ring
  have htel : ∑ i : Fin H, (D i.castSucc - D i.succ) = D (startStep H) - D (Fin.last H) := by
    set d : ℕ → ℝ := fun n ↦ if hn : n < H + 1 then D ⟨n, hn⟩ else 0 with hd
    have h1 (i : Fin H) : D i.castSucc - D i.succ = d i - d (i + 1) := by
      simp only [hd, show (i : ℕ) < H + 1 by omega, show (i : ℕ) + 1 < H + 1 by omega,
        dite_true]
      rfl
    rw [sum_congr rfl fun i _ ↦ h1 i, Fin.sum_univ_eq_sum_range (fun n ↦ d n - d (n + 1)) H,
      sum_range_sub']
    simp only [hd, show 0 < H + 1 by omega, show H < H + 1 by omega, dite_true]
    rfl
  have hlast : D (Fin.last H) = 0 := by
    simp [hD, entropicVarV_last]
  have hfirst : D (startStep H) = entropicVarV M β π (startStep H) s₁ := by
    have h0 : univ.filter (fun i : Fin H ↦ i.castSucc < startStep H) = ∅ := by
      ext i
      simp
    simp only [hD, h0, sum_empty, mul_zero, Real.exp_zero, one_mul]
    rw [integral_congr_ae (g := fun _ ↦ entropicVarV M β π (startStep H) s₁)]
    · simp
    · filter_upwards [ae_obs_zero_stepLaw M π (s₁, startStep H)] with x hx
      rw [show (startStep H : ℕ) = 0 from rfl, hx]
  rw [sum_congr rfl fun i _ ↦ hstep i, htel, hlast, hfirst, sub_zero]

/-- **Telescoping of the entropic variances**: for an MDP with the reward function `r`,
`∑_h E^π[e^{2β ∑_{i ≤ h} r_i(S_i, A_i)} Var_{p_h}(Z^π_{h+1})(S_h, A_h)] = Var_{P^π}(e^{β R})`. -/
lemma sum_integral_exp_mul_vecVar_eq_variance {r : Fin H → S → A → ℝ} (hM : M.HasRewardFn r)
    (π : Policy S A H) (s₁ : S) :
    ∑ h : Fin H, ∫ x, Real.exp (2 * β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x))
        * vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M β π h.succ)
        ∂stepLaw M π (s₁, startStep H)
      = variance (fun x ↦ Real.exp (β * episodeReturn H x)) (stepLaw M π (s₁, startStep H)) := by
  rw [sum_integral_exp_mul_vecVar_eq_entropicVarV hM,
    entropicVarV_eq_variance (integrable_exp_two_mul_of_hasRewardFn hM)]

/-! ### The normalized variance of the exponentiated return -/

/-- If the return lies almost surely in `[0, G]`, then the exponential value is positive. -/
lemma expValue_pos_of_ae_mem_Icc (π : Policy S A H) (h : Fin (H + 1)) (s : S) {G : ℝ}
    (hret : ∀ᵐ x ∂stepLaw M π (s, h), episodeReturn H x ∈ Set.Icc 0 G) :
    0 < expValue M β π h s :=
  (lt_min one_pos (Real.exp_pos _)).trans_le (integral_mem_Icc_of_ae_mem_Icc
    (hret.mono fun _ hx ↦ exp_mul_mem_Icc_min_max (β := β) hx)
    (measurable_exp_mul_episodeReturn β).aestronglyMeasurable).1

/-- **Normalized variance of the exponentiated return** (Lemma 24 of Essakine, Vernade (2026)
applied to the return): if the return lies almost surely in `[0, G]`, then
`Var(e^{β R}) / (Z^π)² ≤ (e^{|β| G} - 1)² / (4 e^{|β| G})`. -/
lemma variance_exp_episodeReturn_div_sq_le (π : Policy S A H) (h : Fin (H + 1)) (s : S) {G : ℝ}
    (hG : 0 ≤ G) (hret : ∀ᵐ x ∂stepLaw M π (s, h), episodeReturn H x ∈ Set.Icc 0 G) :
    variance (fun x ↦ Real.exp (β * episodeReturn H x)) (stepLaw M π (s, h))
        / expValue M β π h s ^ 2
      ≤ (Real.exp (|β| * G) - 1) ^ 2 / (4 * Real.exp (|β| * G)) :=
  variance_exp_div_sq_integral_le hG hret measurable_episodeReturn.aemeasurable

/-- **Normalized variance of the exponentiated return**, with the constant
`V_G = (e^{|β| G} - 1)² / e^{|β| G}` of the paper. -/
lemma variance_exp_episodeReturn_div_sq_le' (π : Policy S A H) (h : Fin (H + 1)) (s : S) {G : ℝ}
    (hG : 0 ≤ G) (hret : ∀ᵐ x ∂stepLaw M π (s, h), episodeReturn H x ∈ Set.Icc 0 G) :
    variance (fun x ↦ Real.exp (β * episodeReturn H x)) (stepLaw M π (s, h))
        / expValue M β π h s ^ 2
      ≤ (Real.exp (|β| * G) - 1) ^ 2 / Real.exp (|β| * G) := by
  refine (variance_exp_episodeReturn_div_sq_le π h s hG hret).trans ?_
  have he := Real.exp_pos (|β| * G)
  exact div_le_div_of_nonneg_left (sq_nonneg _) he (by linarith)

/-- **Normalized variance of the exponentiated return** for rewards in `[0, 1]`, with the maximal
return `G_max(M)`: `Var_{P^π}(e^{β R}) / Z^π_0(s₁)² ≤ (e^{|β| G_max} - 1)² / e^{|β| G_max}`. -/
lemma variance_exp_episodeReturn_div_sq_le_maxReturn (hM : M.RewardsIn (Set.Icc 0 1))
    (π : Policy S A H) (s₁ : S) :
    variance (fun x ↦ Real.exp (β * episodeReturn H x)) (stepLaw M π (s₁, startStep H))
        / expValue M β π (startStep H) s₁ ^ 2
      ≤ (Real.exp (|β| * maxReturn M s₁) - 1) ^ 2 / Real.exp (|β| * maxReturn M s₁) := by
  refine variance_exp_episodeReturn_div_sq_le' π (startStep H) s₁ (maxReturn_nonneg M hM s₁) ?_
  filter_upwards [ae_episodeReturn_mem_Icc M hM π (startStep H) s₁,
    ae_episodeReturn_le_maxReturn M hM π s₁] with x hx hx'
  exact ⟨hx.1, hx'⟩

end Learning.MDP.Episodic
