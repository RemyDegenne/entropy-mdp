/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.EntropicVariance
public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Occupancy
public import Essakine2026Tight.Mathlib.Analysis.SpecialFunctions.Exp
public import Essakine2026Tight.Mathlib.MeasureTheory.Integral.CauchySchwarz

/-!
# Bounds on the terms of an unrolled recursive inequality

For a policy `π` of a finite-horizon MDP `M` from an initial state `s₁`, with the trajectory weights
`W_h = e^{β ∑_{i ≤ h} r_i(S_i, A_i)}`:

* `le_exp_mul_sum_integral_of_backward`: the unrolling of a backward recursive inequality with the
  factor `κ = 1 + c / H` (`Learning.MDP.Episodic.le_sum_integral_of_backward`), with `κ^h ≤ e^c`;
* `sum_integral_exp_mul_sqrt_vecVar_mul_le`: for an MDP with a reward function and nonnegative
  rates `ρ`, the Cauchy–Schwarz inequality along the trajectory combined with the telescoping of the
  entropic variances,
  `∑_h E^π[W_h √(Var_{p_h}(Z^π_{h+1})(S_h, A_h) ρ_h(S_h, A_h))]
    ≤ √(Var_{P^π}(e^{β R})) √(∑_h ∑_{s, a} p^π_h(s, a) ρ_h(s, a))`;
* `sum_integral_exp_mul_mul_le`: if `W_h c_h(S_h, A_h) ≤ C` everywhere, then
  `∑_h E^π[W_h c_h(S_h, A_h) ρ_h(S_h, A_h)] ≤ C ∑_h ∑_{s, a} p^π_h(s, a) ρ_h(s, a)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP
open scoped ENNReal

namespace Learning.MDP.Episodic

variable {S A : Type*} [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] {H : ℕ} {M : EpisodicMDP S A H}
  {π : Policy S A H} {s₁ : S}

omit [Fintype S] [Fintype A] [Nonempty A] in
/-- A function of the state-action pair of a round is integrable under a finite measure. -/
lemma integrable_comp_obs_action [Finite S] [Finite A]
    (P : Measure (ℕ → Round (LayerState S H) A ℝ)) [IsFiniteMeasure P] (f : S → A → ℝ) (j : ℕ) :
    Integrable (fun x ↦ f (IT.obs j x).1 (IT.action j x)) P := by
  simpa using integrable_exp_sum_mul P 0 (fun _ _ _ ↦ 0) ∅ f j

/-- **Unrolling a backward recursive inequality with the factor `1 + c / H`**: if `g_H = 0` and
`g_h(s) ≤ e^{β r_h(s, π_h s)} (u_h(s, π_h s) + (1 + c / H) (p_h g_{h+1})(s, π_h s))` for all `h < H`
and `s`, with `c ≥ 0` and `u ≥ 0`, then
`g_0(s₁) ≤ e^c ∑_h E^π[e^{β ∑_{i ≤ h} r_i(S_i, A_i)} u_h(S_h, A_h)]`. -/
lemma le_exp_mul_sum_integral_of_backward {c β : ℝ} (hc : 0 ≤ c) {r u : Fin H → S → A → ℝ}
    (hu : ∀ h s a, 0 ≤ u h s a) {g : Fin (H + 1) → S → ℝ} (hlast : ∀ s, g (Fin.last H) s = 0)
    (hg : ∀ (h : Fin H) (s : S), g h.castSucc s ≤ Real.exp (β * r h s (π h s))
      * (u h s (π h s) + (1 + c / H) * vecExp (M.transVec h s (π h s)) (g h.succ))) :
    g (startStep H) s₁ ≤ Real.exp c * ∑ h : Fin H,
      ∫ x, Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x))
        * u h (IT.obs h x).1 (IT.action h x) ∂stepLaw M π (s₁, startStep H) := by
  have hκ : 0 ≤ 1 + c / H := by positivity
  refine (le_sum_integral_of_backward (s₁ := s₁) hκ hlast hg).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun h _ ↦ mul_le_mul_of_nonneg_right ?_ ?_
  · exact Real.one_add_div_pow_le_exp hc h.pos h.is_lt.le
  · exact integral_nonneg fun x ↦ mul_nonneg (Real.exp_pos _).le (hu _ _ _)

/-- **Cauchy–Schwarz inequality for the variance terms along the trajectory**: for an MDP with the
reward function `r` and nonnegative rates `ρ`,
`∑_h E^π[e^{β ∑_{i ≤ h} r_i} √(Var_{p_h}(Z^π_{h+1})(S_h, A_h) ρ_h(S_h, A_h))]` is at most
`√(Var_{P^π}(e^{β R})) √(∑_h ∑_{s, a} p^π_h(s, a) ρ_h(s, a))`. -/
lemma sum_integral_exp_mul_sqrt_vecVar_mul_le {r : Fin H → S → A → ℝ} (hM : M.HasRewardFn r)
    (β : ℝ) {ρ : Fin H → S → A → ℝ} (hρ : ∀ h s a, 0 ≤ ρ h s a) :
    ∑ h : Fin H, ∫ x, Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x))
        * √(vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M β π h.succ)
          * ρ h (IT.obs h x).1 (IT.action h x)) ∂stepLaw M π (s₁, startStep H)
      ≤ √(variance (fun x ↦ Real.exp (β * episodeReturn H x)) (stepLaw M π (s₁, startStep H)))
        * √(∑ h, ∑ s, ∑ a, occupancy M π s₁ h s a * ρ h s a) := by
  set P := stepLaw M π (s₁, startStep H) with hP
  have hvar (h : Fin H) (s : S) (a : A) :
      0 ≤ vecVar (M.transVec h s a) (expValue M β π h.succ) :=
    vecVar_nonneg (M.transVec_nonneg h s a) (M.sum_transVec h s a)
  have hW (h : Fin H) : Measurable fun x : ℕ → Round (LayerState S H) A ℝ ↦
      Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x)) :=
    Real.measurable_exp.comp (measurable_const.mul
      (Finset.measurable_sum _ fun i _ ↦ measurable_comp_obs_action (r i) i))
  have hWV (h : Fin H) : Integrable (fun x ↦
      Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x)) ^ 2
        * vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M β π h.succ)) P := by
    refine (integrable_exp_sum_mul P (2 * β) r (Iic h)
      (fun s a ↦ vecVar (M.transVec h s a) (expValue M β π h.succ)) h).congr
      (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [sq, ← Real.exp_add]
    ring_nf
  have hCS := integral_sum_mul_sqrt_mul_le (μ := P) (univ : Finset (Fin H))
    (W := fun h x ↦ Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x)))
    (V := fun h x ↦ vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M β π h.succ))
    (U := fun h x ↦ ρ h (IT.obs h x).1 (IT.action h x))
    (fun h _ ↦ (hW h).aestronglyMeasurable)
    (fun h _ ↦ (measurable_comp_obs_action
      (fun s a ↦ vecVar (M.transVec h s a) (expValue M β π h.succ)) h).aestronglyMeasurable)
    (fun h _ ↦ (measurable_comp_obs_action (ρ h) h).aestronglyMeasurable)
    (fun h _ ↦ Filter.Eventually.of_forall fun x ↦ hvar _ _ _)
    (fun h _ ↦ Filter.Eventually.of_forall fun x ↦ hρ _ _ _)
    (fun h _ ↦ hWV h) (fun h _ ↦ integrable_comp_obs_action P (ρ h) h)
  have h1 : ∫ x, ∑ h : Fin H, Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x))
        * √(vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M β π h.succ)
          * ρ h (IT.obs h x).1 (IT.action h x)) ∂P
      = ∑ h : Fin H, ∫ x, Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x))
        * √(vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M β π h.succ)
          * ρ h (IT.obs h x).1 (IT.action h x)) ∂P :=
    integral_finsetSum _ fun h _ ↦ integrable_exp_sum_mul P β r (Iic h)
      (fun s a ↦ √(vecVar (M.transVec h s a) (expValue M β π h.succ) * ρ h s a)) h
  have h2 : ∫ x, ∑ h : Fin H, Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x)) ^ 2
        * vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M β π h.succ) ∂P
      = variance (fun x ↦ Real.exp (β * episodeReturn H x)) P := by
    rw [integral_finsetSum _ fun h _ ↦ hWV h, ← sum_integral_exp_mul_vecVar_eq_variance hM π s₁]
    refine sum_congr rfl fun h _ ↦ integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [sq, ← Real.exp_add]
    ring_nf
  have h3 : ∫ x, ∑ h : Fin H, ρ h (IT.obs h x).1 (IT.action h x) ∂P
      = ∑ h, ∑ s, ∑ a, occupancy M π s₁ h s a * ρ h s a :=
    integral_sum_comp_obs_action_stepLaw M π s₁ ρ
  rwa [h1, h2, h3] at hCS

/-- **The weighted rate terms along the trajectory**: if `e^{β ∑_{i ≤ h} r_i} c_h(S_h, A_h) ≤ C`
on every trajectory and `ρ ≥ 0`, then
`∑_h E^π[e^{β ∑_{i ≤ h} r_i} c_h(S_h, A_h) ρ_h(S_h, A_h)]` is at most
`C ∑_h ∑_{s, a} p^π_h(s, a) ρ_h(s, a)`. -/
lemma sum_integral_exp_mul_mul_le {r : Fin H → S → A → ℝ} (β : ℝ) {c ρ : Fin H → S → A → ℝ}
    (hρ : ∀ h s a, 0 ≤ ρ h s a) {C : ℝ}
    (hc : ∀ (h : Fin H) (x : ℕ → Round (LayerState S H) A ℝ),
      Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x))
        * c h (IT.obs h x).1 (IT.action h x) ≤ C) :
    ∑ h : Fin H, ∫ x, Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x))
        * (c h (IT.obs h x).1 (IT.action h x) * ρ h (IT.obs h x).1 (IT.action h x))
        ∂stepLaw M π (s₁, startStep H)
      ≤ C * ∑ h, ∑ s, ∑ a, occupancy M π s₁ h s a * ρ h s a := by
  set P := stepLaw M π (s₁, startStep H) with hP
  calc ∑ h : Fin H, ∫ x, Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x))
        * (c h (IT.obs h x).1 (IT.action h x) * ρ h (IT.obs h x).1 (IT.action h x)) ∂P
      ≤ ∑ h : Fin H, ∫ x, C * ρ h (IT.obs h x).1 (IT.action h x) ∂P := by
        refine sum_le_sum fun h _ ↦ integral_mono
          (integrable_exp_sum_mul P β r (Iic h) (fun s a ↦ c h s a * ρ h s a) h)
          ((integrable_comp_obs_action P (ρ h) h).const_mul C) fun x ↦ ?_
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hc h x) (hρ _ _ _)
    _ = C * ∑ h, ∑ s, ∑ a, occupancy M π s₁ h s a * ρ h s a := by
        rw [mul_sum]
        refine sum_congr rfl fun h _ ↦ ?_
        rw [integral_const_mul, integral_comp_obs_action_stepLaw]

end Learning.MDP.Episodic
