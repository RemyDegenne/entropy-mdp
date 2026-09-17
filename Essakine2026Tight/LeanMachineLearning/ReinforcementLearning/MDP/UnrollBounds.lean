/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.EntropicVariance
public import Essakine2026Tight.Mathlib.Analysis.SpecialFunctions.Exp
public import Essakine2026Tight.Mathlib.MeasureTheory.Integral.CauchySchwarz

/-!
# Bounds on the terms of an unrolled recursive inequality

For a policy `π : ℕ → S → A` (measurable at every step) of a finite-horizon MDP `M` with the
horizon `H` from an initial state `s₁`, with the trajectory weights
`W_h = e^{β ∑_{i ≤ h} r_i(S_i, A_i)}`:

* `le_exp_mul_sum_integral_of_backward`: the unrolling of a backward recursive inequality with the
  factor `κ = 1 + c / H` (`Learning.MDP.Episodic.le_sum_integral_of_backward_exp`), with
  `κ^h ≤ e^c`;
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

variable {S A : Type*} [Finite S] [Finite A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] {M : EpisodicMDP S A} {π : ℕ → S → A}
  (hπ : ∀ h, Measurable (π h)) {s₁ : S} {H : ℕ}

include hπ in
/-- **Unrolling a backward recursive inequality with the factor `1 + c / H`**: if `g_H = 0` and
`g_h(s) ≤ e^{β r_h(s, π_h s)} (u_h(s, π_h s) + (1 + c / H) (p_h g_{h+1})(s, π_h s))` for all `h < H`
and `s`, with `c ≥ 0` and `u ≥ 0`, then
`g_0(s₁) ≤ e^c ∑_{h < H} E^π[e^{β ∑_{i ≤ h} r_i(S_i, A_i)} u_h(S_h, A_h)]`. -/
lemma le_exp_mul_sum_integral_of_backward {c β : ℝ} (hc : 0 ≤ c) {r u : ℕ → S → A → ℝ}
    (hu : ∀ h s a, 0 ≤ u h s a) {g : ℕ → S → ℝ} (hlast : ∀ s, g H s = 0)
    (hg : ∀ h < H, ∀ s, g h s ≤ Real.exp (β * r h s (π h s))
      * (u h s (π h s) + (1 + c / H) * ∫ s', g (h + 1) s' ∂M.trans h (s, π h s))) :
    g 0 s₁ ≤ Real.exp c * ∑ h ∈ range H,
      ∫ x, Real.exp (β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
        * u h (IT.obs h x).1 (IT.action h x) ∂stepLaw M π (s₁, 0) := by
  have hκ : 0 ≤ 1 + c / H := by positivity
  refine (le_sum_integral_of_backward_exp hπ (s₁ := s₁) hκ hlast hg).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun h hh ↦ mul_le_mul_of_nonneg_right ?_ ?_
  · have hh := mem_range.1 hh
    exact Real.one_add_div_pow_le_exp hc (by omega) hh.le
  · exact integral_nonneg fun x ↦ mul_nonneg (Real.exp_pos _).le (hu _ _ _)

include hπ in
/-- **Cauchy–Schwarz inequality for the variance terms along the trajectory**: for an MDP with a
bounded reward function `r` and nonnegative rates `ρ`,
`∑_{h < H} E^π[e^{β ∑_{i ≤ h} r_i} √(Var_{p_h}(Z^π_{h+1})(S_h, A_h) ρ_h(S_h, A_h))]` is at most
`√(Var_{P^π}(e^{β R})) √(∑_{h < H} ∑_{s, a} p^π_h(s, a) ρ_h(s, a))`. -/
lemma sum_integral_exp_mul_sqrt_vecVar_mul_le [Fintype S] [Fintype A] {r : ℕ → S → A → ℝ}
    (hM : M.HasRewardFn r) {a b : ℝ} (hr : ∀ h s a', r h s a' ∈ Set.Icc a b) (β : ℝ)
    {ρ : ℕ → S → A → ℝ} (hρ : ∀ h s a, 0 ≤ ρ h s a) :
    ∑ h ∈ range H, ∫ x, Real.exp (β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
        * √(vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M H β π (h + 1))
          * ρ h (IT.obs h x).1 (IT.action h x)) ∂stepLaw M π (s₁, 0)
      ≤ √(variance (fun x ↦ Real.exp (β * episodeReturn H x)) (stepLaw M π (s₁, 0)))
        * √(∑ h ∈ range H, ∑ s, ∑ a, occupancy M π s₁ h s a * ρ h s a) := by
  set P := stepLaw M π (s₁, 0) with hP
  have hvar (h : ℕ) (s : S) (a : A) :
      0 ≤ vecVar (M.transVec h s a) (expValue M H β π (h + 1)) :=
    vecVar_nonneg (M.transVec_nonneg h s a) (M.sum_transVec h s a)
  have hW (h : ℕ) : Measurable fun x : ℕ → Round (S × ℕ) A ℝ ↦
      Real.exp (β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x)) :=
    Real.measurable_exp.comp (measurable_const.mul
      (Finset.measurable_sum _ fun i _ ↦ measurable_comp_obs_action (r i) i))
  have hWV (h : ℕ) : Integrable (fun x ↦
      Real.exp (β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x)) ^ 2
        * vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M H β π (h + 1))) P := by
    refine (integrable_exp_sum_mul P (2 * β) r (range (h + 1))
      (fun s a ↦ vecVar (M.transVec h s a) (expValue M H β π (h + 1))) h).congr
      (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [sq, ← Real.exp_add]
    ring_nf
  have hCS := integral_sum_mul_sqrt_mul_le (μ := P) (range H)
    (W := fun h x ↦ Real.exp (β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x)))
    (V := fun h x ↦
      vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M H β π (h + 1)))
    (U := fun h x ↦ ρ h (IT.obs h x).1 (IT.action h x)) (fun h _ ↦ (hW h).aestronglyMeasurable)
    (fun h _ ↦ (measurable_comp_obs_action
      (fun s a ↦ vecVar (M.transVec h s a) (expValue M H β π (h + 1))) h).aestronglyMeasurable)
    (fun h _ ↦ (measurable_comp_obs_action (ρ h) h).aestronglyMeasurable)
    (fun h _ ↦ Filter.Eventually.of_forall fun x ↦ hvar _ _ _)
    (fun h _ ↦ Filter.Eventually.of_forall fun x ↦ hρ _ _ _)
    (fun h _ ↦ hWV h) (fun h _ ↦ integrable_comp_obs_action P (ρ h) h)
  have h1 : ∫ x, ∑ h ∈ range H,
        Real.exp (β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
        * √(vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M H β π (h + 1))
          * ρ h (IT.obs h x).1 (IT.action h x)) ∂P
      = ∑ h ∈ range H, ∫ x,
        Real.exp (β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
        * √(vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M H β π (h + 1))
          * ρ h (IT.obs h x).1 (IT.action h x)) ∂P :=
    integral_finsetSum _ fun h _ ↦ integrable_exp_sum_mul P β r (range (h + 1))
      (fun s a ↦ √(vecVar (M.transVec h s a) (expValue M H β π (h + 1)) * ρ h s a)) h
  have h2 : ∫ x, ∑ h ∈ range H,
        Real.exp (β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x)) ^ 2
        * vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M H β π (h + 1)) ∂P
      = variance (fun x ↦ Real.exp (β * episodeReturn H x)) P := by
    rw [integral_finsetSum _ fun h _ ↦ hWV h,
      ← sum_integral_exp_mul_vecVar_eq_variance M H β hπ s₁ hM hr]
    refine sum_congr rfl fun h _ ↦ integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [sq, ← Real.exp_add]
    ring_nf
  have h3 : ∫ x, ∑ h ∈ range H, ρ h (IT.obs h x).1 (IT.action h x) ∂P
      = ∑ h ∈ range H, ∑ s, ∑ a, occupancy M π s₁ h s a * ρ h s a :=
    integral_sum_comp_obs_action_stepLaw M π s₁ H ρ
  rwa [h1, h2, h3] at hCS

/-- **The weighted rate terms along the trajectory**: if `e^{β ∑_{i ≤ h} r_i} c_h(S_h, A_h) ≤ C`
on every trajectory and `ρ ≥ 0`, then
`∑_{h < H} E^π[e^{β ∑_{i ≤ h} r_i} c_h(S_h, A_h) ρ_h(S_h, A_h)]` is at most
`C ∑_{h < H} ∑_{s, a} p^π_h(s, a) ρ_h(s, a)`. -/
lemma sum_integral_exp_mul_mul_le [Fintype S] [Fintype A] {r : ℕ → S → A → ℝ} (β : ℝ)
    {c ρ : ℕ → S → A → ℝ} (hρ : ∀ h s a, 0 ≤ ρ h s a) {C : ℝ}
    (hc : ∀ h < H, ∀ (x : ℕ → Round (S × ℕ) A ℝ),
      Real.exp (β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
        * c h (IT.obs h x).1 (IT.action h x) ≤ C) :
    ∑ h ∈ range H, ∫ x, Real.exp (β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
        * (c h (IT.obs h x).1 (IT.action h x) * ρ h (IT.obs h x).1 (IT.action h x))
        ∂stepLaw M π (s₁, 0)
      ≤ C * ∑ h ∈ range H, ∑ s, ∑ a, occupancy M π s₁ h s a * ρ h s a := by
  set P := stepLaw M π (s₁, 0) with hP
  calc ∑ h ∈ range H, ∫ x,
        Real.exp (β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
        * (c h (IT.obs h x).1 (IT.action h x) * ρ h (IT.obs h x).1 (IT.action h x)) ∂P
      ≤ ∑ h ∈ range H, ∫ x, C * ρ h (IT.obs h x).1 (IT.action h x) ∂P := by
        refine sum_le_sum fun h hh ↦ integral_mono
          (integrable_exp_sum_mul P β r (range (h + 1)) (fun s a ↦ c h s a * ρ h s a) h)
          ((integrable_comp_obs_action P (ρ h) h).const_mul C) fun x ↦ ?_
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hc h (mem_range.1 hh) x) (hρ _ _ _)
    _ = C * ∑ h ∈ range H, ∑ s, ∑ a, occupancy M π s₁ h s a * ρ h s a := by
        rw [mul_sum]
        refine sum_congr rfl fun h _ ↦ ?_
        rw [integral_const_mul, integral_comp_obs_action_stepLaw]

end Learning.MDP.Episodic
