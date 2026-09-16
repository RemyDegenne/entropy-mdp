/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A Cauchy–Schwarz inequality for sums of integrals

For real functions `W i`, `V i ≥ 0`, `U i ≥ 0` (`i ∈ s`, a finite set) with `W i ^ 2 * V i` and
`U i` integrable,
`∫ ∑ i ∈ s, W i √(V i U i) ≤ √(∫ ∑ i ∈ s, W i ^ 2 V i) √(∫ ∑ i ∈ s, U i)`
(`MeasureTheory.integral_sum_mul_sqrt_mul_le`). The proof integrates the pointwise inequality
`2 W √(V U) ≤ t W² V + U / t` for every `t > 0` and optimizes over `t`
(`Real.le_sqrt_mul_sqrt_of_forall_two_mul_le`).
-/

@[expose] public section

open MeasureTheory Finset

namespace Real

/-- If `2 c ≤ t a + b / t` for every `t > 0`, with `a, b ≥ 0`, then `c ≤ √a √b`. -/
lemma le_sqrt_mul_sqrt_of_forall_two_mul_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ t, 0 < t → 2 * c ≤ t * a + b / t) : c ≤ √a * √b := by
  rcases ha.eq_or_lt with ha0 | ha0 <;> rcases hb.eq_or_lt with hb0 | hb0
  · have := h 1 one_pos
    rw [← ha0, ← hb0] at this ⊢
    simp only [mul_zero, zero_div, add_zero] at this
    simp only [sqrt_zero, mul_zero]
    linarith
  · rw [← ha0, sqrt_zero, zero_mul]
    by_contra hc
    push Not at hc
    have := h (b / c) (div_pos hb0 hc)
    rw [← ha0, mul_zero, zero_add, div_div_cancel₀ hb0.ne'] at this
    linarith
  · rw [← hb0, sqrt_zero, mul_zero]
    by_contra hc
    push Not at hc
    have := h (c / a) (div_pos hc ha0)
    rw [← hb0, zero_div, add_zero, div_mul_cancel₀ c ha0.ne'] at this
    linarith
  · have hsa := sqrt_pos.2 ha0
    have hsb := sqrt_pos.2 hb0
    have := h (√b / √a) (div_pos hsb hsa)
    have e1 : √b / √a * a = √a * √b := by
      rw [div_mul_eq_mul_div, div_eq_iff hsa.ne']
      calc √b * a = √b * (√a * √a) := by rw [mul_self_sqrt ha]
        _ = √a * √b * √a := by ring
    have e2 : b / (√b / √a) = √a * √b := by
      rw [div_div_eq_mul_div, div_eq_iff hsb.ne']
      calc b * √a = (√b * √b) * √a := by rw [mul_self_sqrt hb]
        _ = √a * √b * √b := by ring
    rw [e1, e2] at this
    linarith

end Real

namespace MeasureTheory

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Cauchy–Schwarz inequality for a finite sum of integrals**:
`∫ ∑ i ∈ s, W i √(V i U i) ≤ √(∫ ∑ i ∈ s, W i ^ 2 V i) √(∫ ∑ i ∈ s, U i)` for `V i, U i ≥ 0`. -/
lemma integral_sum_mul_sqrt_mul_le (s : Finset ι) {W V U : ι → Ω → ℝ}
    (hW : ∀ i ∈ s, AEStronglyMeasurable (W i) μ) (hV : ∀ i ∈ s, AEStronglyMeasurable (V i) μ)
    (hU : ∀ i ∈ s, AEStronglyMeasurable (U i) μ)
    (hV0 : ∀ i ∈ s, 0 ≤ᵐ[μ] V i) (hU0 : ∀ i ∈ s, 0 ≤ᵐ[μ] U i)
    (hWV : ∀ i ∈ s, Integrable (fun ω ↦ W i ω ^ 2 * V i ω) μ) (hUi : ∀ i ∈ s, Integrable (U i) μ) :
    ∫ ω, ∑ i ∈ s, W i ω * √(V i ω * U i ω) ∂μ
      ≤ √(∫ ω, ∑ i ∈ s, W i ω ^ 2 * V i ω ∂μ) * √(∫ ω, ∑ i ∈ s, U i ω ∂μ) := by
  -- the pointwise inequality
  have hpt (t : ℝ) (ht : 0 < t) (w v u : ℝ) (hv : 0 ≤ v) (hu : 0 ≤ u) :
      2 * (w * √(v * u)) ≤ t * (w ^ 2 * v) + u / t := by
    have hst := Real.sqrt_pos.2 ht
    have ha : (√t * (w * √v)) ^ 2 = t * (w ^ 2 * v) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt ht.le, Real.sq_sqrt hv]
    have hb : (√u / √t) ^ 2 = u / t := by
      rw [div_pow, Real.sq_sqrt hu, Real.sq_sqrt ht.le]
    have hab : √t * (w * √v) * (√u / √t) = w * √(v * u) := by
      rw [Real.sqrt_mul hv]
      field_simp
    nlinarith [sq_nonneg (√t * (w * √v) - √u / √t)]
  -- integrability of the left-hand side
  have hint : ∀ i ∈ s, Integrable (fun ω ↦ W i ω * √(V i ω * U i ω)) μ := by
    intro i hi
    refine Integrable.mono' (((hWV i hi).add (hUi i hi)).div_const 2)
      ((hW i hi).mul (((hV i hi).mul (hU i hi)).aemeasurable.sqrt.aestronglyMeasurable)) ?_
    filter_upwards [hV0 i hi, hU0 i hi] with ω hv hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have := hpt 1 one_pos |W i ω| (V i ω) (U i ω) hv hu
    rw [sq_abs] at this
    simp only [one_mul, div_one, Pi.add_apply] at this ⊢
    linarith
  have hint' : Integrable (fun ω ↦ ∑ i ∈ s, W i ω * √(V i ω * U i ω)) μ :=
    integrable_finsetSum _ hint
  have hA : 0 ≤ ∫ ω, ∑ i ∈ s, W i ω ^ 2 * V i ω ∂μ := by
    refine integral_nonneg_of_ae ?_
    have : ∀ᵐ ω ∂μ, ∀ i ∈ s, 0 ≤ V i ω := by
      rw [Filter.eventually_all_finset]
      exact hV0
    filter_upwards [this] with ω hω
    exact sum_nonneg fun i hi ↦ mul_nonneg (sq_nonneg _) (hω i hi)
  have hB : 0 ≤ ∫ ω, ∑ i ∈ s, U i ω ∂μ := by
    refine integral_nonneg_of_ae ?_
    have : ∀ᵐ ω ∂μ, ∀ i ∈ s, 0 ≤ U i ω := by
      rw [Filter.eventually_all_finset]
      exact hU0
    filter_upwards [this] with ω hω
    exact sum_nonneg fun i hi ↦ hω i hi
  refine Real.le_sqrt_mul_sqrt_of_forall_two_mul_le hA hB fun t ht ↦ ?_
  have hVU : ∀ᵐ ω ∂μ, ∀ i ∈ s, 0 ≤ V i ω ∧ 0 ≤ U i ω := by
    rw [Filter.eventually_all_finset]
    exact fun i hi ↦ (hV0 i hi).and (hU0 i hi)
  rw [← integral_const_mul, ← integral_div, ← integral_const_mul, ← integral_add]
  · refine integral_mono_ae (hint'.const_mul 2) ?_ ?_
    · exact ((integrable_finsetSum _ hWV).const_mul t).add
        ((integrable_finsetSum _ hUi).div_const t)
    · filter_upwards [hVU] with ω hω
      simp only [mul_sum, sum_div, ← sum_add_distrib]
      exact sum_le_sum fun i hi ↦ hpt t ht _ _ _ (hω i hi).1 (hω i hi).2
  · exact (integrable_finsetSum _ hWV).const_mul t
  · exact (integrable_finsetSum _ hUi).div_const t

end MeasureTheory
