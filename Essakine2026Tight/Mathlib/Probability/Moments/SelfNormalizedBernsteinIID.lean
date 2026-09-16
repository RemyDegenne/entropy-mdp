/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.Mathlib.Probability.Independence.NaturalPast
public import Essakine2026Tight.Mathlib.Probability.Moments.SelfNormalizedBernstein
public import Mathlib.Probability.HasLaw

/-!
# Time-uniform Bernstein inequality for an i.i.d. sequence

Let `ξ 0, ξ 1, …` be i.i.d. with law `ν`, `g` a measurable function with `|g - ν g| ≤ b` and
`σ² = ν (g - ν g)²` its variance. For `δ ∈ (0, 1)`, with probability at least `1 - δ`, for all
`n`, `|∑_{i < n} (g (ξ i) - ν g)| ≤ √(2 n σ² L n) + 3 b L n` with `L n = log (4 e (2 n + 1) / δ)`
(`ProbabilityTheory.measure_exists_sqrt_add_lt_abs_sum_sub_integral_le`).

This is the explicit self-normalized Bernstein inequality
(`ProbabilityTheory.measure_exists_sqrt_add_lt_abs_selfNormSum_le'`) for the constant weights
`1`, the constant conditional variances `σ²` and the filtration of the strict past
(`MeasureTheory.Filtration.naturalPast`), for which the centered variables are martingale
differences by independence.
-/

@[expose] public section

open MeasureTheory Real Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω α : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ξ : ℕ → Ω → α} {ν : Measure α} {g : α → ℝ} {b δ : ℝ}

/-- **Time-uniform Bernstein inequality for an i.i.d. sequence**: if the `ξ i` are i.i.d. with law
`ν`, `g` is a measurable function with `|g - ν g| ≤ b` and `σ² = ν (g - ν g)²`, then for
`δ ∈ (0, 1)`, with probability at least `1 - δ`, for all `n`,
`|∑_{i < n} (g (ξ i) - ν g)| ≤ √(2 n σ² L n) + 3 b L n` with `L n = log (4 e (2 n + 1) / δ)`. -/
lemma measure_exists_sqrt_add_lt_abs_sum_sub_integral_le (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hlaw : ∀ i, HasLaw (ξ i) ν μ) (hg : Measurable g)
    (hgb : ∀ x, |g x - ∫ y, g y ∂ν| ≤ b) (hδ : 0 < δ) (hδ1 : δ < 1) :
    μ {ω | ∃ n : ℕ, √(2 * (n * ∫ x, (g x - ∫ y, g y ∂ν) ^ 2 ∂ν)
          * log (4 * exp 1 * (2 * n + 1) / δ)) + 3 * b * log (4 * exp 1 * (2 * n + 1) / δ)
        < |∑ i ∈ range n, (g (ξ i ω) - ∫ y, g y ∂ν)|} ≤ ENNReal.ofReal δ := by
  set m := ∫ y, g y ∂ν with hm
  set σ2 := ∫ x, (g x - m) ^ 2 ∂ν with hσ2
  set ℱ := Filtration.naturalPast ξ hξ with hℱ
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hgb (ξ 0 ω₀))
  rcases hb0.lt_or_eq with hb | rfl
  swap
  · -- if `b = 0`, the sums vanish and the event is empty
    have hempty : {ω | ∃ n : ℕ, √(2 * (n * σ2) * log (4 * exp 1 * (2 * n + 1) / δ))
        + 3 * 0 * log (4 * exp 1 * (2 * n + 1) / δ)
        < |∑ i ∈ range n, (g (ξ i ω) - m)|} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun ω ⟨n, hn⟩ ↦ ?_
      have hsum : ∑ i ∈ range n, (g (ξ i ω) - m) = 0 :=
        sum_eq_zero fun i _ ↦ abs_nonpos_iff.1 (hgb _)
      rw [hsum, abs_zero] at hn
      exact absurd hn (not_lt.2 (by simp))
    rw [hempty, measure_empty]
    exact zero_le
  have hν : IsProbabilityMeasure ν := (hlaw 0).isProbabilityMeasure_iff.1 inferInstance
  have hgint : Integrable g ν := by
    refine Integrable.of_bound hg.aestronglyMeasurable (b + |m|) (.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs]
    calc |g x| = |(g x - m) + m| := by ring_nf
      _ ≤ |g x - m| + |m| := abs_add_le _ _
      _ ≤ b + |m| := by linarith [hgb x]
  have hm0 : ∫ x, (g x - m) ∂ν = 0 := by
    rw [integral_sub hgint (integrable_const m)]
    simp [hm]
  have hσ2b : σ2 ∈ Set.Icc 0 (b ^ 2) := by
    refine ⟨integral_nonneg fun x ↦ sq_nonneg _, ?_⟩
    calc σ2 ≤ ∫ _x, b ^ 2 ∂ν := by
          refine integral_mono_of_nonneg (.of_forall fun x ↦ sq_nonneg _) (integrable_const _)
            (.of_forall fun x ↦ ?_)
          simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hgb x) 2
      _ = b ^ 2 := by simp
  have hcond (i : ℕ) {f : ℝ → ℝ} (hf : Measurable f) :
      μ[fun ω ↦ f (g (ξ i ω) - m) | ℱ i] =ᵐ[μ] fun _ ↦ ∫ x, f (g x - m) ∂ν := by
    refine (hind.condExp_naturalPast_ae_eq hξ i (f := fun x ↦ f (g x - m))
      (hf.comp (hg.sub_const m))).trans (.of_forall fun _ ↦ ?_)
    exact (hlaw i).integral_comp (f := fun x ↦ f (g x - m))
      (hf.comp (hg.sub_const m)).aestronglyMeasurable
  have h := measure_exists_sqrt_add_lt_abs_selfNormSum_le' (μ := μ) (ℱ := ℱ)
    (Y := fun i ω ↦ g (ξ i ω) - m) (w := fun _ _ ↦ 1) (v := fun _ _ ↦ σ2) hb
    (fun i ↦ ((hg.comp (Filtration.measurable_naturalPast_succ ξ hξ i)).sub_const m
      ).stronglyMeasurable)
    (fun i ↦ .of_forall fun ω ↦ hgb _)
    (fun i ↦ (hcond i measurable_id).trans (.of_forall fun _ ↦ hm0))
    (fun i ↦ stronglyMeasurable_const) (fun i ω ↦ by simp)
    (fun i ↦ stronglyMeasurable_const) (fun i ω ↦ hσ2b)
    (fun i ↦ (hcond i (measurable_id.pow_const 2)).trans (.of_forall fun _ ↦ rfl)) hδ hδ1
  convert h using 3 with ω
  simp [selfNormSum, selfNormVar]

end ProbabilityTheory
