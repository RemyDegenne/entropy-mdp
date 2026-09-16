/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.Moments.Variance
public import Essakine2026Tight.Mathlib.Probability.Moments.Variance

/-!
# Variance transport inequalities for bounded random variables

Elementary bounds on the variance of a random variable with values in `[0, b]`:

* `ProbabilityTheory.variance_le_integral_sub_sq`: the variance minimizes the centered second
  moment, `Var(f) ≤ ∫ (f - m)²`;
* `ProbabilityTheory.variance_le_mul_integral`: `Var(f) ≤ 𝔼[f²] ≤ b 𝔼[f]` for `f ∈ [0, b]`
  (Lemma 26' of Essakine, Vernade (2026));
* `ProbabilityTheory.variance_le_two_mul_variance_add`: transport between two functions,
  `Var_μ(f) ≤ 2 Var_μ(g) + 2 b 𝔼_μ|f - g|`;
* `ProbabilityTheory.variance_le_variance_add_sum_abs_sub`: transport between two probability
  measures on a finite space, `Var_ν(f) ≤ Var_μ(f) + b² ‖μ - ν‖₁`.

The last two are Lemma 26 of Essakine, Vernade (2026) (Lemma 12 of Ménard et al. (2021)).
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f g : Ω → ℝ} {b m : ℝ}

section IsProbabilityMeasure

variable [IsProbabilityMeasure μ]

/-- A random variable with values in a bounded interval is integrable. -/
lemma integrable_of_ae_mem_Icc {a : ℝ} (hf : ∀ᵐ ω ∂μ, f ω ∈ Set.Icc a b)
    (hfm : AEStronglyMeasurable f μ) : Integrable f μ :=
  (memLp_of_bounded hf hfm 1).integrable le_rfl

/-- The variance minimizes the centered second moment: `Var(f) ≤ ∫ (f - m)²`. -/
lemma variance_le_integral_sub_sq (hfm : AEStronglyMeasurable f μ) (m : ℝ) :
    variance f μ ≤ ∫ ω, (f ω - m) ^ 2 ∂μ := by
  have h := variance_le_expectation_sq (μ := μ) (X := fun ω ↦ f ω - m)
    (hfm.sub aestronglyMeasurable_const)
  rwa [variance_sub_const hfm m] at h

/-- For `f` with values in `[0, b]`, `Var(f) ≤ 𝔼[f²] ≤ b 𝔼[f]`. -/
lemma variance_le_mul_integral (hf : ∀ᵐ ω ∂μ, f ω ∈ Set.Icc 0 b)
    (hfm : AEStronglyMeasurable f μ) : variance f μ ≤ b * μ[f] := by
  have hb : 0 ≤ b := by
    obtain ⟨ω, hω⟩ := hf.exists
    exact le_trans hω.1 hω.2
  have hsq : ∀ᵐ ω ∂μ, f ω ^ 2 ∈ Set.Icc 0 (b ^ 2) := by
    filter_upwards [hf] with ω hω
    exact ⟨by positivity, by nlinarith [hω.1, hω.2]⟩
  have hint : Integrable f μ := integrable_of_ae_mem_Icc hf hfm
  have hint2 : Integrable (fun ω ↦ f ω ^ 2) μ :=
    integrable_of_ae_mem_Icc hsq (hfm.pow 2)
  calc variance f μ ≤ μ[f ^ 2] := variance_le_expectation_sq hfm
    _ = ∫ ω, f ω ^ 2 ∂μ := by simp [Pi.pow_apply]
    _ ≤ ∫ ω, b * f ω ∂μ := by
        refine integral_mono_ae hint2 (hint.const_mul b) ?_
        filter_upwards [hf] with ω hω
        nlinarith [hω.1, hω.2]
    _ = b * μ[f] := integral_const_mul b f

/-- Transport of the variance between two functions with values in `[0, b]`:
`Var_μ(f) ≤ 2 Var_μ(g) + 2 b 𝔼_μ|f - g|`. -/
lemma variance_le_two_mul_variance_add (hf : ∀ᵐ ω ∂μ, f ω ∈ Set.Icc 0 b)
    (hg : ∀ᵐ ω ∂μ, g ω ∈ Set.Icc 0 b) (hfm : AEStronglyMeasurable f μ)
    (hgm : AEStronglyMeasurable g μ) :
    variance f μ ≤ 2 * variance g μ + 2 * b * ∫ ω, |f ω - g ω| ∂μ := by
  have hgint : Integrable g μ := integrable_of_ae_mem_Icc hg hgm
  have hmg : μ[g] ∈ Set.Icc 0 b := integral_mem_Icc_of_ae_mem_Icc hg hgm
  have habs : ∀ᵐ ω ∂μ, |f ω - g ω| ∈ Set.Icc 0 b := by
    filter_upwards [hf, hg] with ω hω hω'
    exact ⟨abs_nonneg _, abs_sub_le_iff.2 ⟨by linarith [hω.2, hω'.1], by linarith [hω.1, hω'.2]⟩⟩
  have hgc : ∀ᵐ ω ∂μ, (g ω - μ[g]) ^ 2 ∈ Set.Icc 0 (b ^ 2) := by
    filter_upwards [hg] with ω hω
    refine ⟨by positivity, ?_⟩
    have h1 : -b ≤ g ω - μ[g] := by linarith [hω.1, hmg.2]
    have h2 : g ω - μ[g] ≤ b := by linarith [hω.2, hmg.1]
    nlinarith
  have hfc : ∀ᵐ ω ∂μ, (f ω - μ[g]) ^ 2 ∈ Set.Icc 0 (b ^ 2) := by
    filter_upwards [hf] with ω hω
    refine ⟨by positivity, ?_⟩
    have h1 : -b ≤ f ω - μ[g] := by linarith [hω.1, hmg.2]
    have h2 : f ω - μ[g] ≤ b := by linarith [hω.2, hmg.1]
    nlinarith
  have habsm : AEStronglyMeasurable (fun ω ↦ |f ω - g ω|) μ := by fun_prop
  have hi1 : Integrable (fun ω ↦ (f ω - μ[g]) ^ 2) μ :=
    integrable_of_ae_mem_Icc hfc (by fun_prop)
  have hi2 : Integrable (fun ω ↦ 2 * b * |f ω - g ω| + 2 * (g ω - μ[g]) ^ 2) μ := by
    refine Integrable.add ?_ ?_
    · exact (integrable_of_ae_mem_Icc habs habsm).const_mul _
    · exact (integrable_of_ae_mem_Icc hgc (by fun_prop)).const_mul _
  calc variance f μ ≤ ∫ ω, (f ω - μ[g]) ^ 2 ∂μ := variance_le_integral_sub_sq hfm _
    _ ≤ ∫ ω, (2 * b * |f ω - g ω| + 2 * (g ω - μ[g]) ^ 2) ∂μ := by
        refine integral_mono_ae hi1 hi2 ?_
        filter_upwards [habs] with ω hω
        have hsq : (f ω - g ω) ^ 2 ≤ b * |f ω - g ω| := by
          have : (f ω - g ω) ^ 2 = |f ω - g ω| ^ 2 := (sq_abs _).symm
          nlinarith [hω.1, hω.2]
        nlinarith [sq_nonneg (f ω - g ω - (g ω - μ[g]))]
    _ = 2 * b * ∫ ω, |f ω - g ω| ∂μ + 2 * variance g μ := by
        rw [integral_add ((integrable_of_ae_mem_Icc habs habsm).const_mul _)
          ((integrable_of_ae_mem_Icc hgc (by fun_prop)).const_mul _),
          integral_const_mul, integral_const_mul, variance_eq_integral hgm.aemeasurable]
    _ = 2 * variance g μ + 2 * b * ∫ ω, |f ω - g ω| ∂μ := by ring

end IsProbabilityMeasure

/-- Transport of the variance between two probability measures on a finite space:
`Var_ν(f) ≤ Var_μ(f) + b² ‖μ - ν‖₁` for `f` with values in `[0, b]`, where
`‖μ - ν‖₁ = ∑ x, |μ{x} - ν{x}|`. -/
lemma variance_le_variance_add_sum_abs_sub {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {μ ν : Measure ι} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : ι → ℝ} {b : ℝ} (hf : ∀ x, f x ∈ Set.Icc 0 b) :
    variance f ν ≤ variance f μ + b ^ 2 * ∑ x, |μ.real {x} - ν.real {x}| := by
  have hfm : ∀ ρ : Measure ι, AEStronglyMeasurable f ρ := fun ρ ↦
    (measurable_of_countable f).aestronglyMeasurable
  have hmean : μ[f] ∈ Set.Icc 0 b :=
    integral_mem_Icc_of_ae_mem_Icc (.of_forall hf) (hfm μ)
  have hbound : ∀ x, (f x - μ[f]) ^ 2 ∈ Set.Icc 0 (b ^ 2) := fun x ↦ by
    have h1 : -b ≤ f x - μ[f] := by linarith [(hf x).1, hmean.2]
    have h2 : f x - μ[f] ≤ b := by linarith [(hf x).2, hmean.1]
    exact ⟨by positivity, by nlinarith⟩
  have key : ∀ ρ : Measure ι, [IsProbabilityMeasure ρ] →
      ∫ x, (f x - μ[f]) ^ 2 ∂ρ = ∑ x, ρ.real {x} * (f x - μ[f]) ^ 2 := by
    intro ρ _
    rw [integral_fintype Integrable.of_finite]
    simp [smul_eq_mul, measureReal_def]
  have hν := key ν
  have hμ := key μ
  have hdiff : ∑ x, ν.real {x} * (f x - μ[f]) ^ 2 - ∑ x, μ.real {x} * (f x - μ[f]) ^ 2
      ≤ b ^ 2 * ∑ x, |μ.real {x} - ν.real {x}| := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    have h1 : ν.real {x} * (f x - μ[f]) ^ 2 - μ.real {x} * (f x - μ[f]) ^ 2
        = (ν.real {x} - μ.real {x}) * (f x - μ[f]) ^ 2 := by ring
    rw [h1]
    have h2 : (ν.real {x} - μ.real {x}) ≤ |μ.real {x} - ν.real {x}| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    nlinarith [(hbound x).1, (hbound x).2, abs_nonneg (μ.real {x} - ν.real {x})]
  have hvν : variance f ν ≤ ∫ x, (f x - μ[f]) ^ 2 ∂ν :=
    variance_le_integral_sub_sq (hfm ν) _
  have hvμ : ∫ x, (f x - μ[f]) ^ 2 ∂μ = variance f μ :=
    (variance_eq_integral (hfm μ).aemeasurable).symm
  rw [hν] at hvν
  rw [hμ] at hvμ
  linarith

end ProbabilityTheory
