/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.Mathlib.Probability.HasCondDistribIntegral
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Conditional expectations from a conditional distribution

If `Y` has conditional law `κ` given `X` under a finite measure `P`, then for every bounded
measurable function `f`, `𝔼[f(X, Y) | σ(X)] = ∫ f(X, y) dκ(X)` almost surely
(`ProbabilityTheory.HasCondDistrib.condExp_comap_ae_eq_integral`). Unlike
`ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib`, no standard Borel assumption is
needed on the space of `Y`: the kernel `κ` is given.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω β γ : Type*} {mΩ : MeasurableSpace Ω} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → β} {Y : Ω → γ}
  {κ : Kernel β γ} [IsMarkovKernel κ]

/-- If `Y` has conditional distribution `κ` given `X`, then for a bounded measurable function
`f`, `𝔼[f(X, Y) | σ(X)] = ∫ f(X, y) dκ(X)` almost surely. -/
lemma HasCondDistrib.condExp_comap_ae_eq_integral (h : HasCondDistrib Y X κ P)
    (hX : Measurable X) {f : β × γ → ℝ} (hf : StronglyMeasurable f) {C : ℝ}
    (hfC : ∀ z, |f z| ≤ C) :
    P[fun ω ↦ f (X ω, Y ω) | mβ.comap X] =ᵐ[P] fun ω ↦ ∫ y, f (X ω, y) ∂κ (X ω) := by
  have hg : StronglyMeasurable fun b ↦ ∫ y, f (b, y) ∂κ b := hf.integral_kernel_prod_right'
  have hgC : ∀ b, |∫ y, f (b, y) ∂κ b| ≤ C := fun b ↦ by
    have := norm_integral_le_of_norm_le_const (μ := κ b) (f := fun y ↦ f (b, y))
      (C := C) (.of_forall fun y ↦ by simpa using hfC (b, y))
    simpa using this
  have hint : Integrable (fun ω ↦ f (X ω, Y ω)) P :=
    Integrable.of_bound (hf.aestronglyMeasurable.comp_aemeasurable h.aemeasurable) C
      (.of_forall fun ω ↦ by simpa using hfC _)
  have hgm : StronglyMeasurable[mβ.comap X] fun ω ↦ ∫ y, f (X ω, y) ∂κ (X ω) :=
    hg.comp_measurable (comap_measurable X)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hint
    (fun s _ _ ↦ (Integrable.of_bound (hgm.mono hX.comap_le).aestronglyMeasurable C
      (.of_forall fun ω ↦ by simpa using hgC _)).integrableOn) (fun s hs _ ↦ ?_)
    hgm.aestronglyMeasurable).symm
  obtain ⟨B, hB, rfl⟩ := hs
  set F : β × γ → ℝ := fun z ↦ B.indicator 1 z.1 * f z with hF
  have hFm : StronglyMeasurable F :=
    ((stronglyMeasurable_const.indicator hB).comp_measurable measurable_fst).mul hf
  have hFint : Integrable F ((P.map X) ⊗ₘ κ) := by
    refine Integrable.of_bound hFm.aestronglyMeasurable C (.of_forall fun z ↦ ?_)
    simp only [hF, Real.norm_eq_abs, abs_mul]
    by_cases hz : z.1 ∈ B
    · simpa [hz] using hfC z
    · simpa [hz] using (abs_nonneg _).trans (hfC z)
  rw [← integral_indicator (hX hB), ← integral_indicator (hX hB)]
  calc ∫ ω, (X ⁻¹' B).indicator (fun ω ↦ ∫ y, f (X ω, y) ∂κ (X ω)) ω ∂P
      = ∫ ω, ∫ y, F (X ω, y) ∂κ (X ω) ∂P := by
        refine integral_congr_ae (.of_forall fun ω ↦ ?_)
        by_cases hω : X ω ∈ B <;> simp [hF, hω]
    _ = ∫ ω, F (X ω, Y ω) ∂P := (h.integral_prodMk hFm hFint).symm
    _ = ∫ ω, (X ⁻¹' B).indicator (fun ω ↦ f (X ω, Y ω)) ω ∂P := by
        refine integral_congr_ae (.of_forall fun ω ↦ ?_)
        by_cases hω : X ω ∈ B <;> simp [hF, hω]

end ProbabilityTheory
