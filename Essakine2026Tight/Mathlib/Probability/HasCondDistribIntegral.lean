/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.HasCondDistrib
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Integrals against a conditional distribution

For random variables `X`, `Y` such that `Y` has conditional law `κ` given `X` under `P`:

* `ProbabilityTheory.HasCondDistrib.lintegral_prodMk`:
  `∫⁻ ω, f (X ω, Y ω) ∂P = ∫⁻ ω, ∫⁻ y, f (X ω, y) ∂κ (X ω) ∂P` for measurable `f ≥ 0`;
* `ProbabilityTheory.HasCondDistrib.integral_prodMk`: the same for the Bochner integral of an
  integrable `f`;
* `ProbabilityTheory.hasCondDistrib_of_lintegral_eq`: conversely, the identity for all measurable
  `f ≥ 0` characterizes the conditional law;
* `ProbabilityTheory.HasCondDistrib.compProd_left_of_sectR`: if `Y` has conditional law `η (a, ·)`
  given `X` under every `κ a`, then under `μ ⊗ₘ κ` the variable `Y ∘ snd` has conditional law `η`
  given `(fst, X ∘ snd)` (a version of `HasCondDistrib.compProd_left` in which the conditional
  law may depend on the first coordinate).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω α β γ δ : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} {P : Measure Ω}
  {X : Ω → α} {Y : Ω → β} {κ : Kernel α β}

/-- The Lebesgue integral of a function of `(X, Y)` is the integral of its conditional expectation
given `X`. -/
lemma HasCondDistrib.lintegral_prodMk [SFinite P] [IsSFiniteKernel κ]
    (h : HasCondDistrib Y X κ P) {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f (X ω, Y ω) ∂P = ∫⁻ ω, ∫⁻ b, f (X ω, b) ∂κ (X ω) ∂P := by
  rw [HasLaw.lintegral_comp h hf.aemeasurable, Measure.lintegral_compProd hf,
    lintegral_map' (hf.lintegral_kernel_prod_right').aemeasurable h.aemeasurable_fst]

/-- The integral of a function of `(X, Y)` is the integral of its conditional expectation given
`X`. -/
lemma HasCondDistrib.integral_prodMk [SFinite P] [IsSFiniteKernel κ]
    (h : HasCondDistrib Y X κ P) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α × β → E} (hfm : StronglyMeasurable f) (hf : Integrable f (P.map X ⊗ₘ κ)) :
    ∫ ω, f (X ω, Y ω) ∂P = ∫ ω, ∫ b, f (X ω, b) ∂κ (X ω) ∂P := by
  have h1 := HasLaw.integral_comp h hf.aestronglyMeasurable
  simp only [Function.comp_def] at h1
  rw [h1, Measure.integral_compProd hf, integral_map h.aemeasurable_fst]
  exact hfm.integral_kernel_prod_right'.aestronglyMeasurable

/-- A kernel `κ` is the conditional law of `Y` given `X` if the integral of every nonnegative
measurable function of `(X, Y)` is the integral of its integral against `κ (X ω)`. -/
lemma hasCondDistrib_of_lintegral_eq [IsFiniteMeasure P] [IsSFiniteKernel κ]
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (h : ∀ f : α × β → ℝ≥0∞, Measurable f →
      ∫⁻ ω, f (X ω, Y ω) ∂P = ∫⁻ ω, ∫⁻ b, f (X ω, b) ∂κ (X ω) ∂P) :
    HasCondDistrib Y X κ P := by
  refine ⟨hX.prodMk hY, ?_⟩
  ext B hB
  rw [Measure.compProd_apply hB,
    lintegral_map' (Kernel.measurable_kernel_prodMk_left hB).aemeasurable hX,
    ← lintegral_indicator_one hB, lintegral_map' (measurable_one.indicator hB).aemeasurable
      (hX.prodMk hY), h _ (measurable_one.indicator hB)]
  refine lintegral_congr fun ω ↦ ?_
  rw [← lintegral_indicator_one (measurable_prodMk_left hB)]
  rfl

/-- If `Y` has conditional law `η.sectR a` given `X` under every `κ a`, then under `μ ⊗ₘ κ` the
variable `Y ∘ snd` has conditional law `η` given `(fst, X ∘ snd)`. -/
lemma HasCondDistrib.compProd_left_of_sectR {μ : Measure α} [SFinite μ] {κ : Kernel α β}
    [IsMarkovKernel κ] {X : β → γ} {Y : β → δ} {η : Kernel (α × γ) δ} [IsSFiniteKernel η]
    (hX : Measurable X) (hY : Measurable Y) (h : ∀ a, HasCondDistrib Y X (η.sectR a) (κ a)) :
    HasCondDistrib (fun p ↦ Y p.2) (fun p ↦ (p.1, X p.2)) η (μ ⊗ₘ κ) where
  aemeasurable := by fun_prop
  map_eq := by
    have hκ : κ.map (fun b ↦ (X b, Y b)) = κ.map X ⊗ₖ η := by
      ext a : 1
      rw [Kernel.map_apply _ (hX.prodMk hY), (h a).map_eq,
        Kernel.compProd_apply_eq_compProd_sectR, Kernel.map_apply _ hX]
    calc (μ ⊗ₘ κ).map (fun p ↦ ((p.1, X p.2), Y p.2))
        = ((μ ⊗ₘ κ).map (fun p ↦ (p.1, (X p.2, Y p.2)))).map
            MeasurableEquiv.prodAssoc.symm := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]; rfl
      _ = (μ ⊗ₘ κ.map (fun b ↦ (X b, Y b))).map MeasurableEquiv.prodAssoc.symm := by
          rw [Measure.compProd_map (hX.prodMk hY)]; rfl
      _ = (μ ⊗ₘ κ.map X) ⊗ₘ η := by
          rw [hκ, Measure.compProd_assoc]
      _ = ((μ ⊗ₘ κ).map (fun p ↦ (p.1, X p.2))) ⊗ₘ η := by
          rw [Measure.compProd_map hX]; rfl

end ProbabilityTheory
