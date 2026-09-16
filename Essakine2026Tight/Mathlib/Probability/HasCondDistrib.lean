/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.HasCondDistrib
public import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Conditional laws under composition-products

* `ProbabilityTheory.hasCondDistrib_snd_compProd`: under `μ ⊗ₘ κ`, the second coordinate has
  conditional law `κ` given the first.
* `ProbabilityTheory.HasCondDistrib.comp_hasLaw`: a conditional law under the law of `V` is a
  conditional law of the composed variables.
* `ProbabilityTheory.HasCondDistrib.compProd_left`: if `Y` has conditional law `η` given `X`
  under every `κ a`, then under `μ ⊗ₘ κ` the variable `Y ∘ snd` has conditional law `η` given
  `(fst, X ∘ snd)`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω α β γ δ : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

/-- Under `μ ⊗ₘ κ`, the second coordinate has conditional law `κ` given the first. -/
lemma hasCondDistrib_snd_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β)
    [IsMarkovKernel κ] :
    HasCondDistrib Prod.snd Prod.fst κ (μ ⊗ₘ κ) where
  aemeasurable := by fun_prop
  map_eq := by
    rw [show (fun p : α × β ↦ (p.1, p.2)) = id from rfl, Measure.map_id,
      show (μ ⊗ₘ κ).map Prod.fst = (μ ⊗ₘ κ).fst from rfl, Measure.fst_compProd]

/-- A conditional law under the law of `V` is a conditional law of the composed variables. -/
lemma HasCondDistrib.comp_hasLaw {P : Measure Ω} {μ : Measure α} {V : Ω → α} {X : α → β}
    {Y : α → γ} {κ : Kernel β γ} (hV : HasLaw V μ P) (hX : Measurable X) (hY : Measurable Y)
    (h : HasCondDistrib Y X κ μ) :
    HasCondDistrib (fun ω ↦ Y (V ω)) (fun ω ↦ X (V ω)) κ P where
  aemeasurable := (hX.prodMk hY).comp_aemeasurable hV.aemeasurable
  map_eq := by
    have h1 : P.map (fun ω ↦ (X (V ω), Y (V ω))) = (P.map V).map (fun a ↦ (X a, Y a)) :=
      (AEMeasurable.map_map_of_aemeasurable (hX.prodMk hY).aemeasurable hV.aemeasurable).symm
    have h2 : P.map (fun ω ↦ X (V ω)) = (P.map V).map X :=
      (AEMeasurable.map_map_of_aemeasurable hX.aemeasurable hV.aemeasurable).symm
    rw [h1, h2, hV.map_eq, h.map_eq]

/-- If `Y` has conditional law `η` given `X` under every `κ a`, then under `μ ⊗ₘ κ` the variable
`Y ∘ snd` has conditional law `η` given `(fst, X ∘ snd)`. -/
lemma HasCondDistrib.compProd_left {μ : Measure α} [SFinite μ] {κ : Kernel α β}
    [IsMarkovKernel κ] {X : β → γ} {Y : β → δ} {η : Kernel γ δ} [IsSFiniteKernel η]
    (hX : Measurable X) (hY : Measurable Y) (h : ∀ a, HasCondDistrib Y X η (κ a)) :
    HasCondDistrib (fun p ↦ Y p.2) (fun p ↦ (p.1, X p.2)) (Kernel.prodMkLeft α η) (μ ⊗ₘ κ) where
  aemeasurable := by fun_prop
  map_eq := by
    have hκ : κ.map (fun b ↦ (X b, Y b)) = κ.map X ⊗ₖ Kernel.prodMkLeft α η := by
      ext a : 1
      rw [Kernel.map_apply _ (hX.prodMk hY), (h a).map_eq,
        Kernel.compProd_apply_eq_compProd_sectR, Kernel.map_apply _ hX, Kernel.sectR_prodMkLeft]
    calc (μ ⊗ₘ κ).map (fun p ↦ ((p.1, X p.2), Y p.2))
        = ((μ ⊗ₘ κ).map (fun p ↦ (p.1, (X p.2, Y p.2)))).map
            MeasurableEquiv.prodAssoc.symm := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]; rfl
      _ = (μ ⊗ₘ κ.map (fun b ↦ (X b, Y b))).map MeasurableEquiv.prodAssoc.symm := by
          rw [Measure.compProd_map (hX.prodMk hY)]; rfl
      _ = (μ ⊗ₘ κ.map X) ⊗ₘ Kernel.prodMkLeft α η := by
          rw [hκ, Measure.compProd_assoc]
      _ = ((μ ⊗ₘ κ).map (fun p ↦ (p.1, X p.2))) ⊗ₘ Kernel.prodMkLeft α η := by
          rw [Measure.compProd_map hX]; rfl

end ProbabilityTheory
