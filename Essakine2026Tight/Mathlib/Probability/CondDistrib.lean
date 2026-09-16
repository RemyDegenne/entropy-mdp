/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.HasCondDistrib

/-!
# Restrictions and transport of conditional distributions

Facts about `HasCondDistrib` used by the chain rule at a stopping time
(`Essakine2026Tight.Mathlib.InformationTheory.KLStoppedPrefix`) and by the construction of runs of
identification algorithms:

* `Measure.restrict_compProd_prod_univ`: `(μ ⊗ₘ κ).restrict (s ×ˢ univ) = μ.restrict s ⊗ₘ κ`;
* `HasCondDistrib.restrict_preimage`: a conditional law given `X` is preserved by restricting the
  measure to an event determined by `X`;
* `HasCondDistrib.comp_of_hasLaw`, `HasCondDistrib.of_comp_hasLaw`: a conditional law of `Z`
  given `X` under the law of `g` is a conditional law of `Z ∘ g` given `X ∘ g`, and conversely
  (no measurability of `X` and `Z` is needed);
* `hasCondDistrib_snd_compProd_comap`: under `μ ⊗ₘ η.comap f`, the second coordinate has
  conditional law `η` given `f` of the first coordinate.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

section compProd

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- The restriction of `μ ⊗ₘ κ` to `s ×ˢ univ` is `μ.restrict s ⊗ₘ κ`. -/
lemma _root_.MeasureTheory.Measure.restrict_compProd_prod_univ (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsSFiniteKernel κ] {s : Set α} (hs : MeasurableSet s) :
    (μ ⊗ₘ κ).restrict (s ×ˢ Set.univ) = μ.restrict s ⊗ₘ κ := by
  ext t ht
  rw [Measure.restrict_apply ht, Measure.compProd_apply (ht.inter (hs.prod MeasurableSet.univ)),
    Measure.compProd_apply ht, ← lintegral_indicator hs]
  refine lintegral_congr fun a ↦ ?_
  by_cases ha : a ∈ s
  · have h : Prod.mk a ⁻¹' (t ∩ s ×ˢ Set.univ) = Prod.mk a ⁻¹' t := by ext b; simp [ha]
    simp [Set.indicator, ha, h]
  · have h : Prod.mk a ⁻¹' (t ∩ s ×ˢ Set.univ) = ∅ := by ext b; simp [ha]
    simp [Set.indicator, ha, h]

end compProd

section restrict

variable {Ω α β : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} {P : Measure Ω} [SFinite P] {X : Ω → α} {Y : Ω → β} {κ : Kernel α β}
  [IsSFiniteKernel κ]

/-- A conditional law given `X` is a conditional law given `X` under the restriction of `P` to an
event determined by `X`. -/
lemma HasCondDistrib.restrict_preimage (hX : Measurable X) (hY : Measurable Y)
    (h : HasCondDistrib Y X κ P) {s : Set α} (hs : MeasurableSet s) :
    HasCondDistrib Y X κ (P.restrict (X ⁻¹' s)) := by
  refine ⟨(hX.prodMk hY).aemeasurable, ?_⟩
  have h1 : (fun ω ↦ (X ω, Y ω)) ⁻¹' (s ×ˢ Set.univ) = X ⁻¹' s := by ext ω; simp
  calc (P.restrict (X ⁻¹' s)).map (fun ω ↦ (X ω, Y ω))
      = (P.map (fun ω ↦ (X ω, Y ω))).restrict (s ×ˢ Set.univ) := by
        rw [Measure.restrict_map (hX.prodMk hY) (hs.prod MeasurableSet.univ), h1]
    _ = (P.map X ⊗ₘ κ).restrict (s ×ˢ Set.univ) := by rw [h.map_eq]
    _ = (P.map X).restrict s ⊗ₘ κ := Measure.restrict_compProd_prod_univ _ _ hs
    _ = (P.restrict (X ⁻¹' s)).map X ⊗ₘ κ := by rw [Measure.restrict_map hX hs]

end restrict

section transport

variable {Ω Ω' 𝓧 𝓩 : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓩 : MeasurableSpace 𝓩} {P : Measure Ω} {P' : Measure Ω'}
  {g : Ω → Ω'}

/-- A conditional distribution is transported along a map `g` carrying `P` to `P'`. -/
lemma HasCondDistrib.comp_of_hasLaw {X : Ω' → 𝓧} {Z : Ω' → 𝓩}
    {κ : Kernel 𝓧 𝓩} (h : HasCondDistrib Z X κ P') (hg : HasLaw g P' P) :
    HasCondDistrib (Z ∘ g) (X ∘ g) κ P := by
  have h' : HasLaw ((fun ω ↦ (X ω, Z ω)) ∘ g) (P'.map X ⊗ₘ κ) P := HasLaw.comp h hg
  have hX : P'.map X = P.map (X ∘ g) := by
    rw [← hg.map_eq, AEMeasurable.map_map_of_aemeasurable (hg.map_eq ▸ h.aemeasurable_fst)
      hg.aemeasurable]
  rw [hX] at h'
  exact h'

/-- A conditional distribution of `Z ∘ g` given `X ∘ g` under `P` is a conditional distribution
of `Z` given `X` under the law `P'` of `g`. -/
lemma HasCondDistrib.of_comp_hasLaw {X : Ω' → 𝓧} {Z : Ω' → 𝓩} {κ : Kernel 𝓧 𝓩}
    (hX : Measurable X) (hZ : Measurable Z) (hg : HasLaw g P' P)
    (h : HasCondDistrib (Z ∘ g) (X ∘ g) κ P) :
    HasCondDistrib Z X κ P' := by
  refine ⟨(hX.prodMk hZ).aemeasurable, ?_⟩
  have h1 : P'.map (fun ω ↦ (X ω, Z ω)) = P.map ((fun ω ↦ (X ω, Z ω)) ∘ g) := by
    rw [← hg.map_eq,
      AEMeasurable.map_map_of_aemeasurable (hX.prodMk hZ).aemeasurable hg.aemeasurable]
  have h2 : P'.map X = P.map (X ∘ g) := by
    rw [← hg.map_eq, AEMeasurable.map_map_of_aemeasurable hX.aemeasurable hg.aemeasurable]
  rw [h1, h2]
  exact h.map_eq

end transport

section compProdComap

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

/-- Under `μ ⊗ₘ η.comap f`, the second coordinate has conditional law `η` given `f` of the
first coordinate, when `η` is a probability measure at every point of the range of `f`. -/
lemma hasCondDistrib_snd_compProd_comap (μ : Measure α) [SFinite μ]
    (η : Kernel β γ) [IsSFiniteKernel η] {f : α → β} (hf : Measurable f)
    (hη : ∀ a, IsProbabilityMeasure (η (f a))) :
    HasCondDistrib Prod.snd (fun p : α × γ ↦ f p.1) η (μ ⊗ₘ η.comap f hf) := by
  have hκ : IsMarkovKernel (η.comap f hf) := ⟨fun a ↦ by rw [Kernel.comap_apply]; exact hη a⟩
  have hfst : (μ ⊗ₘ η.comap f hf).map (fun p : α × γ ↦ f p.1) = μ.map f := by
    calc (μ ⊗ₘ η.comap f hf).map (fun p : α × γ ↦ f p.1)
        = ((μ ⊗ₘ η.comap f hf).map Prod.fst).map f := (Measure.map_map hf measurable_fst).symm
      _ = μ.map f := by
        rw [show (μ ⊗ₘ η.comap f hf).map Prod.fst = (μ ⊗ₘ η.comap f hf).fst from rfl,
          Measure.fst_compProd]
  refine ⟨by fun_prop, ?_⟩
  rw [hfst]
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.compProd_apply (hs.preimage (by fun_prop)),
    Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  refine lintegral_congr fun a ↦ ?_
  rw [Kernel.comap_apply]
  rfl

end compProdComap

end ProbabilityTheory
