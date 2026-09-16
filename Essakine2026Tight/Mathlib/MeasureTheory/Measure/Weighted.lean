/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Weighted measures on a finite type

`weightedMeasure p = ∑ i, p i • δ_i` is the measure on a finite type `ι` with (real) weights `p`;
it is a probability measure when `p` is a probability vector. The map `p ↦ weightedMeasure p` is
measurable (`measurable_weightedMeasure`), which allows building kernels sampling from a
computed distribution.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι]

/-- The measure on `ι` with weights `p`: `∑ i, p i • δ_i`. -/
noncomputable def weightedMeasure (p : ι → ℝ) : Measure ι :=
  ∑ i, ENNReal.ofReal (p i) • Measure.dirac i

lemma weightedMeasure_apply (p : ι → ℝ) {s : Set ι} (hs : MeasurableSet s) :
    weightedMeasure p s = ∑ i, ENNReal.ofReal (p i) * s.indicator 1 i := by
  simp [weightedMeasure, Finset.sum_apply, Measure.dirac_apply' _ hs]

lemma measurable_weightedMeasure : Measurable (weightedMeasure (ι := ι)) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp_rw [weightedMeasure_apply _ hs]
  exact Finset.measurable_sum _ fun i _ ↦
    (ENNReal.measurable_ofReal.comp (measurable_pi_apply i)).mul measurable_const

end MeasureTheory
