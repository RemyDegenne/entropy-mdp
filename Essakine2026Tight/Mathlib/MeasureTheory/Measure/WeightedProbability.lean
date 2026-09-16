/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.Mathlib.MeasureTheory.Measure.Weighted

/-!
# Weighted measures of probability vectors

Point masses of `weightedMeasure p` (`MeasureTheory.weightedMeasure_singleton`), finiteness, the
probability measure of a probability vector (`MeasureTheory.isProbabilityMeasure_weightedMeasure`)
and absolute continuity from the inclusion of supports
(`MeasureTheory.weightedMeasure_absolutelyContinuous`).
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] {p q : ι → ℝ}

/-- The mass of a singleton under `weightedMeasure p`. -/
lemma weightedMeasure_singleton (p : ι → ℝ) (i : ι) :
    weightedMeasure p {i} = ENNReal.ofReal (p i) := by
  classical
  rw [weightedMeasure_apply p (measurableSet_singleton i), Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

/-- The real mass of a singleton under `weightedMeasure p` for nonnegative weights. -/
lemma measureReal_weightedMeasure_singleton (hp : ∀ i, 0 ≤ p i) (i : ι) :
    (weightedMeasure p).real {i} = p i := by
  rw [measureReal_def, weightedMeasure_singleton, ENNReal.toReal_ofReal (hp i)]

/-- A weighted measure is finite. -/
instance isFiniteMeasure_weightedMeasure (p : ι → ℝ) : IsFiniteMeasure (weightedMeasure p) := by
  constructor
  rw [weightedMeasure_apply p MeasurableSet.univ]
  exact ENNReal.sum_lt_top.2 fun i _ ↦ by simp

omit [MeasurableSingletonClass ι] in
/-- The weighted measure of a probability vector is a probability measure. -/
lemma isProbabilityMeasure_weightedMeasure (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    IsProbabilityMeasure (weightedMeasure p) := by
  constructor
  rw [weightedMeasure_apply p MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hp0 i, hp1, ENNReal.ofReal_one]

/-- `weightedMeasure q ≪ weightedMeasure p` when the support of `q` is contained in that of
`p`. -/
lemma weightedMeasure_absolutelyContinuous (hq : ∀ i, 0 < q i → 0 < p i) :
    weightedMeasure q ≪ weightedMeasure p := by
  intro s hs
  rw [weightedMeasure_apply q (s.toFinite.measurableSet)]
  rw [weightedMeasure_apply p (s.toFinite.measurableSet)] at hs
  rw [Finset.sum_eq_zero_iff] at hs ⊢
  intro i _
  have hi := hs i (Finset.mem_univ i)
  by_cases his : i ∈ s
  · simp only [Set.indicator_of_mem his, Pi.one_apply, mul_one, ENNReal.ofReal_eq_zero] at hi ⊢
    by_contra h
    exact absurd hi (not_le.2 (hq i (not_le.1 h)))
  · simp [Set.indicator_of_notMem his]

end MeasureTheory
