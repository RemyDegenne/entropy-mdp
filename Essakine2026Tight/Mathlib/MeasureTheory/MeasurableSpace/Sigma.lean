/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Sigma

/-!
# Measurable singletons in sigma types

A sigma type `Σ i, α i` whose fibers have measurable singletons has measurable singletons: the
preimage of `{⟨i, a⟩}` under `Sigma.mk j` is `{a}` if `j = i` and empty otherwise.
-/

@[expose] public section

open MeasureTheory

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  [∀ i, MeasurableSingletonClass (α i)]

lemma measurableSet_singleton_sigma (x : Σ i, α i) : MeasurableSet {x} := by
  obtain ⟨i, a⟩ := x
  rw [measurableSet_sigma_iff]
  intro j
  by_cases hij : j = i
  · subst hij
    convert measurableSet_singleton a using 1
    ext b
    simp
  · convert MeasurableSet.empty using 1
    ext b
    simp [Sigma.ext_iff, hij]

instance Sigma.instMeasurableSingletonClass : MeasurableSingletonClass (Σ i, α i) :=
  ⟨measurableSet_singleton_sigma⟩
