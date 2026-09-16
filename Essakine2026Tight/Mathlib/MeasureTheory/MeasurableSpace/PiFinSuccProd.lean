/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Splitting off the last coordinate of a dependent product over `Fin (n + 1)`

`MeasurableEquiv.piFinSuccProd X n : (Π i : Fin (n + 1), X i) ≃ᵐ (Π i : Fin n, X i) × X n`:
a sequence of length `n + 1` is its initial segment of length `n` together with its last term
(`Fin.snoc`). It is the dependent version of LML's `MeasurableEquiv.finSuccProd`
(`piFinSuccProd_const`).
-/

@[expose] public section

open Fin

namespace MeasurableEquiv

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

/-- Appending a last term to a sequence of length `n` is measurable. -/
lemma measurable_snoc (n : ℕ) :
    Measurable fun p : (Π i : Fin n, X i) × X n ↦
      snoc (α := fun i : Fin (n + 1) ↦ X i) p.1 p.2 := by
  refine Measurable.of_eval fun i ↦ ?_
  refine lastCases ?_ (fun i ↦ ?_) i
  · simp only [snoc_last]
    exact measurable_snd
  · simp only [snoc_castSucc]
    exact (measurable_pi_apply i).comp measurable_fst

/-- Measurable equivalence between `Π i : Fin (n + 1), X i` and `(Π i : Fin n, X i) × X n`:
a sequence of length `n + 1` is its initial segment of length `n` together with its last term. -/
def piFinSuccProd (X : ℕ → Type*) [∀ n, MeasurableSpace (X n)] (n : ℕ) :
    (Π i : Fin (n + 1), X i) ≃ᵐ (Π i : Fin n, X i) × X n where
  toFun x := (fun i ↦ x (castSucc i), x (last n))
  invFun p := snoc (α := fun i : Fin (n + 1) ↦ X i) p.1 p.2
  left_inv x := by ext i; exact lastCases (by simp) (fun _ ↦ by simp) i
  right_inv p := by ext <;> simp
  measurable_toFun :=
    (Measurable.of_eval fun i ↦ measurable_pi_apply _).prodMk (measurable_pi_apply _)
  measurable_invFun := measurable_snoc n

/-- Unfolding lemma for `piFinSuccProd`. -/
@[simp]
lemma piFinSuccProd_apply (n : ℕ) (x : Π i : Fin (n + 1), X i) :
    piFinSuccProd X n x = (fun i ↦ x (castSucc i), x (last n)) := rfl

/-- Unfolding lemma for the inverse of `piFinSuccProd`. -/
@[simp]
lemma piFinSuccProd_symm_apply (n : ℕ) (p : (Π i : Fin n, X i) × X n) :
    (piFinSuccProd X n).symm p = snoc (α := fun i : Fin (n + 1) ↦ X i) p.1 p.2 := rfl

/-- For a constant family, `piFinSuccProd` is LML's `finSuccProd`. -/
lemma piFinSuccProd_const (R : Type*) [MeasurableSpace R] (n : ℕ) :
    piFinSuccProd (fun _ ↦ R) n = finSuccProd R n := by
  refine MeasurableEquiv.ext (funext fun x ↦ ?_)
  rw [finSuccProd_apply]
  rfl

end MeasurableEquiv
