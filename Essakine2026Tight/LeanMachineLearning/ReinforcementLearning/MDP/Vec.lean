/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Vectors on a finite state space

For a tabular MDP with finite state space `S`, functions `S → ℝ` are the value functions and
the probability vectors. This file defines the expectation `vecExp p f = ∑ s, p s * f s` and the
variance `vecVar p f` of `f` under the probability vector `p` (written `(p f)` and `Var_p(f)` in
the papers), and the transition probabilities `transVec P x : S → ℝ` of a kernel
`P : Kernel X S` at `x` as a vector.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace Learning.MDP

variable {S : Type*} [Fintype S]

/-- The expectation `∑ s, p s * f s` of `f : S → ℝ` under the probability vector `p` (`(p f)` in
the papers). -/
def vecExp (p f : S → ℝ) : ℝ := ∑ s, p s * f s

/-- The variance `Var_p(f) = ∑ p_s f_s² - (∑ p_s f_s)²` of `f` under the probability vector
`p`. -/
def vecVar (p f : S → ℝ) : ℝ := ∑ s, p s * f s ^ 2 - (∑ s, p s * f s) ^ 2

omit [Fintype S] in
/-- The transition probabilities `P(· | x)` of the kernel `P` at `x` as a vector. -/
noncomputable def transVec {X : Type*} [MeasurableSpace X] [MeasurableSpace S] (P : Kernel X S)
    (x : X) : S → ℝ :=
  fun s ↦ (P x).real {s}

lemma vecExp_add (p f g : S → ℝ) : vecExp p (f + g) = vecExp p f + vecExp p g := by
  simp [vecExp, mul_add, sum_add_distrib]

lemma vecExp_sub (p f g : S → ℝ) : vecExp p (f - g) = vecExp p f - vecExp p g := by
  simp [vecExp, mul_sub, sum_sub_distrib]

lemma vecExp_const (p : S → ℝ) (c : ℝ) : vecExp p (fun _ ↦ c) = (∑ s, p s) * c := by
  simp [vecExp, sum_mul]

lemma vecExp_mono {p f g : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hfg : ∀ s, f s ≤ g s) :
    vecExp p f ≤ vecExp p g :=
  sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left (hfg s) (hp s)

lemma vecExp_nonneg {p f : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hf : ∀ s, 0 ≤ f s) : 0 ≤ vecExp p f :=
  sum_nonneg fun s _ ↦ mul_nonneg (hp s) (hf s)

end Learning.MDP
