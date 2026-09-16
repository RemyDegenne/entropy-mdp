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

lemma vecExp_const_mul (p f : S → ℝ) (c : ℝ) : vecExp p (fun s ↦ c * f s) = c * vecExp p f := by
  simp only [vecExp, mul_sum]
  exact sum_congr rfl fun s _ ↦ by ring

/-- The expectation under a probability vector of a function with values in `[a, b]` lies in
`[a, b]`. -/
lemma vecExp_mem_Icc {p f : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) {a b : ℝ}
    (hf : ∀ s, f s ∈ Set.Icc a b) : vecExp p f ∈ Set.Icc a b := by
  constructor
  · calc a = vecExp p (fun _ ↦ a) := by rw [vecExp_const, hp1, one_mul]
      _ ≤ vecExp p f := vecExp_mono hp fun s ↦ (hf s).1
  · calc vecExp p f ≤ vecExp p (fun _ ↦ b) := vecExp_mono hp fun s ↦ (hf s).2
      _ = b := by rw [vecExp_const, hp1, one_mul]

/-- `|p f| ≤ max_s |f s|` for a probability vector `p`. -/
lemma abs_vecExp_le {p f : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) {c : ℝ}
    (hf : ∀ s, |f s| ≤ c) : |vecExp p f| ≤ c :=
  abs_le.2 (vecExp_mem_Icc hp hp1 fun s ↦ abs_le.1 (hf s))

/-- The variance under a probability vector is the mean square deviation from the mean. -/
lemma vecVar_eq_sum_sq {p f : S → ℝ} (hp1 : ∑ s, p s = 1) :
    vecVar p f = ∑ s, p s * (f s - vecExp p f) ^ 2 := by
  simp only [vecVar, vecExp]
  set m := ∑ s, p s * f s
  rw [show ∑ s, p s * (f s - m) ^ 2 = ∑ s, (p s * f s ^ 2 - 2 * m * (p s * f s) + m ^ 2 * p s)
    from sum_congr rfl fun s _ ↦ by ring]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hp1]
  ring

/-- The variance under a probability vector is nonnegative. -/
lemma vecVar_nonneg {p f : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1) : 0 ≤ vecVar p f := by
  rw [vecVar_eq_sum_sq hp1]
  exact sum_nonneg fun s _ ↦ mul_nonneg (hp s) (sq_nonneg _)

omit [Fintype S] in
lemma transVec_nonneg {X : Type*} [MeasurableSpace X] [MeasurableSpace S] (P : Kernel X S) (x : X)
    (s : S) : 0 ≤ transVec P x s :=
  measureReal_nonneg

/-- The transition probabilities of a Markov kernel form a probability vector. -/
lemma sum_transVec {X : Type*} [MeasurableSpace X] [MeasurableSpace S] [MeasurableSingletonClass S]
    (P : Kernel X S) [IsMarkovKernel P] (x : X) : ∑ s, transVec P x s = 1 := by
  simp only [transVec]
  rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]

end Learning.MDP
