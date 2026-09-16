/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Elementary inequalities on real square roots

* `Real.sqrt_add_le`: subadditivity `√(a + b) ≤ √a + √b`.
* `Real.two_mul_sqrt_mul_le`, `Real.sqrt_mul_le_half_add_half`, `Real.sqrt_mul_le_add`: the
  weighted AM–GM inequality `√(a b) ≤ η a / 2 + b / (2 η) ≤ η a + b / η` for `η > 0`.
* `Real.le_add_sqrt_of_sq_le`: the root of a quadratic inequality, `x² ≤ b x + c` with
  `b, c ≥ 0` forces `x ≤ b + √c`.
-/

@[expose] public section

namespace Real

variable {a b c x η : ℝ}

/-- Subadditivity of the square root: `√(a + b) ≤ √a + √b` for `a, b ≥ 0`. -/
lemma sqrt_add_le (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a + b) ≤ √a + √b := by
  rw [sqrt_le_left (by positivity)]
  nlinarith [sq_sqrt ha, sq_sqrt hb, mul_nonneg (sqrt_nonneg a) (sqrt_nonneg b)]

/-- Weighted AM–GM inequality: `2 √(a b) ≤ η a + b / η` for `a, b ≥ 0` and `η > 0`. -/
lemma two_mul_sqrt_mul_le (ha : 0 ≤ a) (hb : 0 ≤ b) (hη : 0 < η) :
    2 * √(a * b) ≤ η * a + b / η := by
  have hx : √(η * a) ^ 2 = η * a := sq_sqrt (by positivity)
  have hy : √(b / η) ^ 2 = b / η := sq_sqrt (by positivity)
  have hxy : √(η * a) * √(b / η) = √(a * b) := by
    rw [← sqrt_mul (by positivity)]
    congr 1
    field_simp
  calc 2 * √(a * b) = 2 * √(η * a) * √(b / η) := by rw [← hxy, mul_assoc]
    _ ≤ √(η * a) ^ 2 + √(b / η) ^ 2 := two_mul_le_add_sq _ _
    _ = η * a + b / η := by rw [hx, hy]

/-- Weighted AM–GM inequality: `√(a b) ≤ η a / 2 + b / (2 η)` for `a, b ≥ 0` and `η > 0`. -/
lemma sqrt_mul_le_half_add_half (ha : 0 ≤ a) (hb : 0 ≤ b) (hη : 0 < η) :
    √(a * b) ≤ η * a / 2 + b / (2 * η) := by
  have h := two_mul_sqrt_mul_le ha hb hη
  have h' : b / (2 * η) = b / η / 2 := by rw [div_div, mul_comm]
  rw [h']
  linarith

/-- Weighted AM–GM inequality, weak form: `√(a b) ≤ η a + b / η` for `a, b ≥ 0` and `η > 0`. -/
lemma sqrt_mul_le_add (ha : 0 ≤ a) (hb : 0 ≤ b) (hη : 0 < η) : √(a * b) ≤ η * a + b / η := by
  have h := sqrt_mul_le_half_add_half ha hb hη
  have h1 : 0 ≤ η * a := by positivity
  have h2 : 0 ≤ b / η := by positivity
  have h' : b / (2 * η) = b / η / 2 := by rw [div_div, mul_comm]
  rw [h'] at h
  linarith

/-- The root of a quadratic inequality: `x² ≤ b x + c` with `b, c ≥ 0` forces `x ≤ b + √c`. -/
lemma le_add_sqrt_of_sq_le (hb : 0 ≤ b) (hc : 0 ≤ c) (h : x ^ 2 ≤ b * x + c) :
    x ≤ b + √c := by
  by_contra! hlt
  have hsc : 0 ≤ √c := sqrt_nonneg c
  have h1 : √c ≤ x := by linarith
  have h2 : √c * √c = c := mul_self_sqrt hc
  have hxpos : 0 < x := by linarith
  have h3 : (b + √c) * x < x * x := mul_lt_mul_of_pos_right hlt hxpos
  have h4 : √c * √c ≤ x * √c := mul_le_mul_of_nonneg_right h1 hsc
  nlinarith

end Real
