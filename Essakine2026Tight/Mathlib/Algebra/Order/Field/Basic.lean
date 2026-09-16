/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Two elementary inequalities in ordered fields

* `two_sub_le_inv`: `2 - x ≤ x⁻¹` for `x > 0`.
* `sub_mul_sub_div_sq_le`: the normalized Bhatia–Davis bound `(M - μ) (μ - m) / μ²` is at most
  `(M - m)² / (4 M m)` for `m, M, μ > 0` (with equality iff `μ = 2 M m / (M + m)`).
-/

@[expose] public section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `2 - x ≤ x⁻¹` for `x > 0`. -/
lemma two_sub_le_inv {x : K} (hx : 0 < x) : 2 - x ≤ x⁻¹ := by
  have h : x⁻¹ - (2 - x) = (1 - x) ^ 2 / x := by field_simp; ring
  have : 0 ≤ (1 - x) ^ 2 / x := by positivity
  linarith

/-- The normalized Bhatia–Davis bound `(M - μ) (μ - m) / μ²` is at most `(M - m)² / (4 M m)` for
`m, M, μ > 0`: the difference `(M - m)² μ² - 4 M m (M - μ) (μ - m)` is `((M + m) μ - 2 M m)²`. -/
lemma sub_mul_sub_div_sq_le {m M μ : K} (hm : 0 < m) (hM : 0 < M) (hμ : 0 < μ) :
    (M - μ) * (μ - m) / μ ^ 2 ≤ (M - m) ^ 2 / (4 * M * m) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ((M + m) * μ - 2 * M * m)]
