/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Logarithms against powers

* `Real.log_le_rpow_div_exp_one_mul`: `log y ≤ y ^ γ / (e γ)` for `y, γ > 0`
  (`Real.log_le_rpow_div` sharpened by a factor `e`).
* `Real.log_le_of_le_mul_sq_log`: if `1 ≤ y ≤ M (log y)²` with `M > 0`, then
  `log y ≤ (8/5) log (4 M)`.
-/

@[expose] public section

namespace Real

/-- `log y ≤ y ^ γ / (e γ)` for `y > 0` and `γ > 0`: `Real.log_le_rpow_div` sharpened by a
factor `e`. -/
lemma log_le_rpow_div_exp_one_mul {y γ : ℝ} (hy : 0 < y) (hγ : 0 < γ) :
    log y ≤ y ^ γ / (exp 1 * γ) := by
  have hz : 0 < y ^ γ := rpow_pos_of_pos hy γ
  have h1 : log (y ^ γ / exp 1) ≤ y ^ γ / exp 1 - 1 := log_le_sub_one_of_pos (by positivity)
  rw [log_div hz.ne' (exp_pos 1).ne', log_exp, log_rpow hy] at h1
  rw [le_div_iff₀ (by positivity)]
  have h2 : γ * log y ≤ y ^ γ / exp 1 := by linarith
  rw [le_div_iff₀ (exp_pos 1)] at h2
  linarith

/-- If `1 ≤ y ≤ M (log y)²` with `M > 0`, then `log y ≤ (8/5) log (4 M)`. -/
lemma log_le_of_le_mul_sq_log {y M : ℝ} (hy : 1 ≤ y) (hM : 0 < M) (h : y ≤ M * log y ^ 2) :
    log y ≤ 8 / 5 * log (4 * M) := by
  have hy0 : 0 < y := by linarith
  have hlog : 0 ≤ log y := log_nonneg hy
  have he : 2.7 < exp 1 := lt_trans (by norm_num) exp_one_gt_d9
  have h1 : log y ≤ 16 / (3 * exp 1) * y ^ (3 / 16 : ℝ) := by
    calc log y ≤ y ^ (3 / 16 : ℝ) / (exp 1 * (3 / 16)) :=
          log_le_rpow_div_exp_one_mul hy0 (by norm_num)
      _ = 16 / (3 * exp 1) * y ^ (3 / 16 : ℝ) := by field_simp
  have h2 : log y ^ 2 ≤ 4 * y ^ (3 / 8 : ℝ) := by
    calc log y ^ 2 ≤ (16 / (3 * exp 1) * y ^ (3 / 16 : ℝ)) ^ 2 := pow_le_pow_left₀ hlog h1 2
      _ = (16 / (3 * exp 1)) ^ 2 * y ^ (3 / 8 : ℝ) := by
          rw [mul_pow, sq (y ^ (3 / 16 : ℝ)), ← rpow_add hy0]; norm_num
      _ ≤ 4 * y ^ (3 / 8 : ℝ) := by
          gcongr
          rw [div_pow, div_le_iff₀ (by positivity)]
          nlinarith
  have h3 : y ^ (5 / 8 : ℝ) ≤ 4 * M := by
    have hy38 : 0 < y ^ (3 / 8 : ℝ) := rpow_pos_of_pos hy0 _
    have h4 : y ≤ 4 * M * y ^ (3 / 8 : ℝ) := by
      calc y ≤ M * log y ^ 2 := h
        _ ≤ M * (4 * y ^ (3 / 8 : ℝ)) := by gcongr
        _ = 4 * M * y ^ (3 / 8 : ℝ) := by ring
    have hsplit : y ^ (5 / 8 : ℝ) * y ^ (3 / 8 : ℝ) = y := by
      rw [← rpow_add hy0]; norm_num
    refine le_of_mul_le_mul_right ?_ hy38
    rw [hsplit]
    exact h4
  have h5 : 5 / 8 * log y ≤ log (4 * M) := by
    rw [← log_rpow hy0]
    exact log_le_log (rpow_pos_of_pos hy0 _) h3
  linarith

end Real
