/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A power bound for `(1 + a / H) ^ h`

`Real.one_add_div_pow_le_exp`: `(1 + a / H) ^ h ≤ exp a` for `a ≥ 0` and `h ≤ H`.
-/

@[expose] public section

namespace Real

/-- `(1 + a / H) ^ h ≤ exp a` for `a ≥ 0` and natural numbers `h ≤ H` with `H > 0`. -/
lemma one_add_div_pow_le_exp {a : ℝ} (ha : 0 ≤ a) {H h : ℕ} (hH : 0 < H) (hh : h ≤ H) :
    (1 + a / H) ^ h ≤ exp a := by
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  calc (1 + a / H) ^ h ≤ (exp (a / H)) ^ h := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [add_one_le_exp (a / H)]
    _ = exp (h * (a / H)) := (exp_nat_mul _ _).symm
    _ ≤ exp a := by
        rw [exp_le_exp]
        calc (h : ℝ) * (a / H) ≤ H * (a / H) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hh) (by positivity)
          _ = a := by field_simp

end Real
