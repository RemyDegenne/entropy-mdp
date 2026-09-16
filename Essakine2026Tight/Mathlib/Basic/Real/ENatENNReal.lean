/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Basic.ENNReal.Real

/-!
# Bounding an extended natural number by a real number

`ENat.toENNReal_le_ofReal_of_forall_natCast_le`: if every natural number `T ≤ τ` is at most the
real number `U`, then `τ ≤ U` in `ℝ≥0∞` (in particular `τ ≠ ⊤`).
-/

@[expose] public section

open scoped ENNReal

namespace ENat

/-- If every natural number `T ≤ τ` is at most the real number `U`, then `τ ≤ U` in `ℝ≥0∞`; in
particular `τ` is finite. -/
lemma toENNReal_le_ofReal_of_forall_natCast_le {τ : ℕ∞} {U : ℝ}
    (h : ∀ T : ℕ, (T : ℕ∞) ≤ τ → (T : ℝ) ≤ U) : (τ : ℝ≥0∞) ≤ ENNReal.ofReal U := by
  induction τ using ENat.recTopCoe with
  | top =>
    exfalso
    have := h (⌊U⌋₊ + 1) le_top
    push_cast at this
    linarith [Nat.lt_floor_add_one U]
  | coe n =>
    rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (h n le_rfl)

end ENat
