/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exploration rates of Entropic-BPI

The exploration rates of Essakine and Vernade (2026), Appendix A: for `S` states, `A` actions,
horizon `H` and confidence `δ`,
* `alphaKL S A H δ n = log(3 S A H / δ) + S log(8 e (n + 1))` (`α(n, δ)`, the KL concentration
  rate),
* `alphaStar S A H δ n = log(3 S A H / δ) + log(8 e (n + 1))` (`α*(n, δ)`, the Bernstein rate),
* `alphaCnt S A H δ = log(3 S A H / δ)` (`α^cnt(δ)`, the counts rate),

and the rate term `rateMin α n = min {α n / n, 1}` of the analysis, equal to `1` for `n = 0`
(the paper's `α(0)/0 = ∞`).

Real numerals at least `2` are written as casts of natural numerals (`((8 : ℕ) : ℝ)`): a real
numeral `n ≥ 2` carries a `Nat.AtLeastTwo n` instance proof, which Lean abstracts into an
auxiliary theorem shared by all definitions of a module, and such sharing differs between the
project and the single-module `comparator` challenges (see `notes/lean-design.md`).
-/

@[expose] public section

namespace Essakine2026Tight

/-- The exploration rate `α(n, δ) = log(3 S A H / δ) + S log(8 e (n + 1))`. -/
noncomputable def alphaKL (S A H : ℕ) (δ : ℝ) (n : ℕ) : ℝ :=
  Real.log ((3 * S * A * H : ℕ) / δ) + S * Real.log ((8 : ℕ) * Real.exp 1 * (n + 1 : ℕ))

/-- The exploration rate `α*(n, δ) = log(3 S A H / δ) + log(8 e (n + 1))`. -/
noncomputable def alphaStar (S A H : ℕ) (δ : ℝ) (n : ℕ) : ℝ :=
  Real.log ((3 * S * A * H : ℕ) / δ) + Real.log ((8 : ℕ) * Real.exp 1 * (n + 1 : ℕ))

/-- The rate `α^cnt(δ) = log(3 S A H / δ)` of the counts event. -/
noncomputable def alphaCnt (S A H : ℕ) (δ : ℝ) : ℝ := Real.log ((3 * S * A * H : ℕ) / δ)

/-- The rate term `min {α(n) / n, 1}` of the analysis, `1` for `n = 0`. -/
noncomputable def rateMin (α : ℕ → ℝ) (n : ℕ) : ℝ := if n = 0 then 1 else min (α n / n) 1

end Essakine2026Tight
