/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Constants of the main theorems of Essakine, Vernade (2026)

* `treeDepth S A`: the depth `d = ⌈log_A((S - 3)(A - 1) + 1)⌉` of the tree of the hard instances
  (Assumption 1 is `H ≥ 3 d`), `effHorizon S A H = H - ⌊H/3⌋ - d` the effective horizon of the
  hard instances, and `ConditionA β H' ε` the small-`ε` condition of the lower bound (Appendix C,
  stated with the effective horizon and a margin).
* `lowerBound S A H β ε δ G`: the lower bound of Theorem 3 on the expected number of episodes,
  for the maximal return `G`, with the constant `1/5000` (the paper's `1/1650`; see the
  blueprint, chapter "Lower bound", for the constant of the general, non-full, tree).
* `upperBound S A H β ε δ G`: the upper bound of Theorem 4 on the number of episodes of
  Entropic-BPI, for the maximal return `G`: the two-term bound obtained by solving the recursive
  inequality of the analysis with the paper's Lemma 29 (blueprint, chapter "Sample complexity",
  `def:upper_bound_const`), with generous absolute constants.

Real numerals at least `2` are written as casts of natural numerals (`((5000 : ℕ) : ℝ)`), so that
the definitions contain no nested proofs (see `notes/lean-design.md`).
-/

@[expose] public section

namespace Essakine2026Tight

/-- The depth `d = ⌈log_A((S - 3)(A - 1) + 1)⌉` of the tree of the hard instances
(Assumption 1 is `H ≥ 3 d`). -/
def treeDepth (S A : ℕ) : ℕ := Nat.clog A ((S - 3) * (A - 1) + 1)

/-- The effective horizon `H' = H - ⌊H/3⌋ - d` of the hard instances: the number of steps at
which a reward can be collected. -/
def effHorizon (S A H : ℕ) : ℕ := H - H / 3 - treeDepth S A

/-- **Condition A** (small-`ε` regime of the lower bound), for the effective horizon `H'`: with
`c = e^{|β| H'} - 1` and `q = e^{|β| ε}`, `q - 1 ≤ c (2 c + 1) / (4 (3 c + 2))` if `β > 0` and
`q - 1 ≤ c / (10 c + 8)` if `β < 0`. This is the paper's condition stated with the effective
horizon `H'` of the construction instead of `H` and with the margin `p₊ ≤ (1 + p₋) / 2`, which
the paper's bound on the binary divergence needs (blueprint, chapter "Lower bound",
`def:condition_a`). -/
noncomputable def ConditionA (β : ℝ) (H' : ℕ) (ε : ℝ) : Prop :=
  let c := Real.exp (|β| * H') - 1
  if 0 < β then
    Real.exp (|β| * ε) - 1 ≤ c * ((2 : ℕ) * c + 1) / ((4 : ℕ) * ((3 : ℕ) * c + (2 : ℕ)))
  else Real.exp (|β| * ε) - 1 ≤ c / ((10 : ℕ) * c + (8 : ℕ))

/-- The variance factor `V_G = (e^{|β| G} - 1)² / e^{|β| G}` of the maximal return `G`. -/
noncomputable def varianceFactor (β G : ℝ) : ℝ :=
  (Real.exp (|β| * G) - 1) ^ 2 / Real.exp (|β| * G)

/-- The lower bound of Theorem 3 on the expected number of episodes, for the maximal return
`G`: `(1/5000) V_G e^{2 min(β, 0) ε} S A H log(1/δ) / (e^{|β| ε} - 1)²`. -/
noncomputable def lowerBound (S A H : ℕ) (β ε δ G : ℝ) : ℝ :=
  1 / (5000 : ℕ) * varianceFactor β G
    * (Real.exp ((2 : ℕ) * min β 0 * ε) * (S * A * H : ℕ) / (Real.exp (|β| * ε) - 1) ^ 2)
    * Real.log (1 / δ)

/-- The progress per non-stopping episode `κ(β, ε) = (e^{|β| ε} - 1) e^{-2 |β| ε} / 2`. -/
noncomputable def progress (β ε : ℝ) : ℝ :=
  (Real.exp (|β| * ε) - 1) * Real.exp (-(2 : ℕ) * |β| * ε) / (2 : ℕ)

/-- The coefficient `C = 10⁹ √(V_G S A H) / κ` of the square-root term of the recursive
inequality of the analysis. -/
noncomputable def coeffSqrt (S A H : ℕ) (β ε G : ℝ) : ℝ :=
  (10 : ℕ) ^ 9 * √(varianceFactor β G * (S * A * H : ℕ)) / progress β ε

/-- The coefficient `D = 10¹⁰ e^{|β| (H + 1)} H² S A / κ` of the linear term of the recursive
inequality of the analysis. -/
noncomputable def coeffLin (S A H : ℕ) (β ε : ℝ) : ℝ :=
  (10 : ℕ) ^ 10 * Real.exp (|β| * (H + 1 : ℕ)) * (H ^ 2 * S * A : ℕ) / progress β ε

/-- The logarithmic factor `C₁ = (8/5) log(11 (8e)² (A₀ + S)(C + D)²)` of the solution of the
recursive inequality (the paper's Lemma 29, whose `(C + D)` must be squared: blueprint, chapter
"Elementary inequalities", `lem:self_bounding`), with `A₀ = log(3 S A H / δ)`. -/
noncomputable def logFactor (S A H : ℕ) (β ε δ G : ℝ) : ℝ :=
  (8 : ℕ) / (5 : ℕ) * Real.log ((11 : ℕ) * ((8 : ℕ) * Real.exp 1) ^ 2
    * (Real.log ((3 * S * A * H : ℕ) / δ) + S) * (coeffSqrt S A H β ε G + coeffLin S A H β ε) ^ 2)

/-- The upper bound of Theorem 4 on the number of episodes of Entropic-BPI, for the maximal
return `G`: `C² (A₀ + 1) C₁² + (D + 2 √D C) (A₀ + S) C₁² + 1` with `A₀ = log(3 S A H / δ)`. -/
noncomputable def upperBound (S A H : ℕ) (β ε δ G : ℝ) : ℝ :=
  let A₀ := Real.log ((3 * S * A * H : ℕ) / δ)
  let C := coeffSqrt S A H β ε G
  let D := coeffLin S A H β ε
  let C₁ := logFactor S A H β ε δ G
  C ^ 2 * (A₀ + 1) * C₁ ^ 2 + (D + (2 : ℕ) * √D * C) * (A₀ + S) * C₁ ^ 2 + 1

end Essakine2026Tight
