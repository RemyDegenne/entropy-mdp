/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecificLimits.Normed
public import Essakine2026Tight.Mathlib.Analysis.Real.Sqrt

/-!
# The Cramér transform of the Poisson distribution and the Bernstein exponential bound

Two elementary functions of the Bernstein/Bennett inequalities:

* `Real.expSubOneSub u = exp u - 1 - u`, so that the `φ_b` of the literature is
  `fun lam ↦ Real.expSubOneSub (lam * b)`;
* `Real.poissonCramer x = (1 + x) * log (1 + x) - x`, the Cramér transform of the Poisson
  distribution of parameter `1`.

Main results:

* `Real.expSubOneSub_nonneg`, `Real.poissonCramer_nonneg`;
* `Real.sq_div_le_poissonCramer`: `x² / (2 (1 + x / 3)) ≤ poissonCramer x` for `x ≥ 0`, through
  the Padé-type bound `Real.div_le_log_one_add`;
* `Real.mul_poissonCramer_eq`: the value of `lam ↦ lam b s - c φ_b(lam)` at
  `lam = log (1 + s / c) / b` is `c * poissonCramer (s / c)`;
* `Real.le_sqrt_add_of_mul_poissonCramer_le`: `c h(s/c) ≤ l` forces `s ≤ √(2 c l) + 2 l / 3`;
* `Real.exp_mul_le_of_abs_le`: the Taylor bound
  `exp (lam y) ≤ 1 + lam y + (y² / b²) φ_b(lam)` for `lam ≥ 0` and `|y| ≤ b`.
-/

@[expose] public section

open scoped Nat

namespace Real

variable {b c l lam s u x y : ℝ}

/-- `expSubOneSub u = e^u - 1 - u`; the function `φ_b` of the Bernstein inequality is
`fun lam ↦ expSubOneSub (lam * b)`. -/
noncomputable def expSubOneSub (u : ℝ) : ℝ := exp u - 1 - u

/-- The Cramér transform of the Poisson distribution of parameter `1`,
`poissonCramer x = (1 + x) log (1 + x) - x`. -/
noncomputable def poissonCramer (x : ℝ) : ℝ := (1 + x) * log (1 + x) - x

/-- `φ(0) = 0`. -/
@[simp] lemma expSubOneSub_zero : expSubOneSub 0 = 0 := by simp [expSubOneSub]

/-- `h(0) = 0`. -/
@[simp] lemma poissonCramer_zero : poissonCramer 0 = 0 := by simp [poissonCramer]

/-- `u ↦ e^u - 1 - u` is continuous. -/
@[fun_prop]
lemma continuous_expSubOneSub : Continuous expSubOneSub := by
  unfold expSubOneSub
  fun_prop

/-- `e^u - 1 - u ≥ 0`. -/
lemma expSubOneSub_nonneg (u : ℝ) : 0 ≤ expSubOneSub u := by
  have := add_one_le_exp u
  simp only [expSubOneSub]
  linarith

/-- The power series of `expSubOneSub`: `e^u - 1 - u = ∑_{k ≥ 2} u^k / k!`. -/
lemma expSubOneSub_eq_tsum (u : ℝ) :
    expSubOneSub u = ∑' n : ℕ, u ^ (n + 2) / ((n + 2)! : ℝ) := by
  have hs : Summable (fun n : ℕ ↦ u ^ n / (n ! : ℝ)) := Real.summable_pow_div_factorial u
  have h := hs.sum_add_tsum_nat_add 2
  have hu : exp u = ∑' n : ℕ, u ^ n / (n ! : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  simp only [expSubOneSub, hu, ← h, Finset.sum_range_succ]
  norm_num
  ring

/-- The scaling bound `e^{ct} - 1 - ct ≤ t² (e^c - 1 - c)` for `c ≥ 0` and `|t| ≤ 1`. -/
lemma expSubOneSub_mul_le (hc : 0 ≤ c) (ht : |x| ≤ 1) :
    expSubOneSub (c * x) ≤ x ^ 2 * expSubOneSub c := by
  rw [expSubOneSub_eq_tsum, expSubOneSub_eq_tsum]
  have hs1 : Summable (fun n : ℕ ↦ (c * x) ^ (n + 2) / (((n + 2))! : ℝ)) :=
    (summable_nat_add_iff 2).2 (Real.summable_pow_div_factorial (c * x))
  have hs2 : Summable (fun n : ℕ ↦ c ^ (n + 2) / (((n + 2))! : ℝ)) :=
    (summable_nat_add_iff 2).2 (Real.summable_pow_div_factorial c)
  rw [← hs2.tsum_mul_left]
  refine hs1.tsum_le_tsum (fun n ↦ ?_) (hs2.mul_left _)
  have hfac : (0 : ℝ) < ((n + 2)! : ℝ) := by positivity
  rw [div_le_iff₀ hfac]
  have hxn : x ^ n ≤ 1 :=
    (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg x) ht)
  have hcn : (0 : ℝ) ≤ c ^ (n + 2) * x ^ 2 := by positivity
  calc (c * x) ^ (n + 2) = c ^ (n + 2) * x ^ 2 * x ^ n := by ring
    _ ≤ c ^ (n + 2) * x ^ 2 * 1 := by gcongr
    _ = x ^ 2 * (c ^ (n + 2) / ((n + 2)! : ℝ)) * ((n + 2)! : ℝ) := by field_simp
    _ = _ := rfl

/-- The Taylor bound `e^{lam y} ≤ 1 + lam y + (y² / b²) φ_b(lam)` for `b > 0`, `lam ≥ 0` and
`|y| ≤ b`, where `φ_b(lam) = expSubOneSub (lam * b)`. -/
lemma exp_mul_le_of_abs_le (hb : 0 < b) (hlam : 0 ≤ lam) (hy : |y| ≤ b) :
    exp (lam * y) ≤ 1 + lam * y + y ^ 2 / b ^ 2 * expSubOneSub (lam * b) := by
  have ht : |y / b| ≤ 1 := by
    rw [abs_div, abs_of_pos hb, div_le_one hb]
    exact hy
  have h := expSubOneSub_mul_le (c := lam * b) (x := y / b) (by positivity) ht
  have hcx : lam * b * (y / b) = lam * y := by field_simp
  rw [hcx] at h
  have hsq : (y / b) ^ 2 = y ^ 2 / b ^ 2 := by rw [div_pow]
  rw [hsq] at h
  simp only [expSubOneSub] at h ⊢
  linarith

/-- A Padé-type lower bound for the logarithm:
`(6 x + 5 x²) / (6 + 8 x + 2 x²) ≤ log (1 + x)` for `x ≥ 0`. -/
lemma div_le_log_one_add (hx : 0 ≤ x) :
    (6 * x + 5 * x ^ 2) / (6 + 8 * x + 2 * x ^ 2) ≤ log (1 + x) := by
  set g : ℝ → ℝ := fun z ↦ log (1 + z) - (6 * z + 5 * z ^ 2) / (6 + 8 * z + 2 * z ^ 2) with hg
  set g' : ℝ → ℝ := fun z ↦ 1 / (1 + z)
      - ((6 + 10 * z) * (6 + 8 * z + 2 * z ^ 2) - (6 * z + 5 * z ^ 2) * (8 + 4 * z))
        / (6 + 8 * z + 2 * z ^ 2) ^ 2 with hg'
  have hd : ∀ z : ℝ, 0 ≤ z → HasDerivAt g (g' z) z := by
    intro z hz
    have hid : HasDerivAt (fun w : ℝ ↦ w) 1 z := hasDerivAt_id' z
    have hsq : HasDerivAt (fun w : ℝ ↦ w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
    have h1 : HasDerivAt (fun w : ℝ ↦ log (1 + w)) (1 / (1 + z)) z := by
      simpa using (hid.const_add (1 : ℝ)).log (by positivity)
    have h2 : HasDerivAt (fun w : ℝ ↦ 6 * w + 5 * w ^ 2) (6 + 10 * z) z := by
      have h := (hid.const_mul (6 : ℝ)).add (hsq.const_mul (5 : ℝ))
      convert h using 1
      ring
    have h3 : HasDerivAt (fun w : ℝ ↦ 6 + 8 * w + 2 * w ^ 2) (8 + 4 * z) z := by
      have h := ((hid.const_mul (8 : ℝ)).const_add (6 : ℝ)).add (hsq.const_mul (2 : ℝ))
      convert h using 1
      ring
    exact h1.sub (h2.div h3 (by positivity))
  have hmono : MonotoneOn g (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun z hz ↦ (hd z hz).continuousAt.continuousWithinAt)
      (fun z hz ↦ (hd z (le_of_lt (by simpa using hz))).hasDerivWithinAt) (fun z hz ↦ ?_)
    have hz0 : (0 : ℝ) < z := by simpa using hz
    rw [hg', sub_nonneg, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg z, hz0.le, sq_nonneg (z * z)]
  have h0 := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simp only [hg] at h0
  norm_num at h0
  linarith

/-- The Bernstein lower bound on the Poisson Cramér transform:
`x² / (2 (1 + x / 3)) ≤ poissonCramer x` for `x ≥ 0`. -/
lemma sq_div_le_poissonCramer (hx : 0 ≤ x) :
    x ^ 2 / (2 * (1 + x / 3)) ≤ poissonCramer x := by
  have hlog := div_le_log_one_add hx
  have hden : (6 : ℝ) + 8 * x + 2 * x ^ 2 ≠ 0 := by positivity
  have hden' : (2 : ℝ) * (1 + x / 3) ≠ 0 := by positivity
  have hkey : (1 + x) * ((6 * x + 5 * x ^ 2) / (6 + 8 * x + 2 * x ^ 2)) - x
      = x ^ 2 / (2 * (1 + x / 3)) := by
    field_simp
    ring
  rw [poissonCramer, ← hkey]
  have : (1 + x) * ((6 * x + 5 * x ^ 2) / (6 + 8 * x + 2 * x ^ 2)) ≤ (1 + x) * log (1 + x) := by
    gcongr
  linarith

/-- The Poisson Cramér transform is nonnegative on `[0, ∞)`. -/
lemma poissonCramer_nonneg (hx : 0 ≤ x) : 0 ≤ poissonCramer x :=
  le_trans (by positivity) (sq_div_le_poissonCramer hx)

/-- The value of `lam ↦ lam b s - c φ_b(lam)` at `lam = log (1 + s / c) / b`: with
`u = log (1 + s / c)`, `u s - c (e^u - 1 - u) = c * poissonCramer (s / c)`. -/
lemma mul_poissonCramer_eq (hc : 0 < c) (hs : 0 ≤ s) :
    log (1 + s / c) * s - c * expSubOneSub (log (1 + s / c)) = c * poissonCramer (s / c) := by
  have hpos : (0 : ℝ) < 1 + s / c := by positivity
  have hexp : exp (log (1 + s / c)) = 1 + s / c := exp_log hpos
  simp only [expSubOneSub, poissonCramer, hexp]
  generalize log (1 + s / c) = L
  field_simp
  ring

/-- If `c h(s / c) ≤ l` with `c > 0`, `s ≥ 0` and `l ≥ 0`, then `s ≤ √(2 c l) + 2 l / 3`. -/
lemma le_sqrt_add_of_mul_poissonCramer_le (hc : 0 < c) (hs : 0 ≤ s) (hl : 0 ≤ l)
    (h : c * poissonCramer (s / c) ≤ l) : s ≤ √(2 * c * l) + 2 / 3 * l := by
  have hsc : 0 ≤ s / c := by positivity
  have h1 : c * ((s / c) ^ 2 / (2 * (1 + s / c / 3))) ≤ l :=
    le_trans (mul_le_mul_of_nonneg_left (sq_div_le_poissonCramer hsc) hc.le) h
  have hne1 : (2 : ℝ) * (1 + s / c / 3) ≠ 0 := by positivity
  have hne2 : (2 : ℝ) * (3 * c + s) ≠ 0 := by positivity
  have hcne : c ≠ 0 := hc.ne'
  have e1 : c * ((s / c) ^ 2 / (2 * (1 + s / c / 3))) = 3 * s ^ 2 / (2 * (3 * c + s)) := by
    field_simp
  rw [e1, div_le_iff₀ (by positivity)] at h1
  have hsq : s ^ 2 ≤ 2 / 3 * l * s + 2 * c * l := by nlinarith [h1]
  have := Real.le_add_sqrt_of_sq_le (b := 2 / 3 * l) (c := 2 * c * l) (by positivity)
    (by positivity) hsq
  linarith

end Real
