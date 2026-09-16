/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.Mathlib.Analysis.Real.Sqrt
public import Essakine2026Tight.Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The self-bounding inequality

If `τ ≥ 0` satisfies `τ ≤ C √(τ (A L + B L²)) + D (A L + E L²)` with `L = log (α τ)`, `α ≥ e`,
`A, B, C, D ≥ 0` and `B ≤ E`, then, with `K = C² (A + B) + (D + 2 √D C) (A + E)`,
`τ ≤ K ((8/5) log (4 α K))² + 1` (`Real.le_mul_sq_log_add_one_of_le_sqrt_mul_add`), and in
particular `τ ≤ K C₁² + 1` for `C₁ = (8/5) log (11 α² (A + E) (C + √D)²)`
(`Real.le_of_le_sqrt_mul_add`), or with `(C + D)²` when `D ≥ 1` (`Real.le_of_le_sqrt_mul_add'`).

This is Lemma 13 of Ménard et al., *Fast active learning for pure exploration in reinforcement
learning* (2021), as quoted in Lemma 29 of Essakine, Vernade (2026), whose constant
`C₁ = (8/5) log (11 α² (A + E) (C + D))` is wrong: the factor `C + D` must be squared
(blueprint, chapter "Elementary inequalities"). The hypotheses `A, B, C, D > 0` and `B ≥ 1` of
the paper are not needed.

The proof: for `τ ≤ 1` there is nothing to prove; otherwise `L ≥ 1`, the hypothesis reduces to
the quadratic inequality `τ ≤ C L √(A + B) √τ + D (A + E) L²` in `√τ`, whose solution is
`τ ≤ K L²` (`Real.le_mul_sq_log_of_le_sqrt_mul_add`), and `Real.log_le_of_le_mul_sq_log`
bounds `L` (`Real.log_le_of_le_sqrt_mul_add`).
-/

@[expose] public section

namespace Real

variable {A B C D E α τ : ℝ}

/-- Reduction of the self-bounding hypothesis to `τ ≤ K L²` with `L = log (α τ)`, when `L ≥ 1`. -/
lemma le_mul_sq_log_of_le_sqrt_mul_add (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hE : B ≤ E) (hτ : 0 ≤ τ) (hL : 1 ≤ log (α * τ))
    (h : τ ≤ C * √(τ * (A * log (α * τ) + B * log (α * τ) ^ 2))
      + D * (A * log (α * τ) + E * log (α * τ) ^ 2)) :
    τ ≤ (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E)) * log (α * τ) ^ 2 := by
  set L := log (α * τ) with hLdef
  have hL0 : 0 ≤ L := by linarith
  have hE0 : 0 ≤ E := hB.trans hE
  have hAB : 0 ≤ A + B := by positivity
  have hAE : 0 ≤ A + E := by positivity
  have hAL : 0 ≤ A * (L * (L - 1)) := mul_nonneg hA (mul_nonneg hL0 (sub_nonneg.2 hL))
  have h1 : A * L + B * L ^ 2 ≤ (A + B) * L ^ 2 := by nlinarith
  have h2 : A * L + E * L ^ 2 ≤ (A + E) * L ^ 2 := by nlinarith
  -- (i) the quadratic inequality in `√τ`
  have hτ' : τ ≤ C * L * √(A + B) * √τ + D * (A + E) * L ^ 2 := by
    calc τ ≤ C * √(τ * (A * L + B * L ^ 2)) + D * (A * L + E * L ^ 2) := h
      _ ≤ C * √(τ * ((A + B) * L ^ 2)) + D * ((A + E) * L ^ 2) := by gcongr
      _ = C * L * √(A + B) * √τ + D * (A + E) * L ^ 2 := by
          rw [show τ * ((A + B) * L ^ 2) = L ^ 2 * ((A + B) * τ) by ring,
            sqrt_mul (by positivity), sqrt_sq hL0, sqrt_mul hAB]
          ring
  -- (ii) its solution
  have hx : √τ ≤ C * L * √(A + B) + √(D * (A + E) * L ^ 2) :=
    le_add_sqrt_of_sq_le (by positivity) (by positivity)
      (by rw [sq_sqrt hτ]; linarith)
  have hsq2 : √(D * (A + E) * L ^ 2) = √D * √(A + E) * L := by
    rw [sqrt_mul (by positivity), sqrt_mul hD, sqrt_sq hL0]
  rw [hsq2] at hx
  have hae : √(A + B) * √(A + E) ≤ A + E := by
    calc √(A + B) * √(A + E) ≤ √(A + E) * √(A + E) :=
          mul_le_mul_of_nonneg_right (sqrt_le_sqrt (by linarith)) (sqrt_nonneg _)
      _ = A + E := mul_self_sqrt hAE
  have key : (C * L * √(A + B) + √D * √(A + E) * L) ^ 2
      = L ^ 2 * (C ^ 2 * (A + B) + D * (A + E))
        + 2 * C * √D * L ^ 2 * (√(A + B) * √(A + E)) := by
    have ha := sq_sqrt hAB
    have he := sq_sqrt hAE
    have hd := sq_sqrt hD
    linear_combination (C ^ 2 * L ^ 2) * ha + (L ^ 2 * √D ^ 2) * he + (L ^ 2 * (A + E)) * hd
  calc τ = √τ ^ 2 := (sq_sqrt hτ).symm
    _ ≤ (C * L * √(A + B) + √D * √(A + E) * L) ^ 2 := pow_le_pow_left₀ (sqrt_nonneg τ) hx 2
    _ = L ^ 2 * (C ^ 2 * (A + B) + D * (A + E))
        + 2 * C * √D * L ^ 2 * (√(A + B) * √(A + E)) := key
    _ ≤ L ^ 2 * (C ^ 2 * (A + B) + D * (A + E)) + 2 * C * √D * L ^ 2 * (A + E) := by gcongr
    _ = (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E)) * L ^ 2 := by ring

/-- `1 ≤ log (α τ)` when `α ≥ e` and `τ > 1`. -/
lemma one_le_log_mul_of_exp_one_le (hα : exp 1 ≤ α) (hτ : 1 < τ) : 1 ≤ log (α * τ) := by
  have hα0 : 0 < α := (exp_pos 1).trans_le hα
  rw [le_log_iff_exp_le (by positivity)]
  calc exp 1 ≤ α := hα
    _ = α * 1 := (mul_one α).symm
    _ ≤ α * τ := by gcongr

/-- The logarithm in the self-bounding inequality: `log (α τ) ≤ (8/5) log (4 α K)` with
`K = C² (A + B) + (D + 2 √D C) (A + E)`, for `τ > 1`. -/
lemma log_le_of_le_sqrt_mul_add (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : B ≤ E)
    (hα : exp 1 ≤ α) (hτ : 1 < τ)
    (h : τ ≤ C * √(τ * (A * log (α * τ) + B * log (α * τ) ^ 2))
      + D * (A * log (α * τ) + E * log (α * τ) ^ 2)) :
    log (α * τ) ≤ 8 / 5 * log (4 * α * (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E))) := by
  have hα0 : 0 < α := (exp_pos 1).trans_le hα
  have hL := one_le_log_mul_of_exp_one_le hα hτ
  have hτK := le_mul_sq_log_of_le_sqrt_mul_add hA hB hC hD hE (by linarith) hL h
  have hK0 : 0 < C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E) := by
    by_contra! hcon
    nlinarith [sq_nonneg (log (α * τ))]
  have hy : 1 ≤ α * τ := by
    have : 1 ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
    nlinarith
  have hyM : α * τ ≤ α * (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E)) * log (α * τ) ^ 2 := by
    calc α * τ ≤ α * ((C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E)) * log (α * τ) ^ 2) := by
          gcongr
      _ = _ := by ring
  have := log_le_of_le_mul_sq_log hy (by positivity) hyM
  rwa [← mul_assoc] at this

/-- The self-bounding inequality, sharp form: `τ ≤ K ((8/5) log M)² + 1` for every
`M ≥ 4 α K`, with `K = C² (A + B) + (D + 2 √D C) (A + E)`. -/
lemma le_mul_sq_log_add_one_of_le_sqrt_mul_add (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hE : B ≤ E) (hα : exp 1 ≤ α) (hτ : 0 ≤ τ)
    (h : τ ≤ C * √(τ * (A * log (α * τ) + B * log (α * τ) ^ 2))
      + D * (A * log (α * τ) + E * log (α * τ) ^ 2))
    {M : ℝ} (hM : 4 * α * (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E)) ≤ M) :
    τ ≤ (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E)) * (8 / 5 * log M) ^ 2 + 1 := by
  have hE0 : 0 ≤ E := hB.trans hE
  have hKnn : 0 ≤ C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E) := by positivity
  rcases le_or_gt τ 1 with h1 | h1
  · have : 0 ≤ (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E)) * (8 / 5 * log M) ^ 2 := by
      positivity
    linarith
  · have hα0 : 0 < α := (exp_pos 1).trans_le hα
    have hL1 := one_le_log_mul_of_exp_one_le hα h1
    have hL := log_le_of_le_sqrt_mul_add hA hB hC hD hE hα h1 h
    have hτK := le_mul_sq_log_of_le_sqrt_mul_add hA hB hC hD hE hτ hL1 h
    have hK0 : 0 < C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E) := by
      by_contra! hcon
      nlinarith [sq_nonneg (log (α * τ))]
    have hL' : log (α * τ) ≤ 8 / 5 * log M := by
      refine hL.trans ?_
      gcongr
    calc τ ≤ (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E)) * log (α * τ) ^ 2 := hτK
      _ ≤ (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E)) * (8 / 5 * log M) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hL' 2) hKnn
      _ ≤ _ := by linarith

/-- `4 α K ≤ 11 α² (A + E) (C + √D)²` for `K = C² (A + B) + (D + 2 √D C) (A + E)`, `α ≥ e`. -/
lemma four_mul_mul_le (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : B ≤ E)
    (hα : exp 1 ≤ α) :
    4 * α * (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E))
      ≤ 11 * α ^ 2 * (A + E) * (C + √D) ^ 2 := by
  have hE0 : 0 ≤ E := hB.trans hE
  have hα0 : 0 < α := (exp_pos 1).trans_le hα
  have he : 2.7 < exp 1 := lt_trans (by norm_num) exp_one_gt_d9
  have hK : C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E) ≤ (A + E) * (C + √D) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hE (sq_nonneg C), sq_sqrt hD]
  have h4 : 4 * α ≤ 11 * α ^ 2 := by nlinarith
  calc 4 * α * (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E))
      ≤ 11 * α ^ 2 * ((A + E) * (C + √D) ^ 2) :=
        mul_le_mul h4 hK (by positivity) (by positivity)
    _ = 11 * α ^ 2 * (A + E) * (C + √D) ^ 2 := by ring

/-- The self-bounding inequality (Lemma 13 of Ménard et al. 2021, the paper's Lemma 29 with the
corrected constant): if `τ ≥ 0` satisfies
`τ ≤ C √(τ (A L + B L²)) + D (A L + E L²)` with `L = log (α τ)`, `α ≥ e`, `A, B, C, D ≥ 0` and
`B ≤ E`, then `τ ≤ C² (A + B) C₁² + (D + 2 √D C) (A + E) C₁² + 1` with
`C₁ = (8/5) log (11 α² (A + E) (C + √D)²)`. -/
lemma le_of_le_sqrt_mul_add (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : B ≤ E)
    (hα : exp 1 ≤ α) (hτ : 0 ≤ τ)
    (h : τ ≤ C * √(τ * (A * log (α * τ) + B * log (α * τ) ^ 2))
      + D * (A * log (α * τ) + E * log (α * τ) ^ 2)) :
    τ ≤ C ^ 2 * (A + B) * (8 / 5 * log (11 * α ^ 2 * (A + E) * (C + √D) ^ 2)) ^ 2
      + (D + 2 * √D * C) * (A + E) * (8 / 5 * log (11 * α ^ 2 * (A + E) * (C + √D) ^ 2)) ^ 2
      + 1 := by
  have := le_mul_sq_log_add_one_of_le_sqrt_mul_add hA hB hC hD hE hα hτ h
    (four_mul_mul_le hA hB hC hD hE hα)
  linarith

/-- The self-bounding inequality with `C₁ = (8/5) log (11 α² (A + E) (C + D)²)`, for `D ≥ 1`. -/
lemma le_of_le_sqrt_mul_add' (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 1 ≤ D) (hE : B ≤ E)
    (hα : exp 1 ≤ α) (hτ : 0 ≤ τ)
    (h : τ ≤ C * √(τ * (A * log (α * τ) + B * log (α * τ) ^ 2))
      + D * (A * log (α * τ) + E * log (α * τ) ^ 2)) :
    τ ≤ C ^ 2 * (A + B) * (8 / 5 * log (11 * α ^ 2 * (A + E) * (C + D) ^ 2)) ^ 2
      + (D + 2 * √D * C) * (A + E) * (8 / 5 * log (11 * α ^ 2 * (A + E) * (C + D) ^ 2)) ^ 2
      + 1 := by
  have hD0 : 0 ≤ D := by linarith
  have hE0 : 0 ≤ E := hB.trans hE
  have hsqrt : √D ≤ D := by
    rw [sqrt_le_left hD0]
    nlinarith
  have hM : 4 * α * (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E))
      ≤ 11 * α ^ 2 * (A + E) * (C + D) ^ 2 := by
    refine (four_mul_mul_le hA hB hC hD0 hE hα).trans ?_
    gcongr
  have := le_mul_sq_log_add_one_of_le_sqrt_mul_add hA hB hC hD0 hE hα hτ h hM
  linarith

end Real
