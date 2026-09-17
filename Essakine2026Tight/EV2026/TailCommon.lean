/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.EV2026.AnalysisCommon
public import Essakine2026Tight.EV2026.Constants
public import Essakine2026Tight.EV2026.EntropicBPIRun
public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.UnrollBounds
public import Essakine2026Tight.Mathlib.Basic.Real.ENatENNReal
public import Essakine2026Tight.Mathlib.Analysis.SpecialFunctions.Log.SelfBounding

/-!
# Tail of the analysis of Entropic-BPI: sign-independent lemmas

* Numerical facts on the constants of the upper bound: `exp_thirteen_le` (`e^13 ≤ 3^13`),
  `progress_pos`, `progress_le_one`, `one_le_upperBound`.
* `natCast_le_upperBound`: the arithmetic of the bound on the stopping time (Steps 1–3 of the
  proof of Lemmas `lem:stopping_time_bound_pos` and `lem:stopping_time_bound_neg` of the
  blueprint): if the progress `κ(β, ε)` is at most `e^13 (36 √(V_G x_t) + 84 H e^{|β| (H+1)} y_t)`
  for every `t < T`, and the sums `∑_{t < T} x_t`, `∑_{t < T} y_t` satisfy the counting bounds
  `16 S A H α*(T - 1) log(T + 1)` and `16 S A H α(T - 1) log(T + 1)`, then
  `T ≤ upperBound S A H β ε δ G`. The proof is the Cauchy–Schwarz inequality over the episodes and
  the self-bounding inequality `Real.le_of_le_sqrt_mul_add'` (the paper's Lemma 29).
* Step 4, from the bound for every `T ≤ τ` to `τ ≤ U` in `ℝ≥0∞` (including the case `τ = ∞`), is
  `ENat.toENNReal_le_ofReal_of_forall_natCast_le` (`Mathlib/Basic/Real/ENatENNReal.lean`).
* `one_sub_le_measureReal_stoppingTime_le`, `measureReal_bad_le`: the passage from pointwise
  statements on an event of probability at least `1 - δ` (the good event) to the probability
  statements of Lemmas `lem:pac_pos` and `lem:pac_neg`, in a run of Entropic-BPI (the policies
  played and the output are almost surely the greedy ones).
* `starRateMin`, `klRateMin`: the rate terms `min {α*(n_h(s, a))/n_h(s, a), 1}` and
  `min {α(n_h(s, a))/n_h(s, a), 1}` of a history as functions of the step `h : ℕ` (`0` beyond the
  horizon, `extendFin`), the form in which they enter the unrolling lemmas of
  `MDP/UnrollBounds.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP.Episodic Learning.MDP
open scoped ENNReal

namespace Essakine2026Tight

/-! ### Numerical facts -/

/-- `e^13 ≤ 3^13`. -/
lemma exp_thirteen_le : Real.exp 13 ≤ 3 ^ 13 := by
  calc Real.exp 13 = Real.exp 1 ^ 13 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ 3 ^ 13 := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 13

/-- The progress constant `κ(β, ε)` is positive for `β ≠ 0` and `ε > 0`. -/
lemma progress_pos {β ε : ℝ} (hβ : β ≠ 0) (hε : 0 < ε) : 0 < progress β ε := by
  unfold progress
  have h1 : 1 < Real.exp (|β| * ε) := Real.one_lt_exp_iff.2 (mul_pos (abs_pos.2 hβ) hε)
  exact div_pos (mul_pos (by linarith) (Real.exp_pos _)) (by norm_num)

/-- The progress constant `κ(β, ε)` is at most `1`. -/
lemma progress_le_one {β ε : ℝ} (hε : 0 ≤ ε) : progress β ε ≤ 1 := by
  unfold progress
  have hu : 1 ≤ Real.exp (|β| * ε) := Real.one_le_exp (mul_nonneg (abs_nonneg β) hε)
  have hv : Real.exp (-(2 : ℕ) * |β| * ε) * Real.exp (|β| * ε) = Real.exp (-(|β| * ε)) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hv1 : Real.exp (-(|β| * ε)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (abs_nonneg β) hε))
  have h2 := Real.exp_pos (-(2 : ℕ) * |β| * ε)
  rw [div_le_one (by norm_num)]
  push_cast at hv h2 ⊢
  nlinarith

/-- The upper bound is at least `1`. -/
lemma one_le_upperBound {nS nA H : ℕ} {β ε δ G : ℝ} (hβ : β ≠ 0) (hε : 0 < ε) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) : 1 ≤ upperBound nS nA H β ε δ G := by
  have hκ := progress_pos hβ hε
  have hA₀ := log_three_mul_div_nonneg nS nA H hδ hδ1
  have hC : 0 ≤ coeffSqrt nS nA H β ε G := div_nonneg (by positivity) hκ.le
  have hD : 0 ≤ coeffLin nS nA H β ε := div_nonneg (by positivity) hκ.le
  unfold upperBound
  simp only
  have h1 : 0 ≤ coeffSqrt nS nA H β ε G ^ 2 * (Real.log ((3 * nS * nA * H : ℕ) / δ) + 1)
      * logFactor nS nA H β ε δ G ^ 2 := by positivity
  have h2 : 0 ≤ (coeffLin nS nA H β ε + (2 : ℕ) * √(coeffLin nS nA H β ε)
      * coeffSqrt nS nA H β ε G) * (Real.log ((3 * nS * nA * H : ℕ) / δ) + nS)
      * logFactor nS nA H β ε δ G ^ 2 := by positivity
  linarith

/-! ### The bound on the stopping time: arithmetic -/

/-- The variance factor `V_G` is nonnegative. -/
lemma varianceFactor_nonneg (β G : ℝ) : 0 ≤ varianceFactor β G :=
  div_nonneg (sq_nonneg _) (Real.exp_pos _).le

/-- `κ C = 10⁹ √(V_G S A H)`. -/
lemma progress_mul_coeffSqrt {nS nA H : ℕ} {β ε G : ℝ} (hβ : β ≠ 0) (hε : 0 < ε) :
    progress β ε * coeffSqrt nS nA H β ε G = 10 ^ 9 * √(varianceFactor β G * (nS * nA * H)) := by
  rw [coeffSqrt, mul_div_cancel₀ _ (progress_pos hβ hε).ne']
  simp only [Nat.cast_mul, Nat.cast_ofNat]

/-- `κ D = 10¹⁰ e^{|β| (H + 1)} H² S A`. -/
lemma progress_mul_coeffLin {nS nA H : ℕ} {β ε : ℝ} (hβ : β ≠ 0) (hε : 0 < ε) :
    progress β ε * coeffLin nS nA H β ε
      = 10 ^ 10 * Real.exp (|β| * (H + 1 : ℕ)) * (H ^ 2 * nS * nA) := by
  rw [coeffLin, mul_div_cancel₀ _ (progress_pos hβ hε).ne']
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- The coefficient `D` of the linear term is at least `1`. -/
lemma one_le_coeffLin {nS nA H : ℕ} (hS : 1 ≤ nS) (hA : 1 ≤ nA) (hH : 1 ≤ H) {β ε : ℝ}
    (hβ : β ≠ 0) (hε : 0 < ε) : 1 ≤ coeffLin nS nA H β ε := by
  have hκ := progress_pos hβ hε
  have hκ1 : progress β ε ≤ 1 := progress_le_one hε.le
  have hE : 1 ≤ Real.exp (|β| * (H + 1 : ℕ)) := Real.one_le_exp (by positivity)
  have hH' : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hS' : (1 : ℝ) ≤ nS := by exact_mod_cast hS
  have hA' : (1 : ℝ) ≤ nA := by exact_mod_cast hA
  have h1 : (1 : ℝ) ≤ H ^ 2 * nS * nA :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hH') hS') hA'
  have h2 : (1 : ℝ) ≤ 10 ^ 10 * Real.exp (|β| * (H + 1 : ℕ)) * (H ^ 2 * nS * nA) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) hE) h1
  rw [← progress_mul_coeffLin (nS := nS) (nA := nA) (H := H) hβ hε] at h2
  by_contra hcon
  push Not at hcon
  have := mul_lt_mul_of_pos_left hcon hκ
  linarith

/-- **Step 3 of the bound on the stopping time**: the self-bounding inequality with the constants
of `upperBound`. If `T ≥ 1` satisfies
`T κ ≤ 10⁹ √(V_G S A H) √(T (A₀ L + L²)) + 10¹⁰ e^{|β| (H + 1)} H² S A (A₀ L + S L²)` with
`A₀ = log(3 S A H / δ)` and `L = log(8 e T)`, then `T ≤ upperBound S A H β ε δ G`. -/
lemma natCast_le_upperBound_of_mul_progress_le {nS nA H : ℕ} (hS : 1 ≤ nS) (hA : 1 ≤ nA)
    (hH : 1 ≤ H) {β ε δ G : ℝ} (hβ : β ≠ 0) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {T : ℕ}
    (h : T * progress β ε ≤ 10 ^ 9 * √(varianceFactor β G * (nS * nA * H))
        * √(T * (Real.log ((3 * nS * nA * H : ℕ) / δ) * Real.log (8 * Real.exp 1 * T)
          + 1 * Real.log (8 * Real.exp 1 * T) ^ 2))
      + 10 ^ 10 * Real.exp (|β| * (H + 1 : ℕ)) * (H ^ 2 * nS * nA)
        * (Real.log ((3 * nS * nA * H : ℕ) / δ) * Real.log (8 * Real.exp 1 * T)
          + nS * Real.log (8 * Real.exp 1 * T) ^ 2)) :
    (T : ℝ) ≤ upperBound nS nA H β ε δ G := by
  have hκ := progress_pos hβ hε
  have hC0 : 0 ≤ coeffSqrt nS nA H β ε G := div_nonneg (by positivity) hκ.le
  have hD1 := one_le_coeffLin hS hA hH hβ hε
  have hrec : (T : ℝ) ≤ coeffSqrt nS nA H β ε G
        * √(T * (Real.log ((3 * nS * nA * H : ℕ) / δ) * Real.log (8 * Real.exp 1 * T)
          + 1 * Real.log (8 * Real.exp 1 * T) ^ 2))
      + coeffLin nS nA H β ε
        * (Real.log ((3 * nS * nA * H : ℕ) / δ) * Real.log (8 * Real.exp 1 * T)
          + nS * Real.log (8 * Real.exp 1 * T) ^ 2) := by
    refine le_of_mul_le_mul_left ?_ hκ
    rw [mul_add, ← mul_assoc, ← mul_assoc, progress_mul_coeffSqrt hβ hε,
      progress_mul_coeffLin hβ hε, mul_comm]
    exact h
  have hα : Real.exp 1 ≤ 8 * Real.exp 1 := by linarith [Real.exp_pos 1]
  have hSR : (1 : ℝ) ≤ nS := by exact_mod_cast hS
  refine (Real.le_of_le_sqrt_mul_add' (log_three_mul_div_nonneg nS nA H hδ hδ1) zero_le_one
    hC0 hD1 hSR hα T.cast_nonneg hrec).trans_eq ?_
  simp only [upperBound, logFactor, Nat.cast_ofNat]

/-- **Steps 1–3 of the bound on the stopping time** (sign-independent arithmetic): if for every
`t < T` the progress `κ(β, ε)` is at most `e^13 (36 √(V_G x_t) + 84 H e^{|β| (H + 1)} y_t)` with
`x ≥ 0`, and `∑_{t < T} x_t ≤ 16 S A H α*(T - 1) log(T + 1)`,
`∑_{t < T} y_t ≤ 16 S A H α(T - 1) log(T + 1)`, then `T ≤ upperBound S A H β ε δ G`. -/
lemma natCast_le_upperBound {nS nA H : ℕ} (hS : 1 ≤ nS) (hA : 1 ≤ nA) {β ε δ G : ℝ}
    (hβ : β ≠ 0) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {T : ℕ} {x y : ℕ → ℝ}
    (hx0 : ∀ t, 0 ≤ x t)
    (hprog : ∀ t < T, progress β ε ≤ Real.exp 13 * (36 * √(varianceFactor β G * x t)
      + 84 * H * Real.exp (|β| * (H + 1 : ℕ)) * y t))
    (hx : ∑ t ∈ range T, x t
      ≤ 16 * (nS * nA * H) * alphaStar nS nA H δ (T - 1) * Real.log (T + 1))
    (hy : ∑ t ∈ range T, y t
      ≤ 16 * (nS * nA * H) * alphaKL nS nA H δ (T - 1) * Real.log (T + 1)) :
    (T : ℝ) ≤ upperBound nS nA H β ε δ G := by
  have hκ := progress_pos hβ hε
  have hV := varianceFactor_nonneg β G
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp only [CharP.cast_eq_zero]
    exact zero_le_one.trans (one_le_upperBound hβ hε hδ hδ1)
  rcases Nat.eq_zero_or_pos H with rfl | hH
  · -- no step: the sums vanish and the progress would be nonpositive
    exfalso
    have hx00 : x 0 ≤ 0 := by
      have := single_le_sum (fun t _ ↦ hx0 t) (mem_range.2 hT)
      simp only [CharP.cast_eq_zero, mul_zero, zero_mul] at hx
      linarith
    have h := hprog 0 hT
    rw [Real.sqrt_eq_zero'.2 (mul_nonpos_of_nonneg_of_nonpos hV hx00)] at h
    simp only [CharP.cast_eq_zero, mul_zero, zero_mul, add_zero] at h
    linarith
  refine natCast_le_upperBound_of_mul_progress_le hS hA hH hβ hε hδ hδ1 ?_
  -- the logarithmic factor `L = log(8 e T)` and `A₀ = log(3 S A H / δ)`
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have he2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hL0 : 0 ≤ Real.log (8 * Real.exp 1 * T) := Real.log_nonneg (by nlinarith)
  have hlogT : Real.log (T + 1) ≤ Real.log (8 * Real.exp 1 * T) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hA₀0 := log_three_mul_div_nonneg nS nA H hδ hδ1
  have hαS : alphaStar nS nA H δ (T - 1)
      = Real.log ((3 * nS * nA * H : ℕ) / δ) + Real.log (8 * Real.exp 1 * T) := by
    simp only [alphaStar, Nat.sub_add_cancel hT, Nat.cast_ofNat]
  have hαK : alphaKL nS nA H δ (T - 1)
      = Real.log ((3 * nS * nA * H : ℕ) / δ) + nS * Real.log (8 * Real.exp 1 * T) := by
    simp only [alphaKL, Nat.sub_add_cancel hT, Nat.cast_ofNat]
  generalize Real.log (8 * Real.exp 1 * T) = L at hL0 hlogT hαS hαK ⊢
  generalize Real.log ((3 * nS * nA * H : ℕ) / δ) = A₀ at hA₀0 hαS hαK ⊢
  have hE0 : 0 ≤ Real.exp (|β| * (H + 1 : ℕ)) := (Real.exp_pos _).le
  generalize Real.exp (|β| * (H + 1 : ℕ)) = E at hE0 hprog ⊢
  generalize progress β ε = κ at hκ hprog ⊢
  generalize varianceFactor β G = V at hV hprog ⊢
  have hSAH : (0 : ℝ) ≤ nS * nA * H := by positivity
  have hxs : ∑ t ∈ range T, x t ≤ 16 * (nS * nA * H) * (A₀ * L + 1 * L ^ 2) := by
    refine hx.trans ?_
    rw [hαS]
    have : (A₀ + L) * Real.log (T + 1) ≤ (A₀ + L) * L :=
      mul_le_mul_of_nonneg_left hlogT (by positivity)
    have h16 : (0 : ℝ) ≤ 16 * (nS * nA * H) := by positivity
    calc 16 * (nS * nA * H) * (A₀ + L) * Real.log (T + 1)
        = 16 * (nS * nA * H) * ((A₀ + L) * Real.log (T + 1)) := by ring
      _ ≤ 16 * (nS * nA * H) * ((A₀ + L) * L) := mul_le_mul_of_nonneg_left this h16
      _ = _ := by ring
  have hys : ∑ t ∈ range T, y t ≤ 16 * (nS * nA * H) * (A₀ * L + nS * L ^ 2) := by
    refine hy.trans ?_
    rw [hαK]
    have : (A₀ + nS * L) * Real.log (T + 1) ≤ (A₀ + nS * L) * L :=
      mul_le_mul_of_nonneg_left hlogT (by positivity)
    have h16 : (0 : ℝ) ≤ 16 * (nS * nA * H) := by positivity
    calc 16 * (nS * nA * H) * (A₀ + nS * L) * Real.log (T + 1)
        = 16 * (nS * nA * H) * ((A₀ + nS * L) * Real.log (T + 1)) := by ring
      _ ≤ 16 * (nS * nA * H) * ((A₀ + nS * L) * L) := mul_le_mul_of_nonneg_left this h16
      _ = _ := by ring
  generalize hQ : A₀ * L + 1 * L ^ 2 = Q at hxs ⊢
  generalize hQ' : A₀ * L + nS * L ^ 2 = Q' at hys ⊢
  have hQ0 : 0 ≤ Q := by rw [← hQ]; positivity
  have hQ'0 : 0 ≤ Q' := by rw [← hQ']; positivity
  -- Step 1: summing the progress over the episodes, with Cauchy–Schwarz
  have hcs := Real.sum_sqrt_mul_sqrt_le (range T) (f := fun _ ↦ (1 : ℝ)) (g := x)
    (fun _ ↦ zero_le_one) hx0
  simp only [Real.sqrt_one, one_mul, sum_const, card_range, nsmul_eq_mul, mul_one] at hcs
  have hsqrt : ∑ t ∈ range T, √(V * x t) ≤ 4 * √(V * (nS * nA * H)) * √(T * Q) := by
    calc ∑ t ∈ range T, √(V * x t) = √V * ∑ t ∈ range T, √(x t) := by
          rw [mul_sum]
          exact sum_congr rfl fun t _ ↦ Real.sqrt_mul hV _
      _ ≤ √V * (√T * √(16 * (nS * nA * H) * Q)) := by
          refine mul_le_mul_of_nonneg_left (hcs.trans ?_) (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxs) (Real.sqrt_nonneg _)
      _ = 4 * √(V * (nS * nA * H)) * √(T * Q) := by
          rw [Real.sqrt_mul (by positivity) Q, Real.sqrt_mul (by norm_num) Q,
            Real.sqrt_mul hV, Real.sqrt_mul (by norm_num),
            show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
          ring
  have hsum : (T : ℝ) * κ ≤ Real.exp 13 * (36 * ∑ t ∈ range T, √(V * x t)
      + 84 * H * E * ∑ t ∈ range T, y t) := by
    calc (T : ℝ) * κ = ∑ _t ∈ range T, κ := by simp [mul_comm]
      _ ≤ ∑ t ∈ range T, Real.exp 13 * (36 * √(V * x t) + 84 * H * E * y t) :=
          sum_le_sum fun t ht ↦ hprog t (mem_range.1 ht)
      _ = _ := by rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum]
  have he13 : Real.exp 13 ≤ 1594323 := by
    have := exp_thirteen_le
    norm_num at this
    exact this
  have he0 := Real.exp_pos 13
  have ha : 0 ≤ √(V * (nS * nA * H)) * √(T * Q) := by positivity
  have hb : 0 ≤ E * (H ^ 2 * nS * nA) * Q' := by positivity
  have hy' : 84 * H * E * ∑ t ∈ range T, y t ≤ 1344 * (E * (H ^ 2 * nS * nA) * Q') := by
    calc 84 * H * E * ∑ t ∈ range T, y t ≤ 84 * H * E * (16 * (nS * nA * H) * Q') :=
          mul_le_mul_of_nonneg_left hys (by positivity)
      _ = 1344 * (E * (H ^ 2 * nS * nA) * Q') := by ring
  calc (T : ℝ) * κ ≤ Real.exp 13 * (36 * (4 * √(V * (nS * nA * H)) * √(T * Q))
        + 1344 * (E * (H ^ 2 * nS * nA) * Q')) := by
        refine hsum.trans (mul_le_mul_of_nonneg_left ?_ he0.le)
        gcongr
    _ = (144 * Real.exp 13) * (√(V * (nS * nA * H)) * √(T * Q))
        + (1344 * Real.exp 13) * (E * (H ^ 2 * nS * nA) * Q') := by ring
    _ ≤ 10 ^ 9 * (√(V * (nS * nA * H)) * √(T * Q))
        + 10 ^ 10 * (E * (H ^ 2 * nS * nA) * Q') := by
        gcongr
        · linarith
        · linarith
    _ = _ := by ring

/-! ### From the good event to probabilities -/

/-! ### Rate terms of a history as functions of the step -/

section Rates

variable {S A : Type*} {H : ℕ}

/-- The extension by `0` beyond the horizon of a function of the steps `h : Fin H`. -/
def extendFin (f : Fin H → S → A → ℝ) (h : ℕ) (s : S) (a : A) : ℝ :=
  if hh : h < H then f ⟨h, hh⟩ s a else 0

lemma extendFin_of_lt (f : Fin H → S → A → ℝ) {h : ℕ} (hh : h < H) (s : S) (a : A) :
    extendFin f h s a = f ⟨h, hh⟩ s a := by
  simp only [extendFin, hh, ↓reduceDIte]

lemma extendFin_fin (f : Fin H → S → A → ℝ) (h : Fin H) (s : S) (a : A) :
    extendFin f h s a = f h s a := by
  simp only [extendFin, h.is_lt, ↓reduceDIte, Fin.eta]

lemma extendFin_nonneg {f : Fin H → S → A → ℝ} (hf : ∀ h s a, 0 ≤ f h s a) (h : ℕ) (s : S)
    (a : A) : 0 ≤ extendFin f h s a := by
  unfold extendFin
  split_ifs
  · exact hf _ _ _
  · exact le_rfl

lemma sum_range_mul_extendFin [Fintype S] [Fintype A] (g : ℕ → S → A → ℝ)
    (f : Fin H → S → A → ℝ) :
    ∑ h ∈ range H, ∑ s, ∑ a, g h s a * extendFin f h s a
      = ∑ h : Fin H, ∑ s, ∑ a, g h s a * f h s a := by
  rw [← Fin.sum_univ_eq_sum_range (fun h ↦ ∑ s, ∑ a, g h s a * extendFin f h s a) H]
  exact sum_congr rfl fun h _ ↦ sum_congr rfl fun s _ ↦ sum_congr rfl fun a _ ↦ by
    rw [extendFin_fin]

variable [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] {t : ℕ}

/-- The rate term `min {α*(n_h(s, a))/n_h(s, a), 1}` of a history, as a function of the step
`h : ℕ` (`0` beyond the horizon). -/
noncomputable def starRateMin (δ : ℝ) (hist : Hist Unit (Policy S A H) (Traj S H) t) :
    ℕ → S → A → ℝ :=
  extendFin fun h s a ↦
    rateMin (alphaStar (Fintype.card S) (Fintype.card A) H δ) (visitCount hist h s a)

/-- The rate term `min {α(n_h(s, a))/n_h(s, a), 1}` of a history, as a function of the step
`h : ℕ` (`0` beyond the horizon). -/
noncomputable def klRateMin (δ : ℝ) (hist : Hist Unit (Policy S A H) (Traj S H) t) :
    ℕ → S → A → ℝ :=
  extendFin fun h s a ↦
    rateMin (alphaKL (Fintype.card S) (Fintype.card A) H δ) (visitCount hist h s a)

variable (δ : ℝ) (hist : Hist Unit (Policy S A H) (Traj S H) t)

lemma starRateMin_of_lt {h : ℕ} (hh : h < H) (s : S) (a : A) :
    starRateMin δ hist h s a
      = rateMin (alphaStar (Fintype.card S) (Fintype.card A) H δ) (visitCount hist ⟨h, hh⟩ s a) :=
  extendFin_of_lt _ hh s a

lemma klRateMin_of_lt {h : ℕ} (hh : h < H) (s : S) (a : A) :
    klRateMin δ hist h s a
      = rateMin (alphaKL (Fintype.card S) (Fintype.card A) H δ) (visitCount hist ⟨h, hh⟩ s a) :=
  extendFin_of_lt _ hh s a

lemma starRateMin_fin (h : Fin H) (s : S) (a : A) :
    starRateMin δ hist h s a
      = rateMin (alphaStar (Fintype.card S) (Fintype.card A) H δ) (visitCount hist h s a) :=
  extendFin_fin _ h s a

lemma klRateMin_fin (h : Fin H) (s : S) (a : A) :
    klRateMin δ hist h s a
      = rateMin (alphaKL (Fintype.card S) (Fintype.card A) H δ) (visitCount hist h s a) :=
  extendFin_fin _ h s a

variable {δ}

lemma starRateMin_nonneg (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h : ℕ) (s : S) (a : A) :
    0 ≤ starRateMin δ hist h s a :=
  extendFin_nonneg (fun _ _ _ ↦ rateMin_nonneg (alphaStar_nonneg _ _ _ hδ hδ1) _) h s a

lemma klRateMin_nonneg (hδ : 0 < δ) (hδ1 : δ ≤ 1) (h : ℕ) (s : S) (a : A) :
    0 ≤ klRateMin δ hist h s a :=
  extendFin_nonneg (fun _ _ _ ↦ rateMin_nonneg (alphaKL_nonneg _ _ _ hδ hδ1) _) h s a

variable (δ) [MeasurableSpace S] [MeasurableSpace A] (M : EpisodicMDP S A)
  (π : ℕ → S → A) (s₁ : S)

/-- The sum over the steps of the occupancies against the Bernstein rate terms, with the steps
`h : ℕ` or `h : Fin H`. -/
lemma sum_range_occupancy_mul_starRateMin :
    ∑ h ∈ range H, ∑ s, ∑ a, occupancy M π s₁ h s a * starRateMin δ hist h s a
      = ∑ h : Fin H, ∑ s, ∑ a, occupancy M π s₁ h s a
        * rateMin (alphaStar (Fintype.card S) (Fintype.card A) H δ) (visitCount hist h s a) :=
  sum_range_mul_extendFin _ _

/-- The sum over the steps of the occupancies against the KL rate terms, with the steps `h : ℕ`
or `h : Fin H`. -/
lemma sum_range_occupancy_mul_klRateMin :
    ∑ h ∈ range H, ∑ s, ∑ a, occupancy M π s₁ h s a * klRateMin δ hist h s a
      = ∑ h : Fin H, ∑ s, ∑ a, occupancy M π s₁ h s a
        * rateMin (alphaKL (Fintype.card S) (Fintype.card A) H δ) (visitCount hist h s a) :=
  sum_range_mul_extendFin _ _

variable {Ω : Type*} (X : ℕ → Ω → Policy S A H) (Y : ℕ → Ω → Traj S H)

omit [MeasurableSpace S] [MeasurableSpace A] in
lemma starRateMin_histAt (t : ℕ) (ω : Ω) (h : Fin H) (s : S) (a : A) :
    starRateMin δ (histAt X Y t ω) h s a = starRateMinAt X Y δ h s a t ω :=
  starRateMin_fin δ _ h s a

omit [MeasurableSpace S] [MeasurableSpace A] in
lemma klRateMin_histAt (t : ℕ) (ω : Ω) (h : Fin H) (s : S) (a : A) :
    klRateMin δ (histAt X Y t ω) h s a = klRateMinAt X Y δ h s a t ω :=
  klRateMin_fin δ _ h s a

end Rates

section Run

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]
  {H : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {M : EpisodicMDP S A} {r : ℕ → S → A → ℝ} {β δ ε : ℝ} {s₁ : S}
  {env : Environment Unit (Policy S A H) (Traj S H)} {X : ℕ → Ω → Policy S A H}
  {Y : ℕ → Ω → Traj S H} {out : Ω → Policy S A H} {E : Set Ω} {U : ℝ}

/-- **The stopping time bound in probability**: in a run of Entropic-BPI, if the stopping time is
at most `U` at every `ω` of an event `E` at which the policies played are the greedy ones, and
`P(Eᶜ) ≤ δ`, then `τ ≤ U` with probability at least `1 - δ`. -/
lemma one_sub_le_measureReal_stoppingTime_le
    (h : (entropicBPI H r β δ ε s₁).IsRun env (fun _ _ ↦ ()) X Y out P) (hδ : 0 ≤ δ)
    (hE : P Eᶜ ≤ ENNReal.ofReal δ)
    (hτ : ∀ ω ∈ E, (∀ t, X t ω = greedyAt X Y r β δ t ω) →
      ((entropicBPI H r β δ ε s₁).stoppingTime (fun _ _ ↦ ()) X Y ω : ℝ≥0∞) ≤ ENNReal.ofReal U) :
    1 - δ ≤ P.real {ω |
      ((entropicBPI H r β δ ε s₁).stoppingTime (fun _ _ ↦ ()) X Y ω : ℝ≥0∞)
        ≤ ENNReal.ofReal U} := by
  set F := {ω | ((entropicBPI H r β δ ε s₁).stoppingTime (fun _ _ ↦ ()) X Y ω : ℝ≥0∞)
    ≤ ENNReal.ofReal U} with hF
  have hsub : Fᶜ ≤ᵐ[P] Eᶜ := by
    filter_upwards [ae_action_eq_greedy h] with ω hX
    change ω ∉ F → ω ∉ E
    exact fun hωF hωE ↦ hωF (hτ ω hωE hX)
  have hc : P.real Fᶜ ≤ δ := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hδ ((measure_mono_ae hsub).trans hE)
  have hu : P.real Set.univ ≤ P.real F + P.real Fᶜ :=
    (Set.union_compl_self F) ▸ measureReal_union_le _ _
  rw [probReal_univ] at hu
  linarith

/-- **The PAC guarantee in probability**: in a run of Entropic-BPI, if at every `ω` of an event
`E` at which the policies played are the greedy ones the stopping time is finite, and the
greedy policy is `ε`-optimal whenever the stopping condition holds, and `P(Eᶜ) ≤ δ`, then the
output is `ε`-optimal with probability at least `1 - δ`. -/
lemma measureReal_bad_le
    (h : (entropicBPI H r β δ ε s₁).IsRun env (fun _ _ ↦ ()) X Y out P) (hδ : 0 ≤ δ)
    (hE : P Eᶜ ≤ ENNReal.ofReal δ)
    (hτ : ∀ ω ∈ E, (∀ t, X t ω = greedyAt X Y r β δ t ω) →
      (entropicBPI H r β δ ε s₁).stoppingTime (fun _ _ ↦ ()) X Y ω ≠ ⊤)
    (hsound : ∀ ω ∈ E, ∀ t, stopCond r β δ ε s₁ (histAt X Y t ω) →
      optEntropicValue M H β 0 s₁
        - entropicValue M H β (greedyAt X Y r β δ t ω).extend 0 s₁ ≤ ε) :
    P.real {ω | ε < optEntropicValue M H β 0 s₁
      - entropicValue M H β (out ω).extend 0 s₁} ≤ δ := by
  have hsub : {ω | ε < optEntropicValue M H β 0 s₁
      - entropicValue M H β (out ω).extend 0 s₁} ≤ᵐ[P] Eᶜ := by
    filter_upwards [ae_action_eq_greedy h, ae_output_eq_greedy h] with ω hX hout
    change ε < optEntropicValue M H β 0 s₁
      - entropicValue M H β (out ω).extend 0 s₁ → ω ∉ E
    intro hbad hωE
    have hstop := stopCond_histAt_stoppingTime (hτ ω hωE hX)
    have := hsound ω hωE _ hstop
    rw [hout] at hbad
    exact (not_le.2 hbad) this
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hδ ((measure_mono_ae hsub).trans hE)

/-- A stopping time bounded by a real number is finite. -/
lemma stoppingTime_ne_top_of_le {ω' : Ω}
    (hτ : ((entropicBPI H r β δ ε s₁).stoppingTime (fun _ _ ↦ ()) X Y ω' : ℝ≥0∞)
      ≤ ENNReal.ofReal U) :
    (entropicBPI H r β δ ε s₁).stoppingTime (fun _ _ ↦ ()) X Y ω' ≠ ⊤ := by
  intro htop
  rw [htop, ENat.toENNReal_top, top_le_iff] at hτ
  exact ENNReal.ofReal_ne_top hτ

end Run

end Essakine2026Tight
