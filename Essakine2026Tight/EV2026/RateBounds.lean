/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.EV2026.Run
public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Occupancy
public import Essakine2026Tight.Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Properties of the exploration rates and the counting argument

The rates `α(n, δ) = log(3 S A H / δ) + S log(8 e (n + 1))` and
`α*(n, δ) = log(3 S A H / δ) + log(8 e (n + 1))` of Entropic-BPI (`EV2026/Rates.lean`) are the
values at integers of the real functions `rateReal a₀ k x = a₀ + k log(8 e (x + 1))`
(`alphaKL_eq_rateReal`, `alphaStar_eq_rateReal`), with `a₀ = α^cnt(δ) = log(3 S A H / δ)`.

* `rateReal_mono`, `rateReal_div_le_div`, `le_rateReal`: `rateReal a₀ k` is nondecreasing on
  `[0, ∞)`, `x ↦ rateReal a₀ k x / x` is nonincreasing on `(0, ∞)`, and `rateReal a₀ k ≥ a₀`
  (`lem:sc_rates_real`); `log_three_le_alphaCnt`, `one_lt_alphaCnt`, `alphaCnt_le_alphaStar`,
  `alphaStar_le_alphaKL`, `alphaKL_mono`, `alphaStar_mono`, `alphaKL_div_le_div`,
  `alphaStar_div_le_div` are the integer forms (`lem:rates_props`);
* `rateMin_le_four_mul_div`: the arithmetic of Lemma 27 (`lem:sc_rate_min_arith`),
  `min {α(n)/n, 1} ≤ 4 α(n̄) / max {n̄, 1}` whenever `n ≥ n̄/2 - a₀`;
* `klRateMinAt_le_of_mem_eventCnt`, `starRateMinAt_le_of_mem_eventCnt`: Lemma 27 on the counts
  event (`lem:pseudo_counts_bound`);
* `sum_occupancy_mul_klRateMinAt_le`, `sum_occupancy_mul_starRateMinAt_le`: the counting
  argument `∑_{t < T} ∑_{h, s, a} p^{π^{t+1}}_h(s, a) ρ(n_h^t(s, a)) ≤ 16 S A H α(T - 1) log(T + 1)`
  on the counts event (`lem:sum_counts_bound`).
-/

@[expose] public section

open Finset Learning Learning.MDP Learning.MDP.Episodic MeasureTheory

namespace Essakine2026Tight

/-! ### The rates as real functions -/

/-- The rate `a₀ + k log(8 e (x + 1))` as a function of a real argument `x`. -/
noncomputable def rateReal (a₀ k x : ℝ) : ℝ := a₀ + k * Real.log (8 * Real.exp 1 * (x + 1))

lemma one_le_log_eight_mul_exp_one_mul {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ Real.log (8 * Real.exp 1 * (x + 1)) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  nlinarith [Real.exp_pos 1]

/-- The real rate is nondecreasing on `[0, ∞)`. -/
lemma rateReal_mono {a₀ k x y : ℝ} (hk : 0 ≤ k) (hx : 0 ≤ x) (hxy : x ≤ y) :
    rateReal a₀ k x ≤ rateReal a₀ k y := by
  unfold rateReal
  gcongr

/-- The real rate is at least `a₀` on `[0, ∞)`. -/
lemma le_rateReal {a₀ k x : ℝ} (hk : 0 ≤ k) (hx : 0 ≤ x) : a₀ ≤ rateReal a₀ k x := by
  unfold rateReal
  nlinarith [one_le_log_eight_mul_exp_one_mul hx]

/-- `x ↦ log(8 e (x + 1)) / x` is nonincreasing on `(0, ∞)`. -/
lemma log_eight_mul_exp_one_mul_div_le_div {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.log (8 * Real.exp 1 * (y + 1)) / y ≤ Real.log (8 * Real.exp 1 * (x + 1)) / x := by
  have hy : 0 < y := hx.trans_le hxy
  have hL := one_le_log_eight_mul_exp_one_mul hx.le
  have hsplit : Real.log (8 * Real.exp 1 * (y + 1))
      = Real.log (8 * Real.exp 1 * (x + 1)) + Real.log ((y + 1) / (x + 1)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hlog : Real.log ((y + 1) / (x + 1)) ≤ (y - x) / (x + 1) := by
    have := Real.log_le_sub_one_of_pos (x := (y + 1) / (x + 1)) (by positivity)
    have heq : (y + 1) / (x + 1) - 1 = (y - x) / (x + 1) := by field_simp; ring
    linarith
  have hfrac : x * ((y - x) / (x + 1)) ≤ (y - x) * Real.log (8 * Real.exp 1 * (x + 1)) := by
    have h1 : x * ((y - x) / (x + 1)) = (y - x) * (x / (x + 1)) := by ring
    have h2 : x / (x + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    rw [h1]
    exact mul_le_mul_of_nonneg_left (h2.trans hL) (by linarith)
  rw [div_le_div_iff₀ hy hx, hsplit]
  nlinarith

/-- `x ↦ rateReal a₀ k x / x` is nonincreasing on `(0, ∞)`. -/
lemma rateReal_div_le_div {a₀ k x y : ℝ} (ha₀ : 0 ≤ a₀) (hk : 0 ≤ k) (hx : 0 < x)
    (hxy : x ≤ y) : rateReal a₀ k y / y ≤ rateReal a₀ k x / x := by
  have hy : 0 < y := hx.trans_le hxy
  unfold rateReal
  rw [add_div, add_div, mul_div_assoc, mul_div_assoc]
  exact add_le_add (div_le_div_of_nonneg_left ha₀ hx hxy)
    (mul_le_mul_of_nonneg_left (log_eight_mul_exp_one_mul_div_le_div hx hxy) hk)

/-! ### The rates of Entropic-BPI -/

lemma alphaKL_eq_rateReal (S A H : ℕ) (δ : ℝ) (n : ℕ) :
    alphaKL S A H δ n = rateReal (alphaCnt S A H δ) S n := by
  simp [alphaKL, rateReal, alphaCnt]

lemma alphaKL_eq_fun_rateReal (S A H : ℕ) (δ : ℝ) :
    alphaKL S A H δ = fun n : ℕ ↦ rateReal (alphaCnt S A H δ) S n :=
  funext (alphaKL_eq_rateReal S A H δ)

lemma alphaStar_eq_rateReal (S A H : ℕ) (δ : ℝ) (n : ℕ) :
    alphaStar S A H δ n = rateReal (alphaCnt S A H δ) 1 n := by
  simp [alphaStar, rateReal, alphaCnt]

lemma alphaStar_eq_fun_rateReal (S A H : ℕ) (δ : ℝ) :
    alphaStar S A H δ = fun n : ℕ ↦ rateReal (alphaCnt S A H δ) 1 n :=
  funext (alphaStar_eq_rateReal S A H δ)

/-- The counts rate is at least `log 3` for `S, A, H ≥ 1` and `δ ∈ (0, 1]`. -/
lemma log_three_le_alphaCnt {S A H : ℕ} (hS : 1 ≤ S) (hA : 1 ≤ A) (hH : 1 ≤ H) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : Real.log 3 ≤ alphaCnt S A H δ := by
  unfold alphaCnt
  have h1 : (1 : ℝ) ≤ S * A * H := by
    have : 1 ≤ S * A * H := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  gcongr
  rw [le_div_iff₀ hδ]
  push_cast
  nlinarith

/-- The counts rate is larger than `1` for `S, A, H ≥ 1` and `δ ∈ (0, 1]`. -/
lemma one_lt_alphaCnt {S A H : ℕ} (hS : 1 ≤ S) (hA : 1 ≤ A) (hH : 1 ≤ H) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 1 < alphaCnt S A H δ := by
  refine lt_of_lt_of_le ?_ (log_three_le_alphaCnt hS hA hH hδ hδ1)
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  exact Real.exp_one_lt_three

lemma alphaCnt_nonneg {S A H : ℕ} (hS : 1 ≤ S) (hA : 1 ≤ A) (hH : 1 ≤ H) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 0 ≤ alphaCnt S A H δ :=
  zero_le_one.trans (one_lt_alphaCnt hS hA hH hδ hδ1).le

lemma alphaCnt_le_alphaStar (S A H : ℕ) (δ : ℝ) (n : ℕ) :
    alphaCnt S A H δ ≤ alphaStar S A H δ n := by
  rw [alphaStar_eq_rateReal]
  exact le_rateReal zero_le_one (Nat.cast_nonneg n)

lemma alphaStar_le_alphaKL {S : ℕ} (hS : 1 ≤ S) (A H : ℕ) (δ : ℝ) (n : ℕ) :
    alphaStar S A H δ n ≤ alphaKL S A H δ n := by
  rw [alphaStar_eq_rateReal, alphaKL_eq_rateReal]
  unfold rateReal
  have hL := one_le_log_eight_mul_exp_one_mul (Nat.cast_nonneg (α := ℝ) n)
  have : (1 : ℝ) ≤ S := by exact_mod_cast hS
  nlinarith

lemma alphaKL_mono (S A H : ℕ) (δ : ℝ) : Monotone (alphaKL S A H δ) := fun m n hmn ↦ by
  simp only [alphaKL_eq_rateReal]
  exact rateReal_mono (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hmn)

lemma alphaStar_mono (S A H : ℕ) (δ : ℝ) : Monotone (alphaStar S A H δ) := fun m n hmn ↦ by
  simp only [alphaStar_eq_rateReal]
  exact rateReal_mono zero_le_one (Nat.cast_nonneg _) (by exact_mod_cast hmn)

/-- `n ↦ α(n, δ) / n` is nonincreasing on `n ≥ 1`. -/
lemma alphaKL_div_le_div {S A H : ℕ} (hS : 1 ≤ S) (hA : 1 ≤ A) (hH : 1 ≤ H) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    alphaKL S A H δ n / n ≤ alphaKL S A H δ m / m := by
  simp only [alphaKL_eq_rateReal]
  exact rateReal_div_le_div (alphaCnt_nonneg hS hA hH hδ hδ1) (Nat.cast_nonneg _)
    (by exact_mod_cast hm) (by exact_mod_cast hmn)

/-- `n ↦ α*(n, δ) / n` is nonincreasing on `n ≥ 1`. -/
lemma alphaStar_div_le_div {S A H : ℕ} (hS : 1 ≤ S) (hA : 1 ≤ A) (hH : 1 ≤ H) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    alphaStar S A H δ n / n ≤ alphaStar S A H δ m / m := by
  simp only [alphaStar_eq_rateReal]
  exact rateReal_div_le_div (alphaCnt_nonneg hS hA hH hδ hδ1) zero_le_one
    (by exact_mod_cast hm) (by exact_mod_cast hmn)

/-! ### Rate terms against pseudo-counts -/

lemma rateMin_le_one (α : ℕ → ℝ) (n : ℕ) : rateMin α n ≤ 1 := by
  unfold rateMin
  split_ifs
  · exact le_rfl
  · exact min_le_right _ _

/-- **The arithmetic of Lemma 27** (Lemma 7 of Ménard et al., 2021): let `f` be nondecreasing on
`[0, ∞)`, with `f x / x` nonincreasing on `[1, ∞)` and `f ≥ a₀ ≥ 1`, and let `α n = f n` on the
integers. If `n ≥ n̄ / 2 - a₀` with `n̄ ≥ 0`, then `min {α(n)/n, 1} ≤ 4 f(n̄) / max {n̄, 1}`. -/
lemma rateMin_le_four_mul_div {α : ℕ → ℝ} {f : ℝ → ℝ} (hαf : ∀ n : ℕ, α n = f n)
    (hmono : ∀ x y, 0 ≤ x → x ≤ y → f x ≤ f y)
    (hdiv : ∀ x y, 1 ≤ x → x ≤ y → f y / y ≤ f x / x) {a₀ : ℝ} (ha₀ : 1 ≤ a₀)
    (hf : ∀ x, 0 ≤ x → a₀ ≤ f x) {n : ℕ} {nbar : ℝ} (hnbar : 0 ≤ nbar)
    (hn : nbar / 2 - a₀ ≤ n) :
    rateMin α n ≤ 4 * f nbar / max nbar 1 := by
  rcases le_or_gt (4 * a₀) nbar with hbig | hsmall
  · have hn1 : (1 : ℝ) ≤ n := by linarith
    have hn0 : n ≠ 0 := by rintro rfl; norm_num at hn1
    have hnbar4 : 1 ≤ nbar / 4 := by linarith
    have hmax : max nbar 1 = nbar := max_eq_left (by linarith)
    have hpos : 0 < nbar := by linarith
    calc rateMin α n ≤ α n / n := by simp only [rateMin, hn0, ↓reduceIte]; exact min_le_left _ _
      _ = f n / n := by rw [hαf]
      _ ≤ f (nbar / 4) / (nbar / 4) := hdiv _ _ hnbar4 (by linarith)
      _ = 4 * f (nbar / 4) / nbar := by field_simp
      _ ≤ 4 * f nbar / nbar := by
          gcongr
          exact hmono _ _ (by linarith) (by linarith)
      _ = 4 * f nbar / max nbar 1 := by rw [hmax]
  · refine (rateMin_le_one α n).trans ?_
    have hfa := hf nbar hnbar
    rw [le_div_iff₀ (by positivity), one_mul]
    rcases le_total nbar 1 with h1 | h1
    · rw [max_eq_right h1]; linarith
    · rw [max_eq_left h1]; linarith

/-- Lemma 27 for a real rate `rateReal a₀ k` with `k ≥ 0` and `a₀ ≥ 1`. -/
lemma rateMin_rateReal_le {a₀ k : ℝ} (ha₀ : 1 ≤ a₀) (hk : 0 ≤ k) {n : ℕ} {nbar : ℝ}
    (hnbar : 0 ≤ nbar) (hn : nbar / 2 - a₀ ≤ n) :
    rateMin (fun n : ℕ ↦ rateReal a₀ k n) n ≤ 4 * rateReal a₀ k nbar / max nbar 1 :=
  rateMin_le_four_mul_div (f := rateReal a₀ k) (fun _ ↦ rfl)
    (fun _ _ hx hxy ↦ rateReal_mono hk hx hxy)
    (fun _ _ hx hxy ↦ rateReal_div_le_div (by linarith) hk (by linarith) hxy) ha₀
    (fun _ hx ↦ le_rateReal hk hx) hnbar hn

section Run

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  {H : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℕ → Ω → Policy S A H}
  {Y : ℕ → Ω → Traj S H} {M : EpisodicMDP S A} {s₁ : S} {δ : ℝ}

omit [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [MeasurableSingletonClass S] in
lemma pseudoCount_nonneg (X : ℕ → Ω → Policy S A H) (M : EpisodicMDP S A) (s₁ : S) (h : Fin H)
    (s : S) (a : A) (t : ℕ) (ω : Ω) : 0 ≤ pseudoCount X M s₁ h s a t ω :=
  sum_nonneg fun _ _ ↦ occupancy_nonneg M _ s₁ h s a

omit [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] in
/-- The pseudo-count after `t` episodes is at most `t`. -/
lemma pseudoCount_le [Countable S] (X : ℕ → Ω → Policy S A H) (M : EpisodicMDP S A) (s₁ : S)
    (h : Fin H)
    (s : S) (a : A) (t : ℕ) (ω : Ω) : pseudoCount X M s₁ h s a t ω ≤ t := by
  unfold pseudoCount
  calc ∑ i ∈ range t, occupancy M (X i ω).extend s₁ h s a ≤ ∑ _i ∈ range t, (1 : ℝ) :=
        sum_le_sum fun i _ ↦ occupancy_le_one M (X i ω).measurable_extend s₁ h s a
    _ = t := by simp

/-- Lemma 27 on the counts event, for a rate `rateReal (α^cnt(δ)) k` with `k ≥ 0`. -/
lemma rateMin_le_of_mem_eventCnt (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ω : Ω}
    (hω : ω ∈ eventCnt X Y M s₁ δ) {k : ℝ} (hk : 0 ≤ k) (h : Fin H) (s : S) (a : A) (t : ℕ) :
    rateMin (fun n : ℕ ↦ rateReal (alphaCnt (Fintype.card S) (Fintype.card A) H δ) k n)
        (visitCountAt X Y h s a t ω)
      ≤ 4 * rateReal (alphaCnt (Fintype.card S) (Fintype.card A) H δ) k t
        / max (pseudoCount X M s₁ h s a t ω) 1 := by
  have hS : 1 ≤ Fintype.card S := Fintype.card_pos_iff.2 ⟨s₁⟩
  have hA : 1 ≤ Fintype.card A := Fintype.card_pos
  have hH : 1 ≤ H := h.pos
  have ha₀ := (one_lt_alphaCnt hS hA hH hδ hδ1).le
  have hnbar := pseudoCount_nonneg X M s₁ h s a t ω
  refine (rateMin_rateReal_le ha₀ hk hnbar (hω t h s a)).trans ?_
  gcongr
  exact rateReal_mono hk hnbar (pseudoCount_le X M s₁ h s a t ω)

/-- **Lemma 27** for the KL rate on the counts event:
`min {α(n)/n, 1} ≤ 4 α(t, δ) / max {n̄_h^t(s, a), 1}`. -/
lemma klRateMinAt_le_of_mem_eventCnt (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ω : Ω}
    (hω : ω ∈ eventCnt X Y M s₁ δ) (h : Fin H) (s : S) (a : A) (t : ℕ) :
    klRateMinAt X Y δ h s a t ω
      ≤ 4 * alphaKL (Fintype.card S) (Fintype.card A) H δ t
        / max (pseudoCount X M s₁ h s a t ω) 1 := by
  rw [klRateMinAt, alphaKL_eq_fun_rateReal]
  exact rateMin_le_of_mem_eventCnt hδ hδ1 hω (Nat.cast_nonneg (Fintype.card S)) h s a t

/-- **Lemma 27** for the Bernstein rate on the counts event:
`min {α*(n)/n, 1} ≤ 4 α*(t, δ) / max {n̄_h^t(s, a), 1}`. -/
lemma starRateMinAt_le_of_mem_eventCnt (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ω : Ω}
    (hω : ω ∈ eventCnt X Y M s₁ δ) (h : Fin H) (s : S) (a : A) (t : ℕ) :
    starRateMinAt X Y δ h s a t ω
      ≤ 4 * alphaStar (Fintype.card S) (Fintype.card A) H δ t
        / max (pseudoCount X M s₁ h s a t ω) 1 := by
  rw [starRateMinAt, alphaStar_eq_fun_rateReal]
  exact rateMin_le_of_mem_eventCnt hδ hδ1 hω zero_le_one h s a t

/-- The counting argument for one triple `(h, s, a)` and a rate `rateReal (α^cnt(δ)) k`. -/
lemma sum_occupancy_mul_rateMin_le (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ω : Ω}
    (hω : ω ∈ eventCnt X Y M s₁ δ) {k : ℝ} (hk : 0 ≤ k) (h : Fin H) (s : S) (a : A) (T : ℕ) :
    ∑ t ∈ range T, occupancy M (X t ω).extend s₁ h s a
        * rateMin (fun n : ℕ ↦ rateReal (alphaCnt (Fintype.card S) (Fintype.card A) H δ) k n)
          (visitCountAt X Y h s a t ω)
      ≤ 16 * rateReal (alphaCnt (Fintype.card S) (Fintype.card A) H δ) k (T - 1 : ℕ)
        * Real.log (T + 1) := by
  set a₀ := alphaCnt (Fintype.card S) (Fintype.card A) H δ
  have hS : 1 ≤ Fintype.card S := Fintype.card_pos_iff.2 ⟨s₁⟩
  have hA : 1 ≤ Fintype.card A := Fintype.card_pos
  have hH : 1 ≤ H := h.pos
  have ha₀ : 0 ≤ a₀ := alphaCnt_nonneg hS hA hH hδ hδ1
  set u : ℕ → ℝ := fun t ↦ occupancy M (X t ω).extend s₁ h s a with hu
  have hu01 : ∀ t, u t ∈ Set.Icc 0 1 := fun t ↦
    ⟨occupancy_nonneg M _ s₁ h s a, occupancy_le_one M (X t ω).measurable_extend s₁ h s a⟩
  have hαT : 0 ≤ rateReal a₀ k (T - 1 : ℕ) :=
    ha₀.trans (le_rateReal hk (Nat.cast_nonneg _))
  have hUT : ∑ i ∈ range T, u i ≤ T := pseudoCount_le X M s₁ h s a T ω
  calc ∑ t ∈ range T, u t * rateMin (fun n : ℕ ↦ rateReal a₀ k n) (visitCountAt X Y h s a t ω)
      ≤ ∑ t ∈ range T, u t * (4 * rateReal a₀ k (T - 1 : ℕ) / max (∑ i ∈ range t, u i) 1) := by
        refine sum_le_sum fun t ht ↦ mul_le_mul_of_nonneg_left ?_ (hu01 t).1
        refine (rateMin_le_of_mem_eventCnt hδ hδ1 hω hk h s a t).trans ?_
        have htT : t ≤ T - 1 := Nat.le_sub_one_of_lt (mem_range.1 ht)
        gcongr
        · exact rateReal_mono hk (Nat.cast_nonneg _) (by exact_mod_cast htT)
        · exact le_rfl
    _ = 4 * rateReal a₀ k (T - 1 : ℕ) * ∑ t ∈ range T, u t / max (∑ i ∈ range t, u i) 1 := by
        rw [mul_sum]
        refine sum_congr rfl fun t _ ↦ ?_
        ring
    _ ≤ 4 * rateReal a₀ k (T - 1 : ℕ) * (4 * Real.log (∑ i ∈ range T, u i + 1)) := by
        gcongr
        exact Real.sum_div_max_one_le_four_mul_log hu01 T
    _ ≤ 4 * rateReal a₀ k (T - 1 : ℕ) * (4 * Real.log (T + 1)) := by
        gcongr
        · have := sum_nonneg fun i (_ : i ∈ range T) ↦ (hu01 i).1
          linarith
    _ = 16 * rateReal a₀ k (T - 1 : ℕ) * Real.log (T + 1) := by ring

/-- The counting argument summed over the triples `(h, s, a)`, for a rate
`rateReal (α^cnt(δ)) k`. -/
lemma sum_sum_occupancy_mul_rateMin_le (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ω : Ω}
    (hω : ω ∈ eventCnt X Y M s₁ δ) {k : ℝ} (hk : 0 ≤ k) (T : ℕ) :
    ∑ t ∈ range T, ∑ h : Fin H, ∑ s, ∑ a, occupancy M (X t ω).extend s₁ h s a
        * rateMin (fun n : ℕ ↦ rateReal (alphaCnt (Fintype.card S) (Fintype.card A) H δ) k n)
          (visitCountAt X Y h s a t ω)
      ≤ 16 * (Fintype.card S * Fintype.card A * H)
        * rateReal (alphaCnt (Fintype.card S) (Fintype.card A) H δ) k (T - 1 : ℕ)
        * Real.log (T + 1) := by
  rw [sum_comm]
  calc ∑ h : Fin H, ∑ t ∈ range T, ∑ s, ∑ a, occupancy M (X t ω).extend s₁ h s a
        * rateMin (fun n : ℕ ↦ rateReal (alphaCnt (Fintype.card S) (Fintype.card A) H δ) k n)
          (visitCountAt X Y h s a t ω)
      = ∑ h : Fin H, ∑ s, ∑ a, ∑ t ∈ range T, occupancy M (X t ω).extend s₁ h s a
        * rateMin (fun n : ℕ ↦ rateReal (alphaCnt (Fintype.card S) (Fintype.card A) H δ) k n)
          (visitCountAt X Y h s a t ω) := by
        refine sum_congr rfl fun h _ ↦ ?_
        rw [sum_comm]
        exact sum_congr rfl fun s _ ↦ sum_comm
    _ ≤ ∑ _h : Fin H, ∑ _s : S, ∑ _a : A,
        16 * rateReal (alphaCnt (Fintype.card S) (Fintype.card A) H δ) k (T - 1 : ℕ)
          * Real.log (T + 1) :=
        sum_le_sum fun h _ ↦ sum_le_sum fun s _ ↦ sum_le_sum fun a _ ↦
          sum_occupancy_mul_rateMin_le hδ hδ1 hω hk h s a T
    _ = 16 * (Fintype.card S * Fintype.card A * H)
        * rateReal (alphaCnt (Fintype.card S) (Fintype.card A) H δ) k (T - 1 : ℕ)
        * Real.log (T + 1) := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **The counting argument** for the KL rate on the counts event:
`∑_{t < T} ∑_{h, s, a} p^{π^{t+1}}_h(s, a) min {α(n_h^t(s, a))/n_h^t(s, a), 1}
≤ 16 S A H α(T - 1, δ) log(T + 1)`. -/
lemma sum_occupancy_mul_klRateMinAt_le (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ω : Ω}
    (hω : ω ∈ eventCnt X Y M s₁ δ) (T : ℕ) :
    ∑ t ∈ range T, ∑ h : Fin H, ∑ s, ∑ a,
        occupancy M (X t ω).extend s₁ h s a * klRateMinAt X Y δ h s a t ω
      ≤ 16 * (Fintype.card S * Fintype.card A * H)
        * alphaKL (Fintype.card S) (Fintype.card A) H δ (T - 1) * Real.log (T + 1) := by
  simp only [klRateMinAt, alphaKL_eq_fun_rateReal]
  exact sum_sum_occupancy_mul_rateMin_le hδ hδ1 hω (Nat.cast_nonneg (Fintype.card S)) T

/-- **The counting argument** for the Bernstein rate on the counts event:
`∑_{t < T} ∑_{h, s, a} p^{π^{t+1}}_h(s, a) min {α*(n_h^t(s, a))/n_h^t(s, a), 1}
≤ 16 S A H α*(T - 1, δ) log(T + 1)`. -/
lemma sum_occupancy_mul_starRateMinAt_le (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ω : Ω}
    (hω : ω ∈ eventCnt X Y M s₁ δ) (T : ℕ) :
    ∑ t ∈ range T, ∑ h : Fin H, ∑ s, ∑ a,
        occupancy M (X t ω).extend s₁ h s a * starRateMinAt X Y δ h s a t ω
      ≤ 16 * (Fintype.card S * Fintype.card A * H)
        * alphaStar (Fintype.card S) (Fintype.card A) H δ (T - 1) * Real.log (T + 1) := by
  simp only [starRateMinAt, alphaStar_eq_fun_rateReal]
  exact sum_sum_occupancy_mul_rateMin_le hδ hδ1 hω zero_le_one T

end Run

end Essakine2026Tight
