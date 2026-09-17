/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.EV2026.Backups
public import Essakine2026Tight.EV2026.Run
public import Essakine2026Tight.EV2026.RateBounds
public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Values
public import Essakine2026Tight.Mathlib.InformationTheory.KLBernstein
public import Essakine2026Tight.Mathlib.MeasureTheory.Measure.WeightedProbability

/-!
# Analysis of Entropic-BPI: sign-independent lemmas

* Probability vectors of measures: the expectation and the variance of a function under a
  probability measure on a finite type are `vecExp` and `vecVar` of its vector of point masses
  (`integral_eq_vecExp_of_measureReal`, `variance_eq_vecVar_of_measureReal`).
* The KL–Bernstein inequality, the variance transport inequalities and the bound
  `Var_p(f) ≤ b p f` for probability vectors and functions with values in `[c, c + b]`
  (`abs_vecExp_sub_le_of_klDiv_le`, `vecVar_le_two_mul_vecVar_add_of_klDiv_le`, …).
* The sign-independent cores of the analysis (Essakine, Vernade 2026, Lemmas 7, 11, 12, 16 and
  the certificate recursion under the true kernel), stated for arbitrary probability vectors:
  `abs_vecExp_sub_le_bonus_add` (concentration of the optimal value),
  `vecExp_sub_vecExp_le_of_klDiv_le` (the third term of Lemmas 11 and 16),
  `vecExp_le_one_add_mul_vecExp_add` (step (i) of the recursion),
  `bonusTerm_le_of_klDiv_le` (step (ii)) and `three_mul_add_le` (step (iii)).
* The good event at a history (`HistConcentration`): the KL inequality for every triple and the
  Bernstein inequality for the optimal exponential values, and its consequence for the histories
  of a run on `goodEvent` (`histConcentration_histAt`).
* Recursion equations of the certificate and the ring value at a step `h : Fin H` in terms of
  the values with `H - 1 - h` steps to go (`cert_sub_eq`, `ringZ_sub_eq`), the bonus with real
  numerals (`bonus_of_pos`, `bonus_of_not_pos`) and the truncated rates (`rateMin_eq_div`,
  `rateMin_eq_one`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP.Episodic Learning.MDP
  InformationTheory
open scoped ENNReal

namespace Essakine2026Tight

/-! ### Probability vectors of measures on a finite type -/

section Vectors

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- The integral under a finite measure on a finite type is the `vecExp` of its point masses. -/
lemma integral_eq_vecExp_of_measureReal (ν : Measure S) [IsFiniteMeasure ν] {q : S → ℝ}
    (hq : ∀ s, ν.real {s} = q s) (f : S → ℝ) : ∫ x, f x ∂ν = vecExp q f := by
  rw [integral_fintype Integrable.of_finite]
  simp [vecExp, hq]

/-- The variance under a probability measure on a finite type is the `vecVar` of its point
masses. -/
lemma variance_eq_vecVar_of_measureReal (ν : Measure S) [IsProbabilityMeasure ν] {q : S → ℝ}
    (hq : ∀ s, ν.real {s} = q s) (f : S → ℝ) : variance f ν = vecVar q f := by
  have hq1 : ∑ s, q s = 1 := by
    simp_rw [← hq]
    rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]
  rw [variance_eq_integral (measurable_of_countable f).aemeasurable, vecVar_eq_sum_sq hq1,
    integral_fintype Integrable.of_finite, integral_eq_vecExp_of_measureReal ν hq]
  simp [hq]

omit [MeasurableSingletonClass S] in
/-- The point masses of a probability measure on a finite type sum to one. -/
lemma sum_measureReal_eq_one {ν : Measure S} [IsProbabilityMeasure ν] [MeasurableSingletonClass S]
    {q : S → ℝ} (hq : ∀ s, ν.real {s} = q s) : ∑ s, q s = 1 := by
  simp_rw [← hq]
  rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- Shifting a function by a constant shifts its expectation under a probability vector. -/
lemma vecExp_sub_const {p : S → ℝ} (hp1 : ∑ s, p s = 1) (f : S → ℝ) (c : ℝ) :
    vecExp p (fun s ↦ f s - c) = vecExp p f - c := by
  have := vecExp_sub p f (fun _ ↦ c)
  rw [vecExp_const, hp1, one_mul] at this
  exact this

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- The variance under a probability vector is invariant under a constant shift. -/
lemma vecVar_sub_const {p : S → ℝ} (hp1 : ∑ s, p s = 1) (f : S → ℝ) (c : ℝ) :
    vecVar p (fun s ↦ f s - c) = vecVar p f := by
  rw [vecVar_eq_sum_sq hp1, vecVar_eq_sum_sq hp1, vecExp_sub_const hp1]
  exact sum_congr rfl fun s _ ↦ by ring

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- A constant has zero variance under a probability vector. -/
lemma vecVar_const {p : S → ℝ} (hp1 : ∑ s, p s = 1) (c : ℝ) : vecVar p (fun _ ↦ c) = 0 := by
  rw [vecVar_eq_sum_sq hp1, vecExp_const, hp1, one_mul]
  simp

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- `p|f - g| = p f - p g` when `g ≤ f` pointwise. -/
lemma vecExp_abs_sub_eq_of_le (p : S → ℝ) {f g : S → ℝ} (hfg : ∀ s, g s ≤ f s) :
    vecExp p (fun s ↦ |f s - g s|) = vecExp p f - vecExp p g := by
  rw [← vecExp_sub]
  congr 1
  funext s
  simp [abs_of_nonneg (sub_nonneg.2 (hfg s))]

variable {p q : S → ℝ} {ν : Measure S} [IsProbabilityMeasure ν] {a b c : ℝ} {f g : S → ℝ}

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [IsProbabilityMeasure ν] in
/-- A function with values in `[c, c + 0]` is constant. -/
lemma eq_const_of_mem_Icc_add_zero (hf : ∀ s, f s ∈ Set.Icc c (c + 0)) : f = fun _ ↦ c :=
  funext fun s ↦ le_antisymm (by simpa using (hf s).2) (hf s).1

/-- **KL–Bernstein inequality for probability vectors**: if `KL(p ‖ ν) ≤ a`, `q` is the vector of
`ν` and `f` has values in `[c, c + b]`, then `|p f - q f| ≤ √(2 Var_q(f) a) + (2/3) b a`. -/
lemma abs_vecExp_sub_le_of_klDiv_le (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (hq : ∀ s, ν.real {s} = q s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hf : ∀ s, f s ∈ Set.Icc c (c + b))
    (hkl : klDiv (weightedMeasure p) ν ≤ ENNReal.ofReal a) :
    |vecExp p f - vecExp q f| ≤ √(2 * vecVar q f * a) + 2 / 3 * b * a := by
  have hq1 := sum_measureReal_eq_one hq
  rcases hb.eq_or_lt with rfl | hb
  · rw [eq_const_of_mem_Icc_add_zero hf, vecExp_const, vecExp_const, hp1, hq1]
    simp only [sub_self, abs_zero]
    positivity
  have := isProbabilityMeasure_weightedMeasure hp hp1
  have hpw : ∀ s, (weightedMeasure p).real {s} = p s := measureReal_weightedMeasure_singleton hp
  have hg : ∀ᵐ x ∂ν, f x - c ∈ Set.Icc 0 b :=
    Filter.Eventually.of_forall fun s ↦ ⟨by linarith [(hf s).1], by linarith [(hf s).2]⟩
  have h := abs_integral_sub_integral_le_of_klDiv_le (μ := weightedMeasure p) (ν := ν)
    (f := fun s ↦ f s - c) hb ha hg (measurable_of_countable _).aestronglyMeasurable hkl
  rw [integral_eq_vecExp_of_measureReal _ hpw, integral_eq_vecExp_of_measureReal _ hq,
    variance_eq_vecVar_of_measureReal _ hq, vecExp_sub_const hp1, vecExp_sub_const hq1,
    vecVar_sub_const hq1] at h
  simpa using h

/-- **Variance transport under a KL constraint for probability vectors**: if `KL(p ‖ ν) ≤ a` and
`f` has values in `[c, c + b]`, then `Var_q(f) ≤ 2 Var_p(f) + 4 b² a`. -/
lemma vecVar_le_two_mul_vecVar_add_of_klDiv_le (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (hq : ∀ s, ν.real {s} = q s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hf : ∀ s, f s ∈ Set.Icc c (c + b))
    (hkl : klDiv (weightedMeasure p) ν ≤ ENNReal.ofReal a) :
    vecVar q f ≤ 2 * vecVar p f + 4 * b ^ 2 * a := by
  have hq1 := sum_measureReal_eq_one hq
  rcases hb.eq_or_lt with rfl | hb
  · rw [eq_const_of_mem_Icc_add_zero hf, vecVar_const hq1, vecVar_const hp1]
    simp
  have := isProbabilityMeasure_weightedMeasure hp hp1
  have hpw : ∀ s, (weightedMeasure p).real {s} = p s := measureReal_weightedMeasure_singleton hp
  have hg : ∀ᵐ x ∂ν, f x - c ∈ Set.Icc 0 b :=
    Filter.Eventually.of_forall fun s ↦ ⟨by linarith [(hf s).1], by linarith [(hf s).2]⟩
  have h := variance_le_two_mul_variance_add_of_klDiv_le (μ := weightedMeasure p) (ν := ν)
    (f := fun s ↦ f s - c) hb ha hg (measurable_of_countable _).aestronglyMeasurable hkl
  rwa [variance_eq_vecVar_of_measureReal _ hq, variance_eq_vecVar_of_measureReal _ hpw,
    vecVar_sub_const hp1, vecVar_sub_const hq1] at h

/-- **Variance transport under a KL constraint for probability vectors**, the other direction:
if `KL(p ‖ ν) ≤ a` and `f` has values in `[c, c + b]`, then `Var_p(f) ≤ 2 Var_q(f) + 4 b² a`. -/
lemma vecVar_le_two_mul_vecVar_add_of_klDiv_le' (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (hq : ∀ s, ν.real {s} = q s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hf : ∀ s, f s ∈ Set.Icc c (c + b))
    (hkl : klDiv (weightedMeasure p) ν ≤ ENNReal.ofReal a) :
    vecVar p f ≤ 2 * vecVar q f + 4 * b ^ 2 * a := by
  have hq1 := sum_measureReal_eq_one hq
  rcases hb.eq_or_lt with rfl | hb
  · rw [eq_const_of_mem_Icc_add_zero hf, vecVar_const hq1, vecVar_const hp1]
    simp
  have := isProbabilityMeasure_weightedMeasure hp hp1
  have hpw : ∀ s, (weightedMeasure p).real {s} = p s := measureReal_weightedMeasure_singleton hp
  have hg : ∀ᵐ x ∂ν, f x - c ∈ Set.Icc 0 b :=
    Filter.Eventually.of_forall fun s ↦ ⟨by linarith [(hf s).1], by linarith [(hf s).2]⟩
  have h := variance_le_two_mul_variance_add_of_klDiv_le' (μ := weightedMeasure p) (ν := ν)
    (f := fun s ↦ f s - c) hb ha hg (measurable_of_countable _).aestronglyMeasurable hkl
  rwa [variance_eq_vecVar_of_measureReal _ hq, variance_eq_vecVar_of_measureReal _ hpw,
    vecVar_sub_const hp1, vecVar_sub_const hq1] at h

omit [MeasurableSpace S] [MeasurableSingletonClass S] [IsProbabilityMeasure ν] in
/-- Transport of the variance between two functions with values in `[c, c + b]` under a
probability vector: `Var_p(f) ≤ 2 Var_p(g) + 2 b p|f - g|`. -/
lemma vecVar_le_two_mul_vecVar_add (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (hf : ∀ s, f s ∈ Set.Icc c (c + b)) (hg : ∀ s, g s ∈ Set.Icc c (c + b)) :
    vecVar p f ≤ 2 * vecVar p g + 2 * b * vecExp p (fun s ↦ |f s - g s|) := by
  let _ : MeasurableSpace S := ⊤
  have : MeasurableSingletonClass S := ⟨fun _ ↦ trivial⟩
  have := isProbabilityMeasure_weightedMeasure hp hp1
  have hpw : ∀ s, (weightedMeasure p).real {s} = p s := measureReal_weightedMeasure_singleton hp
  have h := variance_le_two_mul_variance_add (μ := weightedMeasure p) (b := b)
    (f := fun s ↦ f s - c) (g := fun s ↦ g s - c)
    (Filter.Eventually.of_forall fun s ↦ ⟨by linarith [(hf s).1], by linarith [(hf s).2]⟩)
    (Filter.Eventually.of_forall fun s ↦ ⟨by linarith [(hg s).1], by linarith [(hg s).2]⟩)
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aestronglyMeasurable
  rw [variance_eq_vecVar_of_measureReal _ hpw, variance_eq_vecVar_of_measureReal _ hpw,
    integral_eq_vecExp_of_measureReal _ hpw, vecVar_sub_const hp1, vecVar_sub_const hp1] at h
  simpa using h

omit [MeasurableSpace S] [MeasurableSingletonClass S] [IsProbabilityMeasure ν] in
/-- `Var_p(f) ≤ b p f` for a probability vector `p` and `f` with values in `[0, b]`. -/
lemma vecVar_le_mul_vecExp (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (hf : ∀ s, f s ∈ Set.Icc 0 b) : vecVar p f ≤ b * vecExp p f := by
  let _ : MeasurableSpace S := ⊤
  have : MeasurableSingletonClass S := ⟨fun _ ↦ trivial⟩
  have := isProbabilityMeasure_weightedMeasure hp hp1
  have hpw : ∀ s, (weightedMeasure p).real {s} = p s := measureReal_weightedMeasure_singleton hp
  have h := variance_le_mul_integral (μ := weightedMeasure p) (Filter.Eventually.of_forall hf)
    (measurable_of_countable _).aestronglyMeasurable
  rwa [variance_eq_vecVar_of_measureReal _ hpw, integral_eq_vecExp_of_measureReal _ hpw] at h

end Vectors

/-! ### Sign-independent cores of the analysis -/

section Cores

/-- `√2 ≤ 3/2`. -/
lemma sqrt_two_le_three_halves : √2 ≤ 3 / 2 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

/-- `(√2)² = 2`. -/
lemma sq_sqrt_two : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

/-- `√a ≤ x + y` for `x, y ≥ 0` and `a ≤ x² + y²`. -/
lemma sqrt_le_add_of_le_sq_add_sq {a x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : a ≤ x ^ 2 + y ^ 2) : √a ≤ x + y := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [mul_nonneg hx hy]

/-- `√a ≤ x + y + z` for `x, y, z ≥ 0` and `a ≤ x² + y² + z²`. -/
lemma sqrt_le_add_add_of_le_sq_add_sq_add_sq {a x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (h : a ≤ x ^ 2 + y ^ 2 + z ^ 2) : √a ≤ x + y + z := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz]

/-- The AM–GM inequality `4 u v ≤ (u + v)²`. -/
lemma four_mul_mul_le_sq_add (u v : ℝ) : 4 * u * v ≤ (u + v) ^ 2 := by
  nlinarith [sq_nonneg (u - v)]

/-- `4 (x / H) (y H) = 4 x y` for `H > 0`: the product of the two terms of the AM–GM splitting. -/
lemma four_mul_div_mul_mul {x y H : ℝ} (hH : 0 < H) : 4 * (x / H) * (y * H) = 4 * x * y := by
  field_simp

variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {p q : S → ℝ} {ν : Measure S} [IsProbabilityMeasure ν] {αn αs B c H : ℝ}

/-- **Concentration of the optimal value** (the core of Lemmas 7 and 12 of Essakine, Vernade
2026): if `KL(p ‖ ν) ≤ αn`, `q` is the vector of `ν`, `f` and `g` have values in `[c, c + B]` and
`f` satisfies the Bernstein inequality `|p f - q f| ≤ √(2 Var_q(f) αs) + 3 B αs` with
`0 ≤ αs ≤ αn`, then
`|p f - q f| ≤ 2 √2 √(Var_p(g) αs) + 5 B αn + 4 H B αn + (1/H) p|g - f|` for `H ≥ 1`. -/
lemma abs_vecExp_sub_le_bonus_add (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (hq : ∀ s, ν.real {s} = q s) (hαs : 0 ≤ αs) (hαsn : αs ≤ αn) (hB : 0 ≤ B) (hH : 1 ≤ H)
    {f g : S → ℝ} (hf : ∀ s, f s ∈ Set.Icc c (c + B)) (hg : ∀ s, g s ∈ Set.Icc c (c + B))
    (hkl : klDiv (weightedMeasure p) ν ≤ ENNReal.ofReal αn)
    (hbern : |vecExp p f - vecExp q f| ≤ √(2 * vecVar q f * αs) + 3 * B * αs) :
    |vecExp p f - vecExp q f|
      ≤ 2 * √2 * √(vecVar p g * αs) + 5 * B * αn + 4 * H * B * αn
        + 1 / H * vecExp p (fun s ↦ |g s - f s|) := by
  have hαn : 0 ≤ αn := hαs.trans hαsn
  have h1 := vecVar_le_two_mul_vecVar_add_of_klDiv_le hp hp1 hq hαn hB hf hkl
  have h2 := vecVar_le_two_mul_vecVar_add hp hp1 hf hg
  have hD' : vecExp p (fun s ↦ |f s - g s|) = vecExp p (fun s ↦ |g s - f s|) := by
    simp_rw [abs_sub_comm]
  rw [hD'] at h2
  have hD0 : 0 ≤ vecExp p (fun s ↦ |g s - f s|) := vecExp_nonneg hp fun s ↦ abs_nonneg _
  have hVg : 0 ≤ vecVar p g := vecVar_nonneg hp hp1
  have hHpos : 0 < H := by linarith
  have hs2 := sq_sqrt_two
  have hs := sqrt_two_le_three_halves
  have hsqrt : √(2 * vecVar q f * αs)
      ≤ 2 * √2 * √(vecVar p g * αs)
        + (vecExp p (fun s ↦ |g s - f s|) / H + 2 * B * αs * H) + 2 * √2 * B * αn := by
    refine sqrt_le_add_add_of_le_sq_add_sq_add_sq (by positivity) (by positivity)
      (by positivity) ?_
    have ha1sq : (2 * √2 * √(vecVar p g * αs)) ^ 2 = 8 * (vecVar p g * αs) := by
      rw [mul_pow, mul_pow, hs2, Real.sq_sqrt (by positivity)]
      ring
    have ha2sq := four_mul_mul_le_sq_add (vecExp p (fun s ↦ |g s - f s|) / H)
      (2 * B * αs * H)
    rw [four_mul_div_mul_mul hHpos] at ha2sq
    have ha3sq : (2 * √2 * B * αn) ^ 2 = 8 * B ^ 2 * αn ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, hs2]
      ring
    have hv : vecVar q f ≤ 4 * vecVar p g + 4 * B * vecExp p (fun s ↦ |g s - f s|)
        + 4 * B ^ 2 * αn := by linarith
    have hv' := mul_le_mul_of_nonneg_right hv (by positivity : 0 ≤ 2 * αs)
    have hαα : B ^ 2 * αn * αs ≤ B ^ 2 * αn * αn :=
      mul_le_mul_of_nonneg_left hαsn (by positivity)
    rw [ha1sq, ha3sq]
    nlinarith
  have hlast : 2 * B * αs * H + 2 * √2 * B * αn + 3 * B * αs
      ≤ 5 * B * αn + 4 * H * B * αn := by
    have e1 : B * αs * H ≤ B * αn * H :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαsn hB) hHpos.le
    have e2 : B * αs ≤ B * αn := mul_le_mul_of_nonneg_left hαsn hB
    have e3 : √2 * (B * αn) ≤ 3 / 2 * (B * αn) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    have e4 : B * αn ≤ B * αn * H := le_mul_of_one_le_right (by positivity) hH
    nlinarith
  have hDH : vecExp p (fun s ↦ |g s - f s|) / H = 1 / H * vecExp p (fun s ↦ |g s - f s|) := by
    ring
  linarith

/-- **The third term of Lemmas 11 and 16** (Essakine, Vernade 2026): if `KL(p ‖ ν) ≤ αn`, `q` is
the vector of `ν` and `f` has values in `[0, B]`, then
`q f - p f ≤ (1/H) p f + (5 + 4 H) B αn` for `H ≥ 1`. -/
lemma vecExp_sub_vecExp_le_of_klDiv_le (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (hq : ∀ s, ν.real {s} = q s) (hαn : 0 ≤ αn) (hB : 0 ≤ B) (hH : 1 ≤ H) {f : S → ℝ}
    (hf : ∀ s, f s ∈ Set.Icc 0 B) (hkl : klDiv (weightedMeasure p) ν ≤ ENNReal.ofReal αn) :
    vecExp q f - vecExp p f ≤ 1 / H * vecExp p f + (5 + 4 * H) * B * αn := by
  have hf' : ∀ s, f s ∈ Set.Icc 0 (0 + B) := by simpa using hf
  have h1 := abs_vecExp_sub_le_of_klDiv_le hp hp1 hq hαn hB hf' hkl
  have h2 := vecVar_le_two_mul_vecVar_add_of_klDiv_le hp hp1 hq hαn hB hf' hkl
  have h3 := vecVar_le_mul_vecExp hp hp1 hf
  have hpf : 0 ≤ vecExp p f := vecExp_nonneg hp fun s ↦ (hf s).1
  have hHpos : 0 < H := by linarith
  have hs2 := sq_sqrt_two
  have hs := sqrt_two_le_three_halves
  have hsqrt : √(2 * vecVar q f * αn)
      ≤ (vecExp p f / H + B * αn * H) + 2 * √2 * B * αn := by
    refine sqrt_le_add_of_le_sq_add_sq (by positivity) (by positivity) ?_
    have ha1sq := four_mul_mul_le_sq_add (vecExp p f / H) (B * αn * H)
    rw [four_mul_div_mul_mul hHpos] at ha1sq
    have ha2sq : (2 * √2 * B * αn) ^ 2 = 8 * B ^ 2 * αn ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, hs2]
      ring
    have hv : vecVar q f ≤ 2 * (B * vecExp p f) + 4 * B ^ 2 * αn := by linarith
    have hv' := mul_le_mul_of_nonneg_right hv (by positivity : 0 ≤ 2 * αn)
    rw [ha2sq]
    nlinarith
  have habs := (abs_le.1 (h1.trans (add_le_add_left hsqrt _))).1
  have hc : B * αn * H + 2 * √2 * B * αn + 2 / 3 * B * αn ≤ (5 + 4 * H) * B * αn := by
    have e3 : √2 * (B * αn) ≤ 3 / 2 * (B * αn) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    have e4 : 0 ≤ B * αn * H := by positivity
    nlinarith
  have hDH : vecExp p f / H = 1 / H * vecExp p f := by ring
  linarith

/-- **Step (i) of the certificate recursion under the true kernel** (Essakine, Vernade 2026): if
`KL(p ‖ ν) ≤ αn`, `q` is the vector of `ν` and `g` has values in `[0, B]`, then
`p g ≤ (1 + 1/H) q g + 2 H B αn` for `H ≥ 1`. -/
lemma vecExp_le_one_add_mul_vecExp_add (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (hq : ∀ s, ν.real {s} = q s) (hαn : 0 ≤ αn) (hB : 0 ≤ B) (hH : 1 ≤ H) {g : S → ℝ}
    (hg : ∀ s, g s ∈ Set.Icc 0 B) (hkl : klDiv (weightedMeasure p) ν ≤ ENNReal.ofReal αn) :
    vecExp p g ≤ (1 + 1 / H) * vecExp q g + 2 * H * B * αn := by
  have hq0 : ∀ s, 0 ≤ q s := fun s ↦ (hq s) ▸ measureReal_nonneg
  have hq1 := sum_measureReal_eq_one hq
  have hg' : ∀ s, g s ∈ Set.Icc 0 (0 + B) := by simpa using hg
  have h1 := abs_vecExp_sub_le_of_klDiv_le hp hp1 hq hαn hB hg' hkl
  have h3 := vecVar_le_mul_vecExp hq0 hq1 hg
  have hqg : 0 ≤ vecExp q g := vecExp_nonneg hq0 fun s ↦ (hg s).1
  have hHpos : 0 < H := by linarith
  have hsqrt : √(2 * vecVar q g * αn) ≤ vecExp q g / H + B * αn / 2 * H := by
    rw [Real.sqrt_le_left (by positivity)]
    have ha1sq := four_mul_mul_le_sq_add (vecExp q g / H) (B * αn / 2 * H)
    rw [four_mul_div_mul_mul hHpos] at ha1sq
    have hv' := mul_le_mul_of_nonneg_right h3 (by positivity : 0 ≤ 2 * αn)
    nlinarith
  have habs := (abs_le.1 (h1.trans (add_le_add_left hsqrt _))).2
  have hc : B * αn / 2 * H + 2 / 3 * B * αn ≤ 2 * H * B * αn := by
    have e4 : B * αn ≤ B * αn * H := le_mul_of_one_le_right (by positivity) hH
    nlinarith
  have hDH : vecExp q g / H = 1 / H * vecExp q g := by ring
  nlinarith

/-- **Step (ii) of the certificate recursion under the true kernel** (Essakine, Vernade 2026): if
`KL(p ‖ ν) ≤ αn`, `q` is the vector of `ν`, `G` and `Z` have values in `[c, c + B]`,
`q|G - Z| ≤ Δ` and `0 ≤ αs ≤ αn`, then the bonus-shaped quantity
`2 √2 √(Var_p(G) αs) + 5 B αn + 4 H B αn` is at most `6 √(Var_q(Z) αs) + Δ/H + 23 H B αn` for
`H ≥ 1`. -/
lemma bonusTerm_le_of_klDiv_le (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (hq : ∀ s, ν.real {s} = q s) (hαs : 0 ≤ αs) (hαsn : αs ≤ αn) (hB : 0 ≤ B) (hH : 1 ≤ H)
    {G Z : S → ℝ} (hG : ∀ s, G s ∈ Set.Icc c (c + B)) (hZ : ∀ s, Z s ∈ Set.Icc c (c + B))
    {Δ : ℝ} (hΔ : vecExp q (fun s ↦ |G s - Z s|) ≤ Δ)
    (hkl : klDiv (weightedMeasure p) ν ≤ ENNReal.ofReal αn) :
    2 * √2 * √(vecVar p G * αs) + 5 * B * αn + 4 * H * B * αn
      ≤ 6 * √(vecVar q Z * αs) + 1 / H * Δ + 23 * H * B * αn := by
  have hq0 : ∀ s, 0 ≤ q s := fun s ↦ (hq s) ▸ measureReal_nonneg
  have hq1 := sum_measureReal_eq_one hq
  have hαn : 0 ≤ αn := hαs.trans hαsn
  have h1 := vecVar_le_two_mul_vecVar_add_of_klDiv_le' hp hp1 hq hαn hB hG hkl
  have h2 := vecVar_le_two_mul_vecVar_add hq0 hq1 hG hZ
  have hD0 : 0 ≤ vecExp q (fun s ↦ |G s - Z s|) := vecExp_nonneg hq0 fun s ↦ abs_nonneg _
  have hΔ0 : 0 ≤ Δ := hD0.trans hΔ
  have hVZ : 0 ≤ vecVar q Z := vecVar_nonneg hq0 hq1
  have hVG : 0 ≤ vecVar p G := vecVar_nonneg hp hp1
  have hHpos : 0 < H := by linarith
  have hs2 := sq_sqrt_two
  have hs := sqrt_two_le_three_halves
  have hsqrt : 2 * √2 * √(vecVar p G * αs)
      ≤ 6 * √(vecVar q Z * αs) + (Δ / H + 8 * B * αs * H) + 4 * √2 * B * αn := by
    have e : 2 * √2 * √(vecVar p G * αs) = √(8 * (vecVar p G * αs)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8) (vecVar p G * αs)]
      congr 1
      rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num) 2,
        Real.sqrt_sq (by norm_num)]
    rw [e]
    refine sqrt_le_add_add_of_le_sq_add_sq_add_sq (by positivity) (by positivity)
      (by positivity) ?_
    have ha1sq : (6 * √(vecVar q Z * αs)) ^ 2 = 36 * (vecVar q Z * αs) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    have ha2sq := four_mul_mul_le_sq_add (Δ / H) (8 * B * αs * H)
    rw [four_mul_div_mul_mul hHpos] at ha2sq
    have ha3sq : (4 * √2 * B * αn) ^ 2 = 32 * B ^ 2 * αn ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, hs2]
      ring
    have hB' : B * vecExp q (fun s ↦ |G s - Z s|) ≤ B * Δ := mul_le_mul_of_nonneg_left hΔ hB
    have hv : vecVar p G ≤ 4 * vecVar q Z + 4 * (B * Δ) + 4 * B ^ 2 * αn := by linarith
    have hv' := mul_le_mul_of_nonneg_right hv (by positivity : 0 ≤ 8 * αs)
    have hαα : B ^ 2 * αn * αs ≤ B ^ 2 * αn * αn :=
      mul_le_mul_of_nonneg_left hαsn (by positivity)
    have hVZs : 0 ≤ vecVar q Z * αs := by positivity
    rw [ha1sq, ha3sq]
    nlinarith
  have hc : 8 * B * αs * H + 4 * √2 * B * αn + 5 * B * αn + 4 * H * B * αn
      ≤ 23 * H * B * αn := by
    have e1 : B * αs * H ≤ B * αn * H :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαsn hB) hHpos.le
    have e3 : √2 * (B * αn) ≤ 3 / 2 * (B * αn) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    have e4 : B * αn ≤ B * αn * H := le_mul_of_one_le_right (by positivity) hH
    nlinarith
  have hDH : Δ / H = 1 / H * Δ := by ring
  linarith

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [IsProbabilityMeasure ν] in
/-- **Step (iii) of the certificate recursion under the true kernel**: the arithmetic combining
`b ≤ 6 σ + Δ/H + 23 H B ρ` and `ĝ ≤ (1 + 1/H) Δ + 2 H B' ρ` into
`3 b + (1 + 3/H) ĝ ≤ 36 σ + (1 + 13/H) Δ + 84 H C ρ` for `B, B' ≤ C` and `H ≥ 1`. -/
lemma three_mul_add_le {b ghat σ Δ ρ B' C : ℝ} (hH : 1 ≤ H) (hσ : 0 ≤ σ) (hΔ : 0 ≤ Δ)
    (hρ : 0 ≤ ρ) (hB' : 0 ≤ B') (hBC : B ≤ C) (hB'C : B' ≤ C)
    (hb : b ≤ 6 * σ + 1 / H * Δ + 23 * H * B * ρ)
    (hg : ghat ≤ (1 + 1 / H) * Δ + 2 * H * B' * ρ) :
    3 * b + (1 + 3 / H) * ghat ≤ 36 * σ + (1 + 13 / H) * Δ + 84 * H * C * ρ := by
  have hHpos : 0 < H := by linarith
  set u := 1 / H with hu
  have hinv : u ≤ 1 := by rw [hu, div_le_one hHpos]; exact hH
  have hinv0 : 0 ≤ u := by positivity
  have hHu : H * u = 1 := by rw [hu]; field_simp
  have e6 : 13 / H = 13 * u := by rw [hu]; ring
  have e7 : 3 / H = 3 * u := by rw [hu]; ring
  rw [e6, e7] at *
  have h3H : 0 ≤ 1 + 3 * u := by positivity
  have e1 : (1 + 3 * u) * ghat ≤ (1 + 3 * u) * ((1 + u) * Δ + 2 * H * B' * ρ) :=
    mul_le_mul_of_nonneg_left hg h3H
  have e3 : u * u * Δ ≤ u * Δ := by
    have := mul_le_mul_of_nonneg_right hinv (by positivity : 0 ≤ u * Δ)
    nlinarith
  have e4 : B' * ρ ≤ H * B' * ρ := by
    have := mul_le_mul_of_nonneg_right hH (by positivity : 0 ≤ B' * ρ)
    nlinarith
  have e5 : H * B * ρ ≤ H * C * ρ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBC hHpos.le) hρ
  have e5' : H * B' * ρ ≤ H * C * ρ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB'C hHpos.le) hρ
  have e8 : (1 + 3 * u) * (2 * H * B' * ρ) = 2 * H * B' * ρ + 6 * (H * u) * B' * ρ := by ring
  rw [hHu] at e8
  nlinarith

end Cores

/-! ### The good event at a history -/

section History

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]
  {H : ℕ}

/-- The range parameter `B_h` of the Bernstein event at the step `h` (with `H - 1 - h` steps after
it): `e^{β (H - 1 - h)}` if `β > 0`, `1 - e^{β (H - 1 - h)}` otherwise. -/
noncomputable def bernRange (H : ℕ) (β : ℝ) (h : Fin H) : ℝ :=
  if 0 < β then Real.exp (β * (H - 1 - h : ℕ)) else 1 - Real.exp (β * (H - 1 - h : ℕ))

/-- The concentration inequalities of the good event at the history `hist`: the KL inequality
for every step and pair, and the Bernstein inequality for the optimal exponential values at every
visited pair. -/
structure HistConcentration (M : EpisodicMDP S A) (β δ : ℝ) {t : ℕ}
    (hist : Hist Unit (Policy S A H) (Traj S H) t) : Prop where
  /-- The KL inequality `KL(p̂_h(s, a) ‖ p_h(s, a)) ≤ α(n) / n`. -/
  kl : ∀ h s a, klDiv (weightedMeasure (empTrans hist h s a)) (M.trans h (s, a)) ≤
    klThreshold (Fintype.card S) (Fintype.card A) H δ (visitCount hist h s a)
  /-- The Bernstein inequality for `Z*_{h+1}` at the visited pairs. -/
  bern : ∀ h s a, 0 < visitCount hist h s a →
    |vecExp (empTrans hist h s a) (optExpValue M H β (h + 1))
        - vecExp (M.transVec h s a) (optExpValue M H β (h + 1))| ≤
      √(2 * vecVar (M.transVec h s a) (optExpValue M H β (h + 1))
          * (alphaStar (Fintype.card S) (Fintype.card A) H δ (visitCount hist h s a)
            / visitCount hist h s a))
      + 3 * bernRange H β h
        * (alphaStar (Fintype.card S) (Fintype.card A) H δ (visitCount hist h s a)
          / visitCount hist h s a)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℕ → Ω → Policy S A H} {Y : ℕ → Ω → Traj S H}

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- On the good event, the history of the first `t` episodes satisfies the concentration
inequalities. -/
lemma histConcentration_histAt {M : EpisodicMDP S A} {s₁ : S} {β δ : ℝ} {ω : Ω}
    (hω : ω ∈ goodEvent X Y M s₁ β δ) (t : ℕ) : HistConcentration M β δ (histAt X Y t ω) :=
  ⟨hω.1.1 t, hω.1.2 t⟩

omit [Nonempty A] [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- The KL inequality at a visited pair, with the finite threshold `α(n) / n`. -/
lemma HistConcentration.klDiv_le_ofReal {M : EpisodicMDP S A} {β δ : ℝ} {t : ℕ}
    {hist : Hist Unit (Policy S A H) (Traj S H) t} (hc : HistConcentration M β δ hist) (h : Fin H)
    (s : S) (a : A) (hn : 0 < visitCount hist h s a) :
    klDiv (weightedMeasure (empTrans hist h s a)) (M.trans h (s, a)) ≤
      ENNReal.ofReal (alphaKL (Fintype.card S) (Fintype.card A) H δ (visitCount hist h s a)
        / visitCount hist h s a) := by
  have := hc.kl h s a
  simpa only [klThreshold, hn.ne', ↓reduceIte] using this

omit [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A]
  [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- The point masses of the transition kernel are the transition vector. -/
lemma measureReal_trans_singleton (M : EpisodicMDP S A) (h : Fin H) (s : S) (a : A) (s' : S) :
    (M.trans h (s, a)).real {s'} = M.transVec h s a s' := rfl

/-- `α*(n) / n ≤ α(n) / n` for a nonempty state space. -/
lemma alphaStar_div_le_alphaKL_div (nS nA H : ℕ) (hS : 1 ≤ nS) (δ : ℝ) (n : ℕ) :
    alphaStar nS nA H δ n / n ≤ alphaKL nS nA H δ n / n :=
  div_le_div_of_nonneg_right (alphaStar_le_alphaKL hS nA H δ n) n.cast_nonneg

omit [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A] [MeasurableSpace S]
  [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- A type with an element has cardinality at least one. -/
lemma one_le_card_of_elem (s : S) : 1 ≤ Fintype.card S :=
  Fintype.card_pos_iff.2 ⟨s⟩

omit [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A] [MeasurableSpace S]
  [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The horizon is at least one when there is a step `h : Fin H`. -/
lemma one_le_cast_of_fin (h : Fin H) : (1 : ℝ) ≤ H := by
  exact_mod_cast Nat.one_le_of_lt h.is_lt

omit [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A] [MeasurableSpace S]
  [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The number of steps to go after `h.succ` is `H - 1 - h`. -/
lemma sub_succ_eq (h : Fin H) : H - (h.succ : ℕ) = H - 1 - h := by
  simp only [Fin.val_succ]; omega

omit [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A] [MeasurableSpace S]
  [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- `H - h = (H - 1 - h) + 1` for a step `h : Fin H`, as reals. -/
lemma cast_sub_castSucc_eq (h : Fin H) :
    ((H - (h : ℕ) : ℕ) : ℝ) = ((H - 1 - h : ℕ) : ℝ) + 1 := by
  rw [sub_val_eq h]; push_cast; ring

/-! ### Recursion equations at a step -/

variable {t : ℕ} (hist : Hist Unit (Policy S A H) (Traj S H) t) (r : ℕ → S → A → ℝ) (β δ : ℝ)

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- The certificate at the step `h`. -/
lemma cert_sub_eq (h : Fin H) (s : S) :
    cert r β δ hist (H - h) s =
      if visitCount hist h s (greedy r β δ hist h s) = 0 then
        (if 0 < β then Real.exp (β * ((H - 1 - h : ℕ) + 1)) else 1)
      else min (if 0 < β then Real.exp (β * ((H - 1 - h : ℕ) + 1)) else 1)
        (Real.exp (β * r h s (greedy r β δ hist h s)) *
          ((3 : ℕ) * bonus (Fintype.card S) (Fintype.card A) H β δ (H - 1 - h)
              (visitCount hist h s (greedy r β δ hist h s))
              (empTrans hist h s (greedy r β δ hist h s))
              (optZ r β δ hist (H - 1 - h)).1 (optZ r β δ hist (H - 1 - h)).2
            + (1 + (3 : ℕ) / H) * vecExp (empTrans hist h s (greedy r β δ hist h s))
              (cert r β δ hist (H - 1 - h)))) := by
  rw [sub_val_eq h, cert_succ, certStep]
  simp only [sub_one_sub_lt h.is_lt, ↓reduceDIte, stepOf_sub_one_sub]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- The ring value at the step `h`. -/
lemma ringZ_sub_eq (M : EpisodicMDP S A) (h : Fin H) (s : S) :
    ringZ M r β δ hist (H - h) s = ringU M r β δ hist h s (greedy r β δ hist h s) := by
  rw [sub_val_eq h]
  change ringZStep M r β δ hist (H - 1 - h) (ringZ M r β δ hist (H - 1 - h)) s = _
  simp only [ringZStep, sub_one_sub_lt h.is_lt, ↓reduceDIte, stepOf_sub_one_sub]
  rfl

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- The terminal ring value is `1`. -/
lemma ringZ_zero (M : EpisodicMDP S A) : ringZ M r β δ hist 0 = fun _ ↦ 1 := rfl

end History

/-! ### The bonus and the rate terms -/

section Bonus

variable {S : Type*} [Fintype S] (nS nA H : ℕ) {β : ℝ} (δ : ℝ) (k n : ℕ) (phat Zt Zl : S → ℝ)

/-- The bonus for `β > 0`, with real numerals. -/
lemma bonus_of_pos (hβ : 0 < β) :
    bonus nS nA H β δ k n phat Zt Zl
      = 2 * √2 * √(vecVar phat Zt * (alphaStar nS nA H δ n / n))
        + 5 * Real.exp (β * k) * (alphaKL nS nA H δ n / n)
        + 4 * H * Real.exp (β * k) * (alphaKL nS nA H δ n / n) := by
  simp only [bonus, hβ, ↓reduceIte]
  push_cast
  ring

/-- The bonus for `β ≤ 0`, with real numerals. -/
lemma bonus_of_not_pos (hβ : ¬ 0 < β) :
    bonus nS nA H β δ k n phat Zt Zl
      = 2 * √2 * √(vecVar phat Zl * (alphaStar nS nA H δ n / n))
        + 5 * (1 - Real.exp (β * k)) * (alphaKL nS nA H δ n / n)
        + 4 * H * (1 - Real.exp (β * k)) * (alphaKL nS nA H δ n / n) := by
  simp only [bonus, hβ, ↓reduceIte]
  push_cast
  ring

omit [Fintype S] in
/-- The truncated rate is nonnegative for a nonnegative rate. -/
lemma rateMin_nonneg {α : ℕ → ℝ} (hα : ∀ n, 0 ≤ α n) (n : ℕ) : 0 ≤ rateMin α n := by
  unfold rateMin
  split_ifs
  · exact zero_le_one
  · exact le_min (div_nonneg (hα n) n.cast_nonneg) zero_le_one

omit [Fintype S] in
/-- The truncated rate of a visited pair with `α(n)/n < 1` is `α(n)/n`. -/
lemma rateMin_eq_div {α : ℕ → ℝ} {n : ℕ} (hn : n ≠ 0) (h : α n / n < 1) :
    rateMin α n = α n / n := by
  simp [rateMin, hn, h.le]

omit [Fintype S] in
/-- The truncated rate of a never-visited pair, or with `α(n)/n ≥ 1`, is `1`. -/
lemma rateMin_eq_one {α : ℕ → ℝ} {n : ℕ} (h : n = 0 ∨ 1 ≤ α n / n) : rateMin α n = 1 := by
  rcases h with h | h
  · simp [rateMin, h]
  · by_cases hn : n = 0
    · simp [rateMin, hn]
    · simp [rateMin, hn, h]

end Bonus

/-- For `β > 0`, the interval `[min 1 e^{β u}, max 1 e^{β u}]` is `[1, e^{β u}]`. -/
lemma mem_Icc_one_exp_of_pos {β u x : ℝ} (hβ : 0 < β) (hu : 0 ≤ u)
    (hx : x ∈ Set.Icc (min 1 (Real.exp (β * u))) (max 1 (Real.exp (β * u)))) :
    x ∈ Set.Icc 1 (Real.exp (β * u)) := by
  have h1 : 1 ≤ Real.exp (β * u) := Real.one_le_exp (mul_nonneg hβ.le hu)
  rwa [min_eq_left h1, max_eq_right h1] at hx

/-- For `β < 0`, the interval `[min 1 e^{β u}, max 1 e^{β u}]` is `[e^{β u}, 1]`. -/
lemma mem_Icc_exp_one_of_neg {β u x : ℝ} (hβ : β < 0) (hu : 0 ≤ u)
    (hx : x ∈ Set.Icc (min 1 (Real.exp (β * u))) (max 1 (Real.exp (β * u)))) :
    x ∈ Set.Icc (Real.exp (β * u)) 1 := by
  have h1 : Real.exp (β * u) ≤ 1 :=
    Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hβ.le hu)
  rwa [min_eq_right h1, max_eq_left h1] at hx

/-- An MDP whose reward function has values in `[0, 1]` has rewards in `[0, 1]`. -/
lemma rewardsIn_Icc_of_hasRewardFn {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    {M : EpisodicMDP S A} {r : ℕ → S → A → ℝ} (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc (0 : ℝ) 1) : M.RewardsIn (Set.Icc 0 1) :=
  rewardsIn_of_hasRewardFn M hM measurableSet_Icc hr

end Essakine2026Tight
