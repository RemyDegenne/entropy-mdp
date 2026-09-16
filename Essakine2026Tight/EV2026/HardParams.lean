/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.EV2026.Constants
public import Essakine2026Tight.Mathlib.InformationTheory.KLBer

/-!
# Parameters of the hard instances of the lower bound

For `β ≠ 0`, the effective horizon `H'` and `ε > 0`, with `c = e^{|β| H'} - 1` and
`q = e^{|β| ε}`, the leaf success probabilities are `p₋ = 1/(2(c+1))` (`β > 0`) or
`1 - 1/(2(c+1))` (`β < 0`) and `p₊ = p₋ + Δ` with `Δ = (q - 1)(3c + 2)/(c(c + 1))` (`β > 0`) or
`(q - 1)(3c + 2)/(c(c + 1)(2q - 1))` (`β < 0`).

* Under Condition A: `0 < p₋ < p₊ ≤ (1 + p₋)/2 < 1` and `p₊ (1 - p₊) ≥ 1/(8(c+1))`
  (`hardParams_valid`), hence the binary divergence satisfies
  `klBerReal p₋ p₊ ≤ 72 (c + 1) (q - 1)² / c²` (`klBerReal_hardPMinus_hardPPlus_le`).
* The exponential value of a policy with success probability `p` is
  `hardZ β H' p = 1 + p (e^{β H'} - 1)`, and the entropic gap between `p₊` and `p₋` is
  `|β|⁻¹ log (2q - 1) > ε` (`inv_mul_log_hardZ_div`, `lt_inv_mul_log_hardZ_div`).
* `varianceFactor_mono`, `varianceFactor_eq_hardC`: the factor `(e^{|β| G} - 1)² / e^{|β| G}` of
  the lower bound is nondecreasing in `G ≥ 0` and equals `c² / (c + 1)` at `G = H'`;
  `ofReal_le_sum_klBer` is the lower bound on the sum of binary divergences.
-/

@[expose] public section

open Real InformationTheory

namespace Essakine2026Tight

/-- `c = e^{|β| H'} - 1`. -/
noncomputable def hardC (β : ℝ) (H' : ℕ) : ℝ := exp (|β| * H') - 1

/-- `q = e^{|β| ε}`. -/
noncomputable def hardQ (β ε : ℝ) : ℝ := exp (|β| * ε)

/-- The baseline leaf success probability `p₋`. -/
noncomputable def hardPMinus (β : ℝ) (H' : ℕ) : ℝ :=
  if 0 < β then 1 / (2 * (hardC β H' + 1)) else 1 - 1 / (2 * (hardC β H' + 1))

/-- The gap `Δ = p₊ - p₋`. -/
noncomputable def hardDelta (β : ℝ) (H' : ℕ) (ε : ℝ) : ℝ :=
  if 0 < β then (hardQ β ε - 1) * (3 * hardC β H' + 2) / (hardC β H' * (hardC β H' + 1))
  else (hardQ β ε - 1) * (3 * hardC β H' + 2)
    / (hardC β H' * (hardC β H' + 1) * (2 * hardQ β ε - 1))

/-- The leaf success probability `p₊ = p₋ + Δ` of the modified triple. -/
noncomputable def hardPPlus (β : ℝ) (H' : ℕ) (ε : ℝ) : ℝ := hardPMinus β H' + hardDelta β H' ε

variable {β ε : ℝ} {H' : ℕ}

lemma hardC_pos (hβ : β ≠ 0) (hH' : 1 ≤ H') : 0 < hardC β H' := by
  rw [hardC, sub_pos, one_lt_exp_iff]
  exact mul_pos (abs_pos.2 hβ) (by exact_mod_cast hH')

lemma one_lt_hardQ (hβ : β ≠ 0) (hε : 0 < ε) : 1 < hardQ β ε := by
  rw [hardQ, one_lt_exp_iff]
  exact mul_pos (abs_pos.2 hβ) hε

lemma exp_mul_eq_hardC_add_one (hβ : 0 < β) : exp (β * H') = hardC β H' + 1 := by
  rw [hardC, abs_of_pos hβ]; ring

lemma exp_mul_eq_inv_hardC_add_one (hβ : β < 0) : exp (β * H') = (hardC β H' + 1)⁻¹ := by
  rw [hardC, abs_of_neg hβ, sub_add_cancel, neg_mul, exp_neg, inv_inv]

lemma hardDelta_pos (hβ : β ≠ 0) (hH' : 1 ≤ H') (hε : 0 < ε) : 0 < hardDelta β H' ε := by
  have hc := hardC_pos hβ hH'
  have hq := one_lt_hardQ hβ hε
  unfold hardDelta
  split_ifs
  · exact div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
  · exact div_pos (mul_pos (by linarith) (by linarith))
      (mul_pos (by positivity) (by linarith))

lemma conditionA_of_pos (hβ : 0 < β) (h : ConditionA β H' ε) :
    hardQ β ε - 1 ≤ hardC β H' * (2 * hardC β H' + 1) / (4 * (3 * hardC β H' + 2)) := by
  unfold ConditionA at h
  simp only [hβ, ↓reduceIte] at h
  push_cast at h
  exact h

lemma conditionA_of_neg (hβ : ¬ 0 < β) (h : ConditionA β H' ε) :
    hardQ β ε - 1 ≤ hardC β H' / (10 * hardC β H' + 8) := by
  unfold ConditionA at h
  simp only [hβ, ↓reduceIte] at h
  push_cast at h
  exact h

/-- The consequences of the margin `Δ ≤ (1 - p₋)/2`. -/
lemma valid_of_margin {pm D c : ℝ} (hpm0 : 0 < pm) (hD : 0 < D)
    (hDle : D ≤ (1 - pm) / 2) (hprod : 1 / (8 * (c + 1)) ≤ pm * ((1 - pm) / 2)) :
    0 < pm ∧ pm < pm + D ∧ pm + D ≤ (1 + pm) / 2 ∧ pm + D < 1
      ∧ 1 / (8 * (c + 1)) ≤ (pm + D) * (1 - (pm + D)) := by
  refine ⟨hpm0, by linarith, by linarith, by linarith, hprod.trans ?_⟩
  exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)

lemma hardPMinus_of_pos (hβ : 0 < β) : hardPMinus β H' = 1 / (2 * (hardC β H' + 1)) := by
  simp [hardPMinus, hβ]

lemma hardPMinus_of_neg (hβ : ¬ 0 < β) : hardPMinus β H' = 1 - 1 / (2 * (hardC β H' + 1)) := by
  simp [hardPMinus, hβ]

lemma hardDelta_of_pos (hβ : 0 < β) :
    hardDelta β H' ε
      = (hardQ β ε - 1) * (3 * hardC β H' + 2) / (hardC β H' * (hardC β H' + 1)) := by
  simp [hardDelta, hβ]

lemma hardDelta_of_neg (hβ : ¬ 0 < β) :
    hardDelta β H' ε = (hardQ β ε - 1) * (3 * hardC β H' + 2)
      / (hardC β H' * (hardC β H' + 1) * (2 * hardQ β ε - 1)) := by
  simp [hardDelta, hβ]

/-- **Admissibility of the parameters** under Condition A. -/
lemma hardParams_valid (hβ : β ≠ 0) (hH' : 1 ≤ H') (hε : 0 < ε) (hcond : ConditionA β H' ε) :
    0 < hardPMinus β H' ∧ hardPMinus β H' < hardPPlus β H' ε
      ∧ hardPPlus β H' ε ≤ (1 + hardPMinus β H') / 2 ∧ hardPPlus β H' ε < 1
      ∧ 1 / (8 * (hardC β H' + 1)) ≤ hardPPlus β H' ε * (1 - hardPPlus β H' ε) := by
  have hc := hardC_pos hβ hH'
  have hq := one_lt_hardQ hβ hε
  have hΔ := hardDelta_pos hβ hH' hε
  unfold hardPPlus
  by_cases hβ' : 0 < β
  · have h := conditionA_of_pos hβ' hcond
    rw [hardPMinus_of_pos hβ'] at *
    rw [hardDelta_of_pos hβ'] at hΔ ⊢
    set c := hardC β H'
    set q := hardQ β ε
    refine valid_of_margin (by positivity) hΔ ?_ ?_
    · rw [div_le_iff₀ (by positivity)]
      rw [le_div_iff₀ (by positivity)] at h
      have e : (1 - 1 / (2 * (c + 1))) / 2 * (c * (c + 1)) = c * (2 * c + 1) / 4 := by
        field_simp; ring
      rw [e]
      linarith
    · have e1 : 1 / (2 * (c + 1)) * ((1 - 1 / (2 * (c + 1))) / 2)
          = (2 * c + 1) / (8 * (c + 1) ^ 2) := by field_simp; ring
      rw [e1, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  · have h := conditionA_of_neg hβ' hcond
    rw [hardPMinus_of_neg hβ'] at *
    rw [hardDelta_of_neg hβ'] at hΔ ⊢
    set c := hardC β H'
    set q := hardQ β ε
    have h2q : 0 < 2 * q - 1 := by linarith
    have hcc : 0 < c * (c + 1) * (2 * q - 1) := by
      have := mul_pos hc (show 0 < c + 1 by linarith); positivity
    refine valid_of_margin ?_ hΔ ?_ ?_
    · have : 1 / (2 * (c + 1)) < 1 := by rw [div_lt_one (by positivity)]; linarith
      linarith
    · rw [div_le_iff₀ hcc]
      rw [le_div_iff₀ (by positivity)] at h
      have e : (1 - (1 - 1 / (2 * (c + 1)))) / 2 * (c * (c + 1) * (2 * q - 1))
          = c * (2 * q - 1) / 4 := by
        field_simp; ring
      rw [e]
      nlinarith
    · have e1 : (1 - 1 / (2 * (c + 1))) * ((1 - (1 - 1 / (2 * (c + 1)))) / 2)
          = (2 * c + 1) / (8 * (c + 1) ^ 2) := by field_simp; ring
      rw [e1, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith

lemma hardDelta_le (hβ : β ≠ 0) (hH' : 1 ≤ H') (hε : 0 < ε) :
    hardDelta β H' ε ≤ 3 * (hardQ β ε - 1) / hardC β H' := by
  have hc := hardC_pos hβ hH'
  have hq := one_lt_hardQ hβ hε
  set c := hardC β H'
  set q := hardQ β ε
  have h32 : (3 * c + 2) / (c + 1) ≤ 3 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hbase : (q - 1) * (3 * c + 2) / (c * (c + 1)) ≤ 3 * (q - 1) / c := by
    rw [show (q - 1) * (3 * c + 2) / (c * (c + 1)) = (q - 1) / c * ((3 * c + 2) / (c + 1)) by
      field_simp]
    rw [show 3 * (q - 1) / c = (q - 1) / c * 3 by ring]
    exact mul_le_mul_of_nonneg_left h32 (div_nonneg (by linarith) hc.le)
  unfold hardDelta
  split_ifs
  · exact hbase
  · refine le_trans ?_ hbase
    have h2q : 0 < 2 * q - 1 := by linarith
    have hcc : 0 < c * (c + 1) * (2 * q - 1) := by
      have := mul_pos hc (show 0 < c + 1 by linarith); positivity
    rw [div_le_div_iff₀ hcc (by positivity)]
    have : 0 ≤ (q - 1) * (3 * c + 2) * (c * (c + 1)) := by
      have := mul_pos hc (show 0 < c + 1 by linarith)
      positivity
    nlinarith

/-- **Divergence of the leaf parameters**: `klBerReal p₋ p₊ ≤ 72 (c + 1) (q - 1)² / c²`. -/
lemma klBerReal_hardPMinus_hardPPlus_le (hβ : β ≠ 0) (hH' : 1 ≤ H') (hε : 0 < ε)
    (hcond : ConditionA β H' ε) :
    klBerReal (hardPMinus β H') (hardPPlus β H' ε)
      ≤ 72 * (hardC β H' + 1) * (hardQ β ε - 1) ^ 2 / hardC β H' ^ 2 := by
  obtain ⟨h0, h1, -, h3, h4⟩ := hardParams_valid hβ hH' hε hcond
  have hc := hardC_pos hβ hH'
  have hq := one_lt_hardQ hβ hε
  have hΔ := hardDelta_pos hβ hH' hε
  have hΔle := hardDelta_le hβ hH' hε
  have hprod : 0 < hardPPlus β H' ε * (1 - hardPPlus β H' ε) :=
    mul_pos (by linarith) (by linarith)
  have hkl := klBerReal_le_div h0.le (by linarith) (by linarith) h3
  refine hkl.trans ?_
  rw [show hardPMinus β H' - hardPPlus β H' ε = - hardDelta β H' ε by simp [hardPPlus]]
  rw [neg_sq, div_le_div_iff₀ hprod (by positivity)]
  have h8 : 1 ≤ 8 * (hardC β H' + 1) * (hardPPlus β H' ε * (1 - hardPPlus β H' ε)) := by
    rw [div_le_iff₀ (by positivity)] at h4
    linarith
  have hsq : hardDelta β H' ε ^ 2 * hardC β H' ^ 2 ≤ 9 * (hardQ β ε - 1) ^ 2 := by
    rw [le_div_iff₀ hc] at hΔle
    have := pow_le_pow_left₀ (mul_pos hΔ hc).le hΔle 2
    nlinarith
  nlinarith [sq_nonneg (hardC β H'), sq_nonneg (hardDelta β H' ε)]

/-! ### Exponential values and the gap -/

/-- The exponential value `1 + p (e^{β H'} - 1)` of a policy with success probability `p`. -/
noncomputable def hardZ (β : ℝ) (H' : ℕ) (p : ℝ) : ℝ := 1 + p * (exp (β * H') - 1)

lemma hardZ_pos {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 < hardZ β H' p := by
  unfold hardZ
  have he := exp_pos (β * H')
  rw [show 1 + p * (exp (β * H') - 1) = (1 - p) + p * exp (β * H') by ring]
  rcases hp1.lt_or_eq with h | h
  · have := mul_nonneg hp0 he.le; linarith
  · rw [h]; simpa using he

/-- **The gap**: a policy with success probability `p₋` is `|β|⁻¹ log (2q - 1)`-suboptimal
compared to one with success probability `p₊`. -/
lemma inv_mul_log_hardZ_div (hβ : β ≠ 0) (hH' : 1 ≤ H') (hε : 0 < ε) :
    β⁻¹ * log (hardZ β H' (hardPPlus β H' ε) / hardZ β H' (hardPMinus β H'))
      = |β|⁻¹ * log (2 * hardQ β ε - 1) := by
  have hc := hardC_pos hβ hH'
  have hq := one_lt_hardQ hβ hε
  set c := hardC β H' with hc_def
  set q := hardQ β ε
  have hc0 : c ≠ 0 := hc.ne'
  have hc1 : c + 1 ≠ 0 := by linarith
  have h2q : 2 * q - 1 ≠ 0 := by linarith
  have h32 : 3 * c + 2 ≠ 0 := by linarith
  unfold hardZ hardPPlus
  by_cases hβ' : 0 < β
  · rw [hardPMinus_of_pos hβ', hardDelta_of_pos hβ', exp_mul_eq_hardC_add_one hβ', ← hc_def,
      abs_of_pos hβ']
    have hZm : 1 + 1 / (2 * (c + 1)) * (c + 1 - 1) = (3 * c + 2) / (2 * (c + 1)) := by
      field_simp; ring
    have hZp : 1 + (1 / (2 * (c + 1)) + (q - 1) * (3 * c + 2) / (c * (c + 1))) * (c + 1 - 1)
        = (2 * q - 1) * ((3 * c + 2) / (2 * (c + 1))) := by
      field_simp; ring
    rw [hZm, hZp, mul_div_cancel_right₀ _ (by positivity)]
  · have hβneg : β < 0 := lt_of_le_of_ne (not_lt.1 hβ') hβ
    rw [hardPMinus_of_neg hβ', hardDelta_of_neg hβ', exp_mul_eq_inv_hardC_add_one hβneg,
      ← hc_def, abs_of_neg hβneg]
    have hZm : 1 + (1 - 1 / (2 * (c + 1))) * ((c + 1)⁻¹ - 1)
        = (3 * c + 2) / (2 * (c + 1) ^ 2) := by
      field_simp; ring
    have hZp : 1 + (1 - 1 / (2 * (c + 1))
          + (q - 1) * (3 * c + 2) / (c * (c + 1) * (2 * q - 1))) * ((c + 1)⁻¹ - 1)
        = (3 * c + 2) / (2 * (c + 1) ^ 2) / (2 * q - 1) := by
      field_simp; ring
    rw [hZm, hZp, div_div_cancel_left' (by positivity), log_inv, inv_neg]
    ring

/-- The gap exceeds `ε`. -/
lemma lt_inv_mul_log_hardZ_div (hβ : β ≠ 0) (hH' : 1 ≤ H') (hε : 0 < ε) :
    ε < β⁻¹ * log (hardZ β H' (hardPPlus β H' ε) / hardZ β H' (hardPMinus β H')) := by
  rw [inv_mul_log_hardZ_div hβ hH' hε]
  have hq := one_lt_hardQ hβ hε
  have hb : 0 < |β| := abs_pos.2 hβ
  rw [lt_inv_mul_iff₀ hb, ← log_exp (|β| * ε)]
  refine log_lt_log (exp_pos _) ?_
  rw [show exp (|β| * ε) = hardQ β ε from rfl]
  linarith

/-! ### The variance factor and the counting bound -/

lemma varianceFactor_eq (β G : ℝ) :
    varianceFactor β G = exp (|β| * G) + exp (-(|β| * G)) - 2 := by
  rw [varianceFactor, exp_neg]
  have := exp_pos (|β| * G)
  field_simp
  ring

/-- The variance factor `(e^{|β| G} - 1)² / e^{|β| G}` is nondecreasing in `G ≥ 0`. -/
lemma varianceFactor_mono (β : ℝ) {G G' : ℝ} (hG : 0 ≤ G) (hGG' : G ≤ G') :
    varianceFactor β G ≤ varianceFactor β G' := by
  rw [varianceFactor_eq, varianceFactor_eq]
  set x := |β| * G
  set y := |β| * G'
  have hx : 0 ≤ x := mul_nonneg (abs_nonneg β) hG
  have hxy : x ≤ y := mul_le_mul_of_nonneg_left hGG' (abs_nonneg β)
  have h1 : exp x ≤ exp y := exp_le_exp.2 hxy
  have h2 : exp (-x - y) ≤ 1 := exp_le_one_iff.2 (by linarith)
  have key : exp y + exp (-y) - (exp x + exp (-x)) = (exp y - exp x) * (1 - exp (-x - y)) := by
    rw [show -x - y = -x + -y by ring, exp_add]
    have hxpos := exp_pos x
    have hypos := exp_pos y
    rw [exp_neg, exp_neg]
    field_simp
    ring
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]

lemma varianceFactor_eq_hardC (β : ℝ) (H' : ℕ) :
    varianceFactor β H' = hardC β H' ^ 2 / (hardC β H' + 1) := by
  simp [varianceFactor, hardC]

lemma ofReal_sum_le_sum_ofReal {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

/-- **Lower bound on the sum of binary divergences** (the counting argument of the lower bound):
for at least `4` indices, probabilities `x` summing to at most `1` and probabilities `y` at least
`1 - δ` with `δ ≤ 1/16`, `∑ klBer (x i) (y i) ≥ (card/2) log(1/δ)`. -/
lemma ofReal_le_sum_klBer {ι : Type*} (U : Finset ι) (hU : 4 ≤ U.card) {δ : ℝ} (hδ : 0 < δ)
    (hδ16 : δ ≤ 1 / 16) {x y : ι → ℝ} (hx : ∀ i ∈ U, x i ∈ Set.Icc (0 : ℝ) 1)
    (hxsum : ∑ i ∈ U, x i ≤ 1) (hy : ∀ i ∈ U, y i ∈ Set.Icc (1 - δ) 1) :
    ENNReal.ofReal (U.card / 2 * log (1 / δ)) ≤ ∑ i ∈ U, klBer (x i) (y i) := by
  have hL : 4 * log 2 ≤ log (1 / δ) := by
    rw [← log_rpow (by norm_num : (0 : ℝ) < 2)]
    refine log_le_log (by positivity) ?_
    rw [le_div_iff₀ hδ]
    norm_num
    linarith
  have hterm : ∀ i ∈ U, ENNReal.ofReal ((1 - x i) * log (1 / δ) - log 2) ≤ klBer (x i) (y i) := by
    intro i hi
    obtain ⟨hx0, hx1⟩ := hx i hi
    obtain ⟨hy0, hy1⟩ := hy i hi
    rcases hy1.lt_or_eq with hy1 | hy1
    · have hq0 : 0 < y i := by linarith
      rw [klBer_eq_ofReal hq0.ne' hy1.ne]
      refine ENNReal.ofReal_le_ofReal ((sub_le_sub_right ?_ _).trans
        (sub_log_two_le_klBerReal hx0 hq0 hy1))
      refine mul_le_mul_of_nonneg_left (log_le_log (by positivity) ?_) (by linarith)
      rw [div_le_div_iff₀ hδ (by linarith)]
      linarith
    · rw [hy1, klBer_one_right]
      split_ifs with hx1'
      · rw [hx1', sub_self, zero_mul, zero_sub]
        exact (ENNReal.ofReal_eq_zero.2 (neg_nonpos.2 (log_nonneg (by norm_num)))).le
      · exact le_top
  calc ENNReal.ofReal (U.card / 2 * log (1 / δ))
      ≤ ENNReal.ofReal (∑ i ∈ U, ((1 - x i) * log (1 / δ) - log 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
        have hcard : (4 : ℝ) ≤ U.card := by exact_mod_cast hU
        have hlog2 : 0 < log 2 := log_pos (by norm_num)
        nlinarith
    _ ≤ ∑ i ∈ U, ENNReal.ofReal ((1 - x i) * log (1 / δ) - log 2) := ofReal_sum_le_sum_ofReal _ _
    _ ≤ ∑ i ∈ U, klBer (x i) (y i) := Finset.sum_le_sum hterm

end Essakine2026Tight
