/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Moments.Variance
public import Essakine2026Tight.Mathlib.Algebra.Order.Field.Basic

/-!
# The normalized variance of an exponential transform

For a random variable `f` with values in `[0, R]` and `Y = exp (β f)`, the Bhatia–Davis inequality
(`ProbabilityTheory.variance_le_sub_mul_sub`) gives
`Var(Y) / (𝔼 Y)² ≤ (e^{|β| R} - 1)² / (4 e^{|β| R})`
(`ProbabilityTheory.variance_exp_div_sq_integral_le`; Lemma 24 of Essakine, Vernade (2026)).
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The mean of a random variable with values in `[a, b]` almost surely lies in `[a, b]`. -/
lemma integral_mem_Icc_of_ae_mem_Icc {X : Ω → ℝ} {a b : ℝ} (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hX : AEStronglyMeasurable X μ) : μ[X] ∈ Set.Icc a b := by
  have hint : Integrable X μ := (memLp_of_bounded h hX 1).integrable le_rfl
  constructor
  · calc a = ∫ _, a ∂μ := by simp
      _ ≤ μ[X] := integral_mono_ae (integrable_const a) hint (h.mono fun ω hω ↦ hω.1)
  · calc μ[X] ≤ ∫ _, b ∂μ := integral_mono_ae hint (integrable_const b) (h.mono fun ω hω ↦ hω.2)
      _ = b := by simp

/-- `exp (β f)` lies in `[min 1 e^{β R}, max 1 e^{β R}]` when `f ∈ [0, R]`. -/
lemma exp_mul_mem_Icc_min_max {f R β : ℝ} (hf : f ∈ Set.Icc 0 R) :
    Real.exp (β * f) ∈ Set.Icc (min 1 (Real.exp (β * R))) (max 1 (Real.exp (β * R))) := by
  rcases le_or_gt 0 β with hβ | hβ
  · have h0 : 0 ≤ β * f := mul_nonneg hβ hf.1
    have h1 : β * f ≤ β * R := mul_le_mul_of_nonneg_left hf.2 hβ
    constructor
    · exact (min_le_left _ _).trans (by simpa using Real.exp_le_exp.2 h0)
    · exact (Real.exp_le_exp.2 h1).trans (le_max_right _ _)
  · have h0 : β * f ≤ 0 := by nlinarith [hf.1]
    have h1 : β * R ≤ β * f := mul_le_mul_of_nonpos_left hf.2 hβ.le
    constructor
    · exact (min_le_right _ _).trans (Real.exp_le_exp.2 h1)
    · exact (by simpa using Real.exp_le_exp.2 h0 : Real.exp (β * f) ≤ 1).trans (le_max_left _ _)

/-- `(max 1 e^{β R} - min 1 e^{β R})² / (4 max 1 e^{β R} min 1 e^{β R})` is
`(e^{|β| R} - 1)² / (4 e^{|β| R})` for `R ≥ 0`. -/
lemma max_sub_min_sq_div_eq {R β : ℝ} (hR : 0 ≤ R) :
    (max 1 (Real.exp (β * R)) - min 1 (Real.exp (β * R))) ^ 2
        / (4 * max 1 (Real.exp (β * R)) * min 1 (Real.exp (β * R)))
      = (Real.exp (|β| * R) - 1) ^ 2 / (4 * Real.exp (|β| * R)) := by
  rcases le_or_gt 0 β with hβ | hβ
  · have h1 : 1 ≤ Real.exp (β * R) := by simpa using Real.exp_le_exp.2 (mul_nonneg hβ hR)
    rw [min_eq_left h1, max_eq_right h1, abs_of_nonneg hβ]
    ring
  · have h1 : Real.exp (β * R) ≤ 1 := by
      simpa using Real.exp_le_exp.2 (mul_nonpos_of_nonpos_of_nonneg hβ.le hR)
    rw [min_eq_right h1, max_eq_left h1, abs_of_neg hβ, neg_mul, Real.exp_neg]
    have := (Real.exp_pos (β * R)).ne'
    field_simp

/-- Normalized variance bound for an exponential transform (Lemma 24 of Essakine, Vernade
(2026)): for `f` with values in `[0, R]` almost surely and `Y = exp (β f)`,
`Var(Y) / (𝔼 Y)² ≤ (e^{|β| R} - 1)² / (4 e^{|β| R})`. -/
lemma variance_exp_div_sq_integral_le {f : Ω → ℝ} {R β : ℝ} (hR : 0 ≤ R)
    (hf : ∀ᵐ ω ∂μ, f ω ∈ Set.Icc 0 R) (hfm : AEMeasurable f μ) :
    variance (fun ω ↦ Real.exp (β * f ω)) μ / (μ[fun ω ↦ Real.exp (β * f ω)]) ^ 2
      ≤ (Real.exp (|β| * R) - 1) ^ 2 / (4 * Real.exp (|β| * R)) := by
  have hm : 0 < min 1 (Real.exp (β * R)) := lt_min one_pos (Real.exp_pos _)
  have hM : 0 < max 1 (Real.exp (β * R)) := hm.trans_le min_le_max
  have hY : ∀ᵐ ω ∂μ, Real.exp (β * f ω)
      ∈ Set.Icc (min 1 (Real.exp (β * R))) (max 1 (Real.exp (β * R))) :=
    hf.mono fun ω hω ↦ exp_mul_mem_Icc_min_max hω
  have hYm : AEMeasurable (fun ω ↦ Real.exp (β * f ω)) μ :=
    Real.measurable_exp.comp_aemeasurable (hfm.const_mul β)
  have hmean := integral_mem_Icc_of_ae_mem_Icc hY hYm.aestronglyMeasurable
  have hμ0 : 0 < μ[fun ω ↦ Real.exp (β * f ω)] := hm.trans_le hmean.1
  have hvar := variance_le_sub_mul_sub hY hYm
  calc variance (fun ω ↦ Real.exp (β * f ω)) μ / (μ[fun ω ↦ Real.exp (β * f ω)]) ^ 2
      ≤ (max 1 (Real.exp (β * R)) - μ[fun ω ↦ Real.exp (β * f ω)])
          * (μ[fun ω ↦ Real.exp (β * f ω)] - min 1 (Real.exp (β * R)))
          / (μ[fun ω ↦ Real.exp (β * f ω)]) ^ 2 := by gcongr
    _ ≤ (max 1 (Real.exp (β * R)) - min 1 (Real.exp (β * R))) ^ 2
          / (4 * max 1 (Real.exp (β * R)) * min 1 (Real.exp (β * R))) :=
        sub_mul_sub_div_sq_le hm hM hμ0
    _ = _ := max_sub_min_sq_div_eq hR

end ProbabilityTheory
