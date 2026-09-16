/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.Mathlib.Analysis.SpecialFunctions.PoissonCramer
public import Essakine2026Tight.Mathlib.Probability.Martingale.Ville
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The self-normalized Bernstein inequality

Let `(Y t)` be adapted with `|Y t| ≤ b` and `𝔼[Y t | ℱ t] = 0`, let `v t` be a predictable
version of the conditional variance `𝔼[Y t² | ℱ t]` with values in `[0, b²]`, and let `w t` be
predictable with values in `[0, 1]`. With
`S t = ∑_{i < t} w i Y i` (`ProbabilityTheory.selfNormSum`) and
`V t = ∑_{i < t} w i² v i` (`ProbabilityTheory.selfNormVar`), the processes
`exp (lam S t - φ_b(lam) V t / b²)` are nonnegative supermartingales for every `lam ≥ 0`
(`ProbabilityTheory.supermartingale_exp_selfNorm`), where `φ_b(lam) = e^{lam b} - 1 - lam b`.
-/

@[expose] public section

open MeasureTheory Real Set
open scoped ENNReal

namespace Real

/-- `∫_a^c e^{-u} du = e^{-a} - e^{-c}` as a lower Lebesgue integral. -/
lemma lintegral_Ioc_exp_neg {a c : ℝ} (hac : a ≤ c) :
    ∫⁻ u in Ioc a c, ENNReal.ofReal (exp (-u)) = ENNReal.ofReal (exp (-a) - exp (-c)) := by
  have hint : IntegrableOn (fun u ↦ exp (-u)) (Ioc a c) volume :=
    (continuous_exp.comp continuous_neg).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun _ ↦ (exp_pos _).le)]
  congr 1
  rw [← intervalIntegral.integral_of_le hac, intervalIntegral.integral_comp_neg (fun x ↦ exp x),
    integral_exp]

/-- `e / 4 ≤ e^x / (1 + x)²` for `x ≥ 0`. -/
lemma exp_one_div_four_le {x : ℝ} (hx : 0 ≤ x) : exp 1 / 4 ≤ exp x / (1 + x) ^ 2 := by
  have h1 : (1 + x) / 2 ≤ exp ((x - 1) / 2) := by
    have := add_one_le_exp ((x - 1) / 2)
    linarith
  have h2 : ((1 + x) / 2) ^ 2 ≤ exp ((x - 1) / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have h3 : exp ((x - 1) / 2) ^ 2 = exp x / exp 1 := by
    rw [← exp_nat_mul, ← exp_sub]; congr 1; push_cast; ring
  rw [h3] at h2
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  rw [le_div_iff₀ (exp_pos 1)] at h2
  nlinarith [exp_pos 1]

/-- `θ - θ² ≤ log (1 + θ)` for `θ ≥ 0`. -/
lemma sub_sq_le_log_one_add {θ : ℝ} (hθ : 0 ≤ θ) : θ - θ ^ 2 ≤ log (1 + θ) := by
  have h := one_sub_inv_le_log_of_pos (x := 1 + θ) (by positivity)
  have h' : θ - θ ^ 2 ≤ 1 - (1 + θ)⁻¹ := by
    rw [show 1 - (1 + θ)⁻¹ = θ / (1 + θ) by field_simp; ring]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg θ, mul_nonneg hθ (sq_nonneg θ)]
  linarith

/-- **Lower bound on the exponential mixture**: for `s, v ≥ 0` and
`T = (v + 1) h(s / (v + 1))` (`h = poissonCramer`),
`∫_0^∞ exp (u s - φ(u) v - u) du ≥ e^T / (4 (1 + √(s + v)))`, where `φ = expSubOneSub`. -/
lemma ofReal_exp_div_le_lintegral_mixture {s v : ℝ} (hs : 0 ≤ s) (hv : 0 ≤ v) :
    ENNReal.ofReal (exp ((v + 1) * poissonCramer (s / (v + 1))) / (4 * (1 + √(s + v))))
      ≤ ∫⁻ u in Ioi 0, ENNReal.ofReal (exp (u * s - expSubOneSub u * v - u)) := by
  have hmeas : Measurable fun u ↦ ENNReal.ofReal (exp (u * s - expSubOneSub u * v - u)) := by
    fun_prop
  rcases eq_or_lt_of_le (add_nonneg hs hv) with h0 | hpos
  · have hs0 : s = 0 := by linarith
    have hv0 : v = 0 := by linarith
    subst hs0 hv0
    have hlog2 : (0 : ℝ) ≤ log 2 := log_nonneg (by norm_num)
    calc ENNReal.ofReal (exp ((0 + 1) * poissonCramer (0 / (0 + 1))) / (4 * (1 + √(0 + 0))))
        ≤ ENNReal.ofReal (exp (-0) - exp (-log 2)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h2 : exp (-log 2) = 1 / 2 := by rw [exp_neg, exp_log (by norm_num)]; norm_num
          rw [h2]
          norm_num
      _ = ∫⁻ u in Ioc 0 (log 2), ENNReal.ofReal (exp (-u)) := (lintegral_Ioc_exp_neg hlog2).symm
      _ ≤ ∫⁻ u in Ioi 0, ENNReal.ofReal (exp (-u)) := lintegral_mono_set Ioc_subset_Ioi_self
      _ = _ := by simp
  set x := s / (v + 1) with hx
  have hx0 : 0 ≤ x := by positivity
  set m := log (1 + x) with hm
  have hm0 : 0 ≤ m := log_nonneg (by linarith)
  have hexpm : exp m = 1 + x := exp_log (by linarith)
  set r := √(s + v) with hr
  have hr0 : 0 < r := sqrt_pos.2 hpos
  set θ₀ := 1 / r with hθ₀
  have hθ₀0 : 0 < θ₀ := by positivity
  have hθ₀sq : (s + v) * θ₀ ^ 2 = 1 := by
    rw [hθ₀, div_pow, one_pow, hr, sq_sqrt hpos.le]; field_simp
  set ℓ := log (1 + θ₀) with hℓ
  have hℓ0 : 0 ≤ ℓ := log_nonneg (by linarith)
  have hexpℓ : exp ℓ = 1 + θ₀ := exp_log (by linarith)
  set T := (v + 1) * poissonCramer x with hT
  set φm := expSubOneSub m with hφm
  have hφm_eq : φm = x - m := by simp only [hφm, expSubOneSub, hexpm]; ring
  have hgm : m * s - φm * v = T + φm := by
    have h := mul_poissonCramer_eq (c := v + 1) (s := s) (by positivity) hs
    rw [← hx, ← hm] at h
    rw [hT, ← h]
    ring
  set K := exp (T + φm - 1) with hK
  have hlow : ∀ u ∈ Ioc m (m + ℓ),
      ENNReal.ofReal (K * exp (-u)) ≤ ENNReal.ofReal (exp (u * s - expSubOneSub u * v - u)) := by
    intro u hu
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hK, ← exp_add]
    refine exp_le_exp.2 ?_
    set θ := exp (u - m) - 1 with hθ
    have hθ0 : 0 ≤ θ := by
      have : 1 ≤ exp (u - m) := one_le_exp (by linarith [hu.1])
      linarith
    have hθle : θ ≤ θ₀ := by
      have : exp (u - m) ≤ exp ℓ := exp_le_exp.2 (by linarith [hu.2])
      linarith
    have hlogθ : u - m = log (1 + θ) := by
      rw [hθ, add_sub_cancel, log_exp]
    have hlb := sub_sq_le_log_one_add hθ0
    have hφu : expSubOneSub u = φm + (1 + x) * θ - (u - m) := by
      simp only [hφm, expSubOneSub, hθ]
      rw [mul_sub, ← hexpm, ← exp_add]
      simp only [add_sub_cancel]
      ring
    have hgap : (s + v) - v * (1 + x) = x := by
      rw [hx]; field_simp; ring
    have hθsq : (s + v) * θ ^ 2 ≤ 1 := by
      rw [← hθ₀sq]
      have := pow_le_pow_left₀ hθ0 hθle 2
      nlinarith [add_nonneg hs hv]
    rw [hφu]
    have key : u * s - (φm + (1 + x) * θ - (u - m)) * v
        = (m * s - φm * v) + (u - m) * (s + v) - v * (1 + x) * θ := by ring
    rw [key, hgm]
    have h1 : (θ - θ ^ 2) * (s + v) ≤ (u - m) * (s + v) := by
      rw [hlogθ]; exact mul_le_mul_of_nonneg_right hlb (add_nonneg hs hv)
    nlinarith [mul_nonneg hθ0 hx0]
  have hreal : exp T / (4 * (1 + r)) ≤ K * (exp (-m) - exp (-(m + ℓ))) := by
    have e1 : exp (-m) - exp (-(m + ℓ)) = (1 / (1 + x)) * (1 / (1 + r)) := by
      rw [neg_add, exp_add, exp_neg, exp_neg, hexpm, hexpℓ, hθ₀]
      field_simp
      ring
    have e2 : K = exp T * exp x / (1 + x) * exp (-1) := by
      rw [hK, sub_eq_add_neg, exp_add, exp_add, hφm_eq, exp_sub, hexpm]
      ring
    rw [e1, e2]
    have h4 := exp_one_div_four_le hx0
    have hexp1 : exp 1 * exp (-1) = 1 := by rw [← exp_add]; simp
    have hpos1 : 0 < 1 + r := by linarith
    have hpos2 : 0 < 1 + x := by linarith
    have eR : exp T * exp x / (1 + x) * exp (-1) * (1 / (1 + x) * (1 / (1 + r)))
        = (exp T * exp (-1) / (1 + r)) * (exp x / (1 + x) ^ 2) := by
      field_simp
    have eL : exp T / (4 * (1 + r)) = (exp T * exp (-1) / (1 + r)) * (exp 1 / 4) := by
      rw [exp_neg]
      have := (exp_pos 1).ne'
      field_simp
    rw [eR, eL]
    gcongr
  have hsub : Ioc m (m + ℓ) ⊆ Ioi 0 := fun u hu ↦ lt_of_le_of_lt hm0 hu.1
  calc ENNReal.ofReal (exp T / (4 * (1 + r)))
      ≤ ENNReal.ofReal (K * (exp (-m) - exp (-(m + ℓ)))) := ENNReal.ofReal_le_ofReal hreal
    _ = ∫⁻ u in Ioc m (m + ℓ), ENNReal.ofReal (K * exp (-u)) := by
        have hK0 : 0 ≤ K := (exp_pos _).le
        simp_rw [ENNReal.ofReal_mul hK0]
        rw [lintegral_const_mul _ (by fun_prop), lintegral_Ioc_exp_neg (by linarith)]
    _ ≤ ∫⁻ u in Ioc m (m + ℓ), ENNReal.ofReal (exp (u * s - expSubOneSub u * v - u)) :=
        setLIntegral_mono hmeas hlow
    _ ≤ ∫⁻ u in Ioi 0, ENNReal.ofReal (exp (u * s - expSubOneSub u * v - u)) :=
        lintegral_mono_set hsub

end Real

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ mΩ}
  {Y w v : ℕ → Ω → ℝ} {b lam : ℝ}

/-- The weighted sum `S t = ∑_{i < t} w i Y i` of a self-normalized Bernstein process. -/
def selfNormSum (Y w : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range t, w i ω * Y i ω

/-- The self-normalizing sum `V t = ∑_{i < t} w i² v i`, where `v i` is a version of the
conditional variance `𝔼[Y i² | ℱ i]`. -/
def selfNormVar (v w : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range t, w i ω ^ 2 * v i ω

/-- `S 0 = 0`. -/
@[simp] lemma selfNormSum_zero (Y w : ℕ → Ω → ℝ) (ω : Ω) : selfNormSum Y w 0 ω = 0 := by
  simp [selfNormSum]

/-- `V 0 = 0`. -/
@[simp] lemma selfNormVar_zero (v w : ℕ → Ω → ℝ) (ω : Ω) : selfNormVar v w 0 ω = 0 := by
  simp [selfNormVar]

/-- `S (t + 1) = S t + w t Y t`. -/
lemma selfNormSum_succ (Y w : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    selfNormSum Y w (t + 1) ω = selfNormSum Y w t ω + w t ω * Y t ω := by
  simp [selfNormSum, Finset.sum_range_succ]

/-- `V (t + 1) = V t + w t² v t`. -/
lemma selfNormVar_succ (v w : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    selfNormVar v w (t + 1) ω = selfNormVar v w t ω + w t ω ^ 2 * v t ω := by
  simp [selfNormVar, Finset.sum_range_succ]

/-- `V t ≥ 0` when the conditional variances are nonnegative. -/
lemma selfNormVar_nonneg (hv : ∀ i ω, v i ω ∈ Set.Icc 0 (b ^ 2)) (t : ℕ) (ω : Ω) :
    0 ≤ selfNormVar v w t ω :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg (sq_nonneg _) (hv i ω).1

/-- `V t ≤ t b²` for weights in `[0, 1]` and conditional variances in `[0, b²]`. -/
lemma selfNormVar_le (hv : ∀ i ω, v i ω ∈ Set.Icc 0 (b ^ 2))
    (hw : ∀ i ω, w i ω ∈ Set.Icc 0 1) (t : ℕ) (ω : Ω) :
    selfNormVar v w t ω ≤ t * b ^ 2 := by
  calc selfNormVar v w t ω ≤ ∑ _i ∈ Finset.range t, b ^ 2 := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        have h1 : w i ω ^ 2 ≤ 1 := by nlinarith [(hw i ω).1, (hw i ω).2]
        nlinarith [(hv i ω).1, (hv i ω).2, sq_nonneg (w i ω)]
    _ = t * b ^ 2 := by simp

/-- `|S t| ≤ t b` for weights in `[0, 1]` and increments bounded by `b`. -/
lemma abs_selfNormSum_le (hw : ∀ i ω, w i ω ∈ Set.Icc 0 1) {ω : Ω} {t : ℕ}
    (hY : ∀ i, |Y i ω| ≤ b) : |selfNormSum Y w t ω| ≤ t * b := by
  calc |selfNormSum Y w t ω| ≤ ∑ i ∈ Finset.range t, |w i ω * Y i ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range t, b := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [abs_mul, abs_of_nonneg (hw i ω).1]
        calc w i ω * |Y i ω| ≤ 1 * |Y i ω| := by
              exact mul_le_mul_of_nonneg_right (hw i ω).2 (abs_nonneg _)
          _ = |Y i ω| := one_mul _
          _ ≤ b := hY i
    _ = t * b := by simp

/-- A bounded random variable is integrable. -/
lemma integrable_of_ae_abs_le [IsFiniteMeasure μ] {f : Ω → ℝ} {c : ℝ}
    (hf : ∀ᵐ ω ∂μ, |f ω| ≤ c) (hfm : AEStronglyMeasurable f μ) : Integrable f μ := by
  refine (memLp_of_bounded (a := -c) (b := c) ?_ hfm 1).integrable le_rfl
  filter_upwards [hf] with ω hω using abs_le.1 hω

/-- One step of the Bernstein exponential supermartingale: if `|Z| ≤ b`, `𝔼[Z | m] = 0`,
`𝔼[Z² | m] = V` with `V` `m`-measurable in `[0, b²]` and `W` `m`-measurable in `[0, 1]`, then
`𝔼[exp (lam W Z - φ_b(lam) W² V / b²) | m] ≤ 1` for `lam ≥ 0`. -/
lemma condExp_exp_mul_sub_le_one [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {Z W V : Ω → ℝ} (hb : 0 < b) (hlam : 0 ≤ lam) (hZm : StronglyMeasurable[mΩ] Z)
    (hZb : ∀ᵐ ω ∂μ, |Z ω| ≤ b) (hZ0 : μ[Z | m] =ᵐ[μ] 0) (hWm : StronglyMeasurable[m] W)
    (hWb : ∀ ω, W ω ∈ Set.Icc 0 1) (hVm : StronglyMeasurable[m] V)
    (hVb : ∀ ω, V ω ∈ Set.Icc 0 (b ^ 2)) (hV : μ[fun ω ↦ Z ω ^ 2 | m] =ᵐ[μ] V) :
    μ[fun ω ↦ exp (lam * (W ω * Z ω) - expSubOneSub (lam * b) * (W ω ^ 2 * V ω) / b ^ 2) | m]
      ≤ᵐ[μ] 1 := by
  set φ := expSubOneSub (lam * b) with hφ
  have hφ0 : 0 ≤ φ := expSubOneSub_nonneg _
  set E : Ω → ℝ := fun ω ↦ exp (-(φ * (W ω ^ 2 * V ω) / b ^ 2)) with hE
  set A : Ω → ℝ := fun ω ↦ exp (lam * (W ω * Z ω)) with hA
  set c1 : Ω → ℝ := fun ω ↦ lam * W ω with hc1
  set c2 : Ω → ℝ := fun ω ↦ φ * W ω ^ 2 / b ^ 2 with hc2
  set Z2 : Ω → ℝ := fun ω ↦ Z ω ^ 2 with hZ2
  -- measurability
  have hEm : StronglyMeasurable[m] E := Real.continuous_exp.comp_stronglyMeasurable
    ((((hWm.pow 2).mul hVm).const_mul φ).div stronglyMeasurable_const).neg
  have hc1m : StronglyMeasurable[m] c1 := hWm.const_mul lam
  have hc2m : StronglyMeasurable[m] c2 := ((hWm.pow 2).const_mul φ).div stronglyMeasurable_const
  have hZ2m : StronglyMeasurable[mΩ] Z2 := hZm.pow 2
  have hAm : StronglyMeasurable[mΩ] A :=
    Real.continuous_exp.comp_stronglyMeasurable (((hWm.mono hm).mul hZm).const_mul lam)
  -- bounds
  have hWZ : ∀ᵐ ω ∂μ, |W ω * Z ω| ≤ b := by
    filter_upwards [hZb] with ω hω
    rw [abs_mul, abs_of_nonneg (hWb ω).1]
    calc W ω * |Z ω| ≤ 1 * |Z ω| := mul_le_mul_of_nonneg_right (hWb ω).2 (abs_nonneg _)
      _ ≤ b := by rw [one_mul]; exact hω
  have hEb : ∀ ω, |E ω| ≤ 1 := fun ω ↦ by
    rw [abs_of_pos (exp_pos _)]
    refine exp_le_one_iff.2 ?_
    have : 0 ≤ φ * (W ω ^ 2 * V ω) / b ^ 2 := by
      have := (hVb ω).1
      positivity
    linarith
  have hAb : ∀ᵐ ω ∂μ, |A ω| ≤ exp (lam * b) := by
    filter_upwards [hWZ] with ω hω
    rw [abs_of_pos (exp_pos _)]
    exact exp_le_exp.2 (by nlinarith [abs_le.1 hω])
  -- integrability
  have hZint : Integrable Z μ := integrable_of_ae_abs_le hZb hZm.aestronglyMeasurable
  have hZ2int : Integrable Z2 μ := by
    refine integrable_of_ae_abs_le (c := b ^ 2) ?_ hZ2m.aestronglyMeasurable
    filter_upwards [hZb] with ω hω
    rw [hZ2, abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg (Z ω), sq_abs (Z ω)]
  have hAint : Integrable A μ := integrable_of_ae_abs_le hAb hAm.aestronglyMeasurable
  have hc1Z : Integrable (c1 * Z) μ := by
    refine integrable_of_ae_abs_le (c := lam * b) ?_ ((hc1m.mono hm).mul hZm).aestronglyMeasurable
    filter_upwards [hWZ] with ω hω
    simp only [Pi.mul_apply, hc1]
    rw [mul_assoc, abs_mul, abs_of_nonneg hlam]
    exact mul_le_mul_of_nonneg_left hω hlam
  have hc2Z2 : Integrable (c2 * Z2) μ := by
    refine integrable_of_ae_abs_le (c := φ) ?_ ((hc2m.mono hm).mul hZ2m).aestronglyMeasurable
    filter_upwards [hWZ] with ω hω
    simp only [Pi.mul_apply, hc2, hZ2]
    have heq : φ * W ω ^ 2 / b ^ 2 * Z ω ^ 2 = φ * ((W ω * Z ω) ^ 2 / b ^ 2) := by ring
    rw [heq, abs_mul, abs_of_nonneg hφ0]
    have hsq : (W ω * Z ω) ^ 2 / b ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [abs_nonneg (W ω * Z ω), sq_abs (W ω * Z ω)]
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have hconst : Integrable (fun _ : Ω ↦ (1 : ℝ)) μ := integrable_const 1
  have hBint : Integrable ((fun _ ↦ (1 : ℝ)) + (c1 * Z + c2 * Z2)) μ :=
    hconst.add (hc1Z.add hc2Z2)
  have hEA : Integrable (E * A) μ := by
    refine integrable_of_ae_abs_le (c := exp (lam * b)) ?_
      ((hEm.mono hm).mul hAm).aestronglyMeasurable
    filter_upwards [hAb] with ω hω
    rw [Pi.mul_apply, abs_mul]
    calc |E ω| * |A ω| ≤ 1 * exp (lam * b) :=
          mul_le_mul (hEb ω) hω (abs_nonneg _) zero_le_one
      _ = exp (lam * b) := one_mul _
  -- the function as a product
  have hfun : (fun ω ↦ exp (lam * (W ω * Z ω) - φ * (W ω ^ 2 * V ω) / b ^ 2)) = E * A := by
    funext ω
    simp only [Pi.mul_apply, hE, hA, ← exp_add]
    ring_nf
  -- conditional expectation of the Taylor upper bound
  have hAB : μ[A | m] ≤ᵐ[μ] μ[(fun _ ↦ (1 : ℝ)) + (c1 * Z + c2 * Z2) | m] := by
    refine condExp_mono hAint hBint ?_
    filter_upwards [hWZ] with ω hω
    have h := exp_mul_le_of_abs_le hb hlam hω
    simp only [Pi.add_apply, Pi.mul_apply, hc1, hc2, hZ2, hA]
    calc exp (lam * (W ω * Z ω))
        ≤ 1 + lam * (W ω * Z ω) + (W ω * Z ω) ^ 2 / b ^ 2 * φ := h
      _ = 1 + (lam * W ω * Z ω + φ * W ω ^ 2 / b ^ 2 * Z ω ^ 2) := by ring
  have hB : μ[(fun _ ↦ (1 : ℝ)) + (c1 * Z + c2 * Z2) | m]
      =ᵐ[μ] fun ω ↦ 1 + c2 ω * V ω := by
    have h1 := condExp_add hconst (hc1Z.add hc2Z2) m
    have h2 := condExp_add hc1Z hc2Z2 m
    have h3 : μ[c1 * Z | m] =ᵐ[μ] c1 * μ[Z | m] :=
      condExp_mul_of_stronglyMeasurable_left hc1m hc1Z hZint
    have h4 : μ[c2 * Z2 | m] =ᵐ[μ] c2 * μ[Z2 | m] :=
      condExp_mul_of_stronglyMeasurable_left hc2m hc2Z2 hZ2int
    have h5 : μ[fun _ : Ω ↦ (1 : ℝ) | m] = fun _ ↦ 1 := condExp_const hm 1
    filter_upwards [h1, h2, h3, h4, hZ0, hV] with ω h1ω h2ω h3ω h4ω hZ0ω hVω
    rw [h1ω, Pi.add_apply, h2ω, Pi.add_apply, h3ω, h4ω, h5]
    simp only [Pi.mul_apply, hZ0ω, Pi.zero_apply, mul_zero, zero_add]
    rw [show μ[Z2 | m] ω = V ω from hVω]
  have hpull : μ[E * A | m] =ᵐ[μ] E * μ[A | m] :=
    condExp_mul_of_stronglyMeasurable_left hEm hEA hAint
  rw [hfun]
  filter_upwards [hpull, hAB, hB] with ω hp hab hbω
  rw [hp, Pi.mul_apply, Pi.one_apply]
  have hEpos : 0 < E ω := exp_pos _
  calc E ω * μ[A | m] ω ≤ E ω * (1 + c2 ω * V ω) := by
        refine mul_le_mul_of_nonneg_left ?_ hEpos.le
        rw [← hbω]; exact hab
    _ ≤ E ω * exp (c2 ω * V ω) := by
        refine mul_le_mul_of_nonneg_left ?_ hEpos.le
        linarith [add_one_le_exp (c2 ω * V ω)]
    _ = 1 := by
        simp only [hE, hc2, ← exp_add]
        rw [exp_eq_one_iff]
        ring

/-- `S t` is `ℱ t`-measurable. -/
lemma stronglyMeasurable_selfNormSum (hYm : ∀ i, StronglyMeasurable[ℱ (i + 1)] (Y i))
    (hwm : ∀ i, StronglyMeasurable[ℱ i] (w i)) (t : ℕ) :
    StronglyMeasurable[ℱ t] (selfNormSum Y w t) := by
  unfold selfNormSum
  refine Finset.stronglyMeasurable_fun_sum _ fun i hi ↦ ?_
  have hi' : i < t := Finset.mem_range.1 hi
  exact ((hwm i).mono (ℱ.mono hi'.le)).mul ((hYm i).mono (ℱ.mono (Nat.succ_le_of_lt hi')))

/-- `V t` is `ℱ t`-measurable. -/
lemma stronglyMeasurable_selfNormVar (hvm : ∀ i, StronglyMeasurable[ℱ i] (v i))
    (hwm : ∀ i, StronglyMeasurable[ℱ i] (w i)) (t : ℕ) :
    StronglyMeasurable[ℱ t] (selfNormVar v w t) := by
  unfold selfNormVar
  refine Finset.stronglyMeasurable_fun_sum _ fun i hi ↦ ?_
  have hi' : i < t := Finset.mem_range.1 hi
  exact (((hwm i).mono (ℱ.mono hi'.le)).pow 2).mul ((hvm i).mono (ℱ.mono hi'.le))

/-- **The Bernstein exponential supermartingale**: for `lam ≥ 0`,
`exp (lam S t - φ_b(lam) V t / b²)` is a supermartingale, where `S = selfNormSum Y w`,
`V = selfNormVar v w` and `φ_b(lam) = expSubOneSub (lam * b)`. -/
lemma supermartingale_exp_selfNorm [IsFiniteMeasure μ] (hb : 0 < b) (hlam : 0 ≤ lam)
    (hYm : ∀ i, StronglyMeasurable[ℱ (i + 1)] (Y i)) (hYb : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ b)
    (hY0 : ∀ i, μ[Y i | ℱ i] =ᵐ[μ] 0)
    (hwm : ∀ i, StronglyMeasurable[ℱ i] (w i)) (hwb : ∀ i ω, w i ω ∈ Set.Icc 0 1)
    (hvm : ∀ i, StronglyMeasurable[ℱ i] (v i)) (hvb : ∀ i ω, v i ω ∈ Set.Icc 0 (b ^ 2))
    (hv : ∀ i, μ[fun ω ↦ Y i ω ^ 2 | ℱ i] =ᵐ[μ] v i) :
    Supermartingale (fun t ω ↦ exp (lam * selfNormSum Y w t ω
      - expSubOneSub (lam * b) * selfNormVar v w t ω / b ^ 2)) ℱ μ := by
  set φ := expSubOneSub (lam * b) with hφ
  have hφ0 : 0 ≤ φ := expSubOneSub_nonneg _
  set M : ℕ → Ω → ℝ := fun t ω ↦ exp (lam * selfNormSum Y w t ω
      - φ * selfNormVar v w t ω / b ^ 2) with hM
  have hMm : ∀ t, StronglyMeasurable[ℱ t] (M t) := fun t ↦
    Real.continuous_exp.comp_stronglyMeasurable
      (((stronglyMeasurable_selfNormSum hYm hwm t).const_mul lam).sub
        (((stronglyMeasurable_selfNormVar hvm hwm t).const_mul φ).div stronglyMeasurable_const))
  have hYball : ∀ᵐ ω ∂μ, ∀ i, |Y i ω| ≤ b := ae_all_iff.2 hYb
  have hMb : ∀ t, ∀ᵐ ω ∂μ, |M t ω| ≤ exp (lam * (t * b)) := by
    intro t
    filter_upwards [hYball] with ω hω
    rw [abs_of_pos (exp_pos _)]
    refine exp_le_exp.2 ?_
    have hS := abs_selfNormSum_le (w := w) hwb (t := t) hω
    have hV := selfNormVar_nonneg (w := w) hvb t ω
    have h1 : lam * selfNormSum Y w t ω ≤ lam * (t * b) :=
      mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hS) hlam
    have h2 : 0 ≤ φ * selfNormVar v w t ω / b ^ 2 := by positivity
    linarith
  have hMint : ∀ t, Integrable (M t) μ := fun t ↦
    integrable_of_ae_abs_le (hMb t) ((hMm t).mono (ℱ.le t)).aestronglyMeasurable
  refine supermartingale_nat hMm hMint fun t ↦ ?_
  set Z : Ω → ℝ := fun ω ↦ exp (lam * (w t ω * Y t ω) - φ * (w t ω ^ 2 * v t ω) / b ^ 2)
    with hZ
  have hstep : M (t + 1) = M t * Z := by
    funext ω
    simp only [hM, hZ, Pi.mul_apply, selfNormSum_succ, selfNormVar_succ, ← exp_add]
    ring_nf
  have hone : μ[Z | ℱ t] ≤ᵐ[μ] 1 :=
    condExp_exp_mul_sub_le_one (ℱ.le t) hb hlam ((hYm t).mono (ℱ.le (t + 1))) (hYb t)
      (hY0 t) (hwm t) (hwb t) (hvm t) (hvb t) (hv t)
  have hZm : StronglyMeasurable[mΩ] Z := by
    have hZeq : Z = fun ω ↦ exp (lam * (w t ω * Y t ω) - φ * (w t ω ^ 2 * v t ω) / b ^ 2) := rfl
    rw [hZeq]
    exact Real.continuous_exp.comp_stronglyMeasurable
      (((((hwm t).mono (ℱ.le t)).mul ((hYm t).mono (ℱ.le (t + 1)))).const_mul lam).sub
        (((((hwm t).mono (ℱ.le t)).pow 2).mul
          ((hvm t).mono (ℱ.le t))).const_mul φ |>.div stronglyMeasurable_const))
  have hZint : Integrable Z μ := by
    refine integrable_of_ae_abs_le (c := exp (lam * b)) ?_ hZm.aestronglyMeasurable
    filter_upwards [hYb t] with ω hω
    rw [abs_of_pos (exp_pos _)]
    refine exp_le_exp.2 ?_
    have hwY : w t ω * Y t ω ≤ b := by
      calc w t ω * Y t ω ≤ |w t ω * Y t ω| := le_abs_self _
        _ = w t ω * |Y t ω| := by rw [abs_mul, abs_of_nonneg (hwb t ω).1]
        _ ≤ 1 * b := mul_le_mul (hwb t ω).2 hω (abs_nonneg _) zero_le_one
        _ = b := one_mul b
    have h2 : 0 ≤ φ * (w t ω ^ 2 * v t ω) / b ^ 2 := by
      have := (hvb t ω).1
      positivity
    nlinarith
  have hMZint : Integrable (M t * Z) μ := by rw [← hstep]; exact hMint (t + 1)
  have hpull : μ[M t * Z | ℱ t] =ᵐ[μ] M t * μ[Z | ℱ t] :=
    condExp_mul_of_stronglyMeasurable_left (hMm t) hMZint hZint
  rw [hstep]
  filter_upwards [hpull, hone] with ω hp ho
  rw [hp, Pi.mul_apply]
  calc M t ω * μ[Z | ℱ t] ω ≤ M t ω * 1 :=
        mul_le_mul_of_nonneg_left ho (exp_pos _).le
    _ = M t ω := mul_one _

/-- The weighted sum of `-Y` is `-S`. -/
lemma selfNormSum_neg (Y w : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    selfNormSum (fun i ω ↦ -Y i ω) w t ω = -selfNormSum Y w t ω := by
  simp [selfNormSum, Finset.sum_neg_distrib]

/-- **The Bernstein exponential supermartingale**, negative side: for `lam ≥ 0`,
`exp (-lam S t - φ_b(lam) V t / b²)` is a supermartingale. -/
lemma supermartingale_exp_neg_selfNorm [IsFiniteMeasure μ] (hb : 0 < b) (hlam : 0 ≤ lam)
    (hYm : ∀ i, StronglyMeasurable[ℱ (i + 1)] (Y i)) (hYb : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ b)
    (hY0 : ∀ i, μ[Y i | ℱ i] =ᵐ[μ] 0)
    (hwm : ∀ i, StronglyMeasurable[ℱ i] (w i)) (hwb : ∀ i ω, w i ω ∈ Set.Icc 0 1)
    (hvm : ∀ i, StronglyMeasurable[ℱ i] (v i)) (hvb : ∀ i ω, v i ω ∈ Set.Icc 0 (b ^ 2))
    (hv : ∀ i, μ[fun ω ↦ Y i ω ^ 2 | ℱ i] =ᵐ[μ] v i) :
    Supermartingale (fun t ω ↦ exp (-(lam * selfNormSum Y w t ω)
      - expSubOneSub (lam * b) * selfNormVar v w t ω / b ^ 2)) ℱ μ := by
  have h := supermartingale_exp_selfNorm (Y := fun i ω ↦ -Y i ω) (w := w) (v := v) (ℱ := ℱ)
    (μ := μ) hb hlam (fun i ↦ (hYm i).neg) (fun i ↦ by simpa using hYb i)
    (fun i ↦ (condExp_neg (Y i) (ℱ i)).trans (by
      filter_upwards [hY0 i] with ω hω
      simp [hω]))
    hwm hwb hvm hvb (fun i ↦ by simpa using hv i)
  simpa [selfNormSum_neg] using h

/-- The integrand of the Bernstein mixture. -/
noncomputable def bernsteinMixtureIntegrand (b s v u : ℝ) : ℝ :=
  (exp (u / b * s - expSubOneSub u * v / b ^ 2)
    + exp (-(u / b * s) - expSubOneSub u * v / b ^ 2)) / 2 * exp (-u)

/-- The Bernstein mixture. -/
noncomputable def bernsteinMixture (b s v : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Ioi 0, ENNReal.ofReal (bernsteinMixtureIntegrand b s v u)

/-- The integrand of the Bernstein mixture is nonnegative. -/
lemma bernsteinMixtureIntegrand_nonneg (b s v u : ℝ) : 0 ≤ bernsteinMixtureIntegrand b s v u := by
  unfold bernsteinMixtureIntegrand
  positivity

/-- The integrand of the Bernstein mixture is jointly continuous. -/
@[fun_prop]
lemma continuous_bernsteinMixtureIntegrand (b : ℝ) :
    Continuous (fun p : ℝ × ℝ × ℝ ↦ bernsteinMixtureIntegrand b p.1 p.2.1 p.2.2) := by
  unfold bernsteinMixtureIntegrand
  fun_prop

/-- The Bernstein mixture is a measurable function of `(s, v)`. -/
lemma measurable_bernsteinMixture (b : ℝ) :
    Measurable (fun p : ℝ × ℝ ↦ bernsteinMixture b p.1 p.2) := by
  have hc : Continuous (fun q : (ℝ × ℝ) × ℝ ↦ bernsteinMixtureIntegrand b q.1.1 q.1.2 q.2) :=
    (continuous_bernsteinMixtureIntegrand b).comp
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  have hf : Measurable (fun q : (ℝ × ℝ) × ℝ ↦
      ENNReal.ofReal (bernsteinMixtureIntegrand b q.1.1 q.1.2 q.2)) :=
    ENNReal.measurable_ofReal.comp hc.measurable
  exact hf.lintegral_prod_right' (ν := volume.restrict (Ioi 0))

/-- At `s = v = 0` the Bernstein mixture is `∫_0^∞ e^{-u} du = 1`. -/
lemma bernsteinMixture_zero_zero (b : ℝ) : bernsteinMixture b 0 0 = 1 := by
  have h : ∀ u, bernsteinMixtureIntegrand b 0 0 u = exp (-u) := fun u ↦ by
    simp [bernsteinMixtureIntegrand]
  simp only [bernsteinMixture, h]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
    (.of_forall fun _ ↦ (exp_pos _).le), integral_exp_neg_Ioi_zero, ENNReal.ofReal_one]

/-- Lower bound on the Bernstein mixture:
`e^T / (8 (1 + √(|s| / b + v / b²))) ≤ M(s, v)` with `T = (v / b² + 1) h(b |s| / (v + b²))`. -/
lemma ofReal_le_bernsteinMixture (hb : 0 < b) (s : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    ENNReal.ofReal (exp ((v / b ^ 2 + 1) * poissonCramer (b * |s| / (v + b ^ 2)))
      / (8 * (1 + √(|s| / b + v / b ^ 2)))) ≤ bernsteinMixture b s v := by
  have hs'0 : 0 ≤ |s| / b := by positivity
  have hv'0 : 0 ≤ v / b ^ 2 := by positivity
  have hmix := Real.ofReal_exp_div_le_lintegral_mixture hs'0 hv'0
  have hT : b * |s| / (v + b ^ 2) = |s| / b / (v / b ^ 2 + 1) := by
    field_simp
  have hpt : ∀ u, ENNReal.ofReal (1 / 2)
      * ENNReal.ofReal (exp (u * (|s| / b) - expSubOneSub u * (v / b ^ 2) - u))
      ≤ ENNReal.ofReal (bernsteinMixtureIntegrand b s v u) := by
    intro u
    rw [← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hA : exp (u * (|s| / b) - expSubOneSub u * (v / b ^ 2) - u)
        = exp (u * (|s| / b) - expSubOneSub u * (v / b ^ 2)) * exp (-u) := by
      rw [← exp_add]; ring_nf
    have hmax : exp (u * (|s| / b) - expSubOneSub u * (v / b ^ 2))
        ≤ exp (u / b * s - expSubOneSub u * v / b ^ 2)
          + exp (-(u / b * s) - expSubOneSub u * v / b ^ 2) := by
      have hvv : expSubOneSub u * (v / b ^ 2) = expSubOneSub u * v / b ^ 2 := by ring
      rcases le_total 0 s with h | h
      · have : u * (|s| / b) = u / b * s := by rw [abs_of_nonneg h]; ring
        rw [this, hvv]
        linarith [exp_pos (-(u / b * s) - expSubOneSub u * v / b ^ 2)]
      · have : u * (|s| / b) = -(u / b * s) := by rw [abs_of_nonpos h]; ring
        rw [this, hvv]
        linarith [exp_pos (u / b * s - expSubOneSub u * v / b ^ 2)]
    rw [hA, bernsteinMixtureIntegrand]
    have he : 0 < exp (-u) := exp_pos _
    nlinarith
  calc ENNReal.ofReal (exp ((v / b ^ 2 + 1) * poissonCramer (b * |s| / (v + b ^ 2)))
        / (8 * (1 + √(|s| / b + v / b ^ 2))))
      = ENNReal.ofReal (1 / 2) * ENNReal.ofReal
          (exp ((v / b ^ 2 + 1) * poissonCramer (|s| / b / (v / b ^ 2 + 1)))
            / (4 * (1 + √(|s| / b + v / b ^ 2)))) := by
        rw [← ENNReal.ofReal_mul (by norm_num), hT]
        congr 1
        have key : ∀ x y : ℝ, 0 < y → x / (8 * y) = 1 / 2 * (x / (4 * y)) := by
          intro x y hy
          field_simp
          ring
        exact key _ _ (by positivity)
    _ ≤ ENNReal.ofReal (1 / 2) * ∫⁻ u in Ioi 0,
          ENNReal.ofReal (exp (u * (|s| / b) - expSubOneSub u * (v / b ^ 2) - u)) := by
        gcongr
    _ = ∫⁻ u in Ioi 0, ENNReal.ofReal (1 / 2) *
          ENNReal.ofReal (exp (u * (|s| / b) - expSubOneSub u * (v / b ^ 2) - u)) := by
        rw [lintegral_const_mul _ (by fun_prop)]
    _ ≤ bernsteinMixture b s v := lintegral_mono fun u ↦ hpt u

/-- Measurability of the Bernstein mixture evaluated at measurable `(S, V)`. -/
lemma measurable_bernsteinMixture_comp {S V : Ω → ℝ} {m : MeasurableSpace Ω}
    (hS : Measurable[m] S) (hV : Measurable[m] V) :
    Measurable[m] (fun ω ↦ bernsteinMixture b (S ω) (V ω)) := by
  have h : Measurable[m] (fun ω ↦ (S ω, V ω)) := hS.prodMk hV
  have h2 := (measurable_bernsteinMixture b).comp h
  exact h2

section Mixture

variable [IsProbabilityMeasure μ] (hb : 0 < b) (hYm : ∀ i, StronglyMeasurable[ℱ (i + 1)] (Y i))
  (hYb : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ b) (hY0 : ∀ i, μ[Y i | ℱ i] =ᵐ[μ] 0)
  (hwm : ∀ i, StronglyMeasurable[ℱ i] (w i)) (hwb : ∀ i ω, w i ω ∈ Set.Icc 0 1)
  (hvm : ∀ i, StronglyMeasurable[ℱ i] (v i)) (hvb : ∀ i ω, v i ω ∈ Set.Icc 0 (b ^ 2))
  (hv : ∀ i, μ[fun ω ↦ Y i ω ^ 2 | ℱ i] =ᵐ[μ] v i)
include hb hYm hYb hY0 hwm hwb hvm hvb hv

/-- For a fixed `u ≥ 0`, the integrand of the mixture is a supermartingale (the average of the
two exponential supermartingales at `lam = u / b`). -/
lemma supermartingale_bernsteinMixtureIntegrand {u : ℝ} (hu : 0 ≤ u) :
    Supermartingale (fun t ω ↦ bernsteinMixtureIntegrand b (selfNormSum Y w t ω)
      (selfNormVar v w t ω) u) ℱ μ := by
  have hlam : 0 ≤ u / b := div_nonneg hu hb.le
  have h1 := supermartingale_exp_selfNorm (lam := u / b) hb hlam hYm hYb hY0 hwm hwb hvm hvb hv
  have h2 := supermartingale_exp_neg_selfNorm (lam := u / b) hb hlam hYm hYb hY0 hwm hwb hvm hvb
    hv
  have hub : u / b * b = u := div_mul_cancel₀ u hb.ne'
  rw [hub] at h1 h2
  have h3 := (h1.add h2).smul_nonneg (c := exp (-u) / 2) (by positivity)
  convert h3 using 1
  funext t ω
  simp only [bernsteinMixtureIntegrand, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

omit hb hYb hY0 hwb hvb hv in
/-- The mixture at time `t` is `ℱ t`-measurable. -/
lemma measurable_selfNorm_mixture (t : ℕ) :
    Measurable[ℱ t] (fun ω ↦ bernsteinMixture b (selfNormSum Y w t ω) (selfNormVar v w t ω)) :=
  measurable_bernsteinMixture_comp (stronglyMeasurable_selfNormSum hYm hwm t).measurable
    (stronglyMeasurable_selfNormVar hvm hwm t).measurable

/-- Supermartingale inequality for the mixture in `ℝ≥0∞`, by Tonelli. -/
lemma setLIntegral_selfNorm_mixture_le {i j : ℕ} (hij : i ≤ j) {A : Set Ω}
    (hA : MeasurableSet[ℱ i] A) :
    ∫⁻ ω in A, bernsteinMixture b (selfNormSum Y w j ω) (selfNormVar v w j ω) ∂μ
      ≤ ∫⁻ ω in A, bernsteinMixture b (selfNormSum Y w i ω) (selfNormVar v w i ω) ∂μ := by
  have hswap : ∀ t, ∫⁻ ω in A, bernsteinMixture b (selfNormSum Y w t ω) (selfNormVar v w t ω) ∂μ
      = ∫⁻ u in Ioi 0, ∫⁻ ω in A, ENNReal.ofReal (bernsteinMixtureIntegrand b
          (selfNormSum Y w t ω) (selfNormVar v w t ω) u) ∂μ := by
    intro t
    have hS := ((stronglyMeasurable_selfNormSum hYm hwm t).mono (ℱ.le t)).measurable
    have hV := ((stronglyMeasurable_selfNormVar hvm hwm t).mono (ℱ.le t)).measurable
    have hprod : Measurable (fun p : Ω × ℝ ↦
        (selfNormSum Y w t p.1, selfNormVar v w t p.1, p.2)) :=
      (hS.comp measurable_fst).prodMk ((hV.comp measurable_fst).prodMk measurable_snd)
    have hmeas := ENNReal.measurable_ofReal.comp
      ((continuous_bernsteinMixtureIntegrand b).measurable.comp hprod)
    have hswap' := lintegral_lintegral_swap (μ := μ.restrict A) (ν := volume.restrict (Ioi 0))
      (f := fun ω u ↦ ENNReal.ofReal (bernsteinMixtureIntegrand b
        (selfNormSum Y w t ω) (selfNormVar v w t ω) u)) hmeas.aemeasurable
    exact hswap'
  rw [hswap j, hswap i]
  refine setLIntegral_mono' measurableSet_Ioi fun u hu ↦ ?_
  have hsup := supermartingale_bernsteinMixtureIntegrand hb hYm hYb hY0 hwm hwb hvm hvb hv
    (le_of_lt hu)
  have hle := hsup.setIntegral_le hij hA
  rw [← ofReal_integral_eq_lintegral_ofReal (hsup.integrable j).integrableOn
      (.of_forall fun _ ↦ bernsteinMixtureIntegrand_nonneg _ _ _ _),
    ← ofReal_integral_eq_lintegral_ofReal (hsup.integrable i).integrableOn
      (.of_forall fun _ ↦ bernsteinMixtureIntegrand_nonneg _ _ _ _)]
  exact ENNReal.ofReal_le_ofReal hle

/-- The mixture has expectation at most `1`. -/
lemma lintegral_selfNorm_mixture_le_one (t : ℕ) :
    ∫⁻ ω, bernsteinMixture b (selfNormSum Y w t ω) (selfNormVar v w t ω) ∂μ ≤ 1 := by
  have h := setLIntegral_selfNorm_mixture_le hb hYm hYb hY0 hwm hwb hvm hvb hv
    (Nat.zero_le t) (A := univ) MeasurableSet.univ
  simp only [Measure.restrict_univ, selfNormSum_zero, selfNormVar_zero,
    bernsteinMixture_zero_zero, lintegral_const, measure_univ, mul_one] at h
  exact h

/-- The mixture is almost surely finite at every time. -/
lemma ae_bernsteinMixture_lt_top :
    ∀ᵐ ω ∂μ, ∀ t, bernsteinMixture b (selfNormSum Y w t ω) (selfNormVar v w t ω) < ⊤ := by
  refine ae_all_iff.2 fun t ↦ ae_lt_top ?_ ?_
  · exact (measurable_selfNorm_mixture hYm hwm hvm t).mono (ℱ.le t) le_rfl
  · exact ne_top_of_le_ne_top ENNReal.one_ne_top
      (lintegral_selfNorm_mixture_le_one hb hYm hYb hY0 hwm hwb hvm hvb hv t)

/-- The Bernstein mixture supermartingale
`M t = ∫_0^∞ (M^{u/b}_t + M^{-,u/b}_t)/2 e^{-u} du`, set to `0` where the integral is infinite. -/
noncomputable def selfNormMixture (b : ℝ) (Y w v : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (bernsteinMixture b (selfNormSum Y w t ω) (selfNormVar v w t ω)).toReal

omit hb hYm hYb hY0 hwm hwb hvm hvb hv [IsProbabilityMeasure μ] in
/-- The mixture supermartingale starts at `1`. -/
lemma selfNormMixture_zero (ω : Ω) : selfNormMixture b Y w v 0 ω = 1 := by
  simp [selfNormMixture, bernsteinMixture_zero_zero]

omit hb hYm hYb hY0 hwm hwb hvm hvb hv [IsProbabilityMeasure μ] in
/-- The mixture supermartingale is nonnegative. -/
lemma selfNormMixture_nonneg (t : ℕ) (ω : Ω) : 0 ≤ selfNormMixture b Y w v t ω :=
  ENNReal.toReal_nonneg

/-- **The mixture supermartingale**. -/
lemma supermartingale_selfNormMixture : Supermartingale (selfNormMixture b Y w v) ℱ μ := by
  have hmeas : ∀ t, Measurable[ℱ t] (fun ω ↦ bernsteinMixture b (selfNormSum Y w t ω)
      (selfNormVar v w t ω)) := measurable_selfNorm_mixture hYm hwm hvm
  have hfin := ae_bernsteinMixture_lt_top hb hYm hYb hY0 hwm hwb hvm hvb hv
  have hone := lintegral_selfNorm_mixture_le_one hb hYm hYb hY0 hwm hwb hvm hvb hv
  have hint : ∀ t, Integrable (selfNormMixture b Y w v t) μ := fun t ↦
    integrable_toReal_of_lintegral_ne_top (((hmeas t).mono (ℱ.le t) le_rfl).aemeasurable)
      (ne_top_of_le_ne_top ENNReal.one_ne_top (hone t))
  refine supermartingale_of_setIntegral_succ_le
    (fun t ↦ (hmeas t).ennreal_toReal.stronglyMeasurable) hint fun t A hA ↦ ?_
  have hAm : MeasurableSet A := ℱ.le t A hA
  have hfinA : ∀ t', ∀ᵐ ω ∂μ.restrict A,
      bernsteinMixture b (selfNormSum Y w t' ω) (selfNormVar v w t' ω) < ⊤ := fun t' ↦
    ae_restrict_of_ae (hfin.mono fun ω hω ↦ hω t')
  have e1 := integral_toReal (μ := μ.restrict A)
    (((hmeas (t + 1)).mono (ℱ.le (t + 1)) le_rfl).aemeasurable) (hfinA (t + 1))
  have e2 := integral_toReal (μ := μ.restrict A)
    (((hmeas t).mono (ℱ.le t) le_rfl).aemeasurable) (hfinA t)
  simp only [selfNormMixture]
  rw [e1, e2]
  have hle := setLIntegral_selfNorm_mixture_le hb hYm hYb hY0 hwm hwb hvm hvb hv
    (Nat.le_succ t) hA
  refine ENNReal.toReal_mono ?_ hle
  exact ne_top_of_le_ne_top ENNReal.one_ne_top
    ((setLIntegral_le_lintegral A _).trans (hone t))

/-- Almost surely, for every `t`, the mixture supermartingale dominates
`e^{T t} / (8 (1 + √(2 t)))` with `T t = (V t / b² + 1) h(b |S t| / (V t + b²))`. -/
lemma ae_exp_div_le_selfNormMixture :
    ∀ᵐ ω ∂μ, ∀ t : ℕ, exp ((selfNormVar v w t ω / b ^ 2 + 1)
        * poissonCramer (b * |selfNormSum Y w t ω| / (selfNormVar v w t ω + b ^ 2)))
        / (8 * (1 + √(2 * t))) ≤ selfNormMixture b Y w v t ω := by
  have hfin := ae_bernsteinMixture_lt_top hb hYm hYb hY0 hwm hwb hvm hvb hv
  have hYall : ∀ᵐ ω ∂μ, ∀ i, |Y i ω| ≤ b := ae_all_iff.2 hYb
  filter_upwards [hfin, hYall] with ω hω hY t
  have hV0 := selfNormVar_nonneg (w := w) hvb t ω
  have h1 := ofReal_le_bernsteinMixture hb (selfNormSum Y w t ω) hV0
  rw [ENNReal.ofReal_le_iff_le_toReal (hω t).ne] at h1
  refine le_trans ?_ h1
  have hS := abs_selfNormSum_le (w := w) hwb (t := t) hY
  have hV := selfNormVar_le (w := w) hvb hwb t ω
  have hsum : |selfNormSum Y w t ω| / b + selfNormVar v w t ω / b ^ 2 ≤ 2 * t := by
    have h1 : |selfNormSum Y w t ω| / b ≤ t := by rw [div_le_iff₀ hb]; exact hS
    have h2 : selfNormVar v w t ω / b ^ 2 ≤ t := by rw [div_le_iff₀ (by positivity)]; exact hV
    linarith
  have hsq : √(|selfNormSum Y w t ω| / b + selfNormVar v w t ω / b ^ 2) ≤ √(2 * t) :=
    Real.sqrt_le_sqrt hsum
  gcongr

/-- **The self-normalized Bernstein inequality** (Lemma 21 of Essakine, Vernade (2026), by the
method of mixtures): for every `δ > 0`,
`ℙ(∃ t, (V t / b² + 1) h(b |S t| / (V t + b²)) ≥ log (1/δ) + log (8 (1 + √(2 t)))) ≤ δ`. -/
theorem measure_exists_log_le_selfNorm_poissonCramer_le {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | ∃ t : ℕ, log (1 / δ) + log (8 * (1 + √(2 * t)))
      ≤ (selfNormVar v w t ω / b ^ 2 + 1)
        * poissonCramer (b * |selfNormSum Y w t ω| / (selfNormVar v w t ω + b ^ 2))}
      ≤ ENNReal.ofReal δ := by
  have hsup := supermartingale_selfNormMixture hb hYm hYb hY0 hwm hwb hvm hvb hv
  have hville := hsup.measure_exists_ge_le selfNormMixture_nonneg (c := 1 / δ) (by positivity)
  simp only [selfNormMixture_zero, integral_const, probReal_univ, smul_eq_mul, one_mul,
    one_div_one_div] at hville
  refine le_trans (measure_mono_ae ?_) hville
  filter_upwards [ae_exp_div_le_selfNormMixture hb hYm hYb hY0 hwm hwb hvm hvb hv] with ω hω hmem
  obtain ⟨t, ht⟩ := hmem
  refine ⟨t, le_trans ?_ (hω t)⟩
  have hpos : 0 < 8 * (1 + √(2 * (t : ℝ))) := by positivity
  rw [le_div_iff₀ hpos]
  calc 1 / δ * (8 * (1 + √(2 * (t : ℝ))))
      = exp (log (1 / δ) + log (8 * (1 + √(2 * (t : ℝ))))) := by
        rw [exp_add, exp_log (by positivity), exp_log hpos]
    _ ≤ _ := exp_le_exp.2 ht

omit hb hYm hYb hY0 hwm hwb hvm hvb hv [IsProbabilityMeasure μ] in
/-- `8 (1 + √(2 t)) ≤ 4 e (2 t + 1)`. -/
lemma eight_mul_one_add_sqrt_le (t : ℕ) : 8 * (1 + √(2 * t)) ≤ 4 * exp 1 * (2 * t + 1) := by
  have he : 2 ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h; simp; linarith
  · have ht : (1 : ℝ) ≤ t := by exact_mod_cast h
    have hsq : √(2 * (t : ℝ)) ≤ 2 * t := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    nlinarith

/-- **The self-normalized Bernstein inequality** with the constant of Lemma 21 of Essakine,
Vernade (2026): for every `δ > 0`,
`ℙ(∃ t, (V t / b² + 1) h(b |S t| / (V t + b²)) ≥ log (1/δ) + log (4 e (2 t + 1))) ≤ δ`. -/
theorem measure_exists_log_le_selfNorm_poissonCramer_le' {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | ∃ t : ℕ, log (1 / δ) + log (4 * exp 1 * (2 * t + 1))
      ≤ (selfNormVar v w t ω / b ^ 2 + 1)
        * poissonCramer (b * |selfNormSum Y w t ω| / (selfNormVar v w t ω + b ^ 2))}
      ≤ ENNReal.ofReal δ := by
  refine le_trans (measure_mono ?_)
    (measure_exists_log_le_selfNorm_poissonCramer_le hb hYm hYb hY0 hwm hwb hvm hvb hv hδ)
  intro ω ⟨t, ht⟩
  refine ⟨t, le_trans ?_ ht⟩
  have := log_le_log (by positivity) (eight_mul_one_add_sqrt_le t)
  linarith

/-- **Explicit form of the self-normalized Bernstein inequality**: for `δ ∈ (0, 1)`, with
probability at least `1 - δ`, for all `t`, `|S t| ≤ √(2 (V t + b²) L t) + (2/3) b L t` where
`L t = log (4 e (2 t + 1) / δ)`. -/
lemma measure_exists_sqrt_add_lt_abs_selfNormSum_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    μ {ω | ∃ t : ℕ, √(2 * (selfNormVar v w t ω + b ^ 2) * log (4 * exp 1 * (2 * t + 1) / δ))
      + 2 / 3 * b * log (4 * exp 1 * (2 * t + 1) / δ) < |selfNormSum Y w t ω|}
      ≤ ENNReal.ofReal δ := by
  refine le_trans (measure_mono ?_)
    (measure_exists_log_le_selfNorm_poissonCramer_le' hb hYm hYb hY0 hwm hwb hvm hvb hv hδ)
  intro ω ⟨t, ht⟩
  refine ⟨t, ?_⟩
  set L := log (4 * exp 1 * (2 * t + 1) / δ) with hL
  have hLeq : log (1 / δ) + log (4 * exp 1 * (2 * t + 1)) = L := by
    rw [hL, ← log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [hLeq]
  by_contra hlt'
  have hlt := not_le.1 hlt'
  have hV0 := selfNormVar_nonneg (w := w) hvb t ω
  set c := selfNormVar v w t ω / b ^ 2 + 1 with hc
  have hcpos : 0 < c := by positivity
  set s := |selfNormSum Y w t ω| / b with hs
  have hs0 : 0 ≤ s := by positivity
  have hL0 : 0 ≤ L := by
    rw [hL]
    refine log_nonneg ?_
    rw [le_div_iff₀ hδ]
    have he : 2 ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
    have : (0 : ℝ) ≤ t := t.cast_nonneg
    nlinarith
  have hsc : b * |selfNormSum Y w t ω| / (selfNormVar v w t ω + b ^ 2) = s / c := by
    rw [hs, hc]
    field_simp
  rw [hsc] at hlt
  have hbound := le_sqrt_add_of_mul_poissonCramer_le hcpos hs0 hL0 hlt.le
  have hsqrt : b * √(2 * c * L) = √(2 * (selfNormVar v w t ω + b ^ 2) * L) := by
    have : 2 * (selfNormVar v w t ω + b ^ 2) * L = b ^ 2 * (2 * c * L) := by
      rw [hc]; field_simp
    rw [this, Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb.le]
  have hSeq : |selfNormSum Y w t ω| = b * s := by rw [hs]; field_simp
  have hfinal : b * s ≤ √(2 * (selfNormVar v w t ω + b ^ 2) * L) + 2 / 3 * b * L := by
    calc b * s ≤ b * (√(2 * c * L) + 2 / 3 * L) := mul_le_mul_of_nonneg_left hbound hb.le
      _ = _ := by rw [mul_add, hsqrt]; ring
  linarith

/-- **Explicit form of the self-normalized Bernstein inequality** with the constants of
Essakine, Vernade (2026): for `δ ∈ (0, 1)`, with probability at least `1 - δ`, for all `t`,
`|S t| ≤ √(2 V t L t) + 3 b L t` where `L t = log (4 e (2 t + 1) / δ)`. -/
lemma measure_exists_sqrt_add_lt_abs_selfNormSum_le' {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    μ {ω | ∃ t : ℕ, √(2 * selfNormVar v w t ω * log (4 * exp 1 * (2 * t + 1) / δ))
      + 3 * b * log (4 * exp 1 * (2 * t + 1) / δ) < |selfNormSum Y w t ω|}
      ≤ ENNReal.ofReal δ := by
  refine le_trans (measure_mono ?_)
    (measure_exists_sqrt_add_lt_abs_selfNormSum_le hb hYm hYb hY0 hwm hwb hvm hvb hv hδ hδ1)
  intro ω ⟨t, ht⟩
  refine ⟨t, lt_of_le_of_lt ?_ ht⟩
  set L := log (4 * exp 1 * (2 * t + 1) / δ) with hL
  have hV0 := selfNormVar_nonneg (w := w) hvb t ω
  have he : exp 1 < 3 := exp_one_lt_three
  have hL2 : 2 ≤ L := by
    rw [hL, le_log_iff_exp_le (by positivity)]
    have ht0 : (0 : ℝ) ≤ t := t.cast_nonneg
    have h1 : exp 2 ≤ 4 * exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
      nlinarith [exp_pos 1]
    have h2 : 4 * exp 1 ≤ 4 * exp 1 * (2 * t + 1) / δ := by
      rw [le_div_iff₀ hδ]
      nlinarith [exp_pos 1]
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hsqrtL : √(2 * L) ≤ L := by
    rw [Real.sqrt_le_left hL0]
    nlinarith
  have hsplit : √(2 * (selfNormVar v w t ω + b ^ 2) * L)
      ≤ √(2 * selfNormVar v w t ω * L) + b * √(2 * L) := by
    have h := Real.sqrt_add_le (a := 2 * selfNormVar v w t ω * L) (b := b ^ 2 * (2 * L))
      (by positivity) (by positivity)
    rw [Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb.le] at h
    calc √(2 * (selfNormVar v w t ω + b ^ 2) * L)
        = √(2 * selfNormVar v w t ω * L + b ^ 2 * (2 * L)) := by ring_nf
      _ ≤ _ := h
  have hbL : b * √(2 * L) ≤ b * L := mul_le_mul_of_nonneg_left hsqrtL hb.le
  nlinarith [hb.le, hL0]

end Mixture

end ProbabilityTheory
