/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Ville's maximal inequality

`MeasureTheory.Supermartingale.measure_exists_ge_le`: a nonnegative supermartingale `M` indexed
by `ℕ` satisfies `ℙ(∃ n, M n ≥ c) ≤ 𝔼[M 0] / c` for every `c > 0`.

The proof is the optional stopping theorem applied to the hitting time of `[c, ∞)` truncated at
a fixed horizon `N`, followed by the monotone convergence of the events `{∃ n ≤ N, M n ≥ c}`.

As an application, the Bernoulli maximal inequality of Dann et al. (2017), Lemma F.4 (Lemma 20
of Essakine, Vernade (2026)): if `X i ∈ {0, 1}` is adapted with `𝔼[X i | ℱ i] = P i`, then
`ℙ(∃ n, ∑_{i < n} X i < (1/2) ∑_{i < n} P i - log (1/δ)) ≤ δ`
(`MeasureTheory.measure_exists_sum_lt_half_mul_sum_sub_le`), through the one-step bound
`𝔼[e^{P/2 - X} | 𝒢] ≤ 1` (`MeasureTheory.condExp_exp_sub_le_one`).
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ} {c : ℝ}

/-- Ville's inequality at a finite horizon: for a nonnegative supermartingale `M` and `c > 0`,
`c ℙ(∃ n ≤ N, M n ≥ c) ≤ 𝔼[M 0]`. -/
lemma Supermartingale.mul_measureReal_exists_le_le (hM : Supermartingale M ℱ μ)
    (hnonneg : ∀ n ω, 0 ≤ M n ω) (c : ℝ) (N : ℕ) :
    c * μ.real {ω | ∃ n ≤ N, c ≤ M n ω} ≤ ∫ ω, M 0 ω ∂μ := by
  classical
  have hadapted : Adapted ℱ M := hM.1.adapted
  have hmeas : ∀ n, Measurable (M n) := fun n ↦ (hadapted n).mono (ℱ.le n) le_rfl
  set A : Set Ω := {ω | ∃ n ≤ N, c ≤ M n ω} with hA
  have hAmeas : MeasurableSet A := by
    have : A = ⋃ n, ⋃ _ : n ≤ N, {ω | c ≤ M n ω} := by ext ω; simp [hA]
    rw [this]
    exact MeasurableSet.iUnion fun n ↦ MeasurableSet.iUnion fun _ ↦ measurableSet_le
      measurable_const (hmeas n)
  set τ : Ω → WithTop ℕ := fun ω ↦ (hittingBtwn M (Set.Ici c) 0 N ω : ℕ) with hτdef
  have hτ : IsStoppingTime ℱ τ := hadapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hτbdd : ∀ ω, τ ω ≤ (N : WithTop ℕ) := fun ω ↦ by
    simpa [hτdef] using (hittingBtwn_le (u := M) (s := Set.Ici c) (n := 0) ω)
  have hle : (fun _ : Ω ↦ ((0 : ℕ) : WithTop ℕ)) ≤ τ := fun ω ↦ by simp
  -- optional stopping for the submartingale `-M`
  have hstop := hM.neg.expected_stoppedValue_mono (isStoppingTime_const ℱ (0 : ℕ)) hτ hle hτbdd
  have hval : stoppedValue (-M) τ = fun ω ↦ -(stoppedValue M τ ω) := rfl
  rw [hval, stoppedValue_const] at hstop
  simp only [Pi.neg_apply, integral_neg, neg_le_neg_iff] at hstop
  have hint : Integrable (stoppedValue M τ) μ := by
    have h := hM.neg.integrable_stoppedValue hτ hτbdd
    rw [hval] at h
    simpa using h.neg
  have hSnonneg : ∀ ω, 0 ≤ stoppedValue M τ ω := fun ω ↦ hnonneg _ ω
  have hgeA : ∀ ω ∈ A, c ≤ stoppedValue M τ ω := by
    intro ω hω
    obtain ⟨n, hnN, hn⟩ := hω
    exact stoppedValue_hittingBtwn_mem ⟨n, ⟨Nat.zero_le n, hnN⟩, hn⟩
  calc c * μ.real A ≤ ∫ ω in A, stoppedValue M τ ω ∂μ :=
        setIntegral_ge_of_const_le_real hAmeas (measure_ne_top μ A) hgeA hint.integrableOn
    _ ≤ ∫ ω, stoppedValue M τ ω ∂μ :=
        setIntegral_le_integral hint (.of_forall hSnonneg)
    _ ≤ ∫ ω, M 0 ω ∂μ := hstop

/-- **Ville's maximal inequality**: a nonnegative supermartingale `M` indexed by `ℕ` satisfies
`ℙ(∃ n, M n ≥ c) ≤ 𝔼[M 0] / c` for every `c > 0`. -/
lemma Supermartingale.measure_exists_ge_le (hM : Supermartingale M ℱ μ)
    (hnonneg : ∀ n ω, 0 ≤ M n ω) (hc : 0 < c) :
    μ {ω | ∃ n, c ≤ M n ω} ≤ ENNReal.ofReal ((∫ ω, M 0 ω ∂μ) / c) := by
  classical
  have hadapted : Adapted ℱ M := hM.1.adapted
  have hmeas : ∀ n, Measurable (M n) := fun n ↦ (hadapted n).mono (ℱ.le n) le_rfl
  set A : ℕ → Set Ω := fun N ↦ {ω | ∃ n ≤ N, c ≤ M n ω} with hA
  have hAmono : Monotone A := by
    intro N N' hNN' ω hω
    obtain ⟨n, hn, hn'⟩ := hω
    exact ⟨n, hn.trans hNN', hn'⟩
  have hunion : {ω | ∃ n, c ≤ M n ω} = ⋃ N, A N := by
    ext ω
    simp only [hA, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨fun ⟨n, hn⟩ ↦ ⟨n, n, le_rfl, hn⟩, fun ⟨_, n, _, hn⟩ ↦ ⟨n, hn⟩⟩
  have hbound : ∀ N, μ (A N) ≤ ENNReal.ofReal ((∫ ω, M 0 ω ∂μ) / c) := by
    intro N
    have h := hM.mul_measureReal_exists_le_le hnonneg c N
    have hreal : μ.real (A N) ≤ (∫ ω, M 0 ω ∂μ) / c := by
      rw [le_div_iff₀ hc, mul_comm]
      exact h
    calc μ (A N) = ENNReal.ofReal (μ.real (A N)) :=
          (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
      _ ≤ ENNReal.ofReal ((∫ ω, M 0 ω ∂μ) / c) := ENNReal.ofReal_le_ofReal hreal
  rw [hunion, hAmono.measure_iUnion]
  exact iSup_le hbound

section Bernoulli

variable {m : MeasurableSpace Ω} {X P : Ω → ℝ}

/-- One-step bound for a Bernoulli variable: if `X` has values in `{0, 1}` and `𝔼[X | 𝒢] = P`
with `P` a `𝒢`-measurable variable with values in `[0, 1]`, then `𝔼[e^{P/2 - X} | 𝒢] ≤ 1`. -/
lemma condExp_exp_sub_le_one (hm : m ≤ mΩ) (hX : ∀ ω, X ω = 0 ∨ X ω = 1)
    (hXm : StronglyMeasurable[mΩ] X) (hP : ∀ ω, P ω ∈ Set.Icc 0 1)
    (hPm : StronglyMeasurable[m] P) (hcond : μ[X | m] =ᵐ[μ] P) :
    μ[fun ω ↦ Real.exp (P ω / 2 - X ω) | m] ≤ᵐ[μ] 1 := by
  set k : ℝ := 1 - Real.exp (-1) with hk
  set G : Ω → ℝ := fun ω ↦ Real.exp (P ω / 2) with hG
  have hGm : StronglyMeasurable[m] G :=
    Real.continuous_exp.comp_stronglyMeasurable (hPm.div stronglyMeasurable_const)
  have hGm' : StronglyMeasurable[mΩ] G := hGm.mono hm
  have hGbdd : ∀ ω, G ω ∈ Set.Icc 0 (Real.exp (1 / 2)) := fun ω ↦
    ⟨(Real.exp_pos _).le, Real.exp_le_exp.2 (by linarith [(hP ω).2])⟩
  have hXbdd : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1 := fun ω ↦ by
    rcases hX ω with h | h <;> simp [h]
  have hk0 : 0 ≤ k := by
    simp only [hk, sub_nonneg]
    calc Real.exp (-1) ≤ Real.exp 0 := Real.exp_le_exp.2 (by norm_num)
      _ = 1 := Real.exp_zero
  have hk1 : k ≤ 1 := by
    simp only [hk, sub_le_self_iff]
    exact (Real.exp_pos _).le
  have hXint : Integrable X μ :=
    (memLp_of_bounded (μ := μ) (.of_forall hXbdd) hXm.aestronglyMeasurable 1).integrable le_rfl
  have hGint : Integrable G μ :=
    (memLp_of_bounded (μ := μ) (.of_forall hGbdd) hGm'.aestronglyMeasurable 1).integrable le_rfl
  have hKm : StronglyMeasurable[mΩ] ((fun ω ↦ k * G ω) * X) := (hGm'.const_mul k).mul hXm
  have hKbdd : ∀ ω, ((fun ω ↦ k * G ω) * X) ω ∈ Set.Icc 0 (Real.exp (1 / 2)) := by
    intro ω
    have h2 : 0 ≤ k * G ω := mul_nonneg hk0 (hGbdd ω).1
    have h1 : k * G ω ≤ Real.exp (1 / 2) := by nlinarith [(hGbdd ω).1, (hGbdd ω).2]
    refine ⟨mul_nonneg h2 (hXbdd ω).1, ?_⟩
    calc ((fun ω ↦ k * G ω) * X) ω = k * G ω * X ω := rfl
      _ ≤ k * G ω * 1 := by nlinarith [(hXbdd ω).2]
      _ ≤ Real.exp (1 / 2) := by linarith
  have hKint : Integrable ((fun ω ↦ k * G ω) * X) μ :=
    (memLp_of_bounded (μ := μ) (.of_forall hKbdd) hKm.aestronglyMeasurable 1).integrable le_rfl
  have hfun : (fun ω ↦ Real.exp (P ω / 2 - X ω)) = G - (fun ω ↦ k * G ω) * X := by
    funext ω
    rcases hX ω with h | h <;>
      · simp [hG, hk, h, Real.exp_sub, Real.exp_neg, Pi.sub_apply, Pi.mul_apply]
        try ring
  have hcexp : μ[fun ω ↦ Real.exp (P ω / 2 - X ω) | m]
      =ᵐ[μ] fun ω ↦ G ω - k * G ω * P ω := by
    rw [hfun]
    refine (condExp_sub hGint hKint m).trans ?_
    have h1 : μ[G | m] = G := condExp_of_stronglyMeasurable hm hGm hGint
    have h2 : μ[(fun ω ↦ k * G ω) * X | m] =ᵐ[μ] (fun ω ↦ k * G ω) * μ[X | m] :=
      condExp_mul_of_stronglyMeasurable_left (hGm.const_mul k) hKint hXint
    filter_upwards [h2, hcond] with ω hω hω'
    simp only [Pi.sub_apply, h1, hω, Pi.mul_apply, hω']
  filter_upwards [hcexp] with ω hω
  rw [Pi.one_apply, hω]
  have hPk : 1 - k * P ω ≤ Real.exp (-(P ω / 2)) := by
    have he2 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith [Real.add_one_le_exp (1 : ℝ)]
    have h1 : 1 - k * P ω ≤ 1 - P ω / 2 := by
      simp only [hk]
      nlinarith [(hP ω).1, (hP ω).2]
    linarith [Real.add_one_le_exp (-(P ω / 2))]
  have hGpos : 0 < G ω := Real.exp_pos _
  calc G ω - k * G ω * P ω = G ω * (1 - k * P ω) := by ring
    _ ≤ G ω * Real.exp (-(P ω / 2)) := by nlinarith
    _ = 1 := by rw [hG]; rw [← Real.exp_add]; simp

/-- **The Bernoulli maximal inequality** (Lemma F.4 of Dann et al. (2017), Lemma 20 of
Essakine, Vernade (2026)): if `X i` has values in `{0, 1}` and is `ℱ (i + 1)`-measurable, and
`P i` is `ℱ i`-measurable with values in `[0, 1]` and `𝔼[X i | ℱ i] = P i`, then for every
`δ > 0`,
`ℙ(∃ n, ∑_{i < n} X i < (1/2) ∑_{i < n} P i - log (1/δ)) ≤ δ`. -/
theorem measure_exists_sum_lt_half_mul_sum_sub_le [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {X P : ℕ → Ω → ℝ} (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hXm : ∀ i, StronglyMeasurable[ℱ (i + 1)] (X i)) (hP : ∀ i ω, P i ω ∈ Set.Icc 0 1)
    (hPm : ∀ i, StronglyMeasurable[ℱ i] (P i)) (hcond : ∀ i, μ[X i | ℱ i] =ᵐ[μ] P i)
    {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | ∃ n, ∑ i ∈ Finset.range n, X i ω
        < 1 / 2 * ∑ i ∈ Finset.range n, P i ω - Real.log (1 / δ)} ≤ ENNReal.ofReal δ := by
  classical
  set M : ℕ → Ω → ℝ := fun n ω ↦ Real.exp (∑ i ∈ Finset.range n, (P i ω / 2 - X i ω)) with hM
  have hMnonneg : ∀ n ω, 0 ≤ M n ω := fun n ω ↦ (Real.exp_pos _).le
  have hstepm : ∀ i, StronglyMeasurable[ℱ (i + 1)] (fun ω ↦ P i ω / 2 - X i ω) := fun i ↦
    (((hPm i).mono (ℱ.mono i.le_succ)).div stronglyMeasurable_const).sub (hXm i)
  have hMmeas : ∀ n, StronglyMeasurable[ℱ n] (M n) := by
    intro n
    refine Real.continuous_exp.comp_stronglyMeasurable
      (Finset.stronglyMeasurable_fun_sum _ fun i hi ↦ ?_)
    exact (hstepm i).mono (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_range.1 hi)))
  have hMbdd : ∀ n ω, M n ω ≤ Real.exp (n / 2) := by
    intro n ω
    refine Real.exp_le_exp.2 ?_
    calc ∑ i ∈ Finset.range n, (P i ω / 2 - X i ω) ≤ ∑ _i ∈ Finset.range n, (1 / 2 : ℝ) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rcases hX i ω with h | h <;> simp only [h] <;> linarith [(hP i ω).1, (hP i ω).2]
      _ = n / 2 := by simp [div_eq_mul_inv]
  have hMint : ∀ n, Integrable (M n) μ := fun n ↦
    (memLp_of_bounded (μ := μ) (.of_forall fun ω ↦ ⟨hMnonneg n ω, hMbdd n ω⟩)
      ((hMmeas n).mono (ℱ.le n)).aestronglyMeasurable 1).integrable le_rfl
  have hsuper : Supermartingale M ℱ μ := by
    refine supermartingale_nat (fun n ↦ hMmeas n) hMint fun n ↦ ?_
    have hstep : M (n + 1) = M n * fun ω ↦ Real.exp (P n ω / 2 - X n ω) := by
      funext ω
      simp only [hM, Pi.mul_apply, Finset.sum_range_succ, Real.exp_add]
    have hone := condExp_exp_sub_le_one (μ := μ) (ℱ.le n) (hX n)
      ((hXm n).mono (ℱ.le (n + 1))) (hP n) (hPm n) (hcond n)
    have hint2 : Integrable (M n * fun ω ↦ Real.exp (P n ω / 2 - X n ω)) μ := by
      rw [← hstep]; exact hMint (n + 1)
    have hint3 : Integrable (fun ω ↦ Real.exp (P n ω / 2 - X n ω)) μ := by
      refine (memLp_of_bounded (μ := μ) (b := Real.exp (1 / 2)) (.of_forall fun ω ↦
        ⟨(Real.exp_pos _).le, Real.exp_le_exp.2 ?_⟩)
        ((Real.continuous_exp.comp_stronglyMeasurable
          ((hstepm n).mono (ℱ.le (n + 1)))).aestronglyMeasurable) 1).integrable le_rfl
      rcases hX n ω with h | h <;> simp only [h] <;> linarith [(hP n ω).1, (hP n ω).2]
    rw [hstep]
    have hpull := condExp_mul_of_stronglyMeasurable_left (hMmeas n) hint2 hint3
    filter_upwards [hpull, hone] with ω hω hω'
    rw [hω]
    have hmul := mul_le_mul_of_nonneg_left hω' (hMnonneg n ω)
    simpa using hmul
  have hM0 : ∫ ω, M 0 ω ∂μ = 1 := by simp [hM]
  have hville := hsuper.measure_exists_ge_le hMnonneg (c := 1 / δ) (by positivity)
  rw [hM0] at hville
  refine le_trans (measure_mono ?_) (le_trans hville ?_)
  · intro ω hω
    obtain ⟨n, hn⟩ := hω
    refine ⟨n, ?_⟩
    have hsum : ∑ i ∈ Finset.range n, (P i ω / 2 - X i ω)
        = 1 / 2 * ∑ i ∈ Finset.range n, P i ω - ∑ i ∈ Finset.range n, X i ω := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    have hgt : Real.log (1 / δ) ≤ ∑ i ∈ Finset.range n, (P i ω / 2 - X i ω) := by
      rw [hsum]; linarith
    calc (1 : ℝ) / δ = Real.exp (Real.log (1 / δ)) := (Real.exp_log (by positivity)).symm
      _ ≤ M n ω := Real.exp_le_exp.2 hgt
  · rw [one_div, one_div, inv_inv]

end Bernoulli

end MeasureTheory
