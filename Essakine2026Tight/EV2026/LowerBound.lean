/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Entropic
public import Essakine2026Tight.EV2026.Constants
public import Essakine2026Tight.EV2026.HardMDP
public import Essakine2026Tight.LeanMachineLearning.SequentialLearning.ChangeOfMeasure

/-!
# Theorem 3: lower bound on the sample complexity of entropic best-policy identification

For `S ≥ 6` states, `A ≥ 2` actions, a horizon `H ≥ 3 d` (Assumption 1), `β ≠ 0`, `δ ≤ 1/16` and
`ε` small enough (Condition A for the effective horizon `H - ⌊H/3⌋ - d`), there are a reward
function `r₀` with values in `[0, 1]`, an MDP
`M₀` with reward function `r₀` and an initial state `s₁` such that every `(ε, δ)`-PAC algorithm
for the class of MDPs with reward function `r₀` uses in expectation at least
`(1/5000) (e^{|β| G_max} - 1)² e^{-|β| G_max} e^{2 min(β, 0) ε} S A H log(1/δ) / (e^{|β| ε} - 1)²`
episodes in every run on `M₀`. Theorem 18 is the restatement of this theorem in the appendix.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Learning.MDP.Episodic InformationTheory
open scoped ENNReal

universe u v

namespace Essakine2026Tight

lemma sum_lintegral_le_lintegral_sum {Ω ι : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω}
    (s : Finset ι) (f : ι → Ω → ℝ≥0∞) :
    ∑ i ∈ s, ∫⁻ ω, f i ω ∂μ ≤ ∫⁻ ω, ∑ i ∈ s, f i ω ∂μ := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp only [Finset.sum_cons]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

/-- The final numerical inequality of the lower bound. -/
lemma lowerBound_le_of_card {nS nA H U : ℕ} {β ε δ G : ℝ} (hβ : β ≠ 0) (hε : 0 < ε)
    (hδ : δ ∈ Set.Ioc 0 (1 / 16)) (hH' : 1 ≤ effHorizon nS nA H) (hG0 : 0 ≤ G)
    (hG : G ≤ effHorizon nS nA H) (hU : nS * nA * H ≤ 24 * U) :
    lowerBound nS nA H β ε δ G
      ≤ (U / 2 * Real.log (1 / δ)) / (72 * (hardC β (effHorizon nS nA H) + 1)
        * (hardQ β ε - 1) ^ 2 / hardC β (effHorizon nS nA H) ^ 2) := by
  set c := hardC β (effHorizon nS nA H)
  set q := hardQ β ε
  have hc := hardC_pos hβ hH'
  have hq := one_lt_hardQ hβ hε
  have hL : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ.1]; linarith [hδ.2])
  have hVF : varianceFactor β G ≤ c ^ 2 / (c + 1) := by
    rw [← varianceFactor_eq_hardC]
    exact varianceFactor_mono β hG0 hG
  have hVF0 : 0 ≤ varianceFactor β G := by unfold varianceFactor; positivity
  have hexp : Real.exp ((2 : ℕ) * min β 0 * ε) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) (min_le_right _ _)) hε.le
  have hU' : ((nS * nA * H : ℕ) : ℝ) ≤ 24 * U := by exact_mod_cast hU
  have hq0 : q - 1 ≠ 0 := by linarith
  have hc0 : c ≠ 0 := hc.ne'
  have hc1 : c + 1 ≠ 0 := by linarith
  have hq1 : 0 < (q - 1) ^ 2 := by positivity
  unfold lowerBound
  rw [show Real.exp (|β| * ε) = q from rfl]
  rw [show (U / 2 * Real.log (1 / δ)) / (72 * (c + 1) * (q - 1) ^ 2 / c ^ 2)
      = U * Real.log (1 / δ) * c ^ 2 / (144 * (c + 1) * (q - 1) ^ 2) by
    field_simp; ring]
  rw [le_div_iff₀ (by positivity)]
  have hnum : (1 / ((5000 : ℕ) : ℝ)) = 1 / 5000 := by norm_num
  rw [hnum]
  have hexp0 : 0 ≤ Real.exp ((2 : ℕ) * min β 0 * ε) := (Real.exp_pos _).le
  calc 1 / 5000 * varianceFactor β G
          * (Real.exp ((2 : ℕ) * min β 0 * ε) * ((nS * nA * H : ℕ) : ℝ) / (q - 1) ^ 2)
          * Real.log (1 / δ) * (144 * (c + 1) * (q - 1) ^ 2)
        = 144 / 5000 * (c + 1) * varianceFactor β G
          * (Real.exp ((2 : ℕ) * min β 0 * ε) * ((nS * nA * H : ℕ) : ℝ)) * Real.log (1 / δ) := by
          field_simp
    _ ≤ 144 / 5000 * (c + 1) * (c ^ 2 / (c + 1)) * (1 * (24 * U)) * Real.log (1 / δ) := by
          gcongr
    _ = 3456 / 5000 * c ^ 2 * U * Real.log (1 / δ) := by field_simp; ring
    _ ≤ U * Real.log (1 / δ) * c ^ 2 := by
          have : 0 ≤ c ^ 2 * U * Real.log (1 / δ) := by positivity
          nlinarith

/-- **Theorem 3** (Essakine, Vernade 2026). For finite state and action spaces with `S ≥ 6`,
`A ≥ 2`, a horizon `H ≥ 3 d` with `d = ⌈log_A((S - 3)(A - 1) + 1)⌉` (Assumption 1), `β ≠ 0`,
`δ ∈ (0, 1/16]` and `ε > 0` satisfying Condition A for the effective horizon
`H' = H - ⌊H/3⌋ - d`, there are a reward function `r₀` with
values in `[0, 1]`, an MDP `M₀` with reward function `r₀` and an initial state `s₁` such that
every algorithm which is `(ε, δ)`-PAC for entropic best-policy identification with reward
function `r₀` satisfies, in every run on `M₀`,
`E[τ] ≥ (1/5000) (e^{|β| G_max(M₀)} - 1)² e^{-|β| G_max(M₀)} e^{2 min(β, 0) ε} S A H log(1/δ) /
(e^{|β| ε} - 1)²`. -/
theorem exists_hardMDP_lowerBound_le_lintegral_stoppingTime
    {S A : Type u} [Fintype S] [Fintype A] [Nonempty A]
    [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
    [MeasurableSingletonClass A] (H : ℕ)
    (hS : 6 ≤ Fintype.card S) (hA : 2 ≤ Fintype.card A)
    (hH : 3 * treeDepth (Fintype.card S) (Fintype.card A) ≤ H)
    {β : ℝ} (hβ : β ≠ 0) {δ : ℝ} (hδ : δ ∈ Set.Ioc 0 (1 / 16)) {ε : ℝ} (hε : 0 < ε)
    (hcond : ConditionA β (effHorizon (Fintype.card S) (Fintype.card A) H) ε) :
    ∃ (r₀ : Fin H → S → A → ℝ) (M₀ : EpisodicMDP S A H) (s₁ : S),
      (∀ h s a, r₀ h s a ∈ Set.Icc 0 1) ∧ M₀.HasRewardFn r₀ ∧
      ∀ 𝒜 : BPIAlg S A H, IsEntropicPAC 𝒜 r₀ β ε δ s₁ →
        ∀ {Ω : Type v} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
          (X : ℕ → Ω → Policy S A H) (Y : ℕ → Ω → Traj S H) (out : Ω → Policy S A H),
          𝒜.IsRun (statesEnv M₀ s₁) (fun _ _ ↦ ()) X Y out P →
          ENNReal.ofReal (lowerBound (Fintype.card S) (Fintype.card A) H β ε δ
              (maxReturn M₀ s₁)) ≤
            ∫⁻ ω, (𝒜.stoppingTime (fun _ _ ↦ ()) X Y ω : ℝ≥0∞) ∂P := by
  classical
  have : Nonempty S := Fintype.card_pos_iff.1 (by omega)
  have hd := two_le_treeDepth hS hA
  have hH' : 1 ≤ effHorizon (Fintype.card S) (Fintype.card A) H := by
    unfold effHorizon; omega
  obtain ⟨hp0, hp01, -, hp1, -⟩ := hardParams_valid hβ hH' hε hcond
  refine ⟨hardReward H, hardMDP H β ε none, stateAt S 0, hardReward_mem_Icc H,
    hasRewardFn_hardMDP H β ε none, ?_⟩
  intro 𝒜 hPAC Ω _ P _ X Y out hrun
  set M₀ : EpisodicMDP S A H := hardMDP H β ε none with hM₀
  set s₀ : S := stateAt S 0 with hs₀
  set τ := 𝒜.stoppingTime (fun _ _ ↦ ()) X Y with hτ_def
  set T := ∫⁻ ω, (τ ω : ℝ≥0∞) ∂P with hT_def
  set U := hardTriples (Fintype.card S) (Fintype.card A) H with hU_def
  set pm := hardPMinus β (effHorizon (Fintype.card S) (Fintype.card A) H)
  set pp := hardPPlus β (effHorizon (Fintype.card S) (Fintype.card A) H) ε
  -- Step 0: the case of an infinite expectation
  rcases eq_or_ne T ⊤ with hT | hT
  · rw [hT]; exact le_top
  have hmeasτ : Measurable fun ω ↦ (τ ω : ℝ≥0∞) :=
    (measurable_of_countable (fun n : WithTop ℕ ↦ ENat.toENNReal n)).comp
      (measurable_hittingAfter_sigmaHistory (hrun.isAlgEnvSeq.measurable_obs)
        (hrun.isAlgEnvSeq.measurable_action) (hrun.isAlgEnvSeq.measurable_feedback)
        𝒜.measurableSet_stopSet)
  have hτ : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := by
    filter_upwards [ae_lt_top' hmeasτ.aemeasurable hT] with ω hω
    exact fun h ↦ by simp [h] at hω
  -- the output law
  have hout := hrun.hasLaw_output
  -- the set of policies realizing a triple
  have hmeasE : ∀ t : ℕ × ℕ × ℕ, MeasurableSet {π : Policy S A H | hardTriple π = t} :=
    fun _ ↦ (Set.toFinite _).measurableSet
  -- Step 1: change of measure for each triple
  have hcm : ∀ t ∈ U, klBer ((𝒜.outputMeasure (statesEnv M₀ s₀)).real
        {π | hardTriple π = t})
      ((𝒜.outputMeasure (statesEnv (hardMDP H β ε (some t)) s₀)).real {π | hardTriple π = t})
      ≤ ∑ π, (∫⁻ ω, (pullCount X π (τ ω).toNat ω : ℝ≥0∞) ∂P)
        * (if hardTriple π = t then klBer pm pp else 0) := by
    intro t ht
    have h := IdentAlg.IsRun.klBer_measureReal_outputMeasure_le_sum_pullCount
      (ν := statesKernel M₀ s₀) (ν' := statesKernel (hardMDP H β ε (some t)) s₀) hrun hτ
      (hmeasE t)
    have hxeq : P.real (out ⁻¹' {π | hardTriple π = t})
        = (𝒜.outputMeasure (statesEnv M₀ s₀)).real {π | hardTriple π = t} :=
      hout.measureReal_eq (hmeasE t)
    rw [hxeq] at h
    refine h.trans (Finset.sum_le_sum fun π _ ↦ ?_)
    gcongr
    rw [statesKernel_apply, statesKernel_apply]
    refine (klDiv_statesLaw_hardMDP_le π hS hA hH none (some t)).trans_eq ?_
    have h0 : (succProb β ε H none π : ℝ) = pm := by
      rw [coe_succProb hβ hε hH' hcond]; simp [pm]
    have h1 : (succProb β ε H (some t) π : ℝ) = if hardTriple π = t then pp else pm := by
      rw [coe_succProb hβ hε hH' hcond]; simp [eq_comm, pp, pm]
    rw [h0, h1]
    split_ifs <;> simp
  -- Step 2: the PAC property
  have hy : ∀ t ∈ U, (𝒜.outputMeasure (statesEnv (hardMDP H β ε (some t)) s₀)).real
      {π | hardTriple π = t} ∈ Set.Icc (1 - δ) 1 := by
    intro t ht
    have hbad := hPAC ⟨hardMDP H β ε (some t), hasRewardFn_hardMDP H β ε (some t)⟩
    have hsub : {π : Policy S A H | hardTriple π = t}ᶜ ⊆ {d | ε <
        optEntropicValue (hardMDP H β ε (some t)) β (startStep H) s₀
          - entropicValue (hardMDP H β ε (some t)) β d (startStep H) s₀} :=
      fun π hπ ↦ lt_optEntropicValue_sub_entropicValue_hardMDP hS hA hH hβ hε hH' hcond ht π hπ
    have hc := (measureReal_mono hsub).trans hbad
    rw [measureReal_compl (hmeasE t), probReal_univ] at hc
    exact ⟨by linarith, measureReal_le_one⟩
  have hx : ∀ t ∈ U, (𝒜.outputMeasure (statesEnv M₀ s₀)).real {π | hardTriple π = t}
      ∈ Set.Icc (0 : ℝ) 1 := fun _ _ ↦ ⟨measureReal_nonneg, measureReal_le_one⟩
  have hxsum : ∑ t ∈ U, (𝒜.outputMeasure (statesEnv M₀ s₀)).real {π | hardTriple π = t} ≤ 1 := by
    refine le_trans (le_of_eq (measureReal_biUnion_finset
      (f := fun t ↦ {π : Policy S A H | hardTriple π = t})
      (fun t _ t' _ htt' ↦ Set.disjoint_left.2 fun π h1 h2 ↦
        htt' ((show hardTriple π = t from h1).symm.trans h2)) (fun t _ ↦ hmeasE t)).symm)
      measureReal_le_one
  -- the number of triples
  have hL := card_leafFinset (n := Fintype.card S - 3) hA (by omega)
  have hUcard : Fintype.card S * Fintype.card A * H ≤ 24 * U.card := by
    rw [hU_def, card_hardTriples]
    set L := (leafFinset (Fintype.card S - 3) (Fintype.card A)).card
    calc Fintype.card S * Fintype.card A * H
        ≤ (4 * L) * Fintype.card A * (6 * (H / 3)) := by
          gcongr
          · omega
          · omega
      _ = 24 * (H / 3 * L * Fintype.card A) := by ring
  have hU4 : 4 ≤ U.card := by
    rw [hU_def, card_hardTriples]
    have h1 : 2 ≤ H / 3 := by omega
    have h2 : 2 ≤ (leafFinset (Fintype.card S - 3) (Fintype.card A)).card := by omega
    calc 4 = 2 * 2 * 1 := by norm_num
      _ ≤ H / 3 * (leafFinset (Fintype.card S - 3) (Fintype.card A)).card * Fintype.card A := by
          gcongr; omega
  have hsumkl := ofReal_le_sum_klBer U hU4 hδ.1 hδ.2 hx hxsum hy
  -- Step 3: combining
  have hchain : ENNReal.ofReal (U.card / 2 * Real.log (1 / δ)) ≤ klBer pm pp * T := by
    refine hsumkl.trans ((Finset.sum_le_sum hcm).trans ?_)
    rw [Finset.sum_comm]
    calc ∑ π, ∑ t ∈ U, (∫⁻ ω, (pullCount X π (τ ω).toNat ω : ℝ≥0∞) ∂P)
          * (if hardTriple π = t then klBer pm pp else 0)
        ≤ ∑ π, (∫⁻ ω, (pullCount X π (τ ω).toNat ω : ℝ≥0∞) ∂P) * klBer pm pp := by
          refine Finset.sum_le_sum fun π _ ↦ ?_
          rw [← Finset.mul_sum, Finset.sum_ite_eq]
          gcongr
          split_ifs <;> simp
      _ = klBer pm pp * ∑ π, ∫⁻ ω, (pullCount X π (τ ω).toNat ω : ℝ≥0∞) ∂P := by
          rw [Finset.mul_sum]; simp_rw [mul_comm]
      _ ≤ klBer pm pp * T := by
          gcongr
          refine (sum_lintegral_le_lintegral_sum _ _).trans (lintegral_mono fun ω ↦ ?_)
          rw [← Nat.cast_sum, sum_pullCount]
          induction τ ω using ENat.recTopCoe with
          | top => simp
          | coe n => simp
  -- Step 4: the constants
  set c := hardC β (effHorizon (Fintype.card S) (Fintype.card A) H)
  set q := hardQ β ε
  have hc := hardC_pos hβ hH'
  have hq := one_lt_hardQ hβ hε
  have hk : 0 < 72 * (c + 1) * (q - 1) ^ 2 / c ^ 2 := by
    have : 0 < q - 1 := by linarith
    have : 0 < c + 1 := by linarith
    positivity
  have hK : klBer pm pp ≤ ENNReal.ofReal (72 * (c + 1) * (q - 1) ^ 2 / c ^ 2) := by
    rw [klBer_eq_ofReal (by linarith) hp1.ne]
    exact ENNReal.ofReal_le_ofReal (klBerReal_hardPMinus_hardPPlus_le hβ hH' hε hcond)
  have h2 : ENNReal.ofReal (U.card / 2 * Real.log (1 / δ))
      ≤ ENNReal.ofReal (72 * (c + 1) * (q - 1) ^ 2 / c ^ 2) * T :=
    hchain.trans (by gcongr)
  have h3 : ENNReal.ofReal ((U.card / 2 * Real.log (1 / δ)) / (72 * (c + 1) * (q - 1) ^ 2 / c ^ 2))
      ≤ T := by
    rw [ENNReal.ofReal_div_of_pos hk]
    exact ENNReal.div_le_of_le_mul' h2
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) h3
  have hG0 : 0 ≤ maxReturn M₀ s₀ := maxReturn_nonneg M₀
    (rewardsIn_of_hasRewardFn _ (hasRewardFn_hardMDP H β ε none) measurableSet_Icc
      (hardReward_mem_Icc H)) s₀
  exact lowerBound_le_of_card hβ hε hδ hH' hG0 (maxReturn_hardMDP_le hS hA hH none) hUcard

end Essakine2026Tight
