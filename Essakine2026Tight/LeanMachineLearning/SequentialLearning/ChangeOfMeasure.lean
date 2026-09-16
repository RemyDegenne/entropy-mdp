/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.SequentialLearning.DivergenceDecomposition
public import Essakine2026Tight.LeanMachineLearning.SequentialLearning.IdentificationAlg
public import Essakine2026Tight.Mathlib.InformationTheory.Pinsker

/-!
# Change of measure at a stopping time

Let `A : IdentAlg Unit 𝓐 𝓨 𝓓` be an identification algorithm (sampling rule, stopping rule
`A.stopSet`, output rule `A.output`) with a finite action set `𝓐`, and consider a run of `A` in
the stationary environment with feedback kernel `ν` on `(Ω, P)` and a run in the stationary
environment with feedback kernel `ν'` on `(Ω', P')`. Write `τ = A.stoppingTime O X Y` for the
number of rounds played and `N_a(τ) = pullCount X a τ` for the number of rounds before `τ` at
which the action `a` was played.

## Main statements

* `IsRun.klDiv_map_stoppedHist_out`: the output is drawn from the same kernel in both runs, so the
  divergence between the laws of the pairs (stopped history, output) is the divergence between the
  laws of the stopped histories; `IsRun.klDiv_map_stoppedHist_out_eq_sum_pullCount`: when `τ` is
  almost surely finite under both runs, it is `∑ a, E[N_a(τ)] KL(ν a ‖ ν' a)`.
* `IsRun.klBer_measureReal_le_sum_pullCount`: **the change of measure** (Lemma 1 of Kaufmann,
  Cappé and Garivier, 2016, Lemma 17 of Essakine and Vernade, 2026), in the one-sided form where
  `τ` is only assumed almost surely finite under the *first* run: for every measurable set `C` of
  (stopped history, output) pairs, with `E`, `E'` the events that the pair belongs to `C`,
  `klBer (P E) (P' E') ≤ ∑ a, E[N_a(τ)] KL(ν a ‖ ν' a)`. The same bound in terms of Bernoulli
  measures is `IsRun.klDiv_bernoulliMeasure_le_sum_pullCount`, in real form
  `IsRun.klBerReal_measureReal_le_toReal_sum_pullCount`, and for an event of the output whose
  probability under `ν'` is given by the law `A.outputMeasure` of the output
  `IsRun.klBer_measureReal_outputMeasure_le_sum_pullCount`.

## Proof

When `τ` is almost surely finite under both runs, the bound is the data-processing inequality
`klBer_measureReal_le_klDiv` for the laws of the pairs, together with the divergence decomposition.
In general we truncate at time `M`: the laws of the histories stopped at time `M`, composed with
the output rule, give the truncation `A.truncSet C M` of `C` (the pairs whose history belongs to
the stopping rule and has at most `M` rounds) the probability that the pair of the run belongs to
`C` and `τ ≤ M` (`map_hittingProcess_compProd_apply_truncSet`), so the bounded version of the
decomposition bounds the binary divergence of these probabilities
(`IsRun.klBer_measureReal_inter_le_sum_pullCount`). As `M → ∞` the probabilities converge, to
`P E` under the first run and to `P' (E' ∩ {τ' < ∞})` under the second; the lower semicontinuity
of `klBer` (`klBer_le_of_tendsto`), applied to `C` and to its complement, and the convexity of
`klBer` in its second argument (`klBer_le_max`) handle the mass `P' {τ' = ∞}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset Filter Topology
open scoped ENNReal ENat

section Limit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]

/-- The probability of `E ∩ {τ ≤ M}` converges to the probability of `E ∩ {τ < ∞}`. -/
private lemma tendsto_measureReal_inter_setOf_le_natCast (E : Set Ω) (τ : Ω → WithTop ℕ) :
    Tendsto (fun M : ℕ ↦ P.real (E ∩ {ω | τ ω ≤ (M : WithTop ℕ)})) atTop
      (𝓝 (P.real (E ∩ {ω | τ ω ≠ ⊤}))) := by
  have hmono : Monotone fun M : ℕ ↦ E ∩ {ω | τ ω ≤ (M : WithTop ℕ)} := fun M N hMN ↦
    Set.inter_subset_inter_right _ fun ω (hω : τ ω ≤ (M : WithTop ℕ)) ↦
      show τ ω ≤ (N : WithTop ℕ) from hω.trans (by exact_mod_cast hMN)
  have hU : ⋃ M : ℕ, E ∩ {ω | τ ω ≤ (M : WithTop ℕ)} = E ∩ {ω | τ ω ≠ ⊤} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    refine ⟨fun ⟨M, hE, hM⟩ ↦ ⟨hE, ne_top_of_le_ne_top (WithTop.natCast_ne_top M) hM⟩,
      fun ⟨hE, hne⟩ ↦ ?_⟩
    obtain ⟨M, hM⟩ := WithTop.ne_top_iff_exists.1 hne
    exact ⟨M, hE, hM ▸ le_rfl⟩
  have h := tendsto_measure_iUnion_atTop (μ := P) hmono
  rw [hU] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

end Limit

namespace Learning.IdentAlg

variable {𝓐 𝓨 𝓓 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {m𝓓 : MeasurableSpace 𝓓} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {A : IdentAlg Unit 𝓐 𝓨 𝓓} {O : ℕ → Ω → Unit} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {O' : ℕ → Ω' → Unit} {X' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨}
  {out : Ω → 𝓓} {out' : Ω' → 𝓓} {env env' : Environment Unit 𝓐 𝓨} {ω : Ω} {M : ℕ}
  {C : Set ((Σ n : ℕ, Hist Unit 𝓐 𝓨 n) × 𝓓)}

section Output

/-- **Appending the output does not change the divergence**: for two runs of the same
identification algorithm, the divergence between the laws of the pairs (history at the stopping
time, output) is the divergence between the laws of the histories at the stopping time. -/
lemma IsRun.klDiv_map_stoppedHist_out (h : A.IsRun env O X Y out P)
    (h' : A.IsRun env' O' X' Y' out' P') :
    klDiv (P.map fun ω ↦ (A.stoppedHist O X Y ω, out ω))
        (P'.map fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) =
      klDiv (P.map (A.stoppedHist O X Y)) (P'.map (A.stoppedHist O' X' Y')) := by
  rw [h.hasCondDistrib_output.map_eq, h'.hasCondDistrib_output.map_eq]
  exact klDiv_compProd_left _ _ _

/-- **Data processing for runs**: for two runs of the same identification algorithm, the
divergence between the laws of the outputs is at most the divergence between the laws of the
histories at the stopping time. -/
lemma IsRun.klDiv_map_out_le_stoppedHist (h : A.IsRun env O X Y out P)
    (h' : A.IsRun env' O' X' Y' out' P') :
    klDiv (P.map out) (P'.map out') ≤
      klDiv (P.map (A.stoppedHist O X Y)) (P'.map (A.stoppedHist O' X' Y')) := by
  rw [← h.klDiv_map_stoppedHist_out h']
  have hmap := klDiv_map_le (P.map fun ω ↦ (A.stoppedHist O X Y ω, out ω))
    (P'.map fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) measurable_snd
  rwa [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
    h.hasCondDistrib_output.aemeasurable, AEMeasurable.map_map_of_aemeasurable
    measurable_snd.aemeasurable h'.hasCondDistrib_output.aemeasurable] at hmap

end Output

section Truncation

/-- The history at the stopping time belongs to the stopping rule exactly when the algorithm
stops. -/
lemma stoppedHist_mem_stopSet_iff :
    A.stoppedHist O X Y ω ∈ A.stopSet ↔ A.stoppingTime O X Y ω ≠ ⊤ := by
  refine ⟨fun hmem htop ↦ ?_, stoppedHist_mem_stopSet_of_ne_top⟩
  exact (hittingAfter_eq_top_iff.1 htop) _ (Nat.zero_le _) hmem

/-- The length of the history at the stopping time. -/
lemma fst_stoppedHist : (A.stoppedHist O X Y ω).1 = (A.stoppingTime O X Y ω).untopA := rfl

/-- The truncation of a set of (stopped history, output) pairs to the histories at which the
algorithm has stopped after at most `M` rounds. -/
def truncSet (A : IdentAlg Unit 𝓐 𝓨 𝓓) (C : Set ((Σ n : ℕ, Hist Unit 𝓐 𝓨 n) × 𝓓)) (M : ℕ) :
    Set ((Σ n : ℕ, Hist Unit 𝓐 𝓨 n) × 𝓓) :=
  C ∩ ((A.stopSet ∩ {x | x.1 ≤ M}) ×ˢ Set.univ)

/-- The truncation of a measurable set is measurable. -/
lemma measurableSet_truncSet (hC : MeasurableSet C) : MeasurableSet (A.truncSet C M) :=
  hC.inter ((A.measurableSet_stopSet.inter (measurableSet_sigma_fst_le M)).prod
    MeasurableSet.univ)

/-- The section of the truncation at a history outside `A.stopSet ∩ {x | x.1 ≤ M}` is empty. -/
lemma prodMk_preimage_truncSet_eq_empty {x : Σ n : ℕ, Hist Unit 𝓐 𝓨 n}
    (hx : x ∉ A.stopSet ∩ {z : Σ n : ℕ, Hist Unit 𝓐 𝓨 n | z.1 ≤ M}) :
    Prod.mk x ⁻¹' A.truncSet C M = ∅ := by
  ext d
  simp [truncSet, hx]

/-- The pair (history at the stopping time, output) belongs to the truncation of `C` exactly when
it belongs to `C` and the algorithm has stopped after at most `M` rounds. -/
lemma preimage_truncSet :
    (fun ω ↦ (A.stoppedHist O X Y ω, out ω)) ⁻¹' A.truncSet C M =
      (fun ω ↦ (A.stoppedHist O X Y ω, out ω)) ⁻¹' C ∩
        {ω | A.stoppingTime O X Y ω ≤ (M : WithTop ℕ)} := by
  ext ω
  constructor
  · rintro ⟨hCω, hmem, -⟩
    refine ⟨hCω, ?_⟩
    have hle : (A.stoppedHist O X Y ω).1 ≤ M := hmem.2
    rw [fst_stoppedHist] at hle
    exact (WithTop.untopA_le_iff (stoppedHist_mem_stopSet_iff.1 hmem.1)).1 hle
  · rintro ⟨hCω, hle⟩
    have hne : A.stoppingTime O X Y ω ≠ ⊤ := ne_top_of_le_ne_top (WithTop.natCast_ne_top M) hle
    refine ⟨hCω, ⟨stoppedHist_mem_stopSet_iff.2 hne, ?_⟩, Set.mem_univ _⟩
    change (A.stoppedHist O X Y ω).1 ≤ M
    rw [fst_stoppedHist]
    exact (WithTop.untopA_le_iff hne).2 hle

/-- The history stopped at time `M` and the history at the stopping time have the same
`A.output`-measure on the truncation of `C`: they agree when the algorithm has stopped after at
most `M` rounds, and otherwise neither belongs to the truncation. -/
lemma output_apply_hittingProcess_eq (ω : Ω) :
    A.output (hittingProcess (sigmaHistory O X Y) A.stopSet 0 M ω)
        (Prod.mk (hittingProcess (sigmaHistory O X Y) A.stopSet 0 M ω) ⁻¹' A.truncSet C M) =
      A.output (A.stoppedHist O X Y ω)
        (Prod.mk (A.stoppedHist O X Y ω) ⁻¹' A.truncSet C M) := by
  rcases le_or_gt (A.stoppingTime O X Y ω) (M : WithTop ℕ) with hle | hlt
  · have heq : hittingProcess (sigmaHistory O X Y) A.stopSet 0 M ω = A.stoppedHist O X Y ω :=
      hittingProcess_eq_of_ge (i := M) hle
    rw [heq]
  · have hZ : hittingProcess (sigmaHistory O X Y) A.stopSet 0 M ω = sigmaHistory O X Y M ω :=
      hittingProcess_eq_of_le (i := M) hlt.le
    have h1 : A.stoppedHist O X Y ω ∉ A.stopSet ∩ {z : Σ n : ℕ, Hist Unit 𝓐 𝓨 n | z.1 ≤ M} := by
      rintro ⟨hmem, hfst⟩
      have hne : A.stoppingTime O X Y ω ≠ ⊤ := stoppedHist_mem_stopSet_iff.1 hmem
      rw [Set.mem_ofPred_eq, fst_stoppedHist, WithTop.untopA_le_iff hne] at hfst
      exact absurd hfst (not_le.2 hlt)
    have h2 : hittingProcess (sigmaHistory O X Y) A.stopSet 0 M ω ∉
        A.stopSet ∩ {z : Σ n : ℕ, Hist Unit 𝓐 𝓨 n | z.1 ≤ M} := by
      rintro ⟨hmem, -⟩
      rw [hZ] at hmem
      exact notMem_of_lt_hittingAfter hlt (Nat.zero_le _) hmem
    rw [prodMk_preimage_truncSet_eq_empty (C := C) h1,
      prodMk_preimage_truncSet_eq_empty (C := C) h2]
    simp

/-- The law of the history stopped at time `M`, composed with the output rule, gives the
truncation of `C` the probability that the (stopped history, output) pair of the run belongs to
`C` and the algorithm stops after at most `M` rounds. -/
lemma map_hittingProcess_compProd_apply_truncSet (h : A.IsRun env O X Y out P)
    (hC : MeasurableSet C) (M : ℕ) :
    (P.map (hittingProcess (sigmaHistory O X Y) A.stopSet 0 M) ⊗ₘ A.output) (A.truncSet C M) =
      P ((fun ω ↦ (A.stoppedHist O X Y ω, out ω)) ⁻¹' C ∩
        {ω | A.stoppingTime O X Y ω ≤ (M : WithTop ℕ)}) := by
  have hCM : MeasurableSet (A.truncSet C M) := measurableSet_truncSet hC
  have hstep := h.isAlgEnvSeq.measurable_step
  have hZ : Measurable (hittingProcess (sigmaHistory O X Y) A.stopSet 0 M) :=
    measurable_hittingProcess_sigmaPrefix (Z := step O X Y) hstep A.measurableSet_stopSet M
  have hV : Measurable (A.stoppedHist O X Y) :=
    measurable_hittingValue_sigmaPrefix (Z := step O X Y) hstep A.measurableSet_stopSet
  rw [Measure.compProd_apply hCM, lintegral_map (Kernel.measurable_kernel_prodMk_left hCM) hZ]
  calc ∫⁻ ω, A.output (hittingProcess (sigmaHistory O X Y) A.stopSet 0 M ω)
        (Prod.mk (hittingProcess (sigmaHistory O X Y) A.stopSet 0 M ω) ⁻¹' A.truncSet C M) ∂P
      = ∫⁻ ω, A.output (A.stoppedHist O X Y ω)
          (Prod.mk (A.stoppedHist O X Y ω) ⁻¹' A.truncSet C M) ∂P :=
        lintegral_congr fun ω ↦ output_apply_hittingProcess_eq ω
    _ = (P.map (A.stoppedHist O X Y) ⊗ₘ A.output) (A.truncSet C M) := by
        rw [Measure.compProd_apply hCM, lintegral_map (Kernel.measurable_kernel_prodMk_left hCM) hV]
    _ = P ((fun ω ↦ (A.stoppedHist O X Y ω, out ω)) ⁻¹' A.truncSet C M) := by
        rw [← h.hasCondDistrib_output.map_eq,
          Measure.map_apply_of_aemeasurable h.hasCondDistrib_output.aemeasurable hCM]
    _ = _ := by rw [preimage_truncSet]

/-- **Change of measure at a bounded stopping time**: the binary divergence between the
probabilities that the (stopped history, output) pair belongs to `C` *and the algorithm stops
after at most `M` rounds* is at most the divergence between the laws of the histories stopped at
time `M`. -/
lemma IsRun.klBer_le_klDiv_map_hittingProcess (h : A.IsRun env O X Y out P)
    (h' : A.IsRun env' O' X' Y' out' P') (hC : MeasurableSet C) (M : ℕ) :
    klBer (P.real ((fun ω ↦ (A.stoppedHist O X Y ω, out ω)) ⁻¹' C ∩
          {ω | A.stoppingTime O X Y ω ≤ (M : WithTop ℕ)}))
        (P'.real ((fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) ⁻¹' C ∩
          {ω | A.stoppingTime O' X' Y' ω ≤ (M : WithTop ℕ)})) ≤
      klDiv (P.map (hittingProcess (sigmaHistory O X Y) A.stopSet 0 M))
        (P'.map (hittingProcess (sigmaHistory O' X' Y') A.stopSet 0 M)) := by
  have e1 := map_hittingProcess_compProd_apply_truncSet h hC M
  have e2 := map_hittingProcess_compProd_apply_truncSet h' hC M
  rw [measureReal_def, measureReal_def, ← e1, ← e2, ← measureReal_def, ← measureReal_def]
  refine (klBer_measureReal_le_klDiv (measurableSet_truncSet hC)).trans_eq ?_
  exact klDiv_compProd_left _ _ _

end Truncation

section StationaryEnv

variable {ν ν' : Kernel 𝓐 𝓨} [IsMarkovKernel ν] [IsMarkovKernel ν'] [Fintype 𝓐] [DecidableEq 𝓐]
  [MeasurableSingletonClass 𝓐] [MeasurableSpace.CountablyGenerated 𝓨]

/-- **Divergence decomposition for a run**: for two runs of the same identification algorithm in
two stationary environments with feedback kernels `ν` and `ν'`, with almost surely finite
stopping times, the divergence between the laws of the pairs (stopped history, output) is
`∑ a, E[N_a(τ)] KL(ν a ‖ ν' a)`. -/
lemma IsRun.klDiv_map_stoppedHist_out_eq_sum_pullCount
    (h : A.IsRun (stationaryEnv ν) O X Y out P)
    (h' : A.IsRun (stationaryEnv ν') O' X' Y' out' P')
    (hτ : ∀ᵐ ω ∂P, A.stoppingTime O X Y ω ≠ ⊤)
    (hτ' : ∀ᵐ ω ∂P', A.stoppingTime O' X' Y' ω ≠ ⊤) :
    klDiv (P.map fun ω ↦ (A.stoppedHist O X Y ω, out ω))
        (P'.map fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) =
      ∑ a, (∫⁻ ω, (pullCount X a (ENat.toNat (A.stoppingTime O X Y ω)) ω : ℝ≥0∞) ∂P) *
        klDiv (ν a) (ν' a) := by
  rw [h.klDiv_map_stoppedHist_out h']
  exact h.isAlgEnvSeq.klDiv_map_hittingValue_sigmaHistory_eq_sum_pullCount h'.isAlgEnvSeq
    A.measurableSet_stopSet hτ hτ'

/-- **Change of measure at a bounded stopping time**, with the divergence decomposition: the
binary divergence between the probabilities that the (stopped history, output) pair belongs to
`C` and the algorithm stops after at most `M` rounds is at most `∑ a, E[N_a(τ)] KL(ν a ‖ ν' a)`,
when the stopping time is almost surely finite under the first environment. -/
lemma IsRun.klBer_measureReal_inter_le_sum_pullCount (h : A.IsRun (stationaryEnv ν) O X Y out P)
    (h' : A.IsRun (stationaryEnv ν') O' X' Y' out' P')
    (hτ : ∀ᵐ ω ∂P, A.stoppingTime O X Y ω ≠ ⊤) (hC : MeasurableSet C) (M : ℕ) :
    klBer (P.real ((fun ω ↦ (A.stoppedHist O X Y ω, out ω)) ⁻¹' C ∩
          {ω | A.stoppingTime O X Y ω ≤ (M : WithTop ℕ)}))
        (P'.real ((fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) ⁻¹' C ∩
          {ω | A.stoppingTime O' X' Y' ω ≤ (M : WithTop ℕ)})) ≤
      ∑ a, (∫⁻ ω, (pullCount X a (ENat.toNat (A.stoppingTime O X Y ω)) ω : ℝ≥0∞) ∂P) *
        klDiv (ν a) (ν' a) := by
  refine (h.klBer_le_klDiv_map_hittingProcess h' hC M).trans ?_
  rw [h.isAlgEnvSeq.klDiv_map_hittingProcess_sigmaHistory_eq_sum_pullCount h'.isAlgEnvSeq
    A.measurableSet_stopSet M]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  gcongr ?_ * _
  refine lintegral_mono_ae ?_
  filter_upwards [hτ] with ω hω
  exact Nat.cast_le.2 (pullCount_mono a (ENat.toNat_le_toNat (min_le_left _ _) hω) ω)

/-- **Change of measure at a stopping time** (one-sided form of Lemma 1 of Kaufmann, Cappé and
Garivier, 2016). For two runs of the same identification algorithm in two stationary environments
with feedback kernels `ν` and `ν'`, with a stopping time which is almost surely finite under the
*first* environment, and for every measurable set `C` of (stopped history, output) pairs, the
binary divergence between the probabilities of `C` under the two runs is at most
`∑ a, E[N_a(τ)] KL(ν a ‖ ν' a)`, where `N_a(τ) = pullCount X a τ` is the number of rounds before
stopping at which the action `a` was played. -/
theorem IsRun.klBer_measureReal_le_sum_pullCount (h : A.IsRun (stationaryEnv ν) O X Y out P)
    (h' : A.IsRun (stationaryEnv ν') O' X' Y' out' P')
    (hτ : ∀ᵐ ω ∂P, A.stoppingTime O X Y ω ≠ ⊤) (hC : MeasurableSet C) :
    klBer (P.real ((fun ω ↦ (A.stoppedHist O X Y ω, out ω)) ⁻¹' C))
        (P'.real ((fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) ⁻¹' C)) ≤
      ∑ a, (∫⁻ ω, (pullCount X a (ENat.toNat (A.stoppingTime O X Y ω)) ω : ℝ≥0∞) ∂P) *
        klDiv (ν a) (ν' a) := by
  set D := ∑ a, (∫⁻ ω, (pullCount X a (ENat.toNat (A.stoppingTime O X Y ω)) ω : ℝ≥0∞) ∂P) *
    klDiv (ν a) (ν' a) with hD
  set E := (fun ω ↦ (A.stoppedHist O X Y ω, out ω)) ⁻¹' C with hE
  set E' := (fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) ⁻¹' C with hE'
  set t' := {ω | A.stoppingTime O' X' Y' ω ≠ ⊤} with ht'
  have hEm : NullMeasurableSet E P :=
    h.hasCondDistrib_output.aemeasurable.nullMeasurableSet_preimage hC
  have hEm' : NullMeasurableSet E' P' :=
    h'.hasCondDistrib_output.aemeasurable.nullMeasurableSet_preimage hC
  have hEc : (fun ω ↦ (A.stoppedHist O X Y ω, out ω)) ⁻¹' Cᶜ = Eᶜ := rfl
  have hEc' : (fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) ⁻¹' Cᶜ = E'ᶜ := rfl
  -- the stopping time is almost surely finite under `P`
  have hfin : ∀ F : Set Ω, P.real (F ∩ {ω | A.stoppingTime O X Y ω ≠ ⊤}) = P.real F := fun F ↦
    measureReal_congr (inter_ae_eq_left_of_ae_eq_univ (Filter.eventuallyEqSet_univ.2 hτ))
  -- bounds at time `M` and passage to the limit
  have h1 : klBer (P.real E) (P'.real (E' ∩ t')) ≤ D := by
    refine klBer_le_of_tendsto (fun M ↦ ⟨measureReal_nonneg, measureReal_le_one⟩)
      (fun M ↦ ⟨measureReal_nonneg, measureReal_le_one⟩) ?_
      (tendsto_measureReal_inter_setOf_le_natCast E' _)
      (h.klBer_measureReal_inter_le_sum_pullCount h' hτ hC)
    rw [← hfin E]
    exact tendsto_measureReal_inter_setOf_le_natCast E _
  have h2 : klBer (P.real Eᶜ) (P'.real (E'ᶜ ∩ t')) ≤ D := by
    refine klBer_le_of_tendsto (fun M ↦ ⟨measureReal_nonneg, measureReal_le_one⟩)
      (fun M ↦ ⟨measureReal_nonneg, measureReal_le_one⟩) ?_
      (tendsto_measureReal_inter_setOf_le_natCast E'ᶜ _)
      (fun M ↦ by
        have hM := h.klBer_measureReal_inter_le_sum_pullCount h' hτ hC.compl M
        rw [hEc, hEc'] at hM
        exact hM)
    rw [← hfin Eᶜ]
    exact tendsto_measureReal_inter_setOf_le_natCast Eᶜ _
  -- the complement
  have hcompl : P.real Eᶜ = 1 - P.real E := by
    rw [measureReal_compl₀ hEm, probReal_univ]
  have h2' : klBer (P.real E) (1 - P'.real (E'ᶜ ∩ t')) ≤ D := by
    rw [← klBer_one_sub, sub_sub_cancel, ← hcompl]
    exact h2
  -- convexity in the second argument
  have hle1 : P'.real (E' ∩ t') ≤ P'.real E' := measureReal_mono Set.inter_subset_left
  have hle2 : P'.real E' ≤ 1 - P'.real (E'ᶜ ∩ t') := by
    have h3 : P'.real (E'ᶜ ∩ t') ≤ P'.real E'ᶜ := measureReal_mono Set.inter_subset_left
    rw [measureReal_compl₀ hEm', probReal_univ] at h3
    linarith
  refine (klBer_le_max measureReal_nonneg hle1 hle2
    (by linarith [measureReal_nonneg (μ := P') (s := E'ᶜ ∩ t')])).trans ?_
  exact max_le h1 h2'

/-- **Change of measure at a stopping time**, with Bernoulli measures: the form of
`IsRun.klBer_measureReal_le_sum_pullCount` in which the binary divergence is the divergence
between the laws of the indicators of the two events. -/
theorem IsRun.klDiv_bernoulliMeasure_le_sum_pullCount (h : A.IsRun (stationaryEnv ν) O X Y out P)
    (h' : A.IsRun (stationaryEnv ν') O' X' Y' out' P')
    (hτ : ∀ᵐ ω ∂P, A.stoppingTime O X Y ω ≠ ⊤) (hC : MeasurableSet C) :
    klDiv (bernoulliMeasure true false
          ⟨P.real ((fun ω ↦ (A.stoppedHist O X Y ω, out ω)) ⁻¹' C), measureReal_nonneg,
            measureReal_le_one⟩)
        (bernoulliMeasure true false
          ⟨P'.real ((fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) ⁻¹' C), measureReal_nonneg,
            measureReal_le_one⟩) ≤
      ∑ a, (∫⁻ ω, (pullCount X a (ENat.toNat (A.stoppingTime O X Y ω)) ω : ℝ≥0∞) ∂P) *
        klDiv (ν a) (ν' a) := by
  rw [klDiv_bernoulliMeasure (by decide)]
  exact h.klBer_measureReal_le_sum_pullCount h' hτ hC

/-- **Change of measure at a stopping time**, real form: when the probability of the event under
the second run is in `(0, 1)` and the right-hand side is finite, the real binary divergence
`klBerReal` is bounded by the real right-hand side. -/
theorem IsRun.klBerReal_measureReal_le_toReal_sum_pullCount
    (h : A.IsRun (stationaryEnv ν) O X Y out P) (h' : A.IsRun (stationaryEnv ν') O' X' Y' out' P')
    (hτ : ∀ᵐ ω ∂P, A.stoppingTime O X Y ω ≠ ⊤) (hC : MeasurableSet C)
    (h0 : 0 < P'.real ((fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) ⁻¹' C))
    (h1 : P'.real ((fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) ⁻¹' C) < 1)
    (hD : ∑ a, (∫⁻ ω, (pullCount X a (ENat.toNat (A.stoppingTime O X Y ω)) ω : ℝ≥0∞) ∂P) *
      klDiv (ν a) (ν' a) ≠ ∞) :
    klBerReal (P.real ((fun ω ↦ (A.stoppedHist O X Y ω, out ω)) ⁻¹' C))
        (P'.real ((fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) ⁻¹' C)) ≤
      (∑ a, (∫⁻ ω, (pullCount X a (ENat.toNat (A.stoppingTime O X Y ω)) ω : ℝ≥0∞) ∂P) *
        klDiv (ν a) (ν' a)).toReal := by
  have hle := h.klBer_measureReal_le_sum_pullCount h' hτ hC
  rwa [klBer_eq_ofReal h0.ne' h1.ne, ENNReal.ofReal_le_iff_le_toReal hD] at hle

/-- **Change of measure at a stopping time**, for an event of the output: for a run of `A` in the
stationary environment with feedback kernel `ν` whose stopping time is almost surely finite, and
any other feedback kernel `ν'`, the binary divergence between the probability that the output
belongs to `s` and the probability of `s` under the law `A.outputMeasure (stationaryEnv ν')` of
the output in the second environment is at most `∑ a, E[N_a(τ)] KL(ν a ‖ ν' a)`. -/
theorem IsRun.klBer_measureReal_outputMeasure_le_sum_pullCount
    (h : A.IsRun (stationaryEnv ν) O X Y out P) (hτ : ∀ᵐ ω ∂P, A.stoppingTime O X Y ω ≠ ⊤)
    {s : Set 𝓓} (hs : MeasurableSet s) :
    klBer (P.real (out ⁻¹' s)) ((A.outputMeasure (stationaryEnv ν')).real s) ≤
      ∑ a, (∫⁻ ω, (pullCount X a (ENat.toNat (A.stoppingTime O X Y ω)) ω : ℝ≥0∞) ∂P) *
        klDiv (ν a) (ν' a) := by
  have hrun := A.isRun_runMeasure (stationaryEnv ν')
  have hle := h.klBer_measureReal_le_sum_pullCount hrun hτ (MeasurableSet.univ.prod hs)
  simp only [Set.mk_preimage_prod, Set.preimage_univ, Set.univ_inter] at hle
  rwa [← A.map_snd_runMeasure, map_measureReal_apply measurable_snd hs]

end StationaryEnv

end Learning.IdentAlg
