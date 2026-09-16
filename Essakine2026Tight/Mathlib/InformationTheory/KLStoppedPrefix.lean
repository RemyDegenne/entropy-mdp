/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.ChainRule
public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.DataProcessing
public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.Restrict
public import Essakine2026Tight.Mathlib.Probability.Process.SigmaPrefix

/-!
# The chain rule for the Kullback–Leibler divergence at a stopping time

Let `Z : (n : ℕ) → Ω → X n` be a process with values in a family of measurable spaces `X n` and
`P`, `P'` two probability measures on `Ω` under which `Z n` has conditional law `κ n`,
resp. `κ' n`, given the prefix of length `n`, for Markov kernels
`κ n, κ' n : Kernel (Π i : Fin n, X i) (X n)`. Let `τ` be a stopping time of the prefix
filtration (`prefixFiltration`, see `Essakine2026Tight.Mathlib.Probability.Process.SigmaPrefix`):
whether `τ ≤ n` is determined by the first `n` steps. The divergence between the laws under `P`
and `P'` of the prefix stopped at time `M` is the sum over the steps `t < M` of the conditional
divergences of `κ t` and `κ' t` given the prefix of length `t`, on the event `{t < τ}`
(`klDiv_map_stoppedProcess_sigmaPrefix_compProd`): the *chain rule* at a bounded stopping time.
When `τ` is almost surely finite under `P` and `P'`, the divergence between the laws of the
stopped prefix is the series of these terms (`klDiv_map_stoppedValue_sigmaPrefix_compProd`).
Both are stated in composition-product form, on arbitrary measurable spaces, and in integral
form (`klDiv_map_stoppedProcess_sigmaPrefix`, `klDiv_map_stoppedValue_sigmaPrefix`, when the
`X n` are countably generated), the latter reading
`klDiv (P.map (stoppedValue (sigmaPrefix Z) τ)) (P'.map (stoppedValue (sigmaPrefix Z) τ))
  = ∫⁻ ω, ∑ t < τ ω, klDiv (κ t (finPrefix Z t ω)) (κ' t (finPrefix Z t ω)) ∂P`.

The bounded version is proved by induction on `M`: the law of the prefix stopped at time `M + 1`
splits according to whether `τ ≤ M` (`map_stoppedProcess_sigmaPrefix_succ_eq_add`), the
divergence is additive over disjoint supports (`klDiv_add_add_of_measure_eq_zero`; the supports
are separated thanks to the set `B` of prefixes of length `M` on which `τ ≤ M`, given by
`IsStoppingTime.exists_measurableSet_preimage_finPrefix`) and the chain rule
`klDiv_compProd_eq_add` handles the step `M`, whose conditional law survives the restriction to
`{M < τ}` (`HasCondDistrib.restrict_lt_of_isStoppingTime`). The almost surely finite version
follows by monotone convergence (`klDiv_eq_iSup_restrict`) and the data-processing inequality,
since the prefix stopped at time `M` is the truncation of the stopped prefix
(`HasLaw.stoppedProcess_sigmaPrefix`). The integral forms follow from the composition-product
forms by the integrated chain rule `klDiv_compProd_right_eq_lintegral`.

For a stopping rule `S` (a measurable set of finite sequences of variable length), the laws of
the prefixes stopped by the rule, `hittingValue (sigmaPrefix Z) S 0` and
`hittingProcess (sigmaPrefix Z) S 0 M`, are functions of the law of the path `fun ω n ↦ Z n ω`.
The chain rule for two processes `Z`, `Z'` on two spaces stopped by the same rule follows from
the one above by transport to the path space `Π n, X n`
(`klDiv_map_hittingProcess_sigmaPrefix_compProd`, `klDiv_map_hittingValue_sigmaPrefix_compProd`
and the integral forms `klDiv_map_hittingProcess_sigmaPrefix`,
`klDiv_map_hittingValue_sigmaPrefix`).

This is the change-of-measure identity of sequential analysis: for an algorithm interacting with
two environments it is specialized in
`Essakine2026Tight.LeanMachineLearning.SequentialLearning.DivergenceDecomposition`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal ENat

namespace InformationTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  {Z : (n : ℕ) → Ω → X n} {τ : Ω → WithTop ℕ}
  {κ κ' : (n : ℕ) → Kernel (Π i : Fin n, X i) (X n)}
  [∀ n, IsMarkovKernel (κ n)] [∀ n, IsMarkovKernel (κ' n)]

section OneSpace

variable {P P' : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- **Chain rule at a bounded stopping time**, composition-product form. For two laws `P`, `P'`
of a process `Z` under which its steps have conditional laws `κ n`, `κ' n` given the prefix of
length `n`, and a stopping time `τ` of the prefix filtration, the divergence between the laws of
the prefix stopped at time `M` is the sum over the steps `t < M` of the conditional divergences
of `κ t` and `κ' t` given the prefix of length `t`, on the event `{t < τ}` (the step is
taken). -/
lemma klDiv_map_stoppedProcess_sigmaPrefix_compProd {hZ : ∀ n, Measurable (Z n)}
    (hκ : ∀ n, HasCondDistrib (Z n) (finPrefix Z n) (κ n) P)
    (hκ' : ∀ n, HasCondDistrib (Z n) (finPrefix Z n) (κ' n) P')
    (hτ : IsStoppingTime (prefixFiltration Z hZ) τ) (M : ℕ) :
    klDiv (P.map (stoppedProcess (sigmaPrefix Z) τ M))
        (P'.map (stoppedProcess (sigmaPrefix Z) τ M)) =
      ∑ t ∈ range M,
        klDiv ((P.restrict {ω | (t : WithTop ℕ) < τ ω}).map (finPrefix Z t) ⊗ₘ κ t)
          ((P.restrict {ω | (t : WithTop ℕ) < τ ω}).map (finPrefix Z t) ⊗ₘ κ' t) := by
  have hτm : Measurable τ := hτ.measurable'
  induction M with
  | zero =>
    rw [(hasLaw_stoppedProcess_sigmaPrefix_zero P τ).map_eq,
      (hasLaw_stoppedProcess_sigmaPrefix_zero P' τ).map_eq, klDiv_self, sum_range_zero]
  | succ M ih =>
    obtain ⟨B, hB, hBτ⟩ := hτ.exists_measurableSet_preimage_finPrefix M
    rw [sum_range_succ, ← ih, map_stoppedProcess_sigmaPrefix_succ_eq_add hZ hτm (P := P) M,
      map_stoppedProcess_sigmaPrefix_succ_eq_add hZ hτm (P := P') M,
      map_stoppedProcess_sigmaPrefix_eq_add hZ hτm (P := P) M,
      map_stoppedProcess_sigmaPrefix_eq_add hZ hτm (P := P') M,
      klDiv_add_add_of_measure_eq_zero (measurableSet_sigma_fst_le M)
        (map_restrict_stoppedProcess_sigmaPrefix_apply_compl_fst_le hZ hτm _ M)
        (map_restrict_stoppedProcess_sigmaPrefix_apply_compl_fst_le hZ hτm _ M)
        (Measure.map_sigmaMk_succ_apply_fst_le _) (Measure.map_sigmaMk_succ_apply_fst_le _),
      klDiv_add_add_of_measure_eq_zero ((measurableSet_sigma_fst_lt M).union
          ((measurableEmbedding_sigma_mk M).measurableSet_image.2 hB))
        (map_restrict_le_stoppedProcess_sigmaPrefix_apply_compl hZ hτm (P := P) hB hBτ)
        (map_restrict_le_stoppedProcess_sigmaPrefix_apply_compl hZ hτm (P := P') hB hBτ)
        (map_restrict_lt_map_finPrefix_map_sigmaMk_apply hZ (P := P) hB hBτ)
        (map_restrict_lt_map_finPrefix_map_sigmaMk_apply hZ (P := P') hB hBτ),
      klDiv_map_measurableEmbedding _ _ (measurableEmbedding_sigma_mk (M + 1)),
      klDiv_map_measurableEmbedding _ _ (measurableEmbedding_sigma_mk M),
      map_finPrefix_succ_of_hasCondDistrib hZ ((hκ M).restrict_lt_of_isStoppingTime (hZ M) hτ),
      map_finPrefix_succ_of_hasCondDistrib hZ ((hκ' M).restrict_lt_of_isStoppingTime (hZ M) hτ),
      klDiv_map_measurableEquiv, add_assoc]
    congr 1
    exact klDiv_compProd_eq_add _ _ _ _

/-- **Chain rule at an almost surely finite stopping time**, composition-product form. For two
laws `P`, `P'` of a process `Z` under which its steps have conditional laws `κ n`, `κ' n` given
the prefix of length `n`, and a stopping time `τ` of the prefix filtration which is almost
surely finite under both laws, the divergence between the laws of the stopped prefix is the
series over the steps `t` of the conditional divergences of `κ t` and `κ' t` given the prefix of
length `t`, on the event `{t < τ}`. -/
lemma klDiv_map_stoppedValue_sigmaPrefix_compProd {hZ : ∀ n, Measurable (Z n)}
    (hκ : ∀ n, HasCondDistrib (Z n) (finPrefix Z n) (κ n) P)
    (hκ' : ∀ n, HasCondDistrib (Z n) (finPrefix Z n) (κ' n) P')
    (hτ : IsStoppingTime (prefixFiltration Z hZ) τ)
    (hτ_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (hτ_top' : ∀ᵐ ω ∂P', τ ω ≠ ⊤) :
    klDiv (P.map (stoppedValue (sigmaPrefix Z) τ)) (P'.map (stoppedValue (sigmaPrefix Z) τ)) =
      ∑' t : ℕ,
        klDiv ((P.restrict {ω | (t : WithTop ℕ) < τ ω}).map (finPrefix Z t) ⊗ₘ κ t)
          ((P.restrict {ω | (t : WithTop ℕ) < τ ω}).map (finPrefix Z t) ⊗ₘ κ' t) := by
  have hτm : Measurable τ := hτ.measurable'
  have hB : ∀ M, MeasurableSet {x : Σ n : ℕ, Π i : Fin n, X i | x.1 < M} :=
    measurableSet_sigma_fst_lt
  have hlaw : ∀ M, P.map (stoppedProcess (sigmaPrefix Z) τ M) =
      (P.map (stoppedValue (sigmaPrefix Z) τ)).map (truncFin M) :=
    fun M ↦ ((hasLaw_map (measurable_stoppedValue_sigmaPrefix hZ hτm).aemeasurable)
      |>.stoppedProcess_sigmaPrefix hτ_top M).map_eq
  have hlaw' : ∀ M, P'.map (stoppedProcess (sigmaPrefix Z) τ M) =
      (P'.map (stoppedValue (sigmaPrefix Z) τ)).map (truncFin M) :=
    fun M ↦ ((hasLaw_map (measurable_stoppedValue_sigmaPrefix hZ hτm).aemeasurable)
      |>.stoppedProcess_sigmaPrefix hτ_top' M).map_eq
  rw [ENNReal.tsum_eq_iSup_nat]
  simp_rw [← klDiv_map_stoppedProcess_sigmaPrefix_compProd hκ hκ' hτ, hlaw, hlaw']
  set μ := P.map (stoppedValue (sigmaPrefix Z) τ) with hμ
  set ν := P'.map (stoppedValue (sigmaPrefix Z) τ) with hν
  refine le_antisymm ?_ (iSup_le fun M ↦ klDiv_map_le _ _ (measurable_truncFin M))
  rw [klDiv_eq_iSup_restrict hB (fun M N hMN x hx ↦ lt_of_lt_of_le hx hMN) (by
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨x.1 + 1, x.1.lt_succ_self⟩)]
  refine iSup_mono fun M ↦ ?_
  calc klDiv (μ.restrict {x | x.1 < M}) (ν.restrict {x | x.1 < M})
      = klDiv ((μ.map (truncFin M)).restrict {x | x.1 < M})
          ((ν.map (truncFin M)).restrict {x | x.1 < M}) := by
        rw [restrict_map_truncFin, restrict_map_truncFin]
    _ ≤ klDiv (μ.map (truncFin M)) (ν.map (truncFin M)) := klDiv_restrict_le (hB M)

/-- A sum over `t < M` of terms which vanish unless `t < τ` is a sum over `t < min τ M`. -/
lemma sum_ite_lt_eq_sum_range_toNat_min {β : Type*} [AddCommMonoid β] (f : ℕ → β) (τ : ℕ∞)
    (M : ℕ) :
    ∑ t ∈ range M, (if (t : ℕ∞) < τ then f t else 0) = ∑ t ∈ range (min τ M).toNat, f t := by
  induction τ using ENat.recTopCoe with
  | top => simp
  | coe k =>
    rw [← sum_filter]
    congr 1
    ext t
    simp only [mem_filter, mem_range, ENat.natCast_lt_natCast]
    rcases le_total k M with hkM | hkM
    · rw [min_eq_left (by exact_mod_cast hkM), ENat.toNat_natCast]
      omega
    · rw [min_eq_right (by exact_mod_cast hkM), ENat.toNat_natCast]
      omega

/-- A series of terms which vanish unless `t < τ`, for a finite `τ`, is a sum over `t < τ`. -/
lemma tsum_ite_lt_eq_sum_range_toNat {β : Type*} [AddCommMonoid β] [TopologicalSpace β]
    (f : ℕ → β) {τ : ℕ∞} (hτ : τ ≠ ⊤) :
    ∑' t : ℕ, (if (t : ℕ∞) < τ then f t else 0) = ∑ t ∈ range τ.toNat, f t := by
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.1 hτ
  simp_rw [ENat.natCast_lt_natCast, ENat.toNat_natCast]
  rw [tsum_eq_sum (s := range k) fun t ht ↦ ite_eq_right (by simpa using ht)]
  exact sum_congr rfl fun t ht ↦ ite_eq_left (mem_range.1 ht)

section CountablyGenerated

variable [∀ n, MeasurableSpace.CountablyGenerated (X n)]

/-- The sum over the steps `t < M` of the conditional divergences of `κ t` and `κ' t` given the
prefix of length `t` on `{t < τ}` is the expected sum of the divergences of `κ t` and `κ' t` at
the prefix of length `t`, over the steps `t < min τ M`. -/
lemma sum_klDiv_compProd_restrict_lt_eq_lintegral (hZ : ∀ n, Measurable (Z n))
    (hτ : Measurable τ) (M : ℕ) :
    ∑ t ∈ range M,
        klDiv ((P.restrict {ω | (t : WithTop ℕ) < τ ω}).map (finPrefix Z t) ⊗ₘ κ t)
          ((P.restrict {ω | (t : WithTop ℕ) < τ ω}).map (finPrefix Z t) ⊗ₘ κ' t) =
      ∫⁻ ω, ∑ t ∈ range (ENat.toNat (min (τ ω) M)),
        klDiv (κ t (finPrefix Z t ω)) (κ' t (finPrefix Z t ω)) ∂P := by
  have hmeas : ∀ t, Measurable fun ω ↦ klDiv (κ t (finPrefix Z t ω)) (κ' t (finPrefix Z t ω)) :=
    fun t ↦ (measurable_klDiv_kernel (κ t) (κ' t)).comp (measurable_finPrefix hZ t)
  have hlt : ∀ t : ℕ, MeasurableSet {ω | (t : WithTop ℕ) < τ ω} := fun t ↦ hτ measurableSet_Ioi
  simp_rw [klDiv_compProd_right_eq_lintegral,
    lintegral_map (measurable_klDiv_kernel (κ _) (κ' _)) (measurable_finPrefix hZ _),
    ← lintegral_indicator (hlt _)]
  rw [← lintegral_finsetSum _ fun t _ ↦ (hmeas t).indicator (hlt t)]
  refine lintegral_congr fun ω ↦ ?_
  simp_rw [Set.indicator_apply, Set.mem_ofPred_eq]
  exact sum_ite_lt_eq_sum_range_toNat_min _ _ M

/-- The series over the steps `t` of the conditional divergences of `κ t` and `κ' t` given the
prefix of length `t` on `{t < τ}`, for an almost surely finite `τ`, is the expected sum of the
divergences of `κ t` and `κ' t` at the prefix of length `t`, over the steps `t < τ`. -/
lemma tsum_klDiv_compProd_restrict_lt_eq_lintegral (hZ : ∀ n, Measurable (Z n))
    (hτ : Measurable τ) (hτ_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    ∑' t : ℕ,
        klDiv ((P.restrict {ω | (t : WithTop ℕ) < τ ω}).map (finPrefix Z t) ⊗ₘ κ t)
          ((P.restrict {ω | (t : WithTop ℕ) < τ ω}).map (finPrefix Z t) ⊗ₘ κ' t) =
      ∫⁻ ω, ∑ t ∈ range (ENat.toNat (τ ω)),
        klDiv (κ t (finPrefix Z t ω)) (κ' t (finPrefix Z t ω)) ∂P := by
  have hmeas : ∀ t, Measurable fun ω ↦ klDiv (κ t (finPrefix Z t ω)) (κ' t (finPrefix Z t ω)) :=
    fun t ↦ (measurable_klDiv_kernel (κ t) (κ' t)).comp (measurable_finPrefix hZ t)
  have hlt : ∀ t : ℕ, MeasurableSet {ω | (t : WithTop ℕ) < τ ω} := fun t ↦ hτ measurableSet_Ioi
  simp_rw [klDiv_compProd_right_eq_lintegral,
    lintegral_map (measurable_klDiv_kernel (κ _) (κ' _)) (measurable_finPrefix hZ _),
    ← lintegral_indicator (hlt _)]
  rw [← lintegral_tsum fun t ↦ ((hmeas t).indicator (hlt t)).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [hτ_top] with ω hω
  simp_rw [Set.indicator_apply, Set.mem_ofPred_eq]
  exact tsum_ite_lt_eq_sum_range_toNat (fun t ↦ klDiv (κ t (finPrefix Z t ω))
    (κ' t (finPrefix Z t ω))) hω

/-- **Chain rule at a bounded stopping time**, integral form: the divergence between the laws
of the prefix stopped at time `M` is the expected sum, under the first law, of the divergences of
`κ t` and `κ' t` at the prefix of length `t`, over the steps `t < min τ M`. -/
lemma klDiv_map_stoppedProcess_sigmaPrefix {hZ : ∀ n, Measurable (Z n)}
    (hκ : ∀ n, HasCondDistrib (Z n) (finPrefix Z n) (κ n) P)
    (hκ' : ∀ n, HasCondDistrib (Z n) (finPrefix Z n) (κ' n) P')
    (hτ : IsStoppingTime (prefixFiltration Z hZ) τ) (M : ℕ) :
    klDiv (P.map (stoppedProcess (sigmaPrefix Z) τ M))
        (P'.map (stoppedProcess (sigmaPrefix Z) τ M)) =
      ∫⁻ ω, ∑ t ∈ range (ENat.toNat (min (τ ω) M)),
        klDiv (κ t (finPrefix Z t ω)) (κ' t (finPrefix Z t ω)) ∂P := by
  rw [klDiv_map_stoppedProcess_sigmaPrefix_compProd hκ hκ' hτ M,
    sum_klDiv_compProd_restrict_lt_eq_lintegral hZ hτ.measurable' M]

/-- **Chain rule at an almost surely finite stopping time**, integral form: the divergence
between the laws of the stopped prefix is the expected sum, under the first law, of the
divergences of `κ t` and `κ' t` at the prefix of length `t`, over the steps `t < τ`. -/
lemma klDiv_map_stoppedValue_sigmaPrefix {hZ : ∀ n, Measurable (Z n)}
    (hκ : ∀ n, HasCondDistrib (Z n) (finPrefix Z n) (κ n) P)
    (hκ' : ∀ n, HasCondDistrib (Z n) (finPrefix Z n) (κ' n) P')
    (hτ : IsStoppingTime (prefixFiltration Z hZ) τ)
    (hτ_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (hτ_top' : ∀ᵐ ω ∂P', τ ω ≠ ⊤) :
    klDiv (P.map (stoppedValue (sigmaPrefix Z) τ)) (P'.map (stoppedValue (sigmaPrefix Z) τ)) =
      ∫⁻ ω, ∑ t ∈ range (ENat.toNat (τ ω)),
        klDiv (κ t (finPrefix Z t ω)) (κ' t (finPrefix Z t ω)) ∂P := by
  rw [klDiv_map_stoppedValue_sigmaPrefix_compProd hκ hκ' hτ hτ_top hτ_top',
    tsum_klDiv_compProd_restrict_lt_eq_lintegral hZ hτ.measurable' hτ_top]

end CountablyGenerated

end OneSpace

section TwoSpaces

/-! ### Two processes on two spaces stopped by a stopping rule

The laws of the prefixes stopped by a stopping rule `S` are functions of the law of the path
`fun ω n ↦ Z n ω` in `Π n, X n`, on which the process of coordinates has the same conditional
laws. The chain rule for a process `Z` on `(Ω, P)` and a process `Z'` on `(Ω', P')` stopped by
`S` thus follows from the chain rule for the process of coordinates under the two laws of the
paths. -/

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω} {P' : Measure Ω'}
  [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {Z' : (n : ℕ) → Ω' → X n}
  {S : Set (Σ n : ℕ, Π i : Fin n, X i)}

/-- **Chain rule at a bounded stopping time** for two processes on two spaces, composition-product
form. For two processes `Z`, `Z'` whose steps have conditional laws `κ n`, `κ' n` given the
prefix of length `n`, and a stopping rule `S`, the divergence between the laws of the prefixes
stopped at time `M` is the sum over the steps `t < M` of the conditional divergences of `κ t`
and `κ' t` given the prefix of length `t`, on the event `{t < τ}` (the step is taken). -/
lemma klDiv_map_hittingProcess_sigmaPrefix_compProd (hZ : ∀ n, Measurable (Z n))
    (hZ' : ∀ n, Measurable (Z' n)) (hκ : ∀ n, HasCondDistrib (Z n) (finPrefix Z n) (κ n) P)
    (hκ' : ∀ n, HasCondDistrib (Z' n) (finPrefix Z' n) (κ' n) P') (hS : MeasurableSet S)
    (M : ℕ) :
    klDiv (P.map (hittingProcess (sigmaPrefix Z) S 0 M))
        (P'.map (hittingProcess (sigmaPrefix Z') S 0 M)) =
      ∑ t ∈ range M,
        klDiv ((P.restrict {ω | (t : WithTop ℕ) < hittingAfter (sigmaPrefix Z) S 0 ω}).map
            (finPrefix Z t) ⊗ₘ κ t)
          ((P.restrict {ω | (t : WithTop ℕ) < hittingAfter (sigmaPrefix Z) S 0 ω}).map
            (finPrefix Z t) ⊗ₘ κ' t) := by
  have hW : ∀ n, Measurable fun x : Π n, X n ↦ x n := fun n ↦ measurable_pi_apply n
  have hZm : Measurable fun ω n ↦ Z n ω := Measurable.of_eval hZ
  have hZm' : Measurable fun ω n ↦ Z' n ω := Measurable.of_eval hZ'
  have hlt := measurableSet_lt_hittingAfter_sigmaPrefix hW hS
  have h := klDiv_map_stoppedProcess_sigmaPrefix_compProd
    (P := P.map fun ω n ↦ Z n ω) (P' := P'.map fun ω n ↦ Z' n ω)
    (fun n ↦ (hκ n).of_comp_hasLaw (measurable_finPrefix hW n) (hW n)
      (hasLaw_map hZm.aemeasurable))
    (fun n ↦ (hκ' n).of_comp_hasLaw (measurable_finPrefix hW n) (hW n)
      (hasLaw_map hZm'.aemeasurable))
    (isStoppingTime_hittingAfter_sigmaPrefix hW hS) M
  simp only [← hittingProcess_def] at h
  rw [Measure.map_map (measurable_hittingProcess_sigmaPrefix hW hS M) hZm,
    Measure.map_map (measurable_hittingProcess_sigmaPrefix hW hS M) hZm'] at h
  simp only [Measure.restrict_map hZm (hlt _),
    Measure.map_map (measurable_finPrefix hW _) hZm] at h
  exact h

/-- **Chain rule at an almost surely finite stopping time** for two processes on two spaces,
composition-product form. For two processes `Z`, `Z'` whose steps have conditional laws `κ n`,
`κ' n` given the prefix of length `n`, and a stopping rule `S` whose stopping time is almost
surely finite under both laws, the divergence between the laws of the stopped prefixes is the
series over the steps `t` of the conditional divergences of `κ t` and `κ' t` given the prefix of
length `t`, on the event `{t < τ}`. -/
lemma klDiv_map_hittingValue_sigmaPrefix_compProd (hZ : ∀ n, Measurable (Z n))
    (hZ' : ∀ n, Measurable (Z' n)) (hκ : ∀ n, HasCondDistrib (Z n) (finPrefix Z n) (κ n) P)
    (hκ' : ∀ n, HasCondDistrib (Z' n) (finPrefix Z' n) (κ' n) P') (hS : MeasurableSet S)
    (hτ : ∀ᵐ ω ∂P, hittingAfter (sigmaPrefix Z) S 0 ω ≠ ⊤)
    (hτ' : ∀ᵐ ω ∂P', hittingAfter (sigmaPrefix Z') S 0 ω ≠ ⊤) :
    klDiv (P.map (hittingValue (sigmaPrefix Z) S 0))
        (P'.map (hittingValue (sigmaPrefix Z') S 0)) =
      ∑' t : ℕ,
        klDiv ((P.restrict {ω | (t : WithTop ℕ) < hittingAfter (sigmaPrefix Z) S 0 ω}).map
            (finPrefix Z t) ⊗ₘ κ t)
          ((P.restrict {ω | (t : WithTop ℕ) < hittingAfter (sigmaPrefix Z) S 0 ω}).map
            (finPrefix Z t) ⊗ₘ κ' t) := by
  have hW : ∀ n, Measurable fun x : Π n, X n ↦ x n := fun n ↦ measurable_pi_apply n
  have hZm : Measurable fun ω n ↦ Z n ω := Measurable.of_eval hZ
  have hZm' : Measurable fun ω n ↦ Z' n ω := Measurable.of_eval hZ'
  have hlt := measurableSet_lt_hittingAfter_sigmaPrefix hW hS
  have hτW := measurable_hittingAfter_sigmaPrefix hW hS
  have hne : MeasurableSet {x : Π n, X n | hittingAfter (sigmaPrefix fun n x ↦ x n) S 0 x ≠ ⊤} :=
    hτW (measurableSet_singleton ⊤).compl
  have h := klDiv_map_stoppedValue_sigmaPrefix_compProd
    (P := P.map fun ω n ↦ Z n ω) (P' := P'.map fun ω n ↦ Z' n ω)
    (fun n ↦ (hκ n).of_comp_hasLaw (measurable_finPrefix hW n) (hW n)
      (hasLaw_map hZm.aemeasurable))
    (fun n ↦ (hκ' n).of_comp_hasLaw (measurable_finPrefix hW n) (hW n)
      (hasLaw_map hZm'.aemeasurable))
    (isStoppingTime_hittingAfter_sigmaPrefix hW hS)
    ((ae_map_iff hZm.aemeasurable hne).2 hτ) ((ae_map_iff hZm'.aemeasurable hne).2 hτ')
  simp only [← hittingValue_def] at h
  rw [Measure.map_map (measurable_hittingValue_sigmaPrefix hW hS) hZm,
    Measure.map_map (measurable_hittingValue_sigmaPrefix hW hS) hZm'] at h
  simp only [Measure.restrict_map hZm (hlt _),
    Measure.map_map (measurable_finPrefix hW _) hZm] at h
  exact h

section CountablyGenerated

variable [∀ n, MeasurableSpace.CountablyGenerated (X n)]

/-- **Chain rule at a bounded stopping time** for two processes on two spaces, integral form:
the divergence between the laws of the prefixes stopped at time `M` is the expected sum, along
the first process, of the divergences of `κ t` and `κ' t` at the prefix of length `t`, over the
steps `t < min τ M`. -/
lemma klDiv_map_hittingProcess_sigmaPrefix (hZ : ∀ n, Measurable (Z n))
    (hZ' : ∀ n, Measurable (Z' n)) (hκ : ∀ n, HasCondDistrib (Z n) (finPrefix Z n) (κ n) P)
    (hκ' : ∀ n, HasCondDistrib (Z' n) (finPrefix Z' n) (κ' n) P') (hS : MeasurableSet S)
    (M : ℕ) :
    klDiv (P.map (hittingProcess (sigmaPrefix Z) S 0 M))
        (P'.map (hittingProcess (sigmaPrefix Z') S 0 M)) =
      ∫⁻ ω, ∑ t ∈ range (ENat.toNat (min (hittingAfter (sigmaPrefix Z) S 0 ω) M)),
        klDiv (κ t (finPrefix Z t ω)) (κ' t (finPrefix Z t ω)) ∂P := by
  rw [klDiv_map_hittingProcess_sigmaPrefix_compProd hZ hZ' hκ hκ' hS M,
    sum_klDiv_compProd_restrict_lt_eq_lintegral hZ (measurable_hittingAfter_sigmaPrefix hZ hS) M]

/-- **Chain rule at an almost surely finite stopping time** for two processes on two spaces,
integral form: the divergence between the laws of the stopped prefixes is the expected sum,
along the first process, of the divergences of `κ t` and `κ' t` at the prefix of length `t`,
over the steps `t < τ`. -/
lemma klDiv_map_hittingValue_sigmaPrefix (hZ : ∀ n, Measurable (Z n))
    (hZ' : ∀ n, Measurable (Z' n)) (hκ : ∀ n, HasCondDistrib (Z n) (finPrefix Z n) (κ n) P)
    (hκ' : ∀ n, HasCondDistrib (Z' n) (finPrefix Z' n) (κ' n) P') (hS : MeasurableSet S)
    (hτ : ∀ᵐ ω ∂P, hittingAfter (sigmaPrefix Z) S 0 ω ≠ ⊤)
    (hτ' : ∀ᵐ ω ∂P', hittingAfter (sigmaPrefix Z') S 0 ω ≠ ⊤) :
    klDiv (P.map (hittingValue (sigmaPrefix Z) S 0))
        (P'.map (hittingValue (sigmaPrefix Z') S 0)) =
      ∫⁻ ω, ∑ t ∈ range (ENat.toNat (hittingAfter (sigmaPrefix Z) S 0 ω)),
        klDiv (κ t (finPrefix Z t ω)) (κ' t (finPrefix Z t ω)) ∂P := by
  rw [klDiv_map_hittingValue_sigmaPrefix_compProd hZ hZ' hκ hκ' hS hτ hτ',
    tsum_klDiv_compProd_restrict_lt_eq_lintegral hZ (measurable_hittingAfter_sigmaPrefix hZ hS) hτ]

end CountablyGenerated

end TwoSpaces

end InformationTheory
