/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Essakine2026Tight.Mathlib.InformationTheory.KullbackLeibler.Fintype
public import Essakine2026Tight.Mathlib.MeasureTheory.Measure.WeightedProbability

/-!
# The method of types and Sanov's bound

Let `X : Fin n → Ω → α` be an i.i.d. sample with law `weightedMeasure p` on a finite type `α` with
`m` elements. The *type* of a sequence `x : Fin n → α` is its vector of counts
`InformationTheory.typeCount x`, and its empirical distribution is
`weightedMeasure (InformationTheory.empiricalFreq x)`.

* `InformationTheory.card_piAntidiag_univ`, `Nat.choose_add_le_add_one_pow`,
  `InformationTheory.card_le_pow_of_sum_eq`: there are `(m + n - 1).choose n` count vectors of
  total `n`, and at most `(n + 1)^{m - 1}` of them (number of types);
* `InformationTheory.measure_typeCount_eq_le`: `ℙ(type = N) ≤ e^{-n t}` whenever
  `t ≤ KL(N/n ‖ p)` (probability of a type class);
* `InformationTheory.measure_lt_klDiv_empiricalFreq_le`: Sanov's bound
  `ℙ(KL(p̂ₙ ‖ p) > t) ≤ (n + 1)^{m - 1} e^{-n t}` (Lemma 19 of Essakine, Vernade (2026)), and its
  confidence form `InformationTheory.measure_lt_klDiv_empiricalFreq_le_delta`.
-/

@[expose] public section

open MeasureTheory Real Finset
open scoped ENNReal


namespace InformationTheory

open MeasureTheory

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The type of a finite sequence: the number of occurrences of each letter. -/
def typeCount {n : ℕ} (x : Fin n → α) (a : α) : ℕ := #{k | x k = a}

omit [Fintype α] in
/-- The counts of a sequence of length `n` sum to `n`. -/
lemma sum_typeCount {n : ℕ} (x : Fin n → α) [Fintype α] : ∑ a, typeCount x a = n := by
  unfold typeCount
  rw [← Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_coe.2 (Finset.mem_univ _))]
  simp

/-- `∏ k, f (x k) = ∏ a, f a ^ typeCount x a`. -/
lemma prod_comp_eq_prod_pow_typeCount {M : Type*} [CommMonoid M] {n : ℕ} (f : α → M)
    (x : Fin n → α) : ∏ k, f (x k) = ∏ a, f a ^ typeCount x a := by
  rw [← Finset.prod_fiberwise' Finset.univ x f]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  rw [Finset.prod_const]
  rfl

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The product measure of a type class: `p^{⊗n}(T(N)) = #T(N) ∏ a, p a ^ N a`. -/
lemma pi_weightedMeasure_typeCount_eq {n : ℕ} {r : α → ℝ} (hr : ∀ a, 0 ≤ r a) (N : α → ℕ) :
    Measure.pi (fun _ : Fin n ↦ weightedMeasure r) {x | typeCount x = N}
      = ENNReal.ofReal (#{x : Fin n → α | typeCount x = N} * ∏ a, r a ^ N a) := by
  have hset : {x : Fin n → α | typeCount x = N}
      = ((Finset.univ.filter fun x : Fin n → α ↦ typeCount x = N) : Set (Fin n → α)) := by
    ext x; simp
  rw [hset, ← sum_measure_singleton]
  have hterm : ∀ x ∈ Finset.univ.filter (fun x : Fin n → α ↦ typeCount x = N),
      Measure.pi (fun _ : Fin n ↦ weightedMeasure r) {x} = ENNReal.ofReal (∏ a, r a ^ N a) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Measure.pi_singleton]
    simp_rw [weightedMeasure_singleton]
    rw [prod_comp_eq_prod_pow_typeCount (fun a ↦ ENNReal.ofReal (r a)) x, hx.2]
    rw [ENNReal.ofReal_prod_of_nonneg fun a _ ↦ pow_nonneg (hr a) _]
    simp_rw [ENNReal.ofReal_pow (hr _)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

omit [Fintype α] [DecidableEq α] in
/-- For an i.i.d. sample `X` with law `ρ`, the law of the vector `(X k)ₖ` is `ρ^{⊗n}`. -/
lemma measure_typeCount_eq [Finite α] {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {n : ℕ} {X : Fin n → Ω → α} (hX : ProbabilityTheory.iIndepFun X μ)
    {ρ : Measure α} (hlaw : ∀ k, ProbabilityTheory.HasLaw (X k) ρ μ) (s : Set (Fin n → α)) :
    μ {ω | (fun k ↦ X k ω) ∈ s} = Measure.pi (fun _ ↦ ρ) s := by
  have hmeas : ∀ k, AEMeasurable (X k) μ := fun k ↦ (hlaw k).aemeasurable
  have hmap := hX.map_fun_eq_pi_map hmeas
  simp_rw [(hlaw _).map_eq] at hmap
  rw [← hmap, Measure.map_apply₀ (AEMeasurable.of_eval hmeas)
    (s.toFinite.measurableSet.nullMeasurableSet)]
  rfl


omit [DecidableEq α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **The number of types** (Lemma of the method of types): a finite set of count vectors
`N : α → ℕ` with `∑ a, N a = n` has at most `(n + 1) ^ (card α - 1)` elements. -/
lemma card_le_pow_of_sum_eq (n : ℕ) (s : Finset (α → ℕ)) (hs : ∀ N ∈ s, ∑ a, N a = n) :
    #s ≤ (n + 1) ^ (Fintype.card α - 1) := by
  classical
  rcases isEmpty_or_nonempty α with hα | ⟨⟨x₀⟩⟩
  · have : #s ≤ 1 := Finset.card_le_one.2 fun N _ N' _ ↦ funext fun a ↦ isEmptyElim a
    simpa using this
  have hle : ∀ N ∈ s, ∀ a, N a ≤ n := fun N hN a ↦ by
    rw [← hs N hN]
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
  let f : (α → ℕ) → ({a // a ≠ x₀} → Fin (n + 1)) := fun N a ↦ ⟨min (N a) n, by omega⟩
  have hinj : Set.InjOn f s := by
    intro N hN N' hN' hNN'
    have hne : ∀ a, a ≠ x₀ → N a = N' a := fun a ha ↦ by
      have h := congrArg (fun g ↦ (g ⟨a, ha⟩ : ℕ)) hNN'
      simp only [f, min_eq_left (hle N hN a), min_eq_left (hle N' hN' a)] at h
      exact h
    have hsum : ∀ M : α → ℕ, ∑ a, M a = M x₀ + ∑ a ∈ Finset.univ.erase x₀, M a := fun M ↦
      (Finset.add_sum_erase _ _ (Finset.mem_univ x₀)).symm
    have hrest : ∑ a ∈ Finset.univ.erase x₀, N a = ∑ a ∈ Finset.univ.erase x₀, N' a :=
      Finset.sum_congr rfl fun a ha ↦ hne a (Finset.ne_of_mem_erase ha)
    funext a
    by_cases ha : a = x₀
    · subst ha
      have h1 := hsum N
      have h2 := hsum N'
      rw [hs N hN] at h1
      rw [hs N' hN'] at h2
      omega
    · exact hne a ha
  calc #s ≤ #(Finset.univ : Finset ({a // a ≠ x₀} → Fin (n + 1))) :=
        Finset.card_le_card_of_injOn f (fun _ _ ↦ Finset.mem_coe.2 (Finset.mem_univ _)) hinj
    _ = (n + 1) ^ (Fintype.card α - 1) := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
        congr 1
        have := Fintype.card_subtype_compl (fun a : α ↦ a = x₀)
        rw [Fintype.card_subtype_eq] at this
        exact this

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **The number of types**: the count vectors `N : α → ℕ` with `∑ a, N a = n` (the finset
`piAntidiag univ n`) are `(m + n - 1).choose n` in number, where `m = card α`. -/
lemma card_piAntidiag_univ (n : ℕ) :
    #(piAntidiag (univ : Finset α) n) = (Fintype.card α + n - 1).choose n := by
  have h := Finset.card_finsuppAntidiag_nat_eq_choose (s := (univ : Finset α)) n
  rw [Finset.finsuppAntidiag, card_map, card_attach, card_univ] at h
  exact h

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The number of count vectors of total `n` is at most `(n + 1)^{m - 1}`. -/
lemma card_piAntidiag_univ_le (n : ℕ) :
    #(piAntidiag (univ : Finset α) n) ≤ (n + 1) ^ (Fintype.card α - 1) :=
  card_le_pow_of_sum_eq n _ fun _ hN ↦ (mem_piAntidiag.1 hN).1

/-- The empirical frequency vector `a ↦ #{k | x k = a} / n` of a finite sequence. -/
noncomputable def empiricalFreq {n : ℕ} (x : Fin n → α) (a : α) : ℝ := typeCount x a / n

section Sanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
  {X : Fin n → Ω → α} {p : α → ℝ}

/-- **Probability of a type class**: if `X` is an i.i.d. sample of size `n` with law `p`, then
for every count vector `N` with `∑ N = n` and every `t` with `t ≤ KL(N/n ‖ p)`,
`ℙ(type of X = N) ≤ e^{-n t}`. -/
lemma measure_typeCount_eq_le (hX : ProbabilityTheory.iIndepFun X μ) (hp0 : ∀ a, 0 ≤ p a)
    (hlaw : ∀ k, ProbabilityTheory.HasLaw (X k) (weightedMeasure p) μ) {N : α → ℕ}
    (hN : ∑ a, N a = n) {t : ℝ}
    (ht : ENNReal.ofReal t ≤ klDiv (weightedMeasure (fun a ↦ (N a : ℝ) / n)) (weightedMeasure p)) :
    μ {ω | typeCount (fun k ↦ X k ω) = N} ≤ ENNReal.ofReal (exp (-(n * t))) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simpa using prob_le_one
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set q : α → ℝ := fun a ↦ (N a : ℝ) / n with hq
  have hq0 : ∀ a, 0 ≤ q a := fun a ↦ by positivity
  have hq1 : ∑ a, q a = 1 := by
    simp only [hq, ← Finset.sum_div]
    rw [div_eq_one_iff_eq hnR.ne']
    exact_mod_cast hN
  have hPeq : μ {ω | typeCount (fun k ↦ X k ω) = N}
      = ENNReal.ofReal (#{x : Fin n → α | typeCount x = N} * ∏ a, p a ^ N a) := by
    rw [← pi_weightedMeasure_typeCount_eq hp0 N]
    exact measure_typeCount_eq hX hlaw {x | typeCount x = N}
  have hQle : (#{x : Fin n → α | typeCount x = N} : ℝ) * ∏ a, q a ^ N a ≤ 1 := by
    have := isProbabilityMeasure_weightedMeasure hq0 hq1
    have h := prob_le_one (μ := Measure.pi (fun _ : Fin n ↦ weightedMeasure q))
      (s := {x | typeCount x = N})
    rw [pi_weightedMeasure_typeCount_eq hq0 N] at h
    exact (ENNReal.ofReal_le_one).1 h
  rw [hPeq]
  by_cases hsupp : ∀ a, 0 < N a → 0 < p a
  · have hac : weightedMeasure q ≪ weightedMeasure p :=
      weightedMeasure_absolutelyContinuous fun a ha ↦ hsupp a (by
        simp only [hq] at ha
        exact_mod_cast (div_pos_iff_of_pos_right hnR).1 ha)
    have := isProbabilityMeasure_weightedMeasure hq0 hq1
    have : IsProbabilityMeasure (weightedMeasure p) :=
      (hlaw ⟨0, hn⟩).isProbabilityMeasure_iff.1 inferInstance
    have hKL := toReal_klDiv_eq_sum hac
    simp only [measureReal_weightedMeasure_singleton hq0, measureReal_weightedMeasure_singleton hp0]
      at hKL
    have htKL : t ≤ ∑ a, q a * log (q a / p a) := by
      rw [← hKL]
      exact (ENNReal.ofReal_le_iff_le_toReal (klDiv_ne_top_of_finite hac)).1 ht
    have hkey : ∏ a, p a ^ N a = (∏ a, q a ^ N a) * exp (-(n * ∑ a, q a * log (q a / p a))) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, exp_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a _ ↦ ?_
      rcases Nat.eq_zero_or_pos (N a) with hNa | hNa
      · simp [hq, hNa]
      have hpa := hsupp a hNa
      have hqa : 0 < q a := by simp only [hq]; positivity
      have hnq : (n : ℝ) * q a = N a := by simp only [hq]; field_simp
      have hexp : exp (-(n * (q a * log (q a / p a)))) = (p a / q a) ^ N a := by
        rw [← mul_assoc, hnq, ← Real.exp_log (div_pos hpa hqa), ← Real.exp_nat_mul,
          Real.log_div hqa.ne' hpa.ne', Real.log_div hpa.ne' hqa.ne']
        ring_nf
      rw [hexp, ← mul_pow, mul_div_cancel₀ _ hqa.ne']
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hkey, ← mul_assoc]
    have hexp_le : exp (-(n * ∑ a, q a * log (q a / p a))) ≤ exp (-(n * t)) :=
      exp_le_exp.2 (by nlinarith)
    calc (#{x : Fin n → α | typeCount x = N} : ℝ) * (∏ a, q a ^ N a)
          * exp (-(n * ∑ a, q a * log (q a / p a)))
        ≤ 1 * exp (-(n * t)) :=
          mul_le_mul hQle hexp_le (exp_pos _).le zero_le_one
      _ = exp (-(n * t)) := one_mul _
  · obtain ⟨a, hNa, hpa⟩ : ∃ a, 0 < N a ∧ p a ≤ 0 := by simpa [not_lt] using hsupp
    have hpa0 : p a = 0 := le_antisymm hpa (hp0 a)
    have hprod : ∏ b, p b ^ N b = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ a) (by rw [hpa0]; exact zero_pow hNa.ne')
    rw [hprod, mul_zero, ENNReal.ofReal_zero]
    exact zero_le

/-- **Sanov's high-probability bound** (Lemma 19 of Essakine, Vernade (2026), with the correct
exponent `m - 1`): for an i.i.d. sample of size `n` with law `p` on a finite set of `m` elements
and every `t`, `ℙ(KL(p̂ₙ ‖ p) > t) ≤ (n + 1)^{m - 1} e^{-n t}`. -/
theorem measure_lt_klDiv_empiricalFreq_le (hX : ProbabilityTheory.iIndepFun X μ)
    (hp0 : ∀ a, 0 ≤ p a) (hlaw : ∀ k, ProbabilityTheory.HasLaw (X k) (weightedMeasure p) μ)
    (t : ℝ) :
    μ {ω | ENNReal.ofReal t
        < klDiv (weightedMeasure (empiricalFreq fun k ↦ X k ω)) (weightedMeasure p)}
      ≤ ENNReal.ofReal ((n + 1) ^ (Fintype.card α - 1) * exp (-(n * t))) := by
  classical
  set C := (Finset.univ.image fun x : Fin n → α ↦ typeCount x).filter
    (fun N ↦ ENNReal.ofReal t < klDiv (weightedMeasure (fun a ↦ (N a : ℝ) / n))
      (weightedMeasure p)) with hC
  have hsub : {ω | ENNReal.ofReal t
        < klDiv (weightedMeasure (empiricalFreq fun k ↦ X k ω)) (weightedMeasure p)}
      ⊆ ⋃ N ∈ C, {ω | typeCount (fun k ↦ X k ω) = N} := by
    intro ω hω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    refine ⟨typeCount fun k ↦ X k ω, ?_, rfl⟩
    rw [hC, Finset.mem_filter]
    exact ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hω⟩
  have hcard : #C ≤ (n + 1) ^ (Fintype.card α - 1) := by
    refine card_le_pow_of_sum_eq n C fun N hN ↦ ?_
    rw [hC, Finset.mem_filter, Finset.mem_image] at hN
    obtain ⟨x, -, rfl⟩ := hN.1
    exact sum_typeCount x
  calc μ {ω | ENNReal.ofReal t
        < klDiv (weightedMeasure (empiricalFreq fun k ↦ X k ω)) (weightedMeasure p)}
      ≤ μ (⋃ N ∈ C, {ω | typeCount (fun k ↦ X k ω) = N}) := measure_mono hsub
    _ ≤ ∑ N ∈ C, μ {ω | typeCount (fun k ↦ X k ω) = N} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _N ∈ C, ENNReal.ofReal (exp (-(n * t))) := by
        refine Finset.sum_le_sum fun N hN ↦ ?_
        rw [hC, Finset.mem_filter, Finset.mem_image] at hN
        obtain ⟨⟨x, -, rfl⟩, hlt⟩ := hN
        exact measure_typeCount_eq_le hX hp0 hlaw (sum_typeCount x) hlt.le
    _ = #C * ENNReal.ofReal (exp (-(n * t))) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n + 1) ^ (Fintype.card α - 1) : ℕ) * ENNReal.ofReal (exp (-(n * t))) := by
        gcongr
    _ = ENNReal.ofReal ((n + 1) ^ (Fintype.card α - 1) * exp (-(n * t))) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← ENNReal.ofReal_natCast]
        push_cast
        rfl

/-- **Sanov's high-probability bound**, confidence form: for `δ > 0` and `n ≥ 1`, with
probability at least `1 - δ`, `KL(p̂ₙ ‖ p) ≤ ((m - 1) log (n + 1) + log (1/δ)) / n`. -/
theorem measure_lt_klDiv_empiricalFreq_le_delta (hX : ProbabilityTheory.iIndepFun X μ)
    (hp0 : ∀ a, 0 ≤ p a) (hlaw : ∀ k, ProbabilityTheory.HasLaw (X k) (weightedMeasure p) μ)
    (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | ENNReal.ofReal
          ((((Fintype.card α - 1 : ℕ) : ℝ) * log (n + 1) + log (1 / δ)) / n)
        < klDiv (weightedMeasure (empiricalFreq fun k ↦ X k ω)) (weightedMeasure p)}
      ≤ ENNReal.ofReal δ := by
  refine (measure_lt_klDiv_empiricalFreq_le hX hp0 hlaw _).trans (le_of_eq ?_)
  congr 1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  rw [mul_div_cancel₀ _ hnR.ne', neg_add, exp_add, Real.exp_neg, Real.exp_neg, Real.exp_nat_mul,
    exp_log hn1, exp_log (by positivity)]
  field_simp

end Sanov

end InformationTheory
