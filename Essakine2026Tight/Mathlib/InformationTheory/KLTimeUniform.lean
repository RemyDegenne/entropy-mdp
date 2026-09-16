/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import Essakine2026Tight.Mathlib.InformationTheory.MethodOfTypes
public import Essakine2026Tight.Mathlib.Probability.Martingale.Ville

/-!
# Time-uniform KL concentration of the empirical distribution

Let `ξ 0, ξ 1, …` be an i.i.d. sequence with law `ν` on a finite type `α` with `m` elements and
measurable singletons, and `q̂ₙ = weightedMeasure (empiricalFreq (ξ 0, …, ξ (n - 1)))` the
empirical distribution of its first `n` terms. For every `δ > 0`,
`ℙ(∃ n ≥ 1, KL(q̂ₙ ‖ ν) ≥ (log (1/δ) + (m - 1) log (n + 1) + 1 + log n / 2) / n) ≤ δ`
(`InformationTheory.measure_exists_le_klDiv_empiricalFreq_le`), and the same with the larger
threshold `(log (1/δ) + m log (e (n + 1))) / n`
(`InformationTheory.measure_exists_le_klDiv_empiricalFreq_le'`). Both are also stated for the
coordinate process of the product measure `Measure.infinitePi (fun _ ↦ ν)` on `ℕ → α`
(`InformationTheory.measure_exists_le_klDiv_empiricalFreq_le_infinitePi` and its primed version),
and for a sequence adapted to a filtration `ℱ` with `ξ n` independent of `ℱ n`
(`InformationTheory.measure_exists_le_klDiv_empiricalFreq_le_of_filtration`).

## Proof: the Laplace mixture

With `N_k(a) = #{i < k | ξ i = a}` and `p(a) = ν{a}`, the *Laplace (rule of succession) likelihood
ratio* is `Mₙ = ∏_{k < n} ((N_k(ξ k) + 1) / (k + m)) / p(ξ k)` (`InformationTheory.laplaceRatio`).

* `InformationTheory.supermartingale_laplaceRatio`: `M` is a nonnegative supermartingale with
  `M₀ = 1`, since
  `𝔼[(N_n(ξ n) + 1)/((n + m) p(ξ n)) | ℱ n] = ∑_{p(a) > 0} (N_n(a) + 1)/(n + m) ≤ 1`.
* `InformationTheory.prod_range_typeCount_add_one`, `InformationTheory.laplaceRatio_eq`:
  `∏_{k < n} (N_k(ξ k) + 1) = ∏ₐ N_n(a)!`, hence
  `Mₙ = ∏ₐ N_n(a)! / (m (m + 1) ⋯ (m + n - 1) ∏_{k < n} p(ξ k))`, the value of the mixture of the
  likelihood ratios `∏_{k < n} q(ξ k)/p(ξ k)` over the uniform prior on the simplex.
* `InformationTheory.exp_mul_toReal_klDiv_le_laplaceRatio`: if every `ξ k` has positive mass,
  `exp (n KL(q̂ₙ ‖ ν)) ≤ Mₙ (n + 1)^{m - 1} e √n`, from `N^N ≤ e^N N!`,
  `m (m + 1) ⋯ (m + n - 1) = n! binom(n + m - 1, n) ≤ n! (n + 1)^{m - 1}` and Stirling's upper
  bound `n! ≤ e √n (n/e)^n` (`Stirling.factorial_le_exp_one_mul_sqrt_mul_div_pow`).
* Ville's inequality `ℙ(∃ n, Mₙ ≥ 1/δ) ≤ δ` concludes, the sample points of mass zero forming a
  null event.
-/

@[expose] public section

open MeasureTheory Real Finset
open scoped ENNReal Nat

/-- **Stirling's upper bound**: `n! ≤ e √n (n/e)^n` for `n ≥ 1`. -/
lemma Stirling.factorial_le_exp_one_mul_sqrt_mul_div_pow {n : ℕ} (hn : n ≠ 0) :
    (n ! : ℝ) ≤ exp 1 * √n * (n / exp 1) ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h := Stirling.stirlingSeq'_antitone (Nat.zero_le k)
  simp only [Function.comp_apply, Nat.succ_eq_add_one, zero_add, Stirling.stirlingSeq_one] at h
  unfold Stirling.stirlingSeq at h
  have hpos : 0 < √(2 * ((k + 1 : ℕ) : ℝ)) * (((k + 1 : ℕ) : ℝ) / exp 1) ^ (k + 1) := by
    positivity
  rw [div_le_div_iff₀ hpos (by positivity)] at h
  rw [Real.sqrt_mul (by norm_num) ((k + 1 : ℕ) : ℝ)] at h
  change (((k + 1 : ℕ) ! : ℕ) : ℝ)
    ≤ exp 1 * √((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) / exp 1) ^ (k + 1)
  refine le_of_mul_le_mul_right (h.trans_eq ?_) (by positivity : (0 : ℝ) < √2)
  ring

/-- `m (m + 1) ⋯ (m + n - 1) ≤ n! (n + 1)^{m - 1}` for `m ≥ 1`. -/
lemma Nat.ascFactorial_le_factorial_mul_add_one_pow {m : ℕ} (hm : 0 < m) (n : ℕ) :
    m.ascFactorial n ≤ n ! * (n + 1) ^ (m - 1) := by
  rw [Nat.ascFactorial_eq_factorial_mul_choose']
  refine Nat.mul_le_mul_left _ ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hm
  rw [zero_add, Nat.add_sub_cancel, show m + 1 + n - 1 = n + m by omega, Nat.choose_symm_add]
  exact Nat.choose_add_le_add_one_pow n m

/-- On a countable type with measurable singletons, `μ ≪ ν` as soon as every `ν`-null singleton is
`μ`-null. -/
lemma MeasureTheory.Measure.absolutelyContinuous_of_forall_singleton {α : Type*}
    {mα : MeasurableSpace α} [Countable α] {μ ν : Measure α} (h : ∀ a, ν {a} = 0 → μ {a} = 0) :
    μ ≪ ν := by
  intro s hs
  rw [← Set.biUnion_of_singleton s, measure_biUnion_null_iff s.to_countable]
  exact fun a ha ↦ h a (measure_mono_null (Set.singleton_subset_iff.2 ha) hs)

namespace InformationTheory

variable {α : Type*} [Fintype α] [DecidableEq α]

section Counts

omit [Fintype α] in
/-- The counts of the prefix of length `n + 1` of a sequence are those of the prefix of length `n`
plus the indicator of the letter `x n`. -/
lemma typeCount_prefix_succ (x : ℕ → α) (n : ℕ) (a : α) :
    typeCount (fun k : Fin (n + 1) ↦ x k) a
      = typeCount (fun k : Fin n ↦ x k) a + if x n = a then 1 else 0 := by
  simp only [typeCount, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  simp

omit [Fintype α] in
/-- A letter occurs at most `n` times in a sequence of length `n`. -/
lemma typeCount_le {n : ℕ} (x : Fin n → α) (a : α) : typeCount x a ≤ n :=
  (Finset.card_filter_le _ _).trans (by simp)

/-- **The rule-of-succession product**: `∏_{k < n} (N_k(x k) + 1) = ∏ₐ N_n(a)!`, where `N_k(a)` is
the number of occurrences of `a` among `x 0, …, x (k - 1)`. -/
lemma prod_range_typeCount_add_one (x : ℕ → α) (n : ℕ) :
    ∏ k ∈ range n, (typeCount (fun i : Fin k ↦ x i) (x k) + 1)
      = ∏ a, (typeCount (fun i : Fin n ↦ x i) a)! := by
  induction n with
  | zero => simp [typeCount]
  | succ n ih =>
    rw [prod_range_succ, ih]
    simp_rw [typeCount_prefix_succ]
    have : ∀ a, (typeCount (fun i : Fin n ↦ x i) a + if x n = a then 1 else 0)!
        = (typeCount (fun i : Fin n ↦ x i) a)!
          * if x n = a then typeCount (fun i : Fin n ↦ x i) a + 1 else 1 := by
      intro a
      split_ifs <;> simp [Nat.factorial_succ, mul_comm]
    simp_rw [this, prod_mul_distrib, prod_ite_eq]
    simp

/-- The Laplace factor `(N_k(a) + 1) / (k + m)` is at most `1`. -/
lemma typeCount_add_one_div_le_one (x : ℕ → α) (k : ℕ) (a : α) :
    (typeCount (fun i : Fin k ↦ x i) a + 1 : ℝ) / (k + Fintype.card α) ≤ 1 := by
  have hle : (typeCount (fun i : Fin k ↦ x i) a : ℝ) ≤ k := by exact_mod_cast typeCount_le _ a
  have hm : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos_iff.2 ⟨a⟩
  rw [div_le_one (by positivity)]
  linarith

omit [DecidableEq α] in
/-- The combinatorial core of the lower bound on the Laplace ratio: for counts `N` of total
`n ≥ 1` on a set of `m` elements,
`∏ₐ N(a)^{N(a)} · m (m + 1) ⋯ (m + n - 1) ≤ ∏ₐ N(a)! · n^n · (n + 1)^{m - 1} e √n`. -/
lemma prod_pow_self_mul_ascFactorial_le {n : ℕ} (hn : n ≠ 0) (N : α → ℕ) (hN : ∑ a, N a = n) :
    (∏ a, ((N a : ℝ) ^ N a)) * (Fintype.card α).ascFactorial n
      ≤ (∏ a, ((N a)! : ℝ)) * n ^ n * ((n + 1) ^ (Fintype.card α - 1) * exp 1 * √n) := by
  have hm : 0 < Fintype.card α := by
    rcases isEmpty_or_nonempty α with hα | hα
    · simp only [univ_eq_empty, sum_empty] at hN
      omega
    · exact Fintype.card_pos
  have h1 : ∏ a, ((N a : ℝ) ^ N a) ≤ exp n * ∏ a, ((N a)! : ℝ) := by
    have : ∀ a, (N a : ℝ) ^ N a ≤ exp (N a) * (N a)! := fun a ↦ by
      have h := Real.pow_div_factorial_le_exp (x := (N a : ℝ)) (by positivity) (N a)
      rwa [div_le_iff₀ (by positivity)] at h
    calc ∏ a, ((N a : ℝ) ^ N a) ≤ ∏ a, (exp (N a) * (N a)! : ℝ) :=
          Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun a _ ↦ this a
      _ = exp n * ∏ a, ((N a)! : ℝ) := by
          rw [prod_mul_distrib, ← exp_sum, ← Nat.cast_sum, hN]
  have h2 : ((Fintype.card α).ascFactorial n : ℝ) ≤ n ! * (n + 1) ^ (Fintype.card α - 1) := by
    exact_mod_cast Nat.ascFactorial_le_factorial_mul_add_one_pow hm n
  have h3 := Stirling.factorial_le_exp_one_mul_sqrt_mul_div_pow hn
  have hexp : exp (n : ℝ) * ((n : ℝ) / exp 1) ^ n = (n : ℝ) ^ n := by
    rw [div_pow, ← Real.exp_nat_mul, mul_one]
    field_simp
  calc (∏ a, ((N a : ℝ) ^ N a)) * (Fintype.card α).ascFactorial n
      ≤ (exp n * ∏ a, ((N a)! : ℝ)) * (n ! * (n + 1) ^ (Fintype.card α - 1)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ ≤ (exp n * ∏ a, ((N a)! : ℝ))
          * ((exp 1 * √n * (n / exp 1) ^ n) * (n + 1) ^ (Fintype.card α - 1)) := by
        gcongr
    _ = (∏ a, ((N a)! : ℝ)) * (exp (n : ℝ) * ((n : ℝ) / exp 1) ^ n)
          * ((n + 1) ^ (Fintype.card α - 1) * exp 1 * √n) := by ring
    _ = _ := by rw [hexp]

omit [DecidableEq α] in
/-- The sharp threshold of the time-uniform bound is at most the simplified one:
`(log (1/δ) + (m - 1) log (n + 1) + 1 + log n / 2) / n ≤ (log (1/δ) + m log (e (n + 1))) / n`. -/
lemma timeUniformThreshold_le {n : ℕ} (hn : 0 < n) (hm : 0 < Fintype.card α) (δ : ℝ) :
    (log (1 / δ) + ((Fintype.card α - 1 : ℕ) : ℝ) * log (n + 1) + 1 + log n / 2) / n
      ≤ (log (1 / δ) + Fintype.card α * log (exp 1 * (n + 1))) / n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have hlogn : 0 ≤ log n := Real.log_nonneg hnR
  have hlogn1 : log n ≤ log (n + 1) := Real.log_le_log (by positivity) (by linarith)
  have hm' : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast hm
  rw [Real.log_mul (exp_pos 1).ne' (by positivity), Real.log_exp, Nat.cast_sub hm, Nat.cast_one]
  nlinarith

end Counts

section Ratio

variable [MeasurableSpace α] {ν : Measure α}

/-- The **Laplace (rule of succession) likelihood ratio** of the first `n` terms of a sequence `x`
with respect to a measure `ν`: `∏_{k < n} ((N_k(x k) + 1) / (k + m)) / ν{x k}`, where `m` is the
cardinality of `α` and `N_k(a)` the number of occurrences of `a` among `x 0, …, x (k - 1)`. It is
the mixture of the likelihood ratios `∏_{k < n} q(x k) / ν{x k}` over the uniform prior on the
simplex of probability vectors `q`. -/
noncomputable def laplaceRatio (ν : Measure α) (x : ℕ → α) (n : ℕ) : ℝ :=
  ∏ k ∈ range n,
    (typeCount (fun i : Fin k ↦ x i) (x k) + 1 : ℝ) / (k + Fintype.card α) / ν.real {x k}

@[simp]
lemma laplaceRatio_zero (ν : Measure α) (x : ℕ → α) : laplaceRatio ν x 0 = 1 := by
  simp [laplaceRatio]

lemma laplaceRatio_nonneg (ν : Measure α) (x : ℕ → α) (n : ℕ) : 0 ≤ laplaceRatio ν x n :=
  Finset.prod_nonneg fun _ _ ↦ by positivity

lemma laplaceRatio_succ (ν : Measure α) (x : ℕ → α) (n : ℕ) :
    laplaceRatio ν x (n + 1) = laplaceRatio ν x n
      * ((typeCount (fun i : Fin n ↦ x i) (x n) + 1 : ℝ) / (n + Fintype.card α)
        / ν.real {x n}) :=
  prod_range_succ _ _

/-- `∏_{k < n} ν{x k} = ∏ₐ ν{a}^{N_n(a)}`. -/
lemma prod_range_measureReal_eq_prod_pow_typeCount (ν : Measure α) (x : ℕ → α) (n : ℕ) :
    ∏ k ∈ range n, ν.real {x k} = ∏ a, ν.real {a} ^ typeCount (fun i : Fin n ↦ x i) a := by
  rw [← prod_comp_eq_prod_pow_typeCount (fun a ↦ ν.real {a}) (fun i : Fin n ↦ x i)]
  exact (Fin.prod_univ_eq_prod_range (fun k ↦ ν.real {x k}) n).symm

/-- **Closed form of the Laplace ratio**:
`Mₙ = ∏ₐ N_n(a)! / (m (m + 1) ⋯ (m + n - 1) ∏_{k < n} ν{x k})`. -/
lemma laplaceRatio_eq (ν : Measure α) (x : ℕ → α) (n : ℕ) :
    laplaceRatio ν x n = (∏ a, ((typeCount (fun i : Fin n ↦ x i) a)! : ℝ))
      / (Fintype.card α).ascFactorial n / ∏ k ∈ range n, ν.real {x k} := by
  rw [laplaceRatio, prod_div_distrib, prod_div_distrib, Nat.ascFactorial_eq_prod_range]
  congr 2
  · rw [← Nat.cast_prod, ← prod_range_typeCount_add_one]
    push_cast
    rfl
  · push_cast
    exact prod_congr rfl fun k _ ↦ add_comm _ _

/-- The empirical distribution of a nonempty sample is a probability measure. -/
lemma isProbabilityMeasure_weightedMeasure_empiricalFreq {n : ℕ} (hn : n ≠ 0) (y : Fin n → α) :
    IsProbabilityMeasure (weightedMeasure (empiricalFreq y)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  refine isProbabilityMeasure_weightedMeasure (fun a ↦ by unfold empiricalFreq; positivity) ?_
  simp only [empiricalFreq, ← Finset.sum_div]
  rw [div_eq_one_iff_eq hnR.ne']
  exact_mod_cast sum_typeCount y

variable [MeasurableSingletonClass α]

/-- The empirical distribution of a sample `y` is absolutely continuous with respect to `ν` when
every sample point has positive `ν`-mass. -/
lemma weightedMeasure_empiricalFreq_absolutelyContinuous {n : ℕ} {y : Fin n → α}
    (hy : ∀ k, ν {y k} ≠ 0) : weightedMeasure (empiricalFreq y) ≪ ν := by
  refine Measure.absolutelyContinuous_of_forall_singleton fun a ha ↦ ?_
  rw [weightedMeasure_singleton, ENNReal.ofReal_eq_zero]
  by_contra h
  push Not at h
  have hpos : 0 < typeCount y a := by
    by_contra h0
    simp [empiricalFreq, Nat.eq_zero_of_not_pos h0] at h
  obtain ⟨k, hk⟩ := Finset.card_pos.1 hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  exact hy k (hk ▸ ha)

/-- `exp (n KL(q̂ₙ ‖ ν)) ∏_{k < n} ν{x k} = ∏ₐ N_n(a)^{N_n(a)} / n^n` when every `x k`, `k < n`,
has positive mass. -/
lemma exp_mul_toReal_klDiv_mul_prod_eq [IsProbabilityMeasure ν] {x : ℕ → α} {n : ℕ}
    (hn : n ≠ 0) (hx : ∀ k < n, ν {x k} ≠ 0) :
    exp (n * (klDiv (weightedMeasure (empiricalFreq fun i : Fin n ↦ x i)) ν).toReal)
        * ∏ k ∈ range n, ν.real {x k}
      = (∏ a, ((typeCount (fun i : Fin n ↦ x i) a : ℝ) ^ typeCount (fun i : Fin n ↦ x i) a))
        / (n : ℝ) ^ n := by
  set y : Fin n → α := fun i ↦ x i with hy
  set N := typeCount y with hN
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hq0 : ∀ a, 0 ≤ empiricalFreq y a := fun a ↦ by unfold empiricalFreq; positivity
  have := isProbabilityMeasure_weightedMeasure_empiricalFreq hn y
  have hac : weightedMeasure (empiricalFreq y) ≪ ν :=
    weightedMeasure_empiricalFreq_absolutelyContinuous fun k ↦ hx k k.2
  have hsupp : ∀ a, 0 < N a → ν {a} ≠ 0 := by
    intro a ha
    obtain ⟨k, hk⟩ := Finset.card_pos.1 ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [← hk]
    exact hx k k.2
  rw [toReal_klDiv_eq_sum hac, prod_range_measureReal_eq_prod_pow_typeCount]
  simp only [measureReal_weightedMeasure_singleton hq0]
  have hpow : (n : ℝ) ^ n = ∏ a, (n : ℝ) ^ N a := by
    rw [Finset.prod_pow_eq_pow_sum, hN, sum_typeCount]
  rw [Finset.mul_sum, exp_sum, ← prod_mul_distrib, eq_div_iff (by positivity), hpow,
    ← prod_mul_distrib]
  refine prod_congr rfl fun a _ ↦ ?_
  change exp (n * (N a / n * log ((N a / n) / ν.real {a}))) * ν.real {a} ^ N a * (n : ℝ) ^ N a
    = (N a : ℝ) ^ N a
  rcases Nat.eq_zero_or_pos (N a) with h0 | hpos
  · simp [h0]
  have hνa : 0 < ν.real {a} := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hsupp a hpos) (measure_ne_top _ _)
  have hNa : (0 : ℝ) < N a := by exact_mod_cast hpos
  rw [← mul_assoc, mul_div_cancel₀ _ hnR.ne', Real.exp_nat_mul,
    Real.exp_log (by positivity), ← mul_pow, ← mul_pow]
  congr 1
  field_simp

/-- **Lower bound on the Laplace ratio**: if every `x k`, `k < n`, has positive mass, then
`exp (n KL(q̂ₙ ‖ ν)) ≤ Mₙ (n + 1)^{m - 1} e √n`. -/
lemma exp_mul_toReal_klDiv_le_laplaceRatio [IsProbabilityMeasure ν] {x : ℕ → α} {n : ℕ}
    (hn : n ≠ 0) (hx : ∀ k < n, ν {x k} ≠ 0) :
    exp (n * (klDiv (weightedMeasure (empiricalFreq fun i : Fin n ↦ x i)) ν).toReal)
      ≤ laplaceRatio ν x n * ((n + 1) ^ (Fintype.card α - 1) * exp 1 * √n) := by
  have hP : 0 < ∏ k ∈ range n, ν.real {x k} := by
    refine Finset.prod_pos fun k hk ↦ ?_
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hx k (mem_range.1 hk)) (measure_ne_top _ _)
  have hasc : (0 : ℝ) < (Fintype.card α).ascFactorial n := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt (Fintype.card_pos_iff.2 ⟨x 0⟩)
    rw [hm, zero_add]
    exact_mod_cast Nat.ascFactorial_pos m n
  rw [← mul_le_mul_iff_left₀ hP, exp_mul_toReal_klDiv_mul_prod_eq hn hx, laplaceRatio_eq,
    div_le_iff₀ (by positivity)]
  have hcore := prod_pow_self_mul_ascFactorial_le hn (typeCount fun i : Fin n ↦ x i)
    (sum_typeCount _)
  calc (∏ a, ((typeCount (fun i : Fin n ↦ x i) a : ℝ) ^ typeCount (fun i : Fin n ↦ x i) a))
      = (∏ a, ((typeCount (fun i : Fin n ↦ x i) a : ℝ) ^ typeCount (fun i : Fin n ↦ x i) a))
          * (Fintype.card α).ascFactorial n / (Fintype.card α).ascFactorial n := by
        field_simp
    _ ≤ (∏ a, ((typeCount (fun i : Fin n ↦ x i) a)! : ℝ)) * n ^ n
          * ((n + 1) ^ (Fintype.card α - 1) * exp 1 * √n)
          / (Fintype.card α).ascFactorial n := by
        gcongr
    _ = _ := by field_simp

/-- **The Laplace ratio exceeds `1/δ` on the deviation event**: if every `x k`, `k < n`, has
positive mass and `KL(q̂ₙ ‖ ν) ≥ (log (1/δ) + (m - 1) log (n + 1) + 1 + log n / 2) / n`, then
`Mₙ ≥ 1/δ`. -/
lemma one_div_le_laplaceRatio [IsProbabilityMeasure ν] {x : ℕ → α} {n : ℕ} (hn : n ≠ 0)
    (hx : ∀ k < n, ν {x k} ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (h : ENNReal.ofReal ((log (1 / δ) + ((Fintype.card α - 1 : ℕ) : ℝ) * log (n + 1) + 1
        + log n / 2) / n) ≤ klDiv (weightedMeasure (empiricalFreq fun i : Fin n ↦ x i)) ν) :
    1 / δ ≤ laplaceRatio ν x n := by
  have := isProbabilityMeasure_weightedMeasure_empiricalFreq hn fun i : Fin n ↦ x i
  have hac := weightedMeasure_empiricalFreq_absolutelyContinuous (ν := ν)
    (y := fun i : Fin n ↦ x i) fun k ↦ hx k k.2
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [ENNReal.ofReal_le_iff_le_toReal (klDiv_ne_top_of_finite hac), div_le_iff₀ hnR] at h
  have hexp := (exp_le_exp.2 (h.trans_eq (mul_comm _ _))).trans
    (exp_mul_toReal_klDiv_le_laplaceRatio hn hx)
  have hsqrt : exp (log n / 2) = √n := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnR]
    ring_nf
  have heq : exp (log (1 / δ) + ((Fintype.card α - 1 : ℕ) : ℝ) * log (n + 1) + 1 + log n / 2)
      = 1 / δ * (((n : ℝ) + 1) ^ (Fintype.card α - 1) * exp 1 * √n) := by
    rw [exp_add, exp_add, exp_add, exp_log (by positivity), hsqrt, ← Real.exp_log
      (show (0 : ℝ) < n + 1 by positivity), ← Real.exp_nat_mul, Real.exp_log (by positivity)]
    ring
  rw [heq] at hexp
  exact le_of_mul_le_mul_right hexp (by positivity)

omit [MeasurableSingletonClass α] in
/-- The Laplace ratio is bounded: `Mₙ ≤ (∑ₐ ν{a}⁻¹)^n`. -/
lemma laplaceRatio_le (x : ℕ → α) (n : ℕ) :
    laplaceRatio ν x n ≤ (∑ a, (ν.real {a})⁻¹) ^ n := by
  rw [laplaceRatio]
  refine (Finset.prod_le_prod₀ (g := fun _ ↦ ∑ a, (ν.real {a})⁻¹) (fun _ _ ↦ by positivity)
    fun k _ ↦ ?_).trans_eq (by simp)
  calc (typeCount (fun i : Fin k ↦ x i) (x k) + 1 : ℝ) / (k + Fintype.card α) / ν.real {x k}
      ≤ 1 / ν.real {x k} := by gcongr; exact typeCount_add_one_div_le_one x k (x k)
    _ = (ν.real {x k})⁻¹ := one_div _
    _ ≤ ∑ a, (ν.real {a})⁻¹ :=
        Finset.single_le_sum (f := fun a ↦ (ν.real {a})⁻¹) (fun _ _ ↦ by positivity)
          (mem_univ _)

end Ratio

section Supermartingale

open ProbabilityTheory

variable [MeasurableSpace α] [MeasurableSingletonClass α] {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} {ℱ : Filtration ℕ mΩ} {ξ : ℕ → Ω → α} {ν : Measure α}

omit [Fintype α] in
/-- If `ξ k` is `ℱ (k + 1)`-measurable for every `k`, the counts of the first `k ≤ n` terms are
`ℱ n`-measurable. -/
lemma measurable_typeCount_filtration [Finite α] (hξ : ∀ k, Measurable[ℱ (k + 1)] (ξ k)) {k n : ℕ}
    (hkn : k ≤ n) (a : α) :
    Measurable[ℱ n] (fun ω ↦ (typeCount (fun i : Fin k ↦ ξ i ω) a : ℝ)) := by
  have htuple : Measurable[ℱ n] (fun ω (i : Fin k) ↦ ξ i ω) :=
    @Measurable.of_eval _ _ _ (ℱ n) _ _ fun i ↦
      (hξ i).mono (ℱ.mono (by have := i.2; omega)) le_rfl
  exact (measurable_of_countable (fun y : Fin k → α ↦ (typeCount y a : ℝ))).comp htuple

/-- If `ξ k` is `ℱ (k + 1)`-measurable for every `k`, the Laplace ratio `Mₙ` is
`ℱ n`-measurable. -/
lemma measurable_laplaceRatio_filtration (hξ : ∀ k, Measurable[ℱ (k + 1)] (ξ k)) (n : ℕ) :
    Measurable[ℱ n] (fun ω ↦ laplaceRatio ν (fun k ↦ ξ k ω) n) := by
  unfold laplaceRatio
  refine @Finset.measurable_prod _ _ _ _ _ _ (ℱ n) _ _ fun k hk ↦ ?_
  have hk' : k + 1 ≤ n := mem_range.1 hk
  have htuple : Measurable[ℱ n] (fun ω (i : Fin (k + 1)) ↦ ξ i ω) :=
    @Measurable.of_eval _ _ _ (ℱ n) _ _ fun i ↦
      (hξ i).mono (ℱ.mono (by have := i.2; omega)) le_rfl
  have hg := (measurable_of_countable (fun y : Fin (k + 1) → α ↦
    (typeCount (fun i : Fin k ↦ y i.castSucc) (y (Fin.last k)) + 1 : ℝ)
      / (k + Fintype.card α) / ν.real {y (Fin.last k)})).comp htuple
  exact hg

variable [IsProbabilityMeasure μ]

/-- **The Laplace mixture is a supermartingale**: if `ξ k` is `ℱ (k + 1)`-measurable, `ξ n` is
independent of `ℱ n` and has law `ν` for every `n`, then the Laplace ratio
`Mₙ = ∏_{k < n} ((N_k(ξ k) + 1) / (k + m)) / ν{ξ k}` is a supermartingale for `ℱ`. -/
lemma supermartingale_laplaceRatio (hξ : ∀ k, Measurable[ℱ (k + 1)] (ξ k))
    (hind : ∀ n, Indep (ℱ n) (MeasurableSpace.comap (ξ n) inferInstance) μ)
    (hlaw : ∀ n, HasLaw (ξ n) ν μ) :
    Supermartingale (fun n ω ↦ laplaceRatio ν (fun k ↦ ξ k ω) n) ℱ μ := by
  set L : ℕ → Ω → ℝ := fun n ω ↦ laplaceRatio ν (fun k ↦ ξ k ω) n with hL
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∑ a, (ν.real {a})⁻¹ := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := hC ▸ Finset.sum_nonneg fun _ _ ↦ by positivity
  have hLmeas : ∀ n, Measurable[ℱ n] (L n) := measurable_laplaceRatio_filtration hξ
  have hLm : ∀ n, Measurable (L n) := fun n ↦ (hLmeas n).mono (ℱ.le n) le_rfl
  have hξm : ∀ n, Measurable (ξ n) := fun n ↦ (hξ n).mono (ℱ.le (n + 1)) le_rfl
  have hint_of : ∀ (f : Ω → ℝ) (K : ℝ), Measurable f → (∀ ω, ‖f ω‖ ≤ K) → Integrable f μ :=
    fun f K hf hK ↦ Integrable.of_bound hf.aestronglyMeasurable K (.of_forall hK)
  have hL0 : ∀ n ω, 0 ≤ L n ω := fun n ω ↦ laplaceRatio_nonneg _ _ _
  have hLbdd : ∀ n ω, ‖L n ω‖ ≤ C ^ n := fun n ω ↦ by
    rw [Real.norm_of_nonneg (hL0 n ω), hC]
    exact laplaceRatio_le _ n
  have hLint : ∀ n, Integrable (L n) μ := fun n ↦ hint_of _ _ (hLm n) (hLbdd n)
  refine supermartingale_of_setIntegral_succ_le (fun n ↦ (hLmeas n).stronglyMeasurable) hLint ?_
  intro n s hs
  have hsm : MeasurableSet s := ℱ.le n s hs
  -- decomposition of `M (n + 1) = Mₙ c_{ξ n}` along the value of `ξ n`
  set c : α → Ω → ℝ := fun a ω ↦
    (typeCount (fun i : Fin n ↦ ξ i ω) a + 1 : ℝ) / (n + Fintype.card α) / ν.real {a} with hc
  set F : α → Ω → ℝ := fun a ↦ s.indicator (fun ω ↦ L n ω * c a ω) with hF
  set G : α → Ω → ℝ := fun a ω ↦ if ξ n ω = a then 1 else 0 with hG
  have hcmeas : ∀ a, Measurable[ℱ n] (c a) := fun a ↦
    (((measurable_typeCount_filtration hξ le_rfl a).add_const 1).div_const _).div_const _
  have hc0 : ∀ a ω, 0 ≤ c a ω := fun a ω ↦ by simp only [hc]; positivity
  have hcbdd : ∀ a ω, c a ω ≤ C := fun a ω ↦ by
    calc c a ω ≤ 1 / ν.real {a} := by
          simp only [hc]; gcongr; exact typeCount_add_one_div_le_one (fun k ↦ ξ k ω) n a
      _ = (ν.real {a})⁻¹ := one_div _
      _ ≤ C := hC ▸ Finset.single_le_sum (f := fun a ↦ (ν.real {a})⁻¹)
          (fun _ _ ↦ by positivity) (mem_univ _)
  have hFmeas : ∀ a, Measurable[ℱ n] (F a) := fun a ↦ ((hLmeas n).mul (hcmeas a)).indicator hs
  have hFm : ∀ a, Measurable (F a) := fun a ↦ (hFmeas a).mono (ℱ.le n) le_rfl
  have hFbdd : ∀ a ω, ‖F a ω‖ ≤ C ^ n * C := fun a ω ↦ by
    simp only [hF, Set.indicator]
    split_ifs
    · rw [Real.norm_of_nonneg (mul_nonneg (hL0 n ω) (hc0 a ω))]
      exact mul_le_mul (by simpa [Real.norm_of_nonneg (hL0 n ω)] using hLbdd n ω) (hcbdd a ω)
        (hc0 a ω) (by positivity)
    · simp only [norm_zero]; positivity
  have hFint : ∀ a, Integrable (F a) μ := fun a ↦ hint_of _ _ (hFm a) (hFbdd a)
  have hGmeas : ∀ a, Measurable[MeasurableSpace.comap (ξ n) inferInstance] (G a) := fun a ↦
    (measurable_of_countable (fun b : α ↦ if b = a then (1 : ℝ) else 0)).comp
      (comap_measurable (ξ n))
  have hGm : ∀ a, Measurable (G a) := fun a ↦
    (measurable_of_countable (fun b : α ↦ if b = a then (1 : ℝ) else 0)).comp (hξm n)
  have hFGint : ∀ a, Integrable (fun ω ↦ F a ω * G a ω) μ := fun a ↦
    hint_of _ (C ^ n * C) ((hFm a).mul (hGm a)) fun ω ↦ by
      rw [norm_mul]
      calc ‖F a ω‖ * ‖G a ω‖ ≤ (C ^ n * C) * 1 := by
            refine mul_le_mul (hFbdd a ω) ?_ (norm_nonneg _) (by positivity)
            simp only [hG]; split_ifs <;> simp
        _ = C ^ n * C := mul_one _
  have hGint : ∀ a, ∫ ω, G a ω ∂μ = ν.real {a} := fun a ↦ by
    have : G a = (ξ n ⁻¹' {a}).indicator 1 := by
      ext ω; simp [hG, Set.indicator]
    rw [this, integral_indicator_one ((hξm n) (measurableSet_singleton a)), measureReal_def,
      measureReal_def, ← (hlaw n).map_eq, Measure.map_apply (hξm n) (measurableSet_singleton a)]
  -- independence of `ξ n` from `ℱ n`
  have hFG : ∀ a, ∫ ω, F a ω * G a ω ∂μ = (∫ ω, F a ω ∂μ) * ν.real {a} := fun a ↦ by
    have hind' : IndepFun (F a) (G a) μ := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_right (indep_of_indep_of_le_left (hind n) (hFmeas a).comap_le)
        (hGmeas a).comap_le
    rw [hind'.integral_fun_mul_eq_mul_integral (hFm a).aestronglyMeasurable
      (hGm a).aestronglyMeasurable, hGint]
  have hdecomp : ∀ ω, s.indicator (L (n + 1)) ω = ∑ a, F a ω * G a ω := fun ω ↦ by
    by_cases hω : ω ∈ s
    · simp only [hF, hG, Set.indicator_of_mem hω, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true, hL, hc]
      exact laplaceRatio_succ _ _ _
    · simp [hF, Set.indicator_of_notMem hω]
  -- `∑ₐ c a ν{a} ≤ ∑ₐ (Nₙ(a) + 1) / (n + m) = 1`
  have hsum_le : ∀ ω, ∑ a, F a ω * ν.real {a} ≤ s.indicator (L n) ω := fun ω ↦ by
    by_cases hω : ω ∈ s
    · simp only [hF, Set.indicator_of_mem hω]
      have hm : 0 < Fintype.card α := Fintype.card_pos_iff.2 ⟨ξ 0 ω⟩
      have hnm : (0 : ℝ) < n + Fintype.card α := by positivity
      calc ∑ a, L n ω * c a ω * ν.real {a}
          = L n ω * ∑ a, c a ω * ν.real {a} := by
            rw [Finset.mul_sum]; exact sum_congr rfl fun _ _ ↦ mul_assoc _ _ _
        _ ≤ L n ω * ∑ a, (typeCount (fun i : Fin n ↦ ξ i ω) a + 1 : ℝ)
              / (n + Fintype.card α) := by
            refine mul_le_mul_of_nonneg_left (sum_le_sum fun a _ ↦ ?_) (hL0 n ω)
            simp only [hc]
            rcases eq_or_ne (ν.real {a}) 0 with h0 | h0
            · rw [h0, mul_zero]; positivity
            · rw [div_mul_cancel₀ _ h0]
        _ = L n ω := by
            rw [← Finset.sum_div, Finset.sum_add_distrib, ← Nat.cast_sum, sum_typeCount,
              Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, div_self hnm.ne',
              mul_one]
    · simp [hF, Set.indicator_of_notMem hω]
  calc ∫ ω in s, L (n + 1) ω ∂μ = ∫ ω, s.indicator (L (n + 1)) ω ∂μ :=
        (integral_indicator hsm).symm
    _ = ∫ ω, ∑ a, F a ω * G a ω ∂μ := integral_congr_ae (.of_forall hdecomp)
    _ = ∑ a, ∫ ω, F a ω * G a ω ∂μ := integral_finsetSum _ fun a _ ↦ hFGint a
    _ = ∑ a, (∫ ω, F a ω ∂μ) * ν.real {a} := sum_congr rfl fun a _ ↦ hFG a
    _ = ∫ ω, ∑ a, F a ω * ν.real {a} ∂μ := by
        rw [integral_finsetSum _ fun a _ ↦ (hFint a).mul_const _]
        exact sum_congr rfl fun a _ ↦ (integral_mul_const _ _).symm
    _ ≤ ∫ ω, s.indicator (L n) ω ∂μ :=
        integral_mono (integrable_finsetSum _ fun a _ ↦ (hFint a).mul_const _)
          ((hLint n).indicator hsm) hsum_le
    _ = ∫ ω in s, L n ω ∂μ := integral_indicator hsm

/-- **Time-uniform KL concentration of the empirical distribution**, filtration form: if `ξ k` is
`ℱ (k + 1)`-measurable, `ξ n` is independent of `ℱ n` and has law `ν` for every `n`, then for
every `δ > 0`,
`ℙ(∃ n ≥ 1, KL(q̂ₙ ‖ ν) ≥ (log (1/δ) + (m - 1) log (n + 1) + 1 + log n / 2) / n) ≤ δ`. -/
lemma measure_exists_le_klDiv_empiricalFreq_le_of_filtration
    (hξ : ∀ k, Measurable[ℱ (k + 1)] (ξ k))
    (hind : ∀ n, Indep (ℱ n) (MeasurableSpace.comap (ξ n) inferInstance) μ)
    (hlaw : ∀ n, HasLaw (ξ n) ν μ) {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | ∃ n : ℕ, 0 < n ∧ ENNReal.ofReal ((log (1 / δ) + ((Fintype.card α - 1 : ℕ) : ℝ)
        * log (n + 1) + 1 + log n / 2) / n)
        ≤ klDiv (weightedMeasure (empiricalFreq fun k : Fin n ↦ ξ k ω)) ν}
      ≤ ENNReal.ofReal δ := by
  have := (hlaw 0).isProbabilityMeasure_iff.1 inferInstance
  have hville := (supermartingale_laplaceRatio hξ hind hlaw).measure_exists_ge_le
    (fun n ω ↦ laplaceRatio_nonneg _ _ _) (c := 1 / δ) (by positivity)
  simp only [laplaceRatio_zero, integral_const, probReal_univ, smul_eq_mul, mul_one,
    one_div_one_div] at hville
  refine le_trans (measure_mono_ae ?_) hville
  have hν : ∀ᵐ a ∂ν, ν {a} ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    rw [← Set.biUnion_of_singleton {a | ν {a} = 0}, measure_biUnion_null_iff (Set.to_countable _)]
    exact fun a ha ↦ ha
  have hae : ∀ᵐ ω ∂μ, ∀ k, ν {ξ k ω} ≠ 0 := by
    rw [ae_all_iff]
    intro k
    exact ae_of_ae_map (p := fun a ↦ ν {a} ≠ 0) (hlaw k).aemeasurable
      (by rw [(hlaw k).map_eq]; exact hν)
  filter_upwards [hae] with ω hω hE
  obtain ⟨n, hn, hkl⟩ := hE
  exact ⟨n, one_div_le_laplaceRatio hn.ne' (fun k _ ↦ hω k) hδ hkl⟩

end Supermartingale

section InfinitePi

open ProbabilityTheory

variable [MeasurableSpace α] [MeasurableSingletonClass α] {ν : Measure α}

/-- **Time-uniform KL concentration of the empirical distribution**, for the coordinate process of
the product measure `ν^{⊗ℕ}`: for every `δ > 0`,
`ν^{⊗ℕ}(∃ n ≥ 1, KL(q̂ₙ ‖ ν) ≥ (log (1/δ) + (m - 1) log (n + 1) + 1 + log n / 2) / n) ≤ δ`. -/
lemma measure_exists_le_klDiv_empiricalFreq_le_infinitePi [IsProbabilityMeasure ν] {δ : ℝ}
    (hδ : 0 < δ) :
    Measure.infinitePi (fun _ : ℕ ↦ ν) {x : ℕ → α | ∃ n : ℕ, 0 < n ∧ ENNReal.ofReal
        ((log (1 / δ) + ((Fintype.card α - 1 : ℕ) : ℝ) * log (n + 1) + 1 + log n / 2) / n)
        ≤ klDiv (weightedMeasure (empiricalFreq fun k : Fin n ↦ x k)) ν}
      ≤ ENNReal.ofReal δ := by
  let ℱ : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → α)) :=
    { seq := fun n ↦ ⨆ k ∈ Set.Iio n, MeasurableSpace.comap (fun x : ℕ → α ↦ x k) inferInstance
      mono' := fun i j hij ↦ biSup_mono fun k hk ↦ lt_of_lt_of_le hk hij
      le' := fun n ↦ iSup₂_le fun k _ ↦ (measurable_pi_apply k).comap_le }
  have hindep : iIndepFun (fun k (x : ℕ → α) ↦ x k) (Measure.infinitePi fun _ : ℕ ↦ ν) :=
    iIndepFun_infinitePi (X := fun _ a ↦ a) fun _ ↦ measurable_id
  refine measure_exists_le_klDiv_empiricalFreq_le_of_filtration (ℱ := ℱ) (fun k ↦ ?_)
    (fun n ↦ ?_) (fun n ↦ (measurePreserving_eval_infinitePi _ n).hasLaw) hδ
  · rw [measurable_iff_comap_le]
    exact le_iSup₂ (f := fun j (_ : j ∈ Set.Iio (k + 1)) ↦
      MeasurableSpace.comap (fun x : ℕ → α ↦ x j) inferInstance) k (by simp)
  · have h := indep_iSup_of_disjoint (fun k ↦ (measurable_pi_apply k).comap_le)
      ((iIndepFun_iff_iIndep _ _ _).1 hindep) (S := Set.Iio n) (T := {n}) (by simp)
    rw [_root_.iSup_singleton] at h
    exact h

/-- **Time-uniform KL concentration of the empirical distribution**, for the coordinate process of
`ν^{⊗ℕ}`, simplified threshold: for every `δ > 0`,
`ν^{⊗ℕ}(∃ n ≥ 1, KL(q̂ₙ ‖ ν) ≥ (log (1/δ) + m log (e (n + 1))) / n) ≤ δ`. -/
lemma measure_exists_le_klDiv_empiricalFreq_le_infinitePi' [IsProbabilityMeasure ν] {δ : ℝ}
    (hδ : 0 < δ) :
    Measure.infinitePi (fun _ : ℕ ↦ ν) {x : ℕ → α | ∃ n : ℕ, 0 < n ∧ ENNReal.ofReal
        ((log (1 / δ) + Fintype.card α * log (exp 1 * (n + 1))) / n)
        ≤ klDiv (weightedMeasure (empiricalFreq fun k : Fin n ↦ x k)) ν}
      ≤ ENNReal.ofReal δ := by
  refine (measure_mono fun x hx ↦ ?_).trans
    (measure_exists_le_klDiv_empiricalFreq_le_infinitePi hδ)
  obtain ⟨n, hn, h⟩ := hx
  exact ⟨n, hn, (ENNReal.ofReal_le_ofReal
    (timeUniformThreshold_le hn (Fintype.card_pos_iff.2 ⟨x 0⟩) δ)).trans h⟩

omit [Fintype α] [DecidableEq α] in
/-- An event of the form `∃ n, P n (x 0, …, x (n - 1))` on a countable type is measurable. -/
lemma measurableSet_exists_prefix [Countable α] (P : ∀ n : ℕ, (Fin n → α) → Prop) :
    MeasurableSet {x : ℕ → α | ∃ n, P n fun k : Fin n ↦ x k} := by
  have : {x : ℕ → α | ∃ n, P n fun k : Fin n ↦ x k}
      = ⋃ n, (fun (x : ℕ → α) (k : Fin n) ↦ x k) ⁻¹' {y | P n y} := by
    ext x; simp
  rw [this]
  exact MeasurableSet.iUnion fun n ↦
    (Measurable.of_eval fun k ↦ measurable_pi_apply _) (Set.to_countable _).measurableSet

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ξ : ℕ → Ω → α}

omit [Fintype α] [DecidableEq α] in
/-- For an i.i.d. sequence `ξ` with law `ν` on a countable type, the probability of an event
`∃ n, P n (ξ 0, …, ξ (n - 1))` is the `ν^{⊗ℕ}`-measure of the corresponding set of sequences. -/
lemma measure_exists_prefix_eq_infinitePi [Countable α] (hξ : iIndepFun ξ μ)
    (hlaw : ∀ k, HasLaw (ξ k) ν μ) (P : ∀ n : ℕ, (Fin n → α) → Prop) :
    μ {ω | ∃ n, P n fun k : Fin n ↦ ξ k ω}
      = Measure.infinitePi (fun _ : ℕ ↦ ν) {x : ℕ → α | ∃ n, P n fun k : Fin n ↦ x k} := by
  have hmeas : AEMeasurable (fun ω k ↦ ξ k ω) μ :=
    AEMeasurable.of_eval fun k ↦ (hlaw k).aemeasurable
  have hmap : μ.map (fun ω k ↦ ξ k ω) = Measure.infinitePi (fun _ ↦ ν) := by
    rw [hξ.map_fun_eq_infinitePi_map₀' fun k ↦ (hlaw k).aemeasurable]
    simp_rw [(hlaw _).map_eq]
  rw [← hmap, Measure.map_apply₀ hmeas (measurableSet_exists_prefix P).nullMeasurableSet]
  rfl

variable [IsProbabilityMeasure μ]

/-- **Time-uniform KL concentration of the empirical distribution** (Essakine, Vernade (2026),
the KL event of Lemma 5, after Ménard et al. (2021)): for an i.i.d. sequence `ξ` with law `ν` on a
finite type with `m` elements and every `δ > 0`,
`ℙ(∃ n ≥ 1, KL(q̂ₙ ‖ ν) ≥ (log (1/δ) + (m - 1) log (n + 1) + 1 + log n / 2) / n) ≤ δ`, where
`q̂ₙ` is the empirical distribution of `ξ 0, …, ξ (n - 1)`. -/
lemma measure_exists_le_klDiv_empiricalFreq_le (hξ : iIndepFun ξ μ)
    (hlaw : ∀ k, HasLaw (ξ k) ν μ) {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | ∃ n : ℕ, 0 < n ∧ ENNReal.ofReal ((log (1 / δ) + ((Fintype.card α - 1 : ℕ) : ℝ)
        * log (n + 1) + 1 + log n / 2) / n)
        ≤ klDiv (weightedMeasure (empiricalFreq fun k : Fin n ↦ ξ k ω)) ν}
      ≤ ENNReal.ofReal δ := by
  have := (hlaw 0).isProbabilityMeasure_iff.1 inferInstance
  rw [measure_exists_prefix_eq_infinitePi hξ hlaw (fun n y ↦ 0 < n ∧ ENNReal.ofReal
    ((log (1 / δ) + ((Fintype.card α - 1 : ℕ) : ℝ) * log (n + 1) + 1 + log n / 2) / n)
    ≤ klDiv (weightedMeasure (empiricalFreq y)) ν)]
  exact measure_exists_le_klDiv_empiricalFreq_le_infinitePi hδ

/-- **Time-uniform KL concentration of the empirical distribution**, simplified threshold: for an
i.i.d. sequence `ξ` with law `ν` on a finite type with `m` elements and every `δ > 0`,
`ℙ(∃ n ≥ 1, KL(q̂ₙ ‖ ν) ≥ (log (1/δ) + m log (e (n + 1))) / n) ≤ δ`. -/
lemma measure_exists_le_klDiv_empiricalFreq_le' (hξ : iIndepFun ξ μ)
    (hlaw : ∀ k, HasLaw (ξ k) ν μ) {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | ∃ n : ℕ, 0 < n ∧ ENNReal.ofReal
        ((log (1 / δ) + Fintype.card α * log (exp 1 * (n + 1))) / n)
        ≤ klDiv (weightedMeasure (empiricalFreq fun k : Fin n ↦ ξ k ω)) ν}
      ≤ ENNReal.ofReal δ := by
  have := (hlaw 0).isProbabilityMeasure_iff.1 inferInstance
  rw [measure_exists_prefix_eq_infinitePi hξ hlaw (fun n y ↦ 0 < n ∧ ENNReal.ofReal
    ((log (1 / δ) + Fintype.card α * log (exp 1 * (n + 1))) / n)
    ≤ klDiv (weightedMeasure (empiricalFreq y)) ν)]
  exact measure_exists_le_klDiv_empiricalFreq_le_infinitePi' hδ

end InfinitePi

end InformationTheory
