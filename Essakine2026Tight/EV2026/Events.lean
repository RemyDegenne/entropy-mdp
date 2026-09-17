/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.EV2026.RateBounds
public import Essakine2026Tight.EV2026.VisitCounts
public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Values
public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.VisitConcentration
public import Essakine2026Tight.Mathlib.InformationTheory.KLTimeUniform
public import Essakine2026Tight.Mathlib.Probability.Moments.SelfNormalizedBernsteinIID
public import Mathlib.Probability.HasLawExists

/-!
# Probabilities of the concentration events (Lemma 5)

For a run `(X, Y)` of an arbitrary algorithm in the episode environment of `M` from `s₁` and
`δ ∈ (0, 1]`, each of the three concentration events of the analysis of Entropic-BPI fails with
probability at most `δ / 3`, and the good event has probability at least `1 - δ` (Lemma 5 of
Essakine, Vernade (2026)):

* `pseudoCount_succ`, `sum_pseudoCount`, `integral_visitCountAt_eq_integral_pseudoCount`: the
  increments of the pseudo-counts are the occupancy measures of the policies played, and the
  pseudo-counts have the same expectation as the counts (the conditional probability of a visit
  is `Learning.MDP.Episodic.condExp_visit_filtrationAction_ae_eq`);
* `measure_compl_eventCnt_le`: the counts event, from the Bernoulli maximal inequality for the
  visits (`Learning.MDP.Episodic.measure_exists_pullCount_lt_le`);
* `measure_compl_eventBern_le`: the Bernstein event, from the time-uniform Bernstein inequality for
  an i.i.d. sequence indexed by the number of visits
  (`ProbabilityTheory.measure_exists_sqrt_add_lt_abs_sum_sub_integral_le`);
* `measure_compl_eventKL_le`: the KL event, from the time-uniform KL concentration of the
  empirical distribution of an i.i.d. sequence
  (`InformationTheory.measure_exists_le_klDiv_empiricalFreq_le'`);
* `measure_compl_goodEvent_le`, `one_sub_le_measureReal_goodEvent`: the good event.

The Bernstein and KL events are transferred from an i.i.d. sequence of law `p_h(· | s, a)` to the
next states observed at the successive visits of `(s, a)` at the step `h` by the time-uniform
domination `Learning.MDP.Episodic.measure_exists_visitNextState_mem_le`, the empirical transitions
after `t` episodes being the empirical distribution of the first `n_h^t(s, a)` observed next states
(`empTransAt_eq_empiricalFreq`). Each triple `(h, s, a)` gets the confidence `δ / (3 S A H)`
(`measure_iUnion_le_ofReal_div_three`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP.Episodic Learning.MDP
  InformationTheory
open scoped ENNReal

namespace Essakine2026Tight

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]
  {H : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {alg : Algorithm Unit (Policy S A H) (Traj S H)} {X : ℕ → Ω → Policy S A H}
  {Y : ℕ → Ω → Traj S H} {M : EpisodicMDP S A} {s₁ : S} {δ : ℝ}

/-! ### Pseudo-counts -/

omit [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [MeasurableSingletonClass S]
  [MeasurableSingletonClass A] in
/-- **Increments of the pseudo-counts**: `n̄_h^{t+1}(s, a) = n̄_h^t(s, a) + p^{π_t}_h(s, a)`, where
`π_t = X t` is the policy of the episode `t`. -/
lemma pseudoCount_succ (X : ℕ → Ω → Policy S A H) (M : EpisodicMDP S A) (s₁ : S) (h : Fin H)
    (s : S) (a : A) (t : ℕ) (ω : Ω) :
    pseudoCount X M s₁ h s a (t + 1) ω
      = pseudoCount X M s₁ h s a t ω + occupancy M (X t ω).extend s₁ h s a := by
  simp [pseudoCount, sum_range_succ]

omit [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [MeasurableSingletonClass S]
  [MeasurableSingletonClass A] in
/-- The pseudo-counts vanish before the first episode. -/
@[simp]
lemma pseudoCount_zero (X : ℕ → Ω → Policy S A H) (M : EpisodicMDP S A) (s₁ : S) (h : Fin H)
    (s : S) (a : A) (ω : Ω) : pseudoCount X M s₁ h s a 0 ω = 0 := by
  simp [pseudoCount]

omit [DecidableEq S] [DecidableEq A] in
/-- The pseudo-counts of all pairs sum to the number of episodes: `∑_{s, a} n̄_h^t(s, a) = t`. -/
lemma sum_pseudoCount (X : ℕ → Ω → Policy S A H) (M : EpisodicMDP S A) (s₁ : S) (h : Fin H)
    (t : ℕ) (ω : Ω) : ∑ s, ∑ a, pseudoCount X M s₁ h s a t ω = t := by
  simp only [pseudoCount]
  simp_rw [sum_comm (s := (univ : Finset A)) (t := range t)]
  rw [sum_comm]
  simp [sum_occupancy M (X _ ω).measurable_extend]

omit [Fintype S] [Fintype A] [DecidableEq S] in
/-- **The paper's pseudo-counts are the expectations of the random pseudo-counts**:
`E[n_h^t(s, a)] = E[n̄_h^t(s, a)]` in every run of an algorithm in the episode environment. -/
lemma integral_visitCountAt_eq_integral_pseudoCount [Finite S] [Finite A] [IsProbabilityMeasure P]
    [DecidableEq S] (hseq : IsAlgEnvSeq (fun _ _ ↦ ()) X Y alg (statesEnv M H s₁) P) (h : Fin H)
    (s : S) (a : A) (t : ℕ) :
    ∫ ω, (visitCountAt X Y h s a t ω : ℝ) ∂P = ∫ ω, pseudoCount X M s₁ h s a t ω ∂P := by
  have hvis (i : ℕ) : Integrable
      (fun ω ↦ if stepPair X Y h i ω = (s, a) then (1 : ℝ) else 0) P := by
    refine Integrable.of_bound ((measurable_of_countable (fun q : Policy S A H × Traj S H ↦
      if (q.2 h.castSucc, q.1 h (q.2 h.castSucc)) = (s, a) then (1 : ℝ) else 0)).comp
      ((hseq.measurable_action i).prodMk (hseq.measurable_feedback i))).aestronglyMeasurable 1
      (.of_forall fun ω ↦ ?_)
    split_ifs <;> simp
  have hocc (i : ℕ) : Integrable (fun ω ↦ occupancy M (X i ω).extend s₁ h s a) P := by
    refine Integrable.of_bound ((measurable_of_countable (fun π : Policy S A H ↦
      occupancy M π.extend s₁ h s a)).comp (hseq.measurable_action i)).aestronglyMeasurable 1
      (.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (occupancy_nonneg M _ s₁ h s a)]
    exact occupancy_le_one M (X i ω).measurable_extend s₁ h s a
  simp_rw [visitCountAt_eq_pullCount, pullCount_eq_sum, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  simp only [pseudoCount]
  rw [integral_finsetSum _ fun i _ ↦ hvis i, integral_finsetSum _ fun i _ ↦ hocc i]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← integral_condExp (hseq.filtrationAction.le i)]
  exact integral_congr_ae (condExp_visit_filtrationAction_ae_eq M s₁ hseq i h s a)

/-! ### Union bound over the triples `(h, s, a)` -/

omit [DecidableEq S] [DecidableEq A] [Nonempty A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- **Union bound over the triples `(h, s, a)`**: if each event `E h s a` has probability at most
`δ / (3 S A H)`, their union has probability at most `δ / 3`. -/
lemma measure_iUnion_le_ofReal_div_three {E : Fin H → S → A → Set Ω} (hδ : 0 ≤ δ)
    (hE : ∀ h s a, P (E h s a)
      ≤ ENNReal.ofReal (δ / ((3 * Fintype.card S * Fintype.card A * H : ℕ) : ℝ))) :
    P (⋃ h, ⋃ s, ⋃ a, E h s a) ≤ ENNReal.ofReal (δ / 3) := by
  set c : ℝ := δ / ((3 * Fintype.card S * Fintype.card A * H : ℕ) : ℝ) with hc
  calc P (⋃ h, ⋃ s, ⋃ a, E h s a) ≤ ∑ h, ∑ s, ∑ a, P (E h s a) := by
        refine (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun h _ ↦ ?_)
        refine (measure_iUnion_fintype_le _ _).trans (sum_le_sum fun s _ ↦ ?_)
        exact measure_iUnion_fintype_le _ _
    _ ≤ ∑ _h : Fin H, ∑ _s : S, ∑ _a : A, ENNReal.ofReal c :=
        sum_le_sum fun h _ ↦ sum_le_sum fun s _ ↦ sum_le_sum fun a _ ↦ hE h s a
    _ = ENNReal.ofReal ((H * (Fintype.card S * Fintype.card A) : ℕ) * c) := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
        push_cast
        ring
    _ ≤ ENNReal.ofReal (δ / 3) := by
        refine ENNReal.ofReal_le_ofReal ?_
        set N : ℝ := ((H * (Fintype.card S * Fintype.card A) : ℕ) : ℝ) with hN
        have e : N * c = δ / 3 * (N / N) := by
          rw [hc, hN]
          push_cast
          ring
        rw [e]
        exact mul_le_of_le_one_right (by positivity) (div_self_le_one N)

omit [DecidableEq S] [DecidableEq A] [Nonempty A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The confidence `δ / (3 S A H)` of a triple `(h, s, a)` is positive. -/
lemma div_three_mul_pos (hδ : 0 < δ) (h : Fin H) (s : S) (a : A) :
    0 < δ / ((3 * Fintype.card S * Fintype.card A * H : ℕ) : ℝ) := by
  have hS : 0 < Fintype.card S := Fintype.card_pos_iff.2 ⟨s⟩
  have hA : 0 < Fintype.card A := Fintype.card_pos_iff.2 ⟨a⟩
  have hH : 0 < H := Fin.pos h
  have : 0 < 3 * Fintype.card S * Fintype.card A * H := by positivity
  exact div_pos hδ (by exact_mod_cast this)

omit [DecidableEq S] [DecidableEq A] [Nonempty A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- `log (1 / (δ / (3 S A H))) = α^cnt(δ)`. -/
lemma log_one_div_div_eq_alphaCnt :
    Real.log (1 / (δ / ((3 * Fintype.card S * Fintype.card A * H : ℕ) : ℝ)))
      = alphaCnt (Fintype.card S) (Fintype.card A) H δ := by
  rw [one_div_div, alphaCnt]

/-! ### The counts event -/

/-- The counts event fails for the triple `(h, s, a)` with probability at most `δ / (3 S A H)`. -/
lemma measure_exists_visitCountAt_lt_le [IsProbabilityMeasure P]
    (hseq : IsAlgEnvSeq (fun _ _ ↦ ()) X Y alg (statesEnv M H s₁) P) (hδ : 0 < δ) (h : Fin H)
    (s : S) (a : A) :
    P {ω | ∃ t, (visitCountAt X Y h s a t ω : ℝ) < pseudoCount X M s₁ h s a t ω / 2
        - alphaCnt (Fintype.card S) (Fintype.card A) H δ}
      ≤ ENNReal.ofReal (δ / ((3 * Fintype.card S * Fintype.card A * H : ℕ) : ℝ)) := by
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (measure_exists_pullCount_lt_le M s₁ hseq h s a (div_three_mul_pos hδ h s a))
  obtain ⟨t, ht⟩ := hω
  refine ⟨t, ?_⟩
  rw [log_one_div_div_eq_alphaCnt, ← visitCountAt_eq_pullCount]
  simp only [pseudoCount] at ht
  linarith

/-- **Probability of the counts event**: in every run of an algorithm in the episode environment,
for `δ > 0`, `P(𝓔^cnt fails) ≤ δ / 3`. -/
lemma measure_compl_eventCnt_le [IsProbabilityMeasure P]
    (hseq : IsAlgEnvSeq (fun _ _ ↦ ()) X Y alg (statesEnv M H s₁) P) (hδ : 0 < δ) :
    P (eventCnt X Y M s₁ δ)ᶜ ≤ ENNReal.ofReal (δ / 3) := by
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (measure_iUnion_le_ofReal_div_three hδ.le (measure_exists_visitCountAt_lt_le hseq hδ))
  simp only [eventCnt, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
  obtain ⟨t, h, s, a, hlt⟩ := hω
  exact Set.mem_iUnion.2 ⟨h, Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨a, t, hlt⟩⟩⟩

/-! ### Empirical transitions as empirical distributions -/

omit [Fintype A] [Nonempty A] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- **The empirical transitions are the empirical distribution of the observed next states**: for
`n = n_h^t(s, a) ≥ 1`, `p̂_h^t(· | s, a)` is the empirical distribution of the next states
`W_1, …, W_n` observed at the `n` visits of `(s, a)` at the step `h`. -/
lemma empTransAt_eq_empiricalFreq (X : ℕ → Ω → Policy S A H) (Y : ℕ → Ω → Traj S H) (h : Fin H)
    (s : S) (a : A) (t : ℕ) (ω : Ω) (hn : visitCountAt X Y h s a t ω ≠ 0) :
    empTransAt X Y h s a t ω = empiricalFreq
      (fun k : Fin (visitCountAt X Y h s a t ω) ↦ visitNextState X Y h s a (k + 1) ω) :=
  funext fun s' ↦ empTransAt_eq X Y h s a t ω hn s'

omit [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The expectation of `g` under the empirical distribution of a sequence `x` of length `n` is the
empirical mean `(∑ k, g (x k)) / n`. -/
lemma vecExp_empiricalFreq {n : ℕ} (x : Fin n → S) (g : S → ℝ) :
    vecExp (empiricalFreq x) g = (∑ k, g (x k)) / n := by
  simp only [vecExp, empiricalFreq, typeCount, div_mul_eq_mul_div, ← sum_div]
  congr 1
  rw [← sum_fiberwise univ x (fun k ↦ g (x k))]
  refine sum_congr rfl fun s' _ ↦ ?_
  rw [sum_congr rfl (fun k hk ↦ by rw [(mem_filter.1 hk).2]), sum_const, nsmul_eq_mul]

omit [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A] [MeasurableSpace S]
  [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- If the oscillation of `g` is at most `c`, then `|g x - p g| ≤ c` for every probability vector
`p`. -/
lemma abs_sub_vecExp_le {p g : S → ℝ} {c : ℝ} (hp0 : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (hgc : ∀ x y, g x - g y ≤ c) (x : S) : |g x - vecExp p g| ≤ c := by
  have h1 : g x - vecExp p g = ∑ y, p y * (g x - g y) := by
    simp only [vecExp, mul_sub, sum_sub_distrib, ← sum_mul, hp1, one_mul]
  have h2 : vecExp p g - g x = ∑ y, p y * (g y - g x) := by
    simp only [vecExp, mul_sub, sum_sub_distrib, ← sum_mul, hp1, one_mul]
  have hle (u : S → ℝ) (hu : ∀ y, u y ≤ c) : ∑ y, p y * u y ≤ c :=
    (sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_left (hu y) (hp0 y)).trans
      (by rw [← sum_mul, hp1, one_mul])
  exact abs_sub_le_iff.2 ⟨h1 ▸ hle _ fun y ↦ hgc x y, h2 ▸ hle _ fun y ↦ hgc y x⟩

/-! ### The Bernstein event -/

omit [DecidableEq S] [DecidableEq A] [Nonempty A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The confidence `δ / (3 S A H)` of a triple `(h, s, a)` is less than `1` for `δ ≤ 1`. -/
lemma div_three_mul_lt_one (hδ1 : δ ≤ 1) (h : Fin H) (s : S) (a : A) :
    δ / ((3 * Fintype.card S * Fintype.card A * H : ℕ) : ℝ) < 1 := by
  have hS : 1 ≤ Fintype.card S := Fintype.card_pos_iff.2 ⟨s⟩
  have hA : 1 ≤ Fintype.card A := Fintype.card_pos_iff.2 ⟨a⟩
  have hH : 1 ≤ H := Fin.pos h
  have h3 : 3 ≤ 3 * Fintype.card S * Fintype.card A * H := by
    calc 3 = 3 * 1 * 1 * 1 := by norm_num
      _ ≤ 3 * Fintype.card S * Fintype.card A * H := by gcongr
  have h3' : (3 : ℝ) ≤ ((3 * Fintype.card S * Fintype.card A * H : ℕ) : ℝ) := by exact_mod_cast h3
  rw [div_lt_one (by linarith)]
  linarith

omit [DecidableEq S] [DecidableEq A] [Nonempty A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
/-- The logarithmic term of the Bernstein inequality with the confidence `δ / (3 S A H)` is at most
`α*(n, δ)`: `log (4 e (2 n + 1) / (δ / (3 S A H))) ≤ α*(n, δ)`. -/
lemma log_div_div_le_alphaStar (hδ : 0 < δ) (h : Fin H) (s : S) (a : A) (n : ℕ) :
    Real.log (4 * Real.exp 1 * (2 * n + 1)
        / (δ / ((3 * Fintype.card S * Fintype.card A * H : ℕ) : ℝ)))
      ≤ alphaStar (Fintype.card S) (Fintype.card A) H δ n := by
  have hδ' := div_three_mul_pos hδ h s a
  set C : ℝ := ((3 * Fintype.card S * Fintype.card A * H : ℕ) : ℝ) with hC
  have hCpos : 0 < C := by
    have : 0 < δ / C := hδ'
    exact (div_pos_iff_of_pos_left hδ).1 this
  have he := Real.exp_pos 1
  rw [alphaStar, div_div_eq_mul_div, mul_div_assoc,
    Real.log_mul (by positivity) (by positivity), add_comm]
  refine (add_le_add_iff_left _).2 (Real.log_le_log (by positivity) ?_)
  push_cast
  nlinarith

/-- The Bernstein event fails for the triple `(h, s, a)` with probability at most `δ / (3 S A H)`:
this is the time-uniform Bernstein inequality for an i.i.d. sequence of law `p_h(· | s, a)`,
indexed by the number of visits and transferred to the run by the time-uniform domination of the
observed next states. -/
lemma measure_exists_lt_abs_vecExp_empTransAt_sub_le [IsProbabilityMeasure P]
    (hseq : IsAlgEnvSeq (fun _ _ ↦ ()) X Y alg (statesEnv M H s₁) P) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h : Fin H) (s : S) (a : A) {g : S → ℝ} {c : ℝ} (hgc : ∀ x y, g x - g y ≤ c) :
    P {ω | ∃ t, 0 < visitCountAt X Y h s a t ω ∧
        √(2 * vecVar (M.transVec h s a) g * starRateAt X Y δ h s a t ω)
          + 3 * c * starRateAt X Y δ h s a t ω
        < |vecExp (empTransAt X Y h s a t ω) g - vecExp (M.transVec h s a) g|}
      ≤ ENNReal.ofReal (δ / ((3 * Fintype.card S * Fintype.card A * H : ℕ) : ℝ)) := by
  set δ' := δ / ((3 * Fintype.card S * Fintype.card A * H : ℕ) : ℝ) with hδ'
  have hδ'0 : 0 < δ' := div_three_mul_pos hδ h s a
  have hδ'1 : δ' < 1 := div_three_mul_lt_one hδ1 h s a
  have hc0 : 0 ≤ c := by simpa using hgc s s
  set p := M.trans h (s, a) with hp
  set m := vecExp (M.transVec h s a) g with hm
  set σ2 := vecVar (M.transVec h s a) g with hσ2
  have hσ2_0 : 0 ≤ σ2 := vecVar_nonneg (M.transVec_nonneg h s a) (M.sum_transVec h s a)
  have hint_g : ∫ y, g y ∂p = m := integral_eq_vecExp_transVec M h s a g
  have hint_var : ∫ x, (g x - ∫ y, g y ∂p) ^ 2 ∂p = σ2 := by
    rw [hint_g, integral_eq_vecExp_transVec M h s a, hσ2,
      vecVar_eq_sum_sq (M.sum_transVec h s a)]
    rfl
  set α := alphaStar (Fintype.card S) (Fintype.card A) H δ with hα
  set B : ∀ n, Set (Fin n → S) := fun n ↦
    {x | 0 < n ∧ √(2 * σ2 * (α n / n)) + 3 * c * (α n / n) < |vecExp (empiricalFreq x) g - m|}
    with hB
  obtain ⟨Ω', mΩ', μ', ξ, hξ, hlaw, hind, hμ'⟩ := exists_iid ℕ p
  calc P {ω | ∃ t, 0 < visitCountAt X Y h s a t ω ∧
        √(2 * σ2 * starRateAt X Y δ h s a t ω) + 3 * c * starRateAt X Y δ h s a t ω
        < |vecExp (empTransAt X Y h s a t ω) g - m|}
      ≤ P {ω | ∃ t, (fun k : Fin (pullCount (stepPair X Y h) (s, a) t ω) ↦
          visitNextState X Y h s a (k + 1) ω) ∈ B _} := by
        refine measure_mono fun ω ⟨t, hpos, hlt⟩ ↦ ⟨t, ?_⟩
        have hmem : (fun k : Fin (visitCountAt X Y h s a t ω) ↦
            visitNextState X Y h s a (k + 1) ω) ∈ B (visitCountAt X Y h s a t ω) := by
          refine ⟨hpos, ?_⟩
          rw [← empTransAt_eq_empiricalFreq X Y h s a t ω hpos.ne']
          exact hlt
        rwa [visitCountAt_eq_pullCount] at hmem
    _ ≤ μ' {ω | ∃ n, (fun k : Fin n ↦ ξ k ω) ∈ B n} :=
        measure_exists_visitNextState_mem_le M s₁ hseq h s a hξ hind hlaw B
    _ ≤ μ' {ω | ∃ n : ℕ, √(2 * (n * ∫ x, (g x - ∫ y, g y ∂p) ^ 2 ∂p)
          * Real.log (4 * Real.exp 1 * (2 * n + 1) / δ'))
          + 3 * c * Real.log (4 * Real.exp 1 * (2 * n + 1) / δ')
        < |∑ i ∈ range n, (g (ξ i ω) - ∫ y, g y ∂p)|} := by
        refine measure_mono fun ω ⟨n, hn, hlt⟩ ↦ ⟨n, ?_⟩
        rw [hint_var, hint_g]
        set L := Real.log (4 * Real.exp 1 * (2 * n + 1) / δ') with hL
        set T := ∑ i ∈ range n, (g (ξ i ω) - m) with hT
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have hLα : L ≤ α n := log_div_div_le_alphaStar hδ h s a n
        have hmean : vecExp (empiricalFreq fun k : Fin n ↦ ξ k ω) g - m = T / n := by
          rw [vecExp_empiricalFreq, Fin.sum_univ_eq_sum_range (fun i ↦ g (ξ i ω)) n, hT,
            sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
          field_simp
        rw [hmean, abs_div, abs_of_pos hnR] at hlt
        by_contra hle
        push Not at hle
        have hsq : √(2 * (n * σ2) * L) = n * √(2 * σ2 * (L / n)) := by
          rw [show 2 * (n * σ2) * L = (n : ℝ) ^ 2 * (2 * σ2 * (L / n)) by field_simp,
            Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hnR.le]
        have h1 : |T| / n ≤ √(2 * σ2 * (L / n)) + 3 * c * (L / n) := by
          rw [div_le_iff₀ hnR]
          calc |T| ≤ √(2 * (n * σ2) * L) + 3 * c * L := hle
            _ = (√(2 * σ2 * (L / n)) + 3 * c * (L / n)) * n := by
                rw [hsq]
                field_simp
        have h2 : √(2 * σ2 * (L / n)) + 3 * c * (L / n) ≤ √(2 * σ2 * (α n / n))
            + 3 * c * (α n / n) := by
          have hdiv : L / n ≤ α n / n := div_le_div_of_nonneg_right hLα hnR.le
          gcongr
        linarith
    _ ≤ ENNReal.ofReal δ' :=
        measure_exists_sqrt_add_lt_abs_sum_sub_integral_le hξ hind hlaw (measurable_of_countable g)
          (fun x ↦ hint_g ▸ abs_sub_vecExp_le (M.transVec_nonneg h s a) (M.sum_transVec h s a)
            hgc x) hδ'0 hδ'1

/-- **Probability of the Bernstein event** (for `f` with ranges `b`): in every run of an algorithm
in the episode environment, for `δ ∈ (0, 1]` and `b h ≥ max f_{h+1} - min f_{h+1}`,
`P(𝓔_f fails) ≤ δ / 3`. -/
lemma measure_compl_eventBern_le [IsProbabilityMeasure P]
    (hseq : IsAlgEnvSeq (fun _ _ ↦ ()) X Y alg (statesEnv M H s₁) P) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {f : ℕ → S → ℝ} {b : ℕ → ℝ} (hb : ∀ (h : Fin H) x y, f (h + 1) x - f (h + 1) y ≤ b h) :
    P (eventBern X Y M δ f b)ᶜ ≤ ENNReal.ofReal (δ / 3) := by
  refine le_trans (measure_mono fun ω hω ↦ ?_) (measure_iUnion_le_ofReal_div_three hδ.le
    fun h s a ↦ measure_exists_lt_abs_vecExp_empTransAt_sub_le hseq hδ hδ1 h s a (hb h))
  simp only [eventBern, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
  obtain ⟨t, h, s, a, hpos, hlt⟩ := hω
  exact Set.mem_iUnion.2 ⟨h, Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨a, t, hpos, hlt⟩⟩⟩

/-! ### The KL event -/

/-- The KL event fails for the triple `(h, s, a)` with probability at most `δ / (3 S A H)`: this is
the time-uniform KL concentration of the empirical distribution of an i.i.d. sequence of law
`p_h(· | s, a)`, indexed by the number of visits and transferred to the run by the time-uniform
domination of the observed next states. -/
lemma measure_exists_klThreshold_lt_klDiv_le [IsProbabilityMeasure P]
    (hseq : IsAlgEnvSeq (fun _ _ ↦ ()) X Y alg (statesEnv M H s₁) P) (hδ : 0 < δ) (h : Fin H)
    (s : S) (a : A) :
    P {ω | ∃ t, klThreshold (Fintype.card S) (Fintype.card A) H δ (visitCountAt X Y h s a t ω)
        < klDiv (weightedMeasure (empTransAt X Y h s a t ω)) (M.trans h (s, a))}
      ≤ ENNReal.ofReal (δ / ((3 * Fintype.card S * Fintype.card A * H : ℕ) : ℝ)) := by
  set δ' := δ / ((3 * Fintype.card S * Fintype.card A * H : ℕ) : ℝ) with hδ'
  have hδ'0 : 0 < δ' := div_three_mul_pos hδ h s a
  set B : ∀ n, Set (Fin n → S) := fun n ↦ {x | klThreshold (Fintype.card S) (Fintype.card A) H δ n
    < klDiv (weightedMeasure (empiricalFreq x)) (M.trans h (s, a))} with hB
  have hne (n : ℕ) {κ : ℝ≥0∞} (hlt : klThreshold (Fintype.card S) (Fintype.card A) H δ n < κ) :
      n ≠ 0 := by
    rintro rfl
    simp [klThreshold] at hlt
  obtain ⟨Ω', mΩ', μ', ξ, hξ, hlaw, hind, hμ'⟩ := exists_iid ℕ (M.trans h (s, a))
  calc P {ω | ∃ t, klThreshold (Fintype.card S) (Fintype.card A) H δ (visitCountAt X Y h s a t ω)
        < klDiv (weightedMeasure (empTransAt X Y h s a t ω)) (M.trans h (s, a))}
      ≤ P {ω | ∃ t, (fun k : Fin (pullCount (stepPair X Y h) (s, a) t ω) ↦
          visitNextState X Y h s a (k + 1) ω) ∈ B _} := by
        refine measure_mono fun ω ⟨t, hlt⟩ ↦ ⟨t, ?_⟩
        have hmem : (fun k : Fin (visitCountAt X Y h s a t ω) ↦
            visitNextState X Y h s a (k + 1) ω) ∈ B (visitCountAt X Y h s a t ω) := by
          simp only [hB, Set.mem_ofPred_eq]
          rw [← empTransAt_eq_empiricalFreq X Y h s a t ω (hne _ hlt)]
          exact hlt
        rwa [visitCountAt_eq_pullCount] at hmem
    _ ≤ μ' {ω | ∃ n, (fun k : Fin n ↦ ξ k ω) ∈ B n} :=
        measure_exists_visitNextState_mem_le M s₁ hseq h s a hξ hind hlaw B
    _ ≤ μ' {ω | ∃ n : ℕ, 0 < n ∧ ENNReal.ofReal
          ((Real.log (1 / δ') + Fintype.card S * Real.log (Real.exp 1 * (n + 1))) / n)
          ≤ klDiv (weightedMeasure (empiricalFreq fun k : Fin n ↦ ξ k ω)) (M.trans h (s, a))} := by
        refine measure_mono fun ω ⟨n, hlt⟩ ↦ ⟨n, Nat.pos_of_ne_zero (hne n hlt), le_trans ?_ hlt.le⟩
        have hn := hne n hlt
        have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        rw [klThreshold, ite_eq_right hn]
        refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hnR.le)
        rw [log_one_div_div_eq_alphaCnt, alphaKL, alphaCnt]
        refine (add_le_add_iff_left _).2 (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
        exact Real.log_le_log (by positivity) (by push_cast; nlinarith [Real.exp_pos 1])
    _ ≤ ENNReal.ofReal δ' := measure_exists_le_klDiv_empiricalFreq_le' hind hlaw hδ'0

/-- **Probability of the KL event**: in every run of an algorithm in the episode environment, for
`δ > 0`, `P(𝓔_KL fails) ≤ δ / 3`. -/
lemma measure_compl_eventKL_le [IsProbabilityMeasure P]
    (hseq : IsAlgEnvSeq (fun _ _ ↦ ()) X Y alg (statesEnv M H s₁) P) (hδ : 0 < δ) :
    P (eventKL X Y M δ)ᶜ ≤ ENNReal.ofReal (δ / 3) := by
  refine le_trans (measure_mono fun ω hω ↦ ?_) (measure_iUnion_le_ofReal_div_three hδ.le
    fun h s a ↦ measure_exists_klThreshold_lt_klDiv_le hseq hδ h s a)
  simp only [eventKL, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
  obtain ⟨t, h, s, a, hlt⟩ := hω
  exact Set.mem_iUnion.2 ⟨h, Set.mem_iUnion.2 ⟨s, Set.mem_iUnion.2 ⟨a, t, hlt⟩⟩⟩

/-! ### The good event -/

omit [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] in
/-- **Ranges of the optimal exponential values** (as needed by the Bernstein event of the good
event): for rewards in `[0, 1]` and every `β`, the oscillation of `Z*_{h+1}` is at most
`e^{β (H - 1 - h)}` if `β > 0` and `1 - e^{β (H - 1 - h)}` otherwise. -/
lemma optExpValue_succ_sub_le [Finite S] [Finite A] (hM : M.RewardsIn (Set.Icc 0 1)) (β : ℝ)
    (h : Fin H) (x y : S) :
    optExpValue M H β (h + 1) x - optExpValue M H β (h + 1) y
      ≤ if 0 < β then Real.exp (β * (H - 1 - h : ℕ)) else 1 - Real.exp (β * (H - 1 - h : ℕ)) := by
  rcases eq_or_ne β 0 with rfl | hβ
  · simp [optExpValue]
  have hk : ((H - (h + 1 : ℕ) : ℕ) : ℝ) = ((H - 1 - h : ℕ) : ℝ) := by
    congr 1
    omega
  have hx := optExpValue_mem_Icc M H β hM hβ (h + 1) x
  have hy := optExpValue_mem_Icc M H β hM hβ (h + 1) y
  rw [hk] at hx hy
  set e := Real.exp (β * (H - 1 - h : ℕ)) with he
  rcases hβ.lt_or_gt with hneg | hpos
  · have he1 : e ≤ 1 := Real.exp_le_one_iff.2
      (mul_nonpos_of_nonpos_of_nonneg hneg.le (Nat.cast_nonneg _))
    rw [ite_eq_right hneg.not_gt]
    rw [min_eq_right he1, max_eq_left he1] at hx hy
    linarith [hx.2, hy.1]
  · have he1 : 1 ≤ e := Real.one_le_exp (mul_nonneg hpos.le (Nat.cast_nonneg _))
    rw [ite_eq_left hpos]
    rw [min_eq_left he1, max_eq_right he1] at hx hy
    linarith [hx.2, hy.1]

/-- **Lemma 5, complement form**: in every run of an algorithm in the episode environment of an
MDP with a reward function with values in `[0, 1]`, for every `β` and `δ ∈ (0, 1]`, the good event
fails with probability at most `δ`. -/
lemma measure_compl_goodEvent_le [IsProbabilityMeasure P]
    (hseq : IsAlgEnvSeq (fun _ _ ↦ ()) X Y alg (statesEnv M H s₁) P) {r : ℕ → S → A → ℝ}
    (hM : M.HasRewardFn r) (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (β : ℝ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    P (goodEvent X Y M s₁ β δ)ᶜ ≤ ENNReal.ofReal δ := by
  have hRew : M.RewardsIn (Set.Icc 0 1) := fun h s a ↦ by
    rw [hM h s a]
    exact (ae_dirac_iff measurableSet_Icc).2 (hr h s a)
  have hKL := measure_compl_eventKL_le hseq hδ
  have hBern := measure_compl_eventBern_le hseq hδ hδ1 (f := optExpValue M H β)
    (b := fun h ↦ if 0 < β then Real.exp (β * (H - 1 - h : ℕ))
      else 1 - Real.exp (β * (H - 1 - h : ℕ))) (optExpValue_succ_sub_le hRew β)
  have hCnt := measure_compl_eventCnt_le hseq hδ
  rw [goodEvent, Set.compl_inter, Set.compl_inter]
  calc P ((eventKL X Y M δ)ᶜ ∪ (eventBern X Y M δ (optExpValue M H β) _)ᶜ ∪ (eventCnt X Y M s₁ δ)ᶜ)
      ≤ P (eventKL X Y M δ)ᶜ + P (eventBern X Y M δ (optExpValue M H β) _)ᶜ
        + P (eventCnt X Y M s₁ δ)ᶜ :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) := by
        gcongr
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **Lemma 5** (Essakine, Vernade (2026)): in every run of an algorithm in the episode environment
of an MDP with a reward function with values in `[0, 1]`, for every `β` and `δ ∈ (0, 1]`, the good
event has probability at least `1 - δ`. -/
lemma one_sub_le_measureReal_goodEvent [IsProbabilityMeasure P]
    (hseq : IsAlgEnvSeq (fun _ _ ↦ ()) X Y alg (statesEnv M H s₁) P) {r : ℕ → S → A → ℝ}
    (hM : M.HasRewardFn r) (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (β : ℝ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    1 - δ ≤ P.real (goodEvent X Y M s₁ β δ) := by
  have hc : P.real (goodEvent X Y M s₁ β δ)ᶜ ≤ δ := by
    have := measure_compl_goodEvent_le hseq hM hr β hδ hδ1
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hδ.le this
  have hu : P.real Set.univ ≤ P.real (goodEvent X Y M s₁ β δ) + P.real (goodEvent X Y M s₁ β δ)ᶜ :=
    (Set.union_compl_self (goodEvent X Y M s₁ β δ)) ▸ measureReal_union_le _ _
  rw [probReal_univ] at hu
  linarith

end Essakine2026Tight
