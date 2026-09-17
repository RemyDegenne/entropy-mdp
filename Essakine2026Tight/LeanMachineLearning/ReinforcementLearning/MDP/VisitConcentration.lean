/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Occupancy
public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Visits
public import Essakine2026Tight.Mathlib.Probability.HasCondDistribCondExp
public import Essakine2026Tight.Mathlib.Probability.Independence.NaturalPast
public import Essakine2026Tight.Mathlib.Probability.Martingale.Ville
public import Essakine2026Tight.Mathlib.Probability.Process.FirstEntrance

/-!
# Concentration at the visits of a state-action pair

Let `(X, Y)` be an algorithm-environment sequence for an arbitrary algorithm in the episode
environment `statesEnv M H s₁` of a finite-horizon MDP `M` with the horizon `H`, fix a step `h`
and a pair `(s, a)`, and let `ℱ t = σ(history of the first t episodes, policy of the episode t)`
be LML's `IsAlgEnvSeq.filtrationAction`.

* `measureReal_statesLaw_stepPair_eq`, `condExp_visit_filtrationAction_ae_eq`: given `ℱ t`, the
  pair `(s, a)` is visited at the step `h` of the episode `t` with probability
  `p^{π_t}_h(s, a)`, the occupancy measure of the policy `π_t = X t` played in that episode;
* `measure_exists_pullCount_lt_le`: the Bernoulli maximal inequality for the visits: with
  probability at least `1 - δ`, for all `t`, the number of visits in the first `t` episodes is at
  least `½ ∑_{i < t} p^{π_i}_h(s, a) - log (1/δ)`;
* `measure_exists_le_pullCount_visitNextState_mem_le`, `measure_exists_visitNextState_mem_le`: the
  next states `W_1, W_2, …` observed at the successive visits are dominated by an i.i.d. sequence
  `ξ` of law `p_h(· | s, a)`, uniformly in the number of visits:
  `P(∃ n, T_n < ∞, (W_1, …, W_n) ∈ B n) ≤ P'(∃ n, (ξ 0, …, ξ (n - 1)) ∈ B n)` for every sequence
  of sets `B n`, and in particular `P(∃ t, (W_1, …, W_{n_t}) ∈ B n_t)` is bounded by the same
  quantity, where `n_t` is the number of visits in the first `t` episodes. This is
  the first-entrance decomposition
  (`MeasureTheory.measure_exists_mem_le_of_forall_measure_inter_le`)
  applied to the domination of the prefixes of fixed length
  (`measure_visitNextState_mem_le_pi`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP
open scoped ENNReal

namespace Learning.MDP.Episodic

variable {S A : Type*} [Finite S] [Finite A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] {H : ℕ} (M : EpisodicMDP S A)
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {alg : Algorithm Unit (Policy S A H) (Traj S H)} {O : ℕ → Ω → Unit} {X : ℕ → Ω → Policy S A H}
  {Y : ℕ → Ω → Traj S H}

omit [IsProbabilityMeasure P] in
/-- The probability that the episode played with `π` from `s₁` visits `(s, a)` at the step `h` is
the occupancy measure `p^π_h(s, a)`. -/
lemma measureReal_statesLaw_stepPair_eq (s₁ : S) (π : Policy S A H) (h : Fin H) (s : S) (a : A) :
    (statesLaw M H s₁ π.extend).real {τ | (τ h.castSucc, π h (τ h.castSucc)) = (s, a)}
      = occupancy M π.extend s₁ h s a := by
  rw [statesLaw, map_measureReal_apply (measurable_episodeStates H)
    (Set.to_countable _).measurableSet, occupancy, occupancyMeasure,
    map_measureReal_apply (measurable_stateAction h) (measurableSet_singleton _)]
  refine measureReal_congr ?_
  filter_upwards [ae_action_eq_stepLaw M π.measurable_extend s₁ 0 h] with x hx
  simp only [Nat.zero_add] at hx
  simp [episodeStates, stateAction, hx]

omit [IsProbabilityMeasure P] in
/-- **Conditional probability of a visit**: given the history of the first `t` episodes and the
policy of the episode `t`, the pair `(s, a)` is visited at the step `h` of the episode `t` with
probability `p^{π_t}_h(s, a)`, where `π_t = X t`. -/
lemma condExp_visit_filtrationAction_ae_eq [IsFiniteMeasure P] [DecidableEq S] [DecidableEq A]
    (s₁ : S) (hseq : IsAlgEnvSeq O X Y alg (statesEnv M H s₁) P) (t : ℕ) (h : Fin H) (s : S)
    (a : A) :
    P[fun ω ↦ if stepPair X Y h t ω = (s, a) then (1 : ℝ) else 0 | hseq.filtrationAction t]
      =ᵐ[P] fun ω ↦ occupancy M (X t ω).extend s₁ h s a := by
  have hc := hasCondDistrib_feedback_history_action_statesEnv M H s₁ hseq t
  have hZ : Measurable fun ω ↦ ((history O X Y t ω, O t ω), X t ω) :=
    ((measurable_history hseq.measurable_obs hseq.measurable_action hseq.measurable_feedback
      t).prodMk (hseq.measurable_obs t)).prodMk (hseq.measurable_action t)
  set f : ((Hist Unit (Policy S A H) (Traj S H) t × Unit) × Policy S A H) × Traj S H → ℝ :=
    fun z ↦ if (z.2 h.castSucc, z.1.2 h (z.2 h.castSucc)) = (s, a) then 1 else 0 with hf
  have hfC : ∀ z, |f z| ≤ 1 := fun z ↦ by simp only [hf]; split_ifs <;> simp
  refine (hc.condExp_comap_ae_eq_integral hZ (f := f)
    (measurable_of_countable f).stronglyMeasurable hfC).trans (.of_forall fun ω ↦ ?_)
  simp only [hf, Kernel.prodMkLeft_apply, statesKernel_apply]
  rw [← measureReal_statesLaw_stepPair_eq M s₁ (X t ω) h s a,
    ← integral_indicator_one (Set.to_countable _).measurableSet]
  refine integral_congr_ae (.of_forall fun τ ↦ ?_)
  simp [Set.indicator_apply]

/-- **The Bernoulli maximal inequality for the visits**: with probability at least `1 - δ`, for
all `t`, the number of visits of `(s, a)` at the step `h` in the first `t` episodes is at least
`½ ∑_{i < t} p^{π_i}_h(s, a) - log (1/δ)`, where `π_i = X i` is the policy of the episode `i`. -/
lemma measure_exists_pullCount_lt_le [DecidableEq S] [DecidableEq A] (s₁ : S)
    (hseq : IsAlgEnvSeq O X Y alg (statesEnv M H s₁) P) (h : Fin H) (s : S) (a : A) {δ : ℝ}
    (hδ : 0 < δ) :
    P {ω | ∃ t, (pullCount (stepPair X Y h) (s, a) t ω : ℝ)
        < 1 / 2 * ∑ i ∈ range t, occupancy M (X i ω).extend s₁ h s a - Real.log (1 / δ)}
      ≤ ENNReal.ofReal δ := by
  have hXm (i : ℕ) : Measurable[hseq.filtrationAction (i + 1)] (X i) :=
    (hseq.adapted_action_filtrationAction i).mono
      (hseq.filtrationAction.mono (Nat.le_succ i)) le_rfl
  have hYm (i : ℕ) : Measurable[hseq.filtrationAction (i + 1)] (Y i) :=
    hseq.measurable_feedback_filtrationAction_of_lt (Nat.lt_succ_self i)
  have h' := measure_exists_sum_lt_half_mul_sum_sub_le (μ := P) (ℱ := hseq.filtrationAction)
    (X := fun i ω ↦ if stepPair X Y h i ω = (s, a) then (1 : ℝ) else 0)
    (P := fun i ω ↦ occupancy M (X i ω).extend s₁ h s a) (fun i ω ↦ by split_ifs <;> simp)
    (fun i ↦ ((measurable_of_countable (fun q : Policy S A H × Traj S H ↦
      if (q.2 h.castSucc, q.1 h (q.2 h.castSucc)) = (s, a) then (1 : ℝ) else 0)).comp
      ((hXm i).prodMk (hYm i))).stronglyMeasurable)
    (fun i ω ↦ ⟨occupancy_nonneg M _ s₁ h s a, occupancy_le_one M
    (X i ω).measurable_extend s₁ h s a⟩) (fun i ↦ ((measurable_of_countable
      (fun π : Policy S A H ↦ occupancy M π.extend s₁ h s a)).comp
      (hseq.adapted_action_filtrationAction i)).stronglyMeasurable)
    (fun i ↦ condExp_visit_filtrationAction_ae_eq M s₁ hseq i h s a) hδ
  refine le_trans (measure_mono fun ω hω ↦ ?_) h'
  obtain ⟨t, ht⟩ := hω
  refine ⟨t, ?_⟩
  simp only [pullCount_eq_sum, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at ht
  exact ht

/-- **Domination of the observed next states by an i.i.d. sample, uniformly in the number of
visits**: let `ξ` be an i.i.d. sequence of law `p_h(· | s, a)`. For every sequence of sets `B n` of
sequences of `n` states, the probability that for some `n` the `n`-th visit of `(s, a)` at the step
`h` happens and the next states `W_1, …, W_n` observed at the first `n` visits are in `B n` is at
most the probability that some prefix `(ξ 0, …, ξ (n - 1))` is in `B n`. -/
lemma measure_exists_le_pullCount_visitNextState_mem_le [DecidableEq S] [DecidableEq A] (s₁ : S)
    (hseq : IsAlgEnvSeq O X Y alg (statesEnv M H s₁) P) (h : Fin H) (s : S) (a : A)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} {ξ : ℕ → Ω' → S}
    (hξ : ∀ k, Measurable (ξ k)) (hind : iIndepFun ξ μ')
    (hlaw : ∀ k, HasLaw (ξ k) (M.trans h (s, a)) μ') (B : ∀ n, Set (Fin n → S)) :
    P {ω | ∃ n, (∃ t, n ≤ pullCount (stepPair X Y h) (s, a) t ω)
        ∧ (fun k : Fin n ↦ visitNextState X Y h s a (k + 1) ω) ∈ B n}
      ≤ μ' {ω | ∃ n, (fun k : Fin n ↦ ξ k ω) ∈ B n} := by
  refine measure_exists_mem_le_of_forall_measure_inter_le
    (E := fun n ↦ {ω | ∃ t, n ≤ pullCount (stepPair X Y h) (s, a) t ω})
    (W := fun k ω ↦ visitNextState X Y h s a (k + 1) ω)
    (fun n m hnm ω ⟨t, ht⟩ ↦ ⟨t, hnm.trans ht⟩) hξ (fun n C ↦ ?_) B
  rw [hind.measure_prefix_mem_eq_pi hlaw n C]
  exact measure_visitNextState_mem_le_pi M s₁ hseq h s a n C

/-- **Domination of the observed next states by an i.i.d. sample, uniformly in the episodes**: let
`ξ` be an i.i.d. sequence of law `p_h(· | s, a)`. For every sequence of sets `B n` of sequences of
`n` states, the probability that for some `t` the next states `W_1, …, W_n` observed at the `n`
visits of `(s, a)` at the step `h` in the first `t` episodes are in `B n` is at most the
probability that some prefix `(ξ 0, …, ξ (n - 1))` is in `B n`. -/
lemma measure_exists_visitNextState_mem_le [DecidableEq S] [DecidableEq A] (s₁ : S)
    (hseq : IsAlgEnvSeq O X Y alg (statesEnv M H s₁) P) (h : Fin H) (s : S) (a : A)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} {ξ : ℕ → Ω' → S}
    (hξ : ∀ k, Measurable (ξ k)) (hind : iIndepFun ξ μ')
    (hlaw : ∀ k, HasLaw (ξ k) (M.trans h (s, a)) μ') (B : ∀ n, Set (Fin n → S)) :
    P {ω | ∃ t, (fun k : Fin (pullCount (stepPair X Y h) (s, a) t ω) ↦
        visitNextState X Y h s a (k + 1) ω) ∈ B _}
      ≤ μ' {ω | ∃ n, (fun k : Fin n ↦ ξ k ω) ∈ B n} := by
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (measure_exists_le_pullCount_visitNextState_mem_le M s₁ hseq h s a hξ hind hlaw B)
  obtain ⟨t, ht⟩ := hω
  exact ⟨_, ⟨t, le_rfl⟩, ht⟩

end Learning.MDP.Episodic
