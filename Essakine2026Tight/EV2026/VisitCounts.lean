/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.EV2026.Run
public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Visits

/-!
# Visit counts and empirical transitions of a run

For a run `(X, Y)` in the episode environment, the visit count `n_h^t(s, a)` of the first `t`
episodes (`visitCountAt`) is LML's `pullCount` of the process `stepPair X Y h` of the pairs visited
at the step `h` (`visitCountAt_eq_pullCount`). Consequently:

* `visitCountAt_le`, `sum_visitCountAt`: `n_h^t(s, a) ≤ t` and `∑_{s, a} n_h^t(s, a) = t`;
* `transCount_eq_card`, `empTransAt_eq`: the transition counts and the empirical transitions of the
  first `t` episodes only depend on the next states `W_1, …, W_n` observed at the
  `n = n_h^t(s, a)` visits: `n_h^t(s, a, s') = #{k < n | W_{k+1} = s'}` and
  `p̂_h^t(s' | s, a) = #{k < n | W_{k+1} = s'} / n` for `n ≥ 1`;
* `measure_exists_visitCountAt_eq_le_pi`: for every run of an algorithm in the episode environment,
  `P(∃ t, n_h^t(s, a) = n and (W_1, …, W_n) ∈ C) ≤ p_h(· | s, a)^{⊗ n}(C)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP.Episodic Learning.MDP

namespace Essakine2026Tight

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  {H : ℕ} {Ω : Type*} (X : ℕ → Ω → Policy S A H) (Y : ℕ → Ω → Traj S H)

omit [Fintype S] [Fintype A] in
/-- The visit count of a run is the number of pulls of the pair `(s, a)` by the process of the
pairs visited at the step `h`. -/
lemma visitCountAt_eq_pullCount (h : Fin H) (s : S) (a : A) (t : ℕ) (ω : Ω) :
    visitCountAt X Y h s a t ω = pullCount (stepPair X Y h) (s, a) t ω := by
  simp only [visitCountAt, visitCount, stepModel, EmpiricalModel.count, Prod.fst_sum,
    Finset.sum_apply, EmpiricalModel.ofEpisodeAt, EmpiricalModel.single, pullCount_eq_sum]
  exact Fin.sum_univ_eq_sum_range (fun i ↦ if stepPair X Y h i ω = (s, a) then 1 else 0) t

omit [Fintype S] [Fintype A] in
/-- **Counts and episodes**: `n_h^t(s, a) ≤ t`. -/
lemma visitCountAt_le (h : Fin H) (s : S) (a : A) (t : ℕ) (ω : Ω) :
    visitCountAt X Y h s a t ω ≤ t := by
  rw [visitCountAt_eq_pullCount]
  exact pullCount_le _ _ _

/-- **Counts and episodes**: `∑_{s, a} n_h^t(s, a) = t`. -/
lemma sum_visitCountAt (h : Fin H) (t : ℕ) (ω : Ω) :
    ∑ s, ∑ a, visitCountAt X Y h s a t ω = t := by
  simp_rw [visitCountAt_eq_pullCount, pullCount_eq_sum]
  rw [← Fintype.sum_prod_type' (f := fun s a ↦ ∑ i ∈ range t,
    if stepPair X Y h i ω = (s, a) then 1 else 0), sum_comm]
  simp

omit [Fintype S] [Fintype A] in
/-- The transition counts of a run: `n_h^t(s, a, s')` is the number of episodes `i < t` with
`(s_h, a_h, s_{h+1}) = (s, a, s')`. -/
lemma transCount_eq_sum (h : Fin H) (s : S) (a : A) (s' : S) (t : ℕ) (ω : Ω) :
    (stepModel (histAt X Y t ω) h).2.2 (s, a) s'
      = ∑ i ∈ range t, if stepPair X Y h i ω = (s, a) ∧ Y i ω h.succ = s' then 1 else 0 := by
  simp only [stepModel, Prod.snd_sum, Finset.sum_apply, EmpiricalModel.ofEpisodeAt,
    EmpiricalModel.single]
  exact Fin.sum_univ_eq_sum_range
    (fun i ↦ if stepPair X Y h i ω = (s, a) ∧ Y i ω h.succ = s' then 1 else 0) t

omit [Fintype S] [Fintype A] in
/-- **The transition counts are counts of the observed next states**: with
`n = n_h^t(s, a)`, `n_h^t(s, a, s') = #{k < n | W_{k+1} = s'}`, where `W_k` is the next state
observed at the `k`-th visit. -/
lemma transCount_eq_card (h : Fin H) (s : S) (a : A) (s' : S) (t : ℕ) (ω : Ω) :
    (stepModel (histAt X Y t ω) h).2.2 (s, a) s'
      = #{k : Fin (visitCountAt X Y h s a t ω) | visitNextState X Y h s a (k + 1) ω = s'} := by
  set B := stepPair X Y h with hB
  set n := visitCountAt X Y h s a t ω with hn
  have hn' : n = pullCount B (s, a) t ω := visitCountAt_eq_pullCount X Y h s a t ω
  rw [transCount_eq_sum, card_filter, Fin.sum_univ_eq_sum_range
    (fun k ↦ if visitNextState X Y h s a (k + 1) ω = s' then 1 else 0) n]
  simp_rw [ite_and]
  rw [← sum_filter]
  symm
  refine sum_nbij' (fun k ↦ (stepsUntil B (s, a) (k + 1) ω).toNat) (fun i ↦ pullCount B (s, a) i ω)
    ?_ ?_ ?_ ?_ ?_
  · intro k hk
    have hk' : k < n := mem_range.1 hk
    have hne : stepsUntil B (s, a) (k + 1) ω ≠ ⊤ :=
      (exists_le_pullCount_iff_stepsUntil_ne_top k.succ_ne_zero ω).1 ⟨t, by omega⟩
    have hex := exists_pullCount_eq hne
    simp only [mem_filter, mem_range]
    refine ⟨?_, action_stepsUntil k.succ_ne_zero hex⟩
    by_contra hlt
    push Not at hlt
    rcases t with _ | t
    · simp [hn'] at hk'
    · have hlt' : (t : ℕ∞) < stepsUntil B (s, a) (k + 1) ω := by
        rw [← ENat.natCast_toNat hne]
        exact_mod_cast hlt
      have := pullCount_lt_of_le_stepsUntil (s, a) ω hex hlt'
      omega
  · intro i hi
    simp only [mem_filter, mem_range] at hi
    have h1 : pullCount B (s, a) (i + 1) ω = pullCount B (s, a) i ω + 1 := by
      rw [← hi.2]
      exact pullCount_action_eq_pullCount_add_one i ω
    have h2 := pullCount_mono (A := B) (s, a) (show i + 1 ≤ t by omega) ω
    simp only [mem_range]
    omega
  · intro k hk
    have hne : stepsUntil B (s, a) (k + 1) ω ≠ ⊤ :=
      (exists_le_pullCount_iff_stepsUntil_ne_top k.succ_ne_zero ω).1
        ⟨t, by have := mem_range.1 hk; omega⟩
    have := pullCount_stepsUntil k.succ_ne_zero (exists_pullCount_eq hne)
    simpa using this
  · intro i hi
    simp only [mem_filter, mem_range] at hi
    have h1 : pullCount B (s, a) (i + 1) ω = pullCount B (s, a) i ω + 1 := by
      rw [← hi.2]
      exact pullCount_action_eq_pullCount_add_one i ω
    have hi2 : B i ω = (s, a) := hi.2
    have := stepsUntil_pullCount_eq (A := B) ω i
    rw [hi2, h1] at this
    simp [this]
  · intro k _
    rfl

omit [Fintype A] in
/-- **The empirical transitions are the empirical distribution of the observed next states**:
with `n = n_h^t(s, a) ≥ 1`, `p̂_h^t(s' | s, a) = #{k < n | W_{k+1} = s'} / n`. -/
lemma empTransAt_eq (h : Fin H) (s : S) (a : A) (t : ℕ) (ω : Ω)
    (hn : visitCountAt X Y h s a t ω ≠ 0) (s' : S) :
    empTransAt X Y h s a t ω s'
      = #{k : Fin (visitCountAt X Y h s a t ω) | visitNextState X Y h s a (k + 1) ω = s'}
        / (visitCountAt X Y h s a t ω : ℝ) := by
  have hn' : visitCount (histAt X Y t ω) h s a ≠ 0 := hn
  rw [empTransAt, empTrans, ite_eq_right hn', EmpiricalModel.empTrans, transCount_eq_card]
  rfl

omit [Fintype S] [Fintype A] in
/-- **Domination of the observed next states by an i.i.d. sample, uniformly in the episodes**: in
a run of any algorithm in the episode environment of `M` from `s₁`, for every `n` and every set
`C` of sequences of `n` states,
`P(∃ t, n_h^t(s, a) = n and (W_1, …, W_n) ∈ C) ≤ p_h(· | s, a)^{⊗ n}(C)`. -/
lemma measure_exists_visitCountAt_eq_le_pi [Finite S] [Countable A] [Nonempty A]
    [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
    [MeasurableSingletonClass A]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {alg : Algorithm Unit (Policy S A H) (Traj S H)} (M : EpisodicMDP S A) (s₁ : S)
    (hseq : IsAlgEnvSeq (fun _ _ ↦ ()) X Y alg (statesEnv M H s₁) P) (h : Fin H) (s : S) (a : A)
    (n : ℕ) (C : Set (Fin n → S)) :
    P {ω | (∃ t, visitCountAt X Y h s a t ω = n)
        ∧ (fun k : Fin n ↦ visitNextState X Y h s a (k + 1) ω) ∈ C}
      ≤ Measure.pi (fun _ : Fin n ↦ M.trans h (s, a)) C := by
  refine (measure_mono fun ω hω ↦ ?_).trans
    (measure_visitNextState_mem_le_pi M s₁ hseq h s a n C)
  simp only [Set.mem_ofPred_eq, visitCountAt_eq_pullCount] at hω ⊢
  exact ⟨(exists_pullCount_eq_iff_exists_le_pullCount ω).1 hω.1, hω.2⟩

end Essakine2026Tight
