/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Empirical

/-!
# Consistency of the counts of an empirical model

An empirical model is *consistent* if the transition counts of every pair sum to its visit count
(`EmpiricalModel.IsConsistent`). Single transitions are consistent and sums of consistent models
are consistent, so the models of episodes and of histories are; the empirical transitions of a
visited pair of a consistent model form a probability vector (`sum_empTrans`, `empTrans_nonneg`).
-/

@[expose] public section

open Finset

namespace Learning.MDP.EmpiricalModel

variable {S A : Type*} [Fintype S]

/-- The transition counts of every pair sum to its visit count. -/
def IsConsistent (m : EmpiricalModel S A) : Prop := ∀ p, ∑ t, m.2.2 p t = m.1 p

lemma isConsistent_single [DecidableEq S] [DecidableEq A] (s : S) (a : A) (r : ℝ) (s' : S) :
    (single s a r s').IsConsistent := by
  intro p
  by_cases h : (s, a) = p <;> simp [single, h]

lemma IsConsistent.add {m m' : EmpiricalModel S A} (hm : m.IsConsistent) (hm' : m'.IsConsistent) :
    (m + m').IsConsistent := by
  intro p
  simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, sum_add_distrib, hm p, hm' p]

lemma isConsistent_zero : (0 : EmpiricalModel S A).IsConsistent := by
  intro p
  simp

lemma isConsistent_sum {ι : Type*} (u : Finset ι) {m : ι → EmpiricalModel S A}
    (hm : ∀ i ∈ u, (m i).IsConsistent) : (∑ i ∈ u, m i).IsConsistent := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using isConsistent_zero
  | insert i u hi ih =>
    rw [sum_insert hi]
    exact (hm i (mem_insert_self i u)).add (ih fun j hj ↦ hm j (mem_insert_of_mem hj))

lemma isConsistent_ofEpisodeAt [DecidableEq S] [DecidableEq A] {H : ℕ}
    (π : Episodic.Policy S A H) (τ : Episodic.Traj S H) (r : Fin H → ℝ)
    (h : Fin H) : (ofEpisodeAt π τ r h).IsConsistent :=
  isConsistent_single _ _ _ _

omit [Fintype S] in
lemma empTrans_nonneg (m : EmpiricalModel S A) (p : S × A) (s' : S) : 0 ≤ m.empTrans p s' := by
  unfold empTrans
  positivity

/-- The empirical transitions of a visited pair of a consistent model sum to `1`. -/
lemma IsConsistent.sum_empTrans {m : EmpiricalModel S A} (hm : m.IsConsistent) {p : S × A}
    (hp : m.count p ≠ 0) : ∑ s', m.empTrans p s' = 1 := by
  simp only [empTrans, ← sum_div]
  rw [← Nat.cast_sum, hm p, div_self (by exact_mod_cast hp)]

end Learning.MDP.EmpiricalModel
