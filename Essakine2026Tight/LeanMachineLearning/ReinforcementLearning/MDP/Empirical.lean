/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Episodic

/-!
# Empirical models of a tabular MDP

The empirical model `EmpiricalModel S A = (S × A → ℕ) × (S × A → ℝ) × (S × A → S → ℕ)` of a
tabular MDP records the visit counts, the sums of the rewards and the transition counts of the
state-action pairs. It is an additive monoid: the model of a single transition `(s, a, r, s')` is
`EmpiricalModel.single s a r s'`, and models of several transitions add up. The empirical mean
rewards are `EmpiricalModel.empReward` and the empirical transition probabilities
`EmpiricalModel.empTrans` (`0` for unvisited pairs).

The accessors are `count` (`N(s, a)`), `rewardSum` and `transCount` (`N(s, a, s')`).

Episodes (`MDP/Episodic.lean`): `ofEpisodeAt π τ r h` is the model of the transition at step `h`
of the episode with the `H`-step policy `π`, states `τ` and rewards `r`, and `ofEpisode π τ r` the
model of the whole episode (the counts of all steps pooled, as for a stationary MDP; step-indexed
counts are `fun h ↦ ofEpisodeAt π τ r h`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP Learning.MDP.Episodic

namespace Learning.MDP

/-- The empirical model of a tabular MDP: visit counts, sums of rewards and transition counts of
the state-action pairs. -/
abbrev EmpiricalModel (S A : Type*) := (S × A → ℕ) × (S × A → ℝ) × (S × A → S → ℕ)

namespace EmpiricalModel

variable {S A : Type*}

/-- The visit count `N(s, a)`. -/
def count (m : EmpiricalModel S A) (p : S × A) : ℕ := m.1 p

/-- The sum of the rewards received at `(s, a)`. -/
def rewardSum (m : EmpiricalModel S A) (p : S × A) : ℝ := m.2.1 p

/-- The transition count `N(s, a, s')`. -/
def transCount (m : EmpiricalModel S A) (p : S × A) (s' : S) : ℕ := m.2.2 p s'

/-- The empirical mean reward `r̂(s, a)` (`0` for unvisited pairs). -/
noncomputable def empReward (m : EmpiricalModel S A) (p : S × A) : ℝ := m.2.1 p / m.1 p

/-- The empirical transition probabilities `P̂(· | s, a)` (`0` for unvisited pairs). -/
noncomputable def empTrans (m : EmpiricalModel S A) (p : S × A) : S → ℝ :=
  fun s' ↦ m.2.2 p s' / m.1 p

@[simp] lemma count_add (m m' : EmpiricalModel S A) (p : S × A) :
    (m + m').count p = m.count p + m'.count p := rfl

@[simp] lemma rewardSum_add (m m' : EmpiricalModel S A) (p : S × A) :
    (m + m').rewardSum p = m.rewardSum p + m'.rewardSum p := rfl

@[simp] lemma transCount_add (m m' : EmpiricalModel S A) (p : S × A) (s' : S) :
    (m + m').transCount p s' = m.transCount p s' + m'.transCount p s' := rfl

@[simp] lemma count_zero (p : S × A) : (0 : EmpiricalModel S A).count p = 0 := rfl

lemma count_sum {ι : Type*} (u : Finset ι) (m : ι → EmpiricalModel S A) (p : S × A) :
    (∑ i ∈ u, m i).count p = ∑ i ∈ u, (m i).count p := by
  classical
  induction u using Finset.induction_on with
  | empty => rfl
  | insert i u hi ih => rw [sum_insert hi, sum_insert hi, count_add, ih]

lemma transCount_sum {ι : Type*} (u : Finset ι) (m : ι → EmpiricalModel S A) (p : S × A)
    (s' : S) : (∑ i ∈ u, m i).transCount p s' = ∑ i ∈ u, (m i).transCount p s' := by
  classical
  induction u using Finset.induction_on with
  | empty => rfl
  | insert i u hi ih => rw [sum_insert hi, sum_insert hi, transCount_add, ih]

lemma empTrans_eq (m : EmpiricalModel S A) (p : S × A) (s' : S) :
    m.empTrans p s' = m.transCount p s' / m.count p := rfl

lemma empReward_eq (m : EmpiricalModel S A) (p : S × A) :
    m.empReward p = m.rewardSum p / m.count p := rfl

variable [DecidableEq S] [DecidableEq A]

/-- The empirical model of the single transition `(s, a, r, s')`. -/
def single (s : S) (a : A) (r : ℝ) (s' : S) : EmpiricalModel S A :=
  (fun p ↦ if (s, a) = p then 1 else 0, fun p ↦ if (s, a) = p then r else 0,
    fun p t ↦ if (s, a) = p ∧ s' = t then 1 else 0)

@[simp] lemma count_single (s : S) (a : A) (r : ℝ) (s' : S) (p : S × A) :
    (single s a r s').count p = if (s, a) = p then 1 else 0 := rfl

@[simp] lemma transCount_single (s : S) (a : A) (r : ℝ) (s' : S) (p : S × A) (t : S) :
    (single s a r s').transCount p t = if (s, a) = p ∧ s' = t then 1 else 0 := rfl

section Measurability

variable [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Countable A] {X : Type*} [MeasurableSpace X]

lemma measurable_single {s : X → S} {a : X → A} {r : X → ℝ} {s' : X → S} (hs : Measurable s)
    (ha : Measurable a) (hr : Measurable r) (hs' : Measurable s') :
    Measurable fun x ↦ single (s x) (a x) (r x) (s' x) := by
  unfold single
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact (measurable_of_countable (fun q : S × A ↦ fun p ↦ if q = p then (1 : ℕ) else 0)).comp
      (hs.prodMk ha)
  · refine Measurable.of_eval fun p ↦ ?_
    exact Measurable.ite ((hs.prodMk ha) (measurableSet_singleton p)) hr measurable_const
  · exact (measurable_of_countable (fun q : (S × A) × S ↦
      fun p t ↦ if q.1 = p ∧ q.2 = t then (1 : ℕ) else 0)).comp ((hs.prodMk ha).prodMk hs')

end Measurability

/-! ### Episodes -/

variable {H : ℕ}

/-- The empirical model of the transition at step `h` of the episode with policy `π`, states `τ`
and rewards `r`. -/
def ofEpisodeAt (π : Policy S A H) (τ : Traj S H) (r : Fin H → ℝ) (h : Fin H) :
    EmpiricalModel S A :=
  single (τ h.castSucc) (π h (τ h.castSucc)) (r h) (τ h.succ)

/-- The empirical model of an episode (the counts of all steps pooled). -/
def ofEpisode (π : Policy S A H) (τ : Traj S H) (r : Fin H → ℝ) : EmpiricalModel S A :=
  ∑ h, ofEpisodeAt π τ r h

section Measurability

variable [MeasurableSpace S] [MeasurableSingletonClass S] [Finite S] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Finite A] {X : Type*} [MeasurableSpace X]

instance : MeasurableAdd₂ (EmpiricalModel S A) where
  measurable_add := by
    change Measurable fun p : EmpiricalModel S A × EmpiricalModel S A ↦
      (p.1.1 + p.2.1, p.1.2.1 + p.2.2.1, p.1.2.2 + p.2.2.2)
    fun_prop

lemma measurable_ofEpisodeAt {π : X → Policy S A H} {τ : X → Traj S H} {r : X → Fin H → ℝ}
    (hπ : Measurable π) (hτ : Measurable τ) (hr : Measurable r) (h : Fin H) :
    Measurable fun x ↦ ofEpisodeAt (π x) (τ x) (r x) h := by
  unfold ofEpisodeAt
  have h1 : Measurable fun x ↦ τ x h.castSucc := (measurable_pi_apply _).comp hτ
  have h2 : Measurable fun x ↦ π x h (τ x h.castSucc) :=
    (measurable_of_countable (fun q : Policy S A H × Traj S H ↦ q.1 h (q.2 h.castSucc))).comp
      (hπ.prodMk hτ)
  exact measurable_single h1 h2 ((measurable_pi_apply _).comp hr) ((measurable_pi_apply _).comp hτ)

lemma measurable_ofEpisode {π : X → Policy S A H} {τ : X → Traj S H} {r : X → Fin H → ℝ}
    (hπ : Measurable π) (hτ : Measurable τ) (hr : Measurable r) :
    Measurable fun x ↦ ofEpisode (π x) (τ x) (r x) :=
  Finset.measurable_sum _ fun h _ ↦ measurable_ofEpisodeAt hπ hτ hr h

end Measurability

end EmpiricalModel

end Learning.MDP
