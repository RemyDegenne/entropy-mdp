/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-!
# First-entrance decomposition and time-uniform domination of prefixes

Let `W : ℕ → Ω → α` be a process on `(Ω, μ)` and `ξ : ℕ → Ω' → α` a process on `(Ω', μ')`, with
values in a countable type with measurable singletons. Let `E n` be a nonincreasing sequence of
events such that, for every `n`, the prefix `(W 0, …, W (n - 1))` restricted to `E n` is dominated
by the prefix `(ξ 0, …, ξ (n - 1))`:
`μ(E n ∩ {(W 0, …, W (n - 1)) ∈ C}) ≤ μ'((ξ 0, …, ξ (n - 1)) ∈ C)` for all sets `C`. Then the
domination holds uniformly in `n`
(`MeasureTheory.measure_exists_mem_le_of_forall_measure_inter_le`): for every sequence of sets
`B n` of sequences of length `n`,
`μ(∃ n, E n and (W 0, …, W (n - 1)) ∈ B n) ≤ μ'(∃ n, (ξ 0, …, ξ (n - 1)) ∈ B n)`.

The proof decomposes both events according to the first index `n` at which the prefix enters
`B` (`MeasureTheory.firstEntrance`): these first-entrance events are pairwise disjoint on the
`ξ` side, and cover the event on the `W` side (for which a union bound suffices).

The typical application is a process observed at random times (e.g. the rewards of an arm of a
bandit, or the transitions observed at the visits of a state-action pair of an MDP), `E n` being
the event that the `n`-th observation happens and `ξ` an i.i.d. sequence.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {Ω Ω' α : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {μ' : Measure Ω'}

/-- The sequences of length `n` in `B n` whose prefixes of length `m < n` are not in `B m`: the
sequences whose prefixes enter `B` for the first time at the length `n`. -/
def firstEntrance (B : ∀ n, Set (Fin n → α)) (n : ℕ) : Set (Fin n → α) :=
  {x | x ∈ B n ∧ ∀ m (hm : m < n), (fun k : Fin m ↦ x (Fin.castLT k (k.2.trans hm))) ∉ B m}

/-- The first-entrance set at the length `n` is contained in `B n`. -/
lemma firstEntrance_subset (B : ∀ n, Set (Fin n → α)) (n : ℕ) : firstEntrance B n ⊆ B n :=
  fun _ hx ↦ hx.1

/-- The prefixes of a sequence enter `B` for the first time at most once. -/
lemma pairwise_disjoint_setOf_mem_firstEntrance (ξ : ℕ → Ω' → α) (B : ∀ n, Set (Fin n → α)) :
    Pairwise (Function.onFun Disjoint
      (fun n ↦ {ω | (fun k : Fin n ↦ ξ k ω) ∈ firstEntrance B n})) := by
  intro n n' hnn'
  refine Set.disjoint_left.2 fun ω hω hω' ↦ ?_
  rcases lt_or_gt_of_ne hnn' with h | h
  · exact hω'.2 n h hω.1
  · exact hω.2 n' h hω'.1

/-- If some prefix of `W` of length `n` is in `B n` on the event `E n`, with `E` nonincreasing,
then the shortest such prefix is in the first-entrance set. -/
lemma exists_mem_firstEntrance {E : ℕ → Set Ω} (hE : Antitone E) {W : ℕ → Ω → α}
    {B : ∀ n, Set (Fin n → α)} {ω : Ω} (h : ∃ n, ω ∈ E n ∧ (fun k : Fin n ↦ W k ω) ∈ B n) :
    ∃ n, ω ∈ E n ∧ (fun k : Fin n ↦ W k ω) ∈ firstEntrance B n := by
  classical
  refine ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2, fun m hm hmem ↦ ?_⟩
  exact Nat.find_min h hm ⟨hE hm.le (Nat.find_spec h).1, hmem⟩

variable [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

/-- **First-entrance decomposition**: let `E n` be a nonincreasing sequence of events and `W` a
process such that, for every `n`, the prefix `(W 0, …, W (n - 1))` restricted to `E n` is dominated
by the prefix `(ξ 0, …, ξ (n - 1))` of a measurable process `ξ`. Then for every sequence of sets
`B n` of sequences of length `n`,
`μ(∃ n, E n and (W 0, …, W (n - 1)) ∈ B n) ≤ μ'(∃ n, (ξ 0, …, ξ (n - 1)) ∈ B n)`. -/
lemma measure_exists_mem_le_of_forall_measure_inter_le {E : ℕ → Set Ω} (hE : Antitone E)
    {W : ℕ → Ω → α} {ξ : ℕ → Ω' → α} (hξ : ∀ k, Measurable (ξ k))
    (hdom : ∀ n (C : Set (Fin n → α)),
      μ (E n ∩ {ω | (fun k : Fin n ↦ W k ω) ∈ C}) ≤ μ' {ω | (fun k : Fin n ↦ ξ k ω) ∈ C})
    (B : ∀ n, Set (Fin n → α)) :
    μ {ω | ∃ n, ω ∈ E n ∧ (fun k : Fin n ↦ W k ω) ∈ B n}
      ≤ μ' {ω | ∃ n, (fun k : Fin n ↦ ξ k ω) ∈ B n} := by
  have hmeas (n : ℕ) : MeasurableSet {ω | (fun k : Fin n ↦ ξ k ω) ∈ firstEntrance B n} :=
    (Measurable.of_eval (f := fun ω (k : Fin n) ↦ ξ k ω) fun k ↦ hξ k)
      (Set.to_countable (firstEntrance B n)).measurableSet
  calc μ {ω | ∃ n, ω ∈ E n ∧ (fun k : Fin n ↦ W k ω) ∈ B n}
      ≤ μ (⋃ n, E n ∩ {ω | (fun k : Fin n ↦ W k ω) ∈ firstEntrance B n}) := by
        refine measure_mono fun ω hω ↦ ?_
        obtain ⟨n, hn⟩ := exists_mem_firstEntrance hE hω
        exact Set.mem_iUnion.2 ⟨n, hn⟩
    _ ≤ ∑' n, μ (E n ∩ {ω | (fun k : Fin n ↦ W k ω) ∈ firstEntrance B n}) := measure_iUnion_le _
    _ ≤ ∑' n, μ' {ω | (fun k : Fin n ↦ ξ k ω) ∈ firstEntrance B n} :=
        ENNReal.tsum_le_tsum fun n ↦ hdom n _
    _ = μ' (⋃ n, {ω | (fun k : Fin n ↦ ξ k ω) ∈ firstEntrance B n}) :=
        (measure_iUnion (pairwise_disjoint_setOf_mem_firstEntrance ξ B) hmeas).symm
    _ ≤ μ' {ω | ∃ n, (fun k : Fin n ↦ ξ k ω) ∈ B n} := by
        refine measure_mono fun ω hω ↦ ?_
        obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hω
        exact ⟨n, hn.1⟩

end MeasureTheory
