/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.EV2026.Constants
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The tree of the hard instances

The tree of the hard instances of the lower bound has `n` nodes numbered in the breadth-first
order of the infinite `A`-ary tree: the parent of the node `j + 1` is `j / A`
and the children of the node `j` are the nodes `A j + k + 1` for `k < A` that are smaller than
`n`. This file proves the combinatorial facts used by the lower bound, at the level of natural
numbers:

* the depth `nodeDepth A j` (defined through the parent) increases by one from a node to each of
  its children (`nodeDepth_mul_add`), and the nodes of depth at least `D` are numbered at least
  `geomCount A D = ∑_{i < D} A^i` (`geomCount_le_of_le_nodeDepth`);
* with `d = treeDepth S A` and `n = S - 3` nodes: `n ≤ geomCount A d` (`le_geomCount_treeDepth`),
  hence every node has depth at most `d - 1` (`nodeDepth_lt_treeDepth`), and `d ≥ 2`
  (`two_le_treeDepth`);
* the child function `childIdx n A j k` (the first child when the child `k` is missing) of an
  internal node `j` (`A j + 1 < n`) is a node of depth `nodeDepth A j + 1`;
* the number `L` of leaves (nodes without children) satisfies `4 L ≥ n + 3` (`card_leafFinset`);
* every node is reached from the root by a walk through internal nodes (`exists_walk`).
-/

@[expose] public section

open Finset

namespace Essakine2026Tight

/-! ### Geometric counts and depths -/

/-- The number `∑_{i < D} A^i` of nodes of depth less than `D` of the infinite `A`-ary tree. -/
def geomCount (A D : ℕ) : ℕ := ∑ i ∈ range D, A ^ i

lemma geomCount_zero (A : ℕ) : geomCount A 0 = 0 := rfl

lemma geomCount_succ (A D : ℕ) : geomCount A (D + 1) = A * geomCount A D + 1 := by
  simp only [geomCount, sum_range_succ', pow_succ, pow_zero, mul_sum]
  exact congrArg (· + 1) (sum_congr rfl fun i _ ↦ by ring)

lemma sub_one_mul_geomCount (A D : ℕ) (hA : 1 ≤ A) : (A - 1) * geomCount A D + 1 = A ^ D := by
  induction D with
  | zero => simp [geomCount_zero]
  | succ D ih =>
    rw [geomCount_succ, pow_succ, ← ih]
    obtain ⟨B, rfl⟩ : ∃ B, A = B + 1 := ⟨A - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring

/-- The depth of the node `j` of the breadth-first `A`-ary tree (the parent of `j + 1` is
`j / A`). -/
def nodeDepth (A : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => nodeDepth A (j / A) + 1
decreasing_by exact Nat.lt_succ_of_le (Nat.div_le_self j A)

@[simp] lemma nodeDepth_zero (A : ℕ) : nodeDepth A 0 = 0 := by rw [nodeDepth]

lemma nodeDepth_succ (A j : ℕ) : nodeDepth A (j + 1) = nodeDepth A (j / A) + 1 := by
  rw [nodeDepth]

/-- The depth of the child `k + 1 ∈ [1, A]` of the node `j`. -/
lemma nodeDepth_mul_add (A j k : ℕ) (hk : k < A) :
    nodeDepth A (A * j + k + 1) = nodeDepth A j + 1 := by
  rw [nodeDepth_succ]
  congr 2
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hk, zero_add]

lemma geomCount_le_of_le_nodeDepth (A : ℕ) {D j : ℕ} (h : D ≤ nodeDepth A j) :
    geomCount A D ≤ j := by
  induction D generalizing j with
  | zero => simp [geomCount_zero]
  | succ D ih =>
    rcases j with _ | j
    · simp at h
    · rw [nodeDepth_succ] at h
      have h1 := ih (j := j / A) (by omega)
      rw [geomCount_succ]
      have h2 : A * (j / A) ≤ j := Nat.mul_div_le j A
      calc A * geomCount A D + 1 ≤ A * (j / A) + 1 := by gcongr
        _ ≤ j + 1 := by omega

/-! ### The depth of the tree -/

lemma le_geomCount_treeDepth {S A : ℕ} (hA : 2 ≤ A) :
    S - 3 ≤ geomCount A (treeDepth S A) := by
  have h1 := Nat.le_pow_clog (b := A) (by omega) ((S - 3) * (A - 1) + 1)
  rw [← sub_one_mul_geomCount A _ (by omega)] at h1
  have h2 : (S - 3) * (A - 1) ≤ geomCount A (treeDepth S A) * (A - 1) := by
    unfold treeDepth; linarith
  exact Nat.le_of_mul_le_mul_right h2 (by omega)

/-- Every node of the tree of `S - 3` nodes has depth at most `d - 1`. -/
lemma nodeDepth_lt_treeDepth {S A j : ℕ} (hA : 2 ≤ A) (hj : j < S - 3) :
    nodeDepth A j < treeDepth S A := by
  by_contra! h
  have := geomCount_le_of_le_nodeDepth A h
  have := le_geomCount_treeDepth (S := S) hA
  omega

lemma two_le_treeDepth {S A : ℕ} (hS : 6 ≤ S) (hA : 2 ≤ A) : 2 ≤ treeDepth S A := by
  unfold treeDepth
  rw [Nat.succ_le_iff, Nat.lt_clog_iff_pow_lt (by omega), pow_one]
  have h3 : 3 ≤ S - 3 := by omega
  have h1 : 3 * (A - 1) ≤ (S - 3) * (A - 1) := Nat.mul_le_mul_right _ h3
  omega

/-! ### Children, leaves and walks -/

/-- The child of the node `j` for the action `k < A`: the node `A j + k + 1` if it exists, the
first child `A j + 1` otherwise. -/
def childIdx (n A j k : ℕ) : ℕ := if A * j + k + 1 < n then A * j + k + 1 else A * j + 1

lemma childIdx_of_lt {n A j k : ℕ} (h : A * j + k + 1 < n) : childIdx n A j k = A * j + k + 1 := by
  simp [childIdx, h]

lemma childIdx_lt {n A j k : ℕ} (hj : A * j + 1 < n) : childIdx n A j k < n := by
  unfold childIdx; split_ifs <;> omega

lemma nodeDepth_childIdx {n A j k : ℕ} (hk : k < A) :
    nodeDepth A (childIdx n A j k) = nodeDepth A j + 1 := by
  unfold childIdx
  split_ifs
  · exact nodeDepth_mul_add A j k hk
  · exact nodeDepth_mul_add A j 0 (by omega)

/-- The leaves of the tree with `n` nodes: the nodes without children. -/
def leafFinset (n A : ℕ) : Finset ℕ := (range n).filter fun j ↦ ¬ A * j + 1 < n

/-- The tree with `n ≥ 3` nodes has at least `(n + 3) / 4` leaves. -/
lemma card_leafFinset {n A : ℕ} (hA : 2 ≤ A) (hn : 3 ≤ n) : n + 3 ≤ 4 * #(leafFinset n A) := by
  have hsub : Ico (n / 2) n ⊆ leafFinset n A := by
    intro j hj
    simp only [mem_Ico] at hj
    simp only [leafFinset, mem_filter, mem_range, not_lt]
    have h2 : 2 * j ≤ A * j := Nat.mul_le_mul_right j hA
    exact ⟨hj.2, by omega⟩
  have := card_le_card hsub
  rw [Nat.card_Ico] at this
  omega

/-- The walk from the root following the actions `acts`. -/
def treeWalk (n A : ℕ) (acts : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => childIdx n A (treeWalk n A acts m) (acts m)

/-- Every node `j < n` is reached from the root by a walk of `nodeDepth A j` steps through
internal nodes. -/
lemma exists_walk {n A : ℕ} (hA : 2 ≤ A) {j : ℕ} (hj : j < n) :
    ∃ acts : ℕ → ℕ, (∀ m, acts m < A) ∧ treeWalk n A acts (nodeDepth A j) = j
      ∧ ∀ m < nodeDepth A j, A * treeWalk n A acts m + 1 < n := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases j with _ | j
    · exact ⟨fun _ ↦ 0, fun _ ↦ show 0 < A by omega, by simp [treeWalk],
        fun m hm ↦ by simp at hm⟩
    · have hdiv : j / A ≤ j := Nat.div_le_self j A
      obtain ⟨acts, hacts, hwalk, hint⟩ := ih (j / A) (by omega) (by omega)
      set D := nodeDepth A (j / A) with hD
      refine ⟨Function.update acts D (j % A), fun m ↦ ?_, ?_, fun m hm ↦ ?_⟩
      · rcases eq_or_ne m D with rfl | h
        · simp only [Function.update_self]; exact Nat.mod_lt _ (by omega)
        · rw [Function.update_of_ne h]; exact hacts m
      · have hagree : ∀ m ≤ D, treeWalk n A (Function.update acts D (j % A)) m
            = treeWalk n A acts m := by
          intro m hm
          induction m with
          | zero => rfl
          | succ m ihm =>
            simp only [treeWalk, ihm (by omega), Function.update_of_ne (show m ≠ D by omega)]
        have hj' : A * (j / A) + j % A + 1 = j + 1 := by
          have := Nat.div_add_mod j A; omega
        rw [nodeDepth_succ, treeWalk, hagree D le_rfl, hwalk, Function.update_self,
          childIdx_of_lt (by omega), hj']
      · rw [nodeDepth_succ] at hm
        have hagree : ∀ m ≤ D, treeWalk n A (Function.update acts D (j % A)) m
            = treeWalk n A acts m := by
          intro m hm
          induction m with
          | zero => rfl
          | succ m ihm =>
            simp only [treeWalk, ihm (by omega), Function.update_of_ne (show m ≠ D by omega)]
        rcases Nat.lt_or_ge m D with h | h
        · rw [hagree m h.le]; exact hint m h
        · have hmD : m = D := by omega
          rw [hmD, hagree D le_rfl, hwalk]
          have := Nat.mul_div_le j A
          omega

end Essakine2026Tight
