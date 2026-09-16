/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.EV2026.HardTree
public import Essakine2026Tight.EV2026.HardParams
public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.StateSeq
public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Values
public import Mathlib.Probability.Distributions.Bernoulli
public import Essakine2026Tight.Mathlib.InformationTheory.Pinsker

/-!
# The hard instances of the lower bound

For finite types `S` (with `nS = card S ≥ 6` states) and `A` (with `nA = card A ≥ 2` actions),
enumerated by `Fintype.equivFin`, the state of index `0` is the waiting state, `1` the good
absorbing state, `2` the bad absorbing state, and `j + 3` the node `j` of the breadth-first
`nA`-ary tree with `nS - 3` nodes (`EV2026/HardTree.lean`); actions are indexed by `aIdx`, the
waiting action having index `0`. Steps are `0`-indexed.

* From the waiting state at the step `h`, the action of index `0` keeps waiting if
  `h + 2 ≤ H / 3`, and every other action (or the last waiting step) leads to the root.
* From an internal node `j` (`nA j + 1 < nS - 3`) the action of index `k` leads to the node
  `childIdx (nS - 3) nA j k`.
* From a leaf `j` at the step `h` with the action of index `k`, the next state is the good state
  with probability `p₊` if `u = some (h, j, k)` and `p₋` otherwise, the bad state otherwise
  (`bernoulliMeasure`).
* The good and bad states are absorbing; the reward is `1` in the good state from the step
  `H / 3 + d` on (`d = treeDepth nS nA`) and `0` otherwise.

`hardMDP u` is the instance `𝓜_u` (`u = none` for `𝓜₀`). Every policy follows a deterministic path
of state indices `pathIdx π` from the waiting state until it reaches a leaf at the step
`arrival π < H / 3 + d` (`arrival_lt`); its *triple* is `(arrival, leaf, action index)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Learning.MDP Learning.MDP.Episodic unitInterval
open scoped ENNReal

namespace Essakine2026Tight

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S]

/-! ### Indices -/

/-- The index of a state. -/
noncomputable def sIdx (s : S) : ℕ := (Fintype.equivFin S s : ℕ)

/-- The index of an action. -/
noncomputable def aIdx (a : A) : ℕ := (Fintype.equivFin A a : ℕ)

/-- The state of index `i` (an arbitrary state if `i` is too large). -/
noncomputable def stateAt (S : Type*) [Fintype S] [Nonempty S] (i : ℕ) : S :=
  if h : i < Fintype.card S then (Fintype.equivFin S).symm ⟨i, h⟩ else Classical.arbitrary S

omit [Nonempty S] in
lemma sIdx_lt (s : S) : sIdx s < Fintype.card S := (Fintype.equivFin S s).is_lt

omit [Nonempty S] in
lemma aIdx_lt (a : A) : aIdx a < Fintype.card A := (Fintype.equivFin A a).is_lt

lemma sIdx_stateAt {i : ℕ} (hi : i < Fintype.card S) : sIdx (stateAt S i) = i := by
  simp [sIdx, stateAt, hi]

lemma stateAt_sIdx (s : S) : stateAt S (sIdx s) = s := by
  simp [sIdx, stateAt]

lemma stateAt_injOn {i j : ℕ} (hi : i < Fintype.card S) (hj : j < Fintype.card S)
    (h : stateAt S i = stateAt S j) : i = j := by
  rw [← sIdx_stateAt hi, ← sIdx_stateAt hj, h]

/-! ### Transitions -/

/-- The index of the next state along a deterministic transition from the state of index `i`
with the action of index `k` at the step `h` (leaves lead to the bad state). -/
def nextIdx (nS nA Hb h i k : ℕ) : ℕ :=
  if i = 0 then (if k = 0 ∧ h + 2 ≤ Hb then 0 else 3)
  else if i < 3 then i
  else if nA * (i - 3) + 1 < nS - 3 then childIdx (nS - 3) nA (i - 3) k + 3
  else 2

/-- The state of index `i` is a leaf of the tree. -/
def IsLeafIdx (nS nA i : ℕ) : Prop := 3 ≤ i ∧ i < nS ∧ ¬ nA * (i - 3) + 1 < nS - 3

instance (nS nA i : ℕ) : Decidable (IsLeafIdx nS nA i) := by unfold IsLeafIdx; infer_instance

/-- The success probability at the leaf of index `i` at the step `h` with the action of index
`k`, in the instance `u` (clamped to `[0, 1]`). -/
noncomputable def leafProb (β ε : ℝ) (H' : ℕ) (u : Option (ℕ × ℕ × ℕ)) (h i k : ℕ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one
    (if u = some (h, i - 3, k) then hardPPlus β H' ε else hardPMinus β H')

variable [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A]

/-- The transition function of the hard instance `u`. -/
noncomputable def hardTransFun (H : ℕ) (β ε : ℝ) (u : Option (ℕ × ℕ × ℕ)) (h : ℕ) (s : S)
    (a : A) : Measure S :=
  if IsLeafIdx (Fintype.card S) (Fintype.card A) (sIdx s) then
    bernoulliMeasure (stateAt S 1) (stateAt S 2)
      (leafProb β ε (effHorizon (Fintype.card S) (Fintype.card A) H) u h (sIdx s) (aIdx a))
  else Measure.dirac (stateAt S (nextIdx (Fintype.card S) (Fintype.card A) (H / 3) h (sIdx s)
    (aIdx a)))

omit [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma isProbabilityMeasure_hardTransFun (H : ℕ) (β ε : ℝ) (u : Option (ℕ × ℕ × ℕ)) (h : ℕ)
    (s : S) (a : A) : IsProbabilityMeasure (hardTransFun H β ε u h s a) := by
  unfold hardTransFun
  split_ifs
  · infer_instance
  · infer_instance

/-- The transition kernels of the hard instance `u`. -/
noncomputable def hardTrans (H : ℕ) (β ε : ℝ) (u : Option (ℕ × ℕ × ℕ)) (h : Fin H) :
    Kernel (S × A) S :=
  ⟨fun p ↦ hardTransFun H β ε u h p.1 p.2, measurable_of_countable _⟩

instance (H : ℕ) (β ε : ℝ) (u : Option (ℕ × ℕ × ℕ)) (h : Fin H) :
    IsMarkovKernel (hardTrans (S := S) (A := A) H β ε u h) :=
  ⟨fun p ↦ isProbabilityMeasure_hardTransFun H β ε u h p.1 p.2⟩

omit [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- The reward function of the hard instances: `1` in the good state from the step `H / 3 + d`
on. -/
noncomputable def hardReward (H : ℕ) (h : Fin H) (s : S) (_a : A) : ℝ :=
  if sIdx s = 1 ∧ H / 3 + treeDepth (Fintype.card S) (Fintype.card A) ≤ h then 1 else 0

/-- The hard instance `𝓜_u` (`u = none` for `𝓜₀`). -/
noncomputable def hardMDP (H : ℕ) (β ε : ℝ) (u : Option (ℕ × ℕ × ℕ)) : EpisodicMDP S A H :=
  EpisodicMDP.ofDet (hardTrans H β ε u) (hardReward H)

lemma hasRewardFn_hardMDP (H : ℕ) (β ε : ℝ) (u : Option (ℕ × ℕ × ℕ)) :
    (hardMDP (S := S) (A := A) H β ε u).HasRewardFn (hardReward H) :=
  EpisodicMDP.hasRewardFn_ofDet _ _

omit [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma hardReward_mem_Icc (H : ℕ) (h : Fin H) (s : S) (a : A) :
    hardReward H h s a ∈ Set.Icc (0 : ℝ) 1 := by
  unfold hardReward; split_ifs <;> simp

/-! ### The path of a policy -/

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- The index of the action of the policy `π` at the step `h` in the state of index `i`. -/
noncomputable def actIdx {H : ℕ} (π : Policy S A H) (h i : ℕ) : ℕ :=
  if hh : h < H then aIdx (π ⟨h, hh⟩ (stateAt S i)) else 0

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- The deterministic path of state indices of the policy `π` from the waiting state. -/
noncomputable def pathIdx {H : ℕ} (π : Policy S A H) : ℕ → ℕ
  | 0 => 0
  | h + 1 => nextIdx (Fintype.card S) (Fintype.card A) (H / 3) h (pathIdx π h)
      (actIdx π h (pathIdx π h))

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- The invariant of the path before the leaf: waiting before the step `H / 3`, or at a node of
depth at least the number of steps after `H / 3`. -/
def PathInv {H : ℕ} (π : Policy S A H) (h : ℕ) : Prop :=
  (pathIdx π h = 0 ∧ h + 1 ≤ H / 3)
    ∨ (3 ≤ pathIdx π h ∧ pathIdx π h < Fintype.card S
      ∧ h ≤ H / 3 + nodeDepth (Fintype.card A) (pathIdx π h - 3))

variable {H : ℕ}

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma pathInv_zero (π : Policy S A H) (hH : 3 ≤ H) : PathInv π 0 := by
  left; exact ⟨rfl, by omega⟩

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma pathInv_succ (π : Policy S A H) (hA : 2 ≤ Fintype.card A) (hS : 6 ≤ Fintype.card S)
    {h : ℕ} (hinv : PathInv π h) (hleaf : ¬ IsLeafIdx (Fintype.card S) (Fintype.card A)
      (pathIdx π h)) : PathInv π (h + 1) := by
  have hk := fun h i ↦ show actIdx π h i < Fintype.card A by
    unfold actIdx; split_ifs
    · exact aIdx_lt _
    · omega
  rcases hinv with ⟨h0, hh⟩ | ⟨h3, hlt, hdep⟩
  · simp only [PathInv, pathIdx, h0, nextIdx, ↓reduceIte]
    split_ifs with hw
    · left; exact ⟨rfl, by omega⟩
    · right; simp only [Nat.sub_self, nodeDepth_zero]; omega
  · have hint : Fintype.card A * (pathIdx π h - 3) + 1 < Fintype.card S - 3 := by
      simp only [IsLeafIdx, not_and, not_not] at hleaf
      exact hleaf h3 hlt
    right
    simp only [pathIdx, nextIdx, show pathIdx π h ≠ 0 by omega, show ¬ pathIdx π h < 3 by omega,
      hint, ↓reduceIte, Nat.add_sub_cancel]
    refine ⟨by omega, by have := childIdx_lt (k := actIdx π h (pathIdx π h)) hint; omega, ?_⟩
    rw [nodeDepth_childIdx (hk _ _)]
    omega

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- Every policy reaches a leaf before the step `H / 3 + d`. -/
lemma exists_isLeafIdx_pathIdx (π : Policy S A H) (hS : 6 ≤ Fintype.card S)
    (hA : 2 ≤ Fintype.card A) (hH : 3 * treeDepth (Fintype.card S) (Fintype.card A) ≤ H) :
    ∃ h, h < H / 3 + treeDepth (Fintype.card S) (Fintype.card A)
      ∧ IsLeafIdx (Fintype.card S) (Fintype.card A) (pathIdx π h) := by
  have hd := two_le_treeDepth hS hA
  by_contra! hcon
  have hinv : ∀ h ≤ H / 3 + treeDepth (Fintype.card S) (Fintype.card A), PathInv π h := by
    intro h hh
    induction h with
    | zero => exact pathInv_zero π (by omega)
    | succ h ih => exact pathInv_succ π hA hS (ih (by omega)) (hcon h (by omega))
  set N := H / 3 + treeDepth (Fintype.card S) (Fintype.card A) with hN
  rcases hinv N le_rfl with ⟨_, hh⟩ | ⟨h3, hlt, hdep⟩
  · omega
  · have := nodeDepth_lt_treeDepth (S := Fintype.card S) hA (j := pathIdx π N - 3) (by omega)
    omega

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- The step at which the policy `π` reaches a leaf. -/
noncomputable def arrival (π : Policy S A H) : ℕ :=
  sInf {h | IsLeafIdx (Fintype.card S) (Fintype.card A) (pathIdx π h)}

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma not_isLeafIdx_of_lt_arrival (π : Policy S A H) {h : ℕ} (hh : h < arrival π) :
    ¬ IsLeafIdx (Fintype.card S) (Fintype.card A) (pathIdx π h) :=
  Nat.notMem_of_lt_sInf hh

section Arrival

variable (π : Policy S A H) (hS : 6 ≤ Fintype.card S) (hA : 2 ≤ Fintype.card A)
  (hH : 3 * treeDepth (Fintype.card S) (Fintype.card A) ≤ H)

include hS hA hH

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma isLeafIdx_pathIdx_arrival :
    IsLeafIdx (Fintype.card S) (Fintype.card A) (pathIdx π (arrival π)) := by
  obtain ⟨h, -, hh⟩ := exists_isLeafIdx_pathIdx π hS hA hH
  exact Nat.sInf_mem (s := {h | IsLeafIdx (Fintype.card S) (Fintype.card A) (pathIdx π h)})
    ⟨h, hh⟩

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma arrival_lt : arrival π < H / 3 + treeDepth (Fintype.card S) (Fintype.card A) := by
  obtain ⟨h, hlt, hh⟩ := exists_isLeafIdx_pathIdx π hS hA hH
  exact (Nat.sInf_le (s := {h | IsLeafIdx (Fintype.card S) (Fintype.card A) (pathIdx π h)})
    hh).trans_lt hlt

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma pathInv_of_le_arrival {h : ℕ} (hh : h ≤ arrival π) : PathInv π h := by
  induction h with
  | zero => exact pathInv_zero π (by have := two_le_treeDepth hS hA; omega)
  | succ h ih =>
    exact pathInv_succ π hA hS (ih (by omega)) (not_isLeafIdx_of_lt_arrival π (by omega))

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma arrival_lt_H : arrival π < H := by
  have := arrival_lt π hS hA hH
  have := two_le_treeDepth hS hA
  omega

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma pathIdx_lt {h : ℕ} (hh : h ≤ arrival π) : pathIdx π h < Fintype.card S := by
  rcases pathInv_of_le_arrival π hS hA hH hh with ⟨h0, -⟩ | ⟨-, hlt, -⟩ <;> omega

end Arrival

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- The triple of the policy `π`: its arrival step, the leaf it reaches and the index of the action
it plays there. -/
noncomputable def hardTriple (π : Policy S A H) : ℕ × ℕ × ℕ :=
  (arrival π, pathIdx π (arrival π) - 3, actIdx π (arrival π) (pathIdx π (arrival π)))

/-! ### Transitions along the path -/

section Transitions

variable {β ε : ℝ} {u : Option (ℕ × ℕ × ℕ)}

omit [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma hardTransFun_absorbing (hS : 6 ≤ Fintype.card S) {i : ℕ} (hi : i = 1 ∨ i = 2) (h : ℕ)
    (a : A) : hardTransFun H β ε u h (stateAt S i) a = Measure.dirac (stateAt S i) := by
  have hlt : i < Fintype.card S := by omega
  have hleaf : ¬ IsLeafIdx (Fintype.card S) (Fintype.card A) i := by unfold IsLeafIdx; omega
  unfold hardTransFun
  simp only [sIdx_stateAt hlt, hleaf, ↓reduceIte]
  congr 2
  unfold nextIdx
  simp only [show i ≠ 0 by omega, show i < 3 by omega, ↓reduceIte]

omit [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma hardTransFun_path (π : Policy S A H) (hS : 6 ≤ Fintype.card S) (hA : 2 ≤ Fintype.card A)
    (hH : 3 * treeDepth (Fintype.card S) (Fintype.card A) ≤ H) {m : ℕ} (hm : m < arrival π) :
    hardTransFun H β ε u m (stateAt S (pathIdx π m))
        (π ⟨m, by have := arrival_lt_H π hS hA hH; omega⟩ (stateAt S (pathIdx π m)))
      = Measure.dirac (stateAt S (pathIdx π (m + 1))) := by
  have hlt := pathIdx_lt π hS hA hH hm.le
  unfold hardTransFun
  simp only [sIdx_stateAt hlt, not_isLeafIdx_of_lt_arrival π hm, ↓reduceIte]
  congr 2
  simp only [pathIdx, actIdx, show m < H by have := arrival_lt_H π hS hA hH; omega,
    ↓reduceDIte]

omit [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma hardTransFun_arrival (π : Policy S A H) (hS : 6 ≤ Fintype.card S)
    (hA : 2 ≤ Fintype.card A) (hH : 3 * treeDepth (Fintype.card S) (Fintype.card A) ≤ H) :
    hardTransFun H β ε u (arrival π) (stateAt S (pathIdx π (arrival π)))
        (π ⟨arrival π, arrival_lt_H π hS hA hH⟩ (stateAt S (pathIdx π (arrival π))))
      = bernoulliMeasure (stateAt S 1) (stateAt S 2)
          (leafProb β ε (effHorizon (Fintype.card S) (Fintype.card A) H) u (arrival π)
            (pathIdx π (arrival π)) (actIdx π (arrival π) (pathIdx π (arrival π)))) := by
  have hlt := pathIdx_lt π hS hA hH le_rfl
  unfold hardTransFun
  simp only [sIdx_stateAt hlt, isLeafIdx_pathIdx_arrival π hS hA hH, ↓reduceIte, actIdx,
    arrival_lt_H π hS hA hH, ↓reduceDIte]

end Transitions

lemma _root_.ProbabilityTheory.ae_bernoulliMeasure {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] {x y : X} (p : unitInterval) :
    ∀ᵐ z ∂bernoulliMeasure x y p, z = x ∨ z = y := by
  rw [bernoulliMeasure_def, ae_add_measure_iff]
  constructor
  · refine Measure.ae_smul_measure ?_ _
    rw [ae_dirac_eq]
    simp
  · refine Measure.ae_smul_measure ?_ _
    rw [ae_dirac_eq]
    simp

/-! ### The law of an episode -/

section Law

variable [Nonempty A] {β ε : ℝ} {u : Option (ℕ × ℕ × ℕ)}

omit [Nonempty A] in
lemma hardMDP_trans_apply (h : Fin H) (s : S) (a : A) :
    (hardMDP H β ε u).trans h (s, a) = hardTransFun H β ε u h s a := rfl

/-- In the good and bad states the sequence of states is constant. -/
lemma stateSeqLaw_hardMDP_absorbing (π : Policy S A H) (hS : 6 ≤ Fintype.card S) {i : ℕ}
    (hi : i = 1 ∨ i = 2) (h : Fin (H + 1)) :
    stateSeqLaw (hardMDP H β ε u) π h (stateAt S i) = Measure.dirac fun _ ↦ stateAt S i := by
  induction h using Fin.reverseInduction with
  | last => exact stateSeqLaw_last _ _ _
  | cast j ih =>
    rw [stateSeqLaw_castSucc, hardMDP_trans_apply, hardTransFun_absorbing hS hi,
      Measure.dirac_bind (Kernel.measurable _), Kernel.map_apply _ (measurable_seqCons _),
      stateSeqKernel_apply, ih, Measure.map_dirac' (measurable_seqCons _)]
    congr 1
    funext k
    simp [seqCons]

omit [Nonempty A] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- The sequence of states of the policy `π` when the leaf leads to `s'`. -/
noncomputable def pathSeq (π : Policy S A H) (s' : S) (m : ℕ) : S :=
  if m ≤ arrival π then stateAt S (pathIdx π m) else s'

omit [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma measurable_pathSeq_shift (π : Policy S A H) (m : ℕ) :
    Measurable fun s' k ↦ pathSeq π s' (m + k) :=
  measurable_of_countable _

/-- The success probability of the policy `π` in the instance `u`. -/
noncomputable def succProb (β ε : ℝ) (H : ℕ) (u : Option (ℕ × ℕ × ℕ)) (π : Policy S A H) :
    unitInterval :=
  leafProb β ε (effHorizon (Fintype.card S) (Fintype.card A) H) u (arrival π)
    (pathIdx π (arrival π)) (actIdx π (arrival π) (pathIdx π (arrival π)))

/-- The law of the sequence of states from the leaf reached by `π`. -/
lemma stateSeqLaw_hardMDP_arrival (π : Policy S A H) (hS : 6 ≤ Fintype.card S)
    (hA : 2 ≤ Fintype.card A) (hH : 3 * treeDepth (Fintype.card S) (Fintype.card A) ≤ H) :
    stateSeqLaw (hardMDP H β ε u) π ⟨arrival π, by have := arrival_lt_H π hS hA hH; omega⟩
        (stateAt S (pathIdx π (arrival π)))
      = (bernoulliMeasure (stateAt S 1) (stateAt S 2) (succProb β ε H u π)).map
          fun s' k ↦ pathSeq π s' (arrival π + k) := by
  have harr := arrival_lt_H π hS hA hH
  have hcs : (⟨arrival π, by omega⟩ : Fin (H + 1)) = (⟨arrival π, harr⟩ : Fin H).castSucc := rfl
  rw [hcs, stateSeqLaw_castSucc, hardMDP_trans_apply]
  change (Kernel.map (stateSeqKernel (hardMDP H β ε u) π (⟨arrival π, harr⟩ : Fin H).succ)
    (seqCons (stateAt S (pathIdx π (arrival π))))) ∘ₘ hardTransFun H β ε u (arrival π) _ _ = _
  rw [hardTransFun_arrival π hS hA hH, ← Measure.deterministic_comp_eq_map
    (measurable_pathSeq_shift π (arrival π))]
  refine Measure.comp_congr ?_
  filter_upwards [ae_bernoulliMeasure (x := stateAt S 1) (y := stateAt S 2) (succProb β ε H u π)]
    with z hz
  rw [Kernel.map_apply _ (measurable_seqCons _), stateSeqKernel_apply, Kernel.deterministic_apply]
  have hz' : ∃ i, (i = 1 ∨ i = 2) ∧ z = stateAt S i := by
    rcases hz with hz | hz
    · exact ⟨1, Or.inl rfl, hz⟩
    · exact ⟨2, Or.inr rfl, hz⟩
  obtain ⟨i, hi, rfl⟩ := hz'
  rw [show (⟨arrival π, harr⟩ : Fin H).succ = (⟨arrival π + 1, by omega⟩ : Fin (H + 1)) from rfl,
    stateSeqLaw_hardMDP_absorbing π hS hi, Measure.map_dirac' (measurable_seqCons _)]
  congr 1
  funext k
  rcases k with _ | k
  · simp [seqCons, pathSeq]
  · simp [seqCons, pathSeq]

/-- **The law of the sequence of states along the path**: from the step `m ≤ arrival π`, the
sequence of states is the path followed by the good or the bad state, the good state having
probability `succProb β ε H u π`. -/
lemma stateSeqLaw_hardMDP_path (π : Policy S A H) (hS : 6 ≤ Fintype.card S)
    (hA : 2 ≤ Fintype.card A) (hH : 3 * treeDepth (Fintype.card S) (Fintype.card A) ≤ H)
    (m : ℕ) (hm : m ≤ arrival π) :
    stateSeqLaw (hardMDP H β ε u) π ⟨m, by have := arrival_lt_H π hS hA hH; omega⟩
        (stateAt S (pathIdx π m))
      = (bernoulliMeasure (stateAt S 1) (stateAt S 2) (succProb β ε H u π)).map
          fun s' k ↦ pathSeq π s' (m + k) := by
  have harr := arrival_lt_H π hS hA hH
  obtain ⟨n, hn⟩ : ∃ n, m + n = arrival π := ⟨arrival π - m, by omega⟩
  induction n generalizing m with
  | zero =>
    obtain rfl : m = arrival π := by omega
    exact stateSeqLaw_hardMDP_arrival π hS hA hH
  | succ n ih =>
    have hmlt : m < arrival π := by omega
    have hcs : (⟨m, by omega⟩ : Fin (H + 1)) = (⟨m, by omega⟩ : Fin H).castSucc := rfl
    rw [hcs, stateSeqLaw_castSucc, hardMDP_trans_apply, hardTransFun_path π hS hA hH hmlt,
      Measure.dirac_bind (Kernel.measurable _), Kernel.map_apply _ (measurable_seqCons _),
      stateSeqKernel_apply]
    have ih' := ih (m + 1) (by omega) (by omega)
    rw [show (⟨m, by omega⟩ : Fin H).succ = (⟨m + 1, by omega⟩ : Fin (H + 1)) from rfl, ih',
      Measure.map_map (measurable_seqCons _) (measurable_pathSeq_shift π (m + 1))]
    congr 1
    funext s' k
    rcases k with _ | k
    · simp [seqCons, pathSeq, hm]
    · simp only [seqCons, Function.comp_apply, Nat.add_one_ne_zero, ↓reduceIte,
        Nat.add_sub_cancel]
      congr 1
      omega

/-- The law of the states of an episode of `π` from the waiting state. -/
lemma statesLaw_hardMDP (π : Policy S A H) (hS : 6 ≤ Fintype.card S) (hA : 2 ≤ Fintype.card A)
    (hH : 3 * treeDepth (Fintype.card S) (Fintype.card A) ≤ H) :
    statesLaw (hardMDP H β ε u) (stateAt S 0) π
      = (bernoulliMeasure (stateAt S 1) (stateAt S 2) (succProb β ε H u π)).map
          fun s' (h : Fin (H + 1)) ↦ pathSeq π s' h := by
  have h0 := stateSeqLaw_hardMDP_path (u := u) (β := β) (ε := ε) π hS hA hH 0 (Nat.zero_le _)
  rw [statesLaw_eq_map_stateSeqLaw]
  change (stateSeqLaw (hardMDP H β ε u) π ⟨0, _⟩ (stateAt S (pathIdx π 0))).map _ = _
  rw [h0, Measure.map_map (Measurable.of_eval fun _ ↦ measurable_pi_apply _)
    (measurable_pathSeq_shift π 0)]
  congr 1
  funext s' h
  simp

/-- **Divergence of one episode**: the divergence between the laws of an episode of `π` in two
hard instances is at most the binary divergence of their success probabilities. -/
lemma klDiv_statesLaw_hardMDP_le (π : Policy S A H) (hS : 6 ≤ Fintype.card S)
    (hA : 2 ≤ Fintype.card A) (hH : 3 * treeDepth (Fintype.card S) (Fintype.card A) ≤ H)
    (u u' : Option (ℕ × ℕ × ℕ)) :
    InformationTheory.klDiv (statesLaw (hardMDP H β ε u) (stateAt S 0) π)
        (statesLaw (hardMDP H β ε u') (stateAt S 0) π)
      ≤ InformationTheory.klBer (succProb β ε H u π) (succProb β ε H u' π) := by
  rw [statesLaw_hardMDP π hS hA hH, statesLaw_hardMDP π hS hA hH]
  refine (InformationTheory.klDiv_map_le _ _ (measurable_of_countable _)).trans_eq ?_
  exact InformationTheory.klDiv_bernoulliMeasure
    (fun h ↦ absurd (stateAt_injOn (by omega) (by omega) h) (by omega)) _ _

end Law

/-! ### Exponential values -/

section Values

variable [Nonempty A] {β ε : ℝ} {u : Option (ℕ × ℕ × ℕ)}

omit [Nonempty A] in
lemma integrable_exp_hardMDP (β' : ℝ) (h : Fin H) (s : S) (a : A) :
    Integrable (fun x ↦ Real.exp (β' * x)) ((hardMDP H β ε u).reward h (s, a)) :=
  integrable_exp_mul_of_rewardsIn _ β'
    (rewardsIn_of_hasRewardFn _ (hasRewardFn_hardMDP H β ε u) measurableSet_Icc
      (hardReward_mem_Icc H)) h s a

omit [Nonempty A] in
lemma vecExp_hardMDP_transVec (h : Fin H) (s : S) (a : A) (f : S → ℝ) :
    vecExp ((hardMDP H β ε u).transVec h s a) f = ∫ s', f s' ∂hardTransFun H β ε u h s a :=
  (integral_eq_vecExp_transVec _ h s a f).symm

/-- The number of rewarded steps from the step `m` in the good state. -/
def rewardCount (H rs m : ℕ) : ℕ := H - max m rs

/-- The exponential value of the good state. -/
lemma expValue_hardMDP_good (π : Policy S A H) (hS : 6 ≤ Fintype.card S) (m : Fin (H + 1)) :
    expValue (hardMDP H β ε u) β π m (stateAt S 1)
      = Real.exp (β * rewardCount H (H / 3 + treeDepth (Fintype.card S) (Fintype.card A)) m) := by
  induction m using Fin.reverseInduction with
  | last => simp [expValue_last, rewardCount]
  | cast i ih =>
    rw [expValue_castSucc _ β (integrable_exp_hardMDP β), expQ_of_hasRewardFn _ β
      (hasRewardFn_hardMDP H β ε u), vecExp_hardMDP_transVec,
      hardTransFun_absorbing hS (Or.inl rfl), integral_dirac, ih, ← Real.exp_add]
    congr 1
    simp only [hardReward, sIdx_stateAt (show 1 < Fintype.card S by omega), true_and,
      rewardCount, Fin.val_castSucc, Fin.val_succ]
    split_ifs with hrs
    · have hi := i.is_lt
      rw [max_eq_left hrs, max_eq_left (by omega), show H - (i : ℕ) = (H - ((i : ℕ) + 1)) + 1 by
        omega]
      push_cast
      ring
    · rw [max_eq_right (by omega), max_eq_right (by omega)]
      ring

/-- The exponential value of the bad state. -/
lemma expValue_hardMDP_bad (π : Policy S A H) (hS : 6 ≤ Fintype.card S) (m : Fin (H + 1)) :
    expValue (hardMDP H β ε u) β π m (stateAt S 2) = 1 := by
  induction m using Fin.reverseInduction with
  | last => exact expValue_last _ _ _ _
  | cast i ih =>
    rw [expValue_castSucc _ β (integrable_exp_hardMDP β), expQ_of_hasRewardFn _ β
      (hasRewardFn_hardMDP H β ε u), vecExp_hardMDP_transVec,
      hardTransFun_absorbing hS (Or.inr rfl), integral_dirac, ih]
    simp [hardReward, sIdx_stateAt (show 2 < Fintype.card S by omega)]

omit [Nonempty A] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma hardReward_path (π : Policy S A H) (hS : 6 ≤ Fintype.card S) (hA : 2 ≤ Fintype.card A)
    (hH : 3 * treeDepth (Fintype.card S) (Fintype.card A) ≤ H) {m : ℕ} (hm : m ≤ arrival π)
    (h : Fin H) (a : A) : hardReward H h (stateAt S (pathIdx π m)) a = 0 := by
  have hlt := pathIdx_lt π hS hA hH hm
  have hne : pathIdx π m ≠ 1 := by
    rcases pathInv_of_le_arrival π hS hA hH hm with ⟨h0, -⟩ | ⟨h3, -, -⟩ <;> omega
  simp [hardReward, sIdx_stateAt hlt, hne]

/-- **The exponential value along the path**: from the step `m ≤ arrival π`, the exponential
value of `π` is `1 + p (e^{β H'} - 1)` with `p` its success probability. -/
lemma expValue_hardMDP_path (π : Policy S A H) (hS : 6 ≤ Fintype.card S)
    (hA : 2 ≤ Fintype.card A) (hH : 3 * treeDepth (Fintype.card S) (Fintype.card A) ≤ H)
    (m : ℕ) (hm : m ≤ arrival π) :
    expValue (hardMDP H β ε u) β π ⟨m, by have := arrival_lt_H π hS hA hH; omega⟩
        (stateAt S (pathIdx π m))
      = hardZ β (effHorizon (Fintype.card S) (Fintype.card A) H) (succProb β ε H u π) := by
  have harr := arrival_lt_H π hS hA hH
  have hlt := arrival_lt π hS hA hH
  obtain ⟨n, hn⟩ : ∃ n, m + n = arrival π := ⟨arrival π - m, by omega⟩
  induction n generalizing m with
  | zero =>
    obtain rfl : m = arrival π := by omega
    have hcs : (⟨arrival π, by omega⟩ : Fin (H + 1)) = (⟨arrival π, harr⟩ : Fin H).castSucc := rfl
    rw [hcs, expValue_castSucc _ β (integrable_exp_hardMDP β), expQ_of_hasRewardFn _ β
      (hasRewardFn_hardMDP H β ε u), vecExp_hardMDP_transVec, hardReward_path π hS hA hH le_rfl,
      mul_zero, Real.exp_zero, one_mul]
    change ∫ s', expValue (hardMDP H β ε u) β π ⟨arrival π + 1, by omega⟩ s'
      ∂hardTransFun H β ε u (arrival π) _ (π ⟨arrival π, harr⟩ _) = _
    rw [hardTransFun_arrival π hS hA hH, integral_bernoulliMeasure,
      expValue_hardMDP_good π hS, expValue_hardMDP_bad π hS]
    simp only [rewardCount, hardZ, smul_eq_mul, succProb, effHorizon]
    rw [max_eq_right (by omega), Nat.sub_sub]
    ring
  | succ n ih =>
    have hmlt : m < arrival π := by omega
    have hcs : (⟨m, by omega⟩ : Fin (H + 1)) = (⟨m, by omega⟩ : Fin H).castSucc := rfl
    rw [hcs, expValue_castSucc _ β (integrable_exp_hardMDP β), expQ_of_hasRewardFn _ β
      (hasRewardFn_hardMDP H β ε u), vecExp_hardMDP_transVec, hardReward_path π hS hA hH hm,
      mul_zero, Real.exp_zero, one_mul]
    change ∫ s', expValue (hardMDP H β ε u) β π ⟨m + 1, by omega⟩ s'
      ∂hardTransFun H β ε u m _ (π ⟨m, by omega⟩ _) = _
    rw [hardTransFun_path π hS hA hH hmlt, integral_dirac]
    exact ih (m + 1) (by omega) (by omega)

/-- The exponential value of a policy from the waiting state at the first step. -/
lemma expValue_hardMDP_start (π : Policy S A H) (hS : 6 ≤ Fintype.card S)
    (hA : 2 ≤ Fintype.card A) (hH : 3 * treeDepth (Fintype.card S) (Fintype.card A) ≤ H) :
    expValue (hardMDP H β ε u) β π (startStep H) (stateAt S 0)
      = hardZ β (effHorizon (Fintype.card S) (Fintype.card A) H) (succProb β ε H u π) :=
  expValue_hardMDP_path π hS hA hH 0 (Nat.zero_le _)

end Values

/-! ### Success probabilities, triples and realizing policies -/

section Triples

variable {β ε : ℝ}

omit [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma coe_projIcc_of_mem {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ((Set.projIcc 0 1 zero_le_one x : unitInterval) : ℝ) = x := by
  rw [Set.projIcc_of_mem _ hx]

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- The success probability of a policy in the instance `u`, under Condition A. -/
lemma coe_succProb (hβ : β ≠ 0) (hε : 0 < ε)
    (hH' : 1 ≤ effHorizon (Fintype.card S) (Fintype.card A) H)
    (hcond : ConditionA β (effHorizon (Fintype.card S) (Fintype.card A) H) ε)
    (u : Option (ℕ × ℕ × ℕ)) (π : Policy S A H) :
    (succProb β ε H u π : ℝ)
      = if u = some (hardTriple π) then
          hardPPlus β (effHorizon (Fintype.card S) (Fintype.card A) H) ε
        else hardPMinus β (effHorizon (Fintype.card S) (Fintype.card A) H) := by
  obtain ⟨h0, h1, -, h3, -⟩ := hardParams_valid hβ hH' hε hcond
  unfold succProb leafProb
  rw [coe_projIcc_of_mem (by split_ifs <;> constructor <;> linarith)]
  rfl

omit [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- The triples of the hard instances: `(e + 1 + depth j, j, k)` for an exit step `e < H / 3`, a
leaf `j` and an action index `k`. -/
def hardTriples (nS nA H : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (H / 3)) ×ˢ (leafFinset (nS - 3) nA) ×ˢ (Finset.range nA)).image
    fun t ↦ (t.1 + 1 + nodeDepth nA t.2.1, t.2.1, t.2.2)

lemma card_hardTriples (nS nA H : ℕ) :
    (hardTriples nS nA H).card = H / 3 * (leafFinset (nS - 3) nA).card * nA := by
  rw [hardTriples, Finset.card_image_of_injective, Finset.card_product, Finset.card_product,
    Finset.card_range, Finset.card_range, mul_assoc]
  rintro ⟨e, j, k⟩ ⟨e', j', k'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, rfl, rfl⟩ := h
  simp only [Prod.mk.injEq, and_true]
  omega

/-- The action of index `k` (an arbitrary action if `k` is too large). -/
noncomputable def actionAt (A : Type*) [Fintype A] [Nonempty A] (k : ℕ) : A :=
  if h : k < Fintype.card A then (Fintype.equivFin A).symm ⟨k, h⟩ else Classical.arbitrary A

omit [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma aIdx_actionAt [Nonempty A] {k : ℕ} (hk : k < Fintype.card A) : aIdx (actionAt A k) = k := by
  simp [aIdx, actionAt, hk]

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- **A realizing policy exists** for every triple of `hardTriples`. -/
lemma exists_hardTriple_eq [Nonempty A] (hS : 6 ≤ Fintype.card S) (hA : 2 ≤ Fintype.card A)
    (hH : 3 * treeDepth (Fintype.card S) (Fintype.card A) ≤ H) {t : ℕ × ℕ × ℕ}
    (ht : t ∈ hardTriples (Fintype.card S) (Fintype.card A) H) :
    ∃ π : Policy S A H, hardTriple π = t := by
  simp only [hardTriples, Finset.mem_image, Finset.mem_product, Finset.mem_range] at ht
  obtain ⟨⟨e, j, k⟩, ⟨he, hj, hk⟩, rfl⟩ := ht
  have hjn : j < Fintype.card S - 3 := (Finset.mem_filter.1 hj).1 |> Finset.mem_range.1
  have hjleaf : ¬ Fintype.card A * j + 1 < Fintype.card S - 3 := (Finset.mem_filter.1 hj).2
  obtain ⟨acts, hacts, hwalk, hint⟩ := exists_walk hA hjn
  set D := nodeDepth (Fintype.card A) j with hD
  have hd := two_le_treeDepth hS hA
  have hDd : D < treeDepth (Fintype.card S) (Fintype.card A) := nodeDepth_lt_treeDepth hA hjn
  let π : Policy S A H := fun h s ↦
    if sIdx s = 0 then actionAt A (if (h : ℕ) < e then 0 else 1)
    else actionAt A (if (h : ℕ) = e + 1 + D then k else acts ((h : ℕ) - (e + 1)))
  refine ⟨π, ?_⟩
  -- the waiting phase
  have hwait : ∀ m ≤ e, pathIdx π m = 0 := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      have hmH : m < H := by omega
      simp only [pathIdx, ih (by omega), actIdx, hmH, ↓reduceDIte, nextIdx, ↓reduceIte, π,
        sIdx_stateAt (show 0 < Fintype.card S by omega), show m < e by omega,
        aIdx_actionAt (show 0 < Fintype.card A by omega), true_and,
        show m + 2 ≤ H / 3 by omega]
  -- the tree phase
  have htree : ∀ m ≤ D, pathIdx π (e + 1 + m) = treeWalk (Fintype.card S - 3) (Fintype.card A)
      acts m + 3 := by
    intro m hm
    induction m with
    | zero =>
      have heH : e < H := by omega
      simp only [pathIdx, hwait e le_rfl, actIdx, heH, ↓reduceDIte, nextIdx, ↓reduceIte,
        π, sIdx_stateAt (show 0 < Fintype.card S by omega), lt_irrefl,
        aIdx_actionAt (show 1 < Fintype.card A by omega), one_ne_zero, false_and, treeWalk]
    | succ m ih =>
      have hmD : m < D := by omega
      have hwm := hint m hmD
      have hle := Nat.le_mul_of_pos_left (treeWalk (Fintype.card S - 3) (Fintype.card A) acts m)
        (show 0 < Fintype.card A by omega)
      have hlt : treeWalk (Fintype.card S - 3) (Fintype.card A) acts m + 3 < Fintype.card S := by
        omega
      have hmH : e + 1 + m < H := by omega
      rw [show e + 1 + (m + 1) = (e + 1 + m) + 1 by omega, pathIdx, ih (by omega)]
      simp only [actIdx, hmH, ↓reduceDIte, π, sIdx_stateAt hlt,
        show treeWalk (Fintype.card S - 3) (Fintype.card A) acts m + 3 ≠ 0 by omega, ↓reduceIte,
        show e + 1 + m ≠ e + 1 + D by omega, show e + 1 + m - (e + 1) = m by omega,
        aIdx_actionAt (hacts m), nextIdx, show ¬ treeWalk (Fintype.card S - 3) (Fintype.card A)
          acts m + 3 < 3 by omega, Nat.add_sub_cancel, hwm, treeWalk]
  -- the arrival step
  have hleafD : IsLeafIdx (Fintype.card S) (Fintype.card A) (pathIdx π (e + 1 + D)) := by
    rw [htree D le_rfl, hwalk]
    exact ⟨by omega, by omega, by simpa using hjleaf⟩
  have hnot : ∀ m < e + 1 + D, ¬ IsLeafIdx (Fintype.card S) (Fintype.card A) (pathIdx π m) := by
    intro m hm hleaf
    rcases Nat.lt_or_ge m (e + 1) with h1 | h1
    · rw [hwait m (by omega)] at hleaf; exact absurd hleaf.1 (by omega)
    · obtain ⟨m', rfl⟩ : ∃ m', m = e + 1 + m' := ⟨m - (e + 1), by omega⟩
      rw [htree m' (by omega)] at hleaf
      have := hint m' (by omega)
      exact hleaf.2.2 (by simpa using this)
  have harr : arrival π = e + 1 + D := by
    refine le_antisymm (Nat.sInf_le (s := {h | IsLeafIdx (Fintype.card S) (Fintype.card A)
      (pathIdx π h)}) hleafD) ?_
    by_contra! hlt
    exact hnot _ hlt (isLeafIdx_pathIdx_arrival π hS hA hH)
  have hHD : e + 1 + D < H := by omega
  have hjS : j + 3 < Fintype.card S := by omega
  simp only [hardTriple, harr, htree D le_rfl, hwalk, Nat.add_sub_cancel, actIdx, hHD,
    ↓reduceDIte, π, sIdx_stateAt hjS, show j + 3 ≠ 0 by omega, ↓reduceIte, aIdx_actionAt hk]

end Triples

/-! ### Missing the triple is more than `ε`-suboptimal; the maximal return -/

section Optimal

variable [Nonempty A] {β ε : ℝ}

/-- **Missing the triple is more than `ε`-suboptimal** in the instance of the triple. -/
lemma lt_optEntropicValue_sub_entropicValue_hardMDP (hS : 6 ≤ Fintype.card S)
    (hA : 2 ≤ Fintype.card A) (hH : 3 * treeDepth (Fintype.card S) (Fintype.card A) ≤ H)
    (hβ : β ≠ 0) (hε : 0 < ε) (hH' : 1 ≤ effHorizon (Fintype.card S) (Fintype.card A) H)
    (hcond : ConditionA β (effHorizon (Fintype.card S) (Fintype.card A) H) ε)
    {t : ℕ × ℕ × ℕ} (ht : t ∈ hardTriples (Fintype.card S) (Fintype.card A) H)
    (π : Policy S A H) (hπ : hardTriple π ≠ t) :
    ε < optEntropicValue (hardMDP (A := A) H β ε (some t)) β (startStep H) (stateAt S 0)
      - entropicValue (hardMDP H β ε (some t)) β π (startStep H) (stateAt S 0) := by
  set M := hardMDP (S := S) (A := A) H β ε (some t)
  set H' := effHorizon (Fintype.card S) (Fintype.card A) H
  obtain ⟨hp0, hp01, -, hp1, -⟩ := hardParams_valid hβ hH' hε hcond
  have hZ : ∀ π', expValue M β π' (startStep H) (stateAt S 0)
      = hardZ β H' (if some t = some (hardTriple π') then hardPPlus β H' ε
        else hardPMinus β H') := by
    intro π'
    rw [expValue_hardMDP_start π' hS hA hH, coe_succProb hβ hε hH' hcond]
  have hZpos : ∀ π', 0 < expValue M β π' (startStep H) (stateAt S 0) :=
    fun π' ↦ expValue_pos M β (integrable_exp_hardMDP β) π' _ _
  obtain ⟨πu, hπu⟩ := exists_hardTriple_eq hS hA hH ht
  have hZu : expValue M β πu (startStep H) (stateAt S 0) = hardZ β H' (hardPPlus β H' ε) := by
    rw [hZ]
    simp [hπu]
  have hZπ : expValue M β π (startStep H) (stateAt S 0) = hardZ β H' (hardPMinus β H') := by
    have hne : t ≠ hardTriple π := fun h ↦ hπ h.symm
    rw [hZ]
    simp [hne]
  have hgap := lt_inv_mul_log_hardZ_div hβ hH' hε
  have hzp := hardZ_pos (β := β) (H' := H') (by linarith : 0 ≤ hardPPlus β H' ε) hp1.le
  have hzm := hardZ_pos (β := β) (H' := H') hp0.le (by linarith : hardPMinus β H' ≤ 1)
  have hZstar : optExpValue M β (startStep H) (stateAt S 0) = hardZ β H' (hardPPlus β H' ε) := by
    obtain ⟨π₀, hπ₀⟩ := exists_expValue_eq_optExpValue M β hβ hZpos
    rw [← hπ₀, hZ]
    split_ifs with h
    · rfl
    · exfalso
      have hZ₀ : optExpValue M β (startStep H) (stateAt S 0) = hardZ β H' (hardPMinus β H') := by
        rw [← hπ₀, hZ]
        simp only [h, ↓reduceIte]
      rcases hβ.lt_or_gt with hneg | hpos
      · have hle := optExpValue_le_expValue M β hneg (hZpos πu)
        rw [hZ₀, hZu] at hle
        have hlog : 0 ≤ Real.log (hardZ β H' (hardPPlus β H' ε) / hardZ β H' (hardPMinus β H')) :=
          Real.log_nonneg ((one_le_div hzm).2 hle)
        have : β⁻¹ * Real.log (hardZ β H' (hardPPlus β H' ε) / hardZ β H' (hardPMinus β H')) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.2 hneg.le) hlog
        linarith
      · have hle := expValue_le_optExpValue M β hpos (hZpos πu)
        rw [hZ₀, hZu] at hle
        have hlog : Real.log (hardZ β H' (hardPPlus β H' ε) / hardZ β H' (hardPMinus β H')) ≤ 0 :=
          Real.log_nonpos (by positivity) ((div_le_one hzm).2 hle)
        have : β⁻¹ * Real.log (hardZ β H' (hardPPlus β H' ε) / hardZ β H' (hardPMinus β H')) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hpos.le) hlog
        linarith
  rw [optEntropicValue_sub_entropicValue M β hβ (hZpos π), hZstar, hZπ]
  exact hgap

/-- The maximal return of the hard instances is at most the effective horizon. -/
lemma maxReturn_hardMDP_le (hS : 6 ≤ Fintype.card S) (hA : 2 ≤ Fintype.card A)
    (hH : 3 * treeDepth (Fintype.card S) (Fintype.card A) ≤ H) (u : Option (ℕ × ℕ × ℕ)) :
    maxReturn (hardMDP (A := A) H β ε u) (stateAt S 0)
      ≤ effHorizon (Fintype.card S) (Fintype.card A) H := by
  set rs := H / 3 + treeDepth (Fintype.card S) (Fintype.card A)
  have hrs : rs ≤ H := by have := two_le_treeDepth hS hA; omega
  set c : ℕ → ℝ := fun k ↦ if rs ≤ k then 1 else 0
  have hM : ∀ (k : Fin H) (s : S) (a : A), ∀ᵐ x ∂(hardMDP H β ε u).reward k (s, a),
      x ∈ Set.Icc 0 (c k) := by
    intro k s a
    rw [hasRewardFn_hardMDP H β ε u k s a]
    refine (ae_dirac_iff (p := fun x ↦ x ∈ Set.Icc 0 (c k)) measurableSet_Icc).2 ?_
    simp only [hardReward, c, Set.mem_Icc]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.2 h2
    · simp
    · simp
  have hsum : ∑ k ∈ Finset.Ico ((startStep H : Fin (H + 1)) : ℕ) H, c k
      = effHorizon (Fintype.card S) (Fintype.card A) H := by
    simp only [c, startStep, Finset.sum_boole]
    rw [show (Finset.Ico 0 H).filter (fun k ↦ rs ≤ k) = Finset.Ico rs H by
      ext k; simp; omega, Nat.card_Ico, effHorizon, Nat.sub_sub]
  refine ciSup_le fun π ↦ ?_
  have hae := ae_episodeReturn_mem_Icc_sum (hardMDP H β ε u) π hM (startStep H) (stateAt S 0)
  rw [hsum] at hae
  exact essSup_le_of_ae_le _ (hae.mono fun _ hx ↦ hx.2)
    (Filter.isCoboundedUnder_le_of_eventually_le _ (hae.mono fun _ hx ↦ hx.1))

end Optimal

end Essakine2026Tight
