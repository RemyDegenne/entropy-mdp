/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Basic
public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Vec
public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import LeanMachineLearning.SequentialLearning.IdentificationAlg

/-!
# Finite-horizon (episodic) MDPs

A finite-horizon MDP `M : EpisodicMDP S A H` is given by its transition kernels
`M.trans h : Kernel (S × A) S` and its reward kernels `M.reward h : Kernel (S × A) ℝ` (the law of
the reward of a state-action pair at step `h : Fin H`), mirroring the stationary
`Learning.MDP`. Special cases: `EpisodicMDP.ofDet trans r` (transition kernels and a
deterministic reward function `r`). The transition probabilities `M.transVec h s a`, the mean
reward `M.meanReward h s a`, the conditions `M.RewardsIn I` (rewards almost surely in `I`) and
`M.HasRewardFn r` (the rewards are the deterministic function `r`) are derived. A (deterministic,
non-stationary) policy is a `Policy S A H = Fin H → S → A`.

## Trajectory laws through the layered MDP

The finite-horizon MDP is embedded in the stationary MDP `layerMDP M : MDP (LayerState S H) A ℝ`
on the *layered* state space `LayerState S H = S × Fin (H + 1)`: from `(s, h)` with `h < H`, the
action `a` yields the reward `R ∼ M.reward h (s, a)` and the next state `(s', h + 1)` with
`s' ∼ M.trans h (s, a)`; the terminal layer `H` is absorbing with reward `0`. The law of the
trajectory of the policy `π` (as the stationary policy `π.layer` of the layered MDP) from the
layered state `p₀` is `stepLaw M π p₀`, the trajectory law of `MDP.policyAlg π.layer` in
`(layerMDP M).env (dirac p₀)`. The return of an episode is `episodeReturn H` (the sum of the
first `H` rewards) and its states are `episodeStates H`. The occupancy measure
`occupancy M π s₁ h s a = P^π(S_h = s, A_h = a)` is defined from `stepLaw`.

## Episodes as rounds

In the online interaction each round is an episode: the learner plays a policy and observes the
states `Traj S H = Fin (H + 1) → S` of the episode (the rewards being known). With a fixed
initial state `s₁`, the law of the state sequence of the episode played with `π` is
`statesKernel M s₁ π`, and `statesEnv M s₁ = stationaryEnv (statesKernel M s₁)` is the
environment (no observation, action = policy, feedback = state sequence). A best-policy
identification algorithm is an identification algorithm `BPIAlg S A H` in this environment,
with output a policy.

## Conventions

The first step is `startStep H : Fin (H + 1)` (equal to `0`, `startStep_eq_zero`), and the
kernels are built with explicit measurability lemmas rather than `Kernel.ofFunOfCountable`: the
definitions of this file are kept free of nested proofs, so that the statements built on them
can be compared across environments by `comparator`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP

namespace Learning.MDP.Episodic

variable {S A : Type*} [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] {H : ℕ}

/-- A finite-horizon MDP with horizon `H`: the transition kernels `trans h : Kernel (S × A) S`
and the reward kernels `reward h : Kernel (S × A) ℝ` at each step `h : Fin H`. -/
structure EpisodicMDP (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] (H : ℕ) where
  /-- The transition kernel at step `h`: the law of the next state. -/
  trans : Fin H → Kernel (S × A) S
  /-- The transition kernels are Markov kernels. -/
  [isMarkovKernel_trans : ∀ h, IsMarkovKernel (trans h)]
  /-- The reward kernel at step `h`: the law of the reward. -/
  reward : Fin H → Kernel (S × A) ℝ
  /-- The reward kernels are Markov kernels. -/
  [isMarkovKernel_reward : ∀ h, IsMarkovKernel (reward h)]

/-- A deterministic non-stationary policy. -/
abbrev Policy (S A : Type*) (H : ℕ) := Fin H → S → A

/-- The state sequence `s_1, …, s_{H+1}` of an episode. -/
abbrev Traj (S : Type*) (H : ℕ) := Fin (H + 1) → S

/-- The layered state space: a state together with a step index. -/
abbrev LayerState (S : Type*) (H : ℕ) := S × Fin (H + 1)

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- The first step, `0 : Fin (H + 1)` (written without the numeral, which would introduce a
nested `NeZero` proof in every definition using it). -/
def startStep (H : ℕ) : Fin (H + 1) := ⟨0, Nat.zero_lt_succ H⟩

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
@[simp] lemma startStep_eq_zero : startStep H = 0 := rfl

namespace EpisodicMDP

instance (M : EpisodicMDP S A H) (h : Fin H) : IsMarkovKernel (M.trans h) :=
  M.isMarkovKernel_trans h

instance (M : EpisodicMDP S A H) (h : Fin H) : IsMarkovKernel (M.reward h) :=
  M.isMarkovKernel_reward h

omit [Fintype S] [Fintype A] in
lemma measurable_rewardFn [Finite S] [Finite A] (r : Fin H → S → A → ℝ) (h : Fin H) :
    Measurable fun p : S × A ↦ r h p.1 p.2 :=
  measurable_of_countable _

/-- The finite-horizon MDP with transition kernels `trans h` and the deterministic reward
function `r`. -/
noncomputable def ofDet (trans : Fin H → Kernel (S × A) S) [∀ h, IsMarkovKernel (trans h)]
    (r : Fin H → S → A → ℝ) : EpisodicMDP S A H where
  trans := trans
  reward h := Kernel.deterministic (fun p ↦ r h p.1 p.2) (measurable_rewardFn r h)

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- The transition probabilities `p_h(· | s, a)` as a vector. -/
noncomputable def transVec (M : EpisodicMDP S A H) (h : Fin H) (s : S) (a : A) : S → ℝ :=
  MDP.transVec (M.trans h) (s, a)

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- The mean reward `r_h(s, a) = E[R]` at step `h`. -/
noncomputable def meanReward (M : EpisodicMDP S A H) (h : Fin H) (s : S) (a : A) : ℝ :=
  ∫ x, x ∂(M.reward h (s, a))

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- The rewards of `M` all lie almost surely in the set `I`. -/
def RewardsIn (M : EpisodicMDP S A H) (I : Set ℝ) : Prop :=
  ∀ h s a, ∀ᵐ x ∂(M.reward h (s, a)), x ∈ I

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- The rewards of `M` are the deterministic reward function `r`: the reward of `(s, a)` at step
`h` is `r h s a` almost surely. -/
def HasRewardFn (M : EpisodicMDP S A H) (r : Fin H → S → A → ℝ) : Prop :=
  ∀ h s a, M.reward h (s, a) = Measure.dirac (r h s a)

lemma hasRewardFn_ofDet (trans : Fin H → Kernel (S × A) S) [∀ h, IsMarkovKernel (trans h)]
    (r : Fin H → S → A → ℝ) : (ofDet trans r).HasRewardFn r := by
  intro h s a
  simp [ofDet, Kernel.deterministic_apply]

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
lemma meanReward_eq_of_hasRewardFn {M : EpisodicMDP S A H} {r : Fin H → S → A → ℝ}
    (hM : M.HasRewardFn r) (h : Fin H) (s : S) (a : A) : M.meanReward h s a = r h s a := by
  simp [meanReward, hM h s a]

end EpisodicMDP

/-! ### The layered MDP -/

/-- The transition function of the layered MDP: from `(s, h)` with action `a`, the next layered
state is `(s', h + 1)` with `s' ∼ M.trans h (s, a)` if `h < H`, and `(s, h)` is absorbing at the
terminal layer. -/
noncomputable def layerTransFun (M : EpisodicMDP S A H) (p : LayerState S H × A) :
    Measure (LayerState S H) :=
  if hh : (p.1.2 : ℕ) < H then
    (M.trans ⟨p.1.2, hh⟩ (p.1.1, p.2)).map fun s' ↦ (s', ⟨p.1.2 + 1, Nat.succ_lt_succ hh⟩)
  else Measure.dirac p.1

omit [Fintype S] [Fintype A] in
lemma measurable_layerTransFun [Finite S] [Finite A] (M : EpisodicMDP S A H) :
    Measurable (layerTransFun M) :=
  measurable_of_countable _

/-- The transition kernel of the layered MDP. -/
noncomputable def layerTrans (M : EpisodicMDP S A H) :
    Kernel (LayerState S H × A) (LayerState S H) :=
  ⟨layerTransFun M, measurable_layerTransFun M⟩

lemma layerTrans_apply (M : EpisodicMDP S A H) (p : LayerState S H × A) :
    layerTrans M p = layerTransFun M p := rfl

lemma isProbabilityMeasure_layerTrans (M : EpisodicMDP S A H) (p : LayerState S H × A) :
    IsProbabilityMeasure (layerTrans M p) := by
  rw [layerTrans_apply, layerTransFun]
  split_ifs <;> infer_instance

instance (M : EpisodicMDP S A H) : IsMarkovKernel (layerTrans M) :=
  ⟨isProbabilityMeasure_layerTrans M⟩

/-- The reward function of the layered MDP: `M.reward h (s, a)` at `(s, h)` with `h < H`, and the
reward `0` at the terminal layer. -/
noncomputable def layerRewardFun (M : EpisodicMDP S A H) (p : LayerState S H × A) : Measure ℝ :=
  if hh : (p.1.2 : ℕ) < H then M.reward ⟨p.1.2, hh⟩ (p.1.1, p.2) else Measure.dirac 0

omit [Fintype S] [Fintype A] in
lemma measurable_layerRewardFun [Finite S] [Finite A] (M : EpisodicMDP S A H) :
    Measurable (layerRewardFun M) :=
  measurable_of_countable _

/-- The reward kernel of the layered MDP. -/
noncomputable def layerReward (M : EpisodicMDP S A H) : Kernel (LayerState S H × A) ℝ :=
  ⟨layerRewardFun M, measurable_layerRewardFun M⟩

lemma layerReward_apply (M : EpisodicMDP S A H) (p : LayerState S H × A) :
    layerReward M p = layerRewardFun M p := rfl

lemma isProbabilityMeasure_layerReward (M : EpisodicMDP S A H) (p : LayerState S H × A) :
    IsProbabilityMeasure (layerReward M p) := by
  rw [layerReward_apply, layerRewardFun]
  split_ifs <;> infer_instance

instance (M : EpisodicMDP S A H) : IsMarkovKernel (layerReward M) :=
  ⟨isProbabilityMeasure_layerReward M⟩

/-- The stationary MDP on the layered state space which embeds the finite-horizon MDP `M`. -/
noncomputable def layerMDP (M : EpisodicMDP S A H) : MDP (LayerState S H) A ℝ where
  P := layerTrans M
  R := layerReward M

variable [Nonempty A]

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
/-- A policy of the finite-horizon MDP as a stationary policy of the layered MDP (arbitrary at
the terminal layer). -/
noncomputable def Policy.layer (π : Policy S A H) (p : LayerState S H) : A :=
  if hh : (p.2 : ℕ) < H then π ⟨p.2, hh⟩ p.1 else Classical.arbitrary A

omit [Fintype S] [Fintype A] [MeasurableSingletonClass A] in
lemma Policy.measurable_layer [Finite S] (π : Policy S A H) : Measurable π.layer :=
  measurable_of_countable _

/-- The law of the trajectory of the layered MDP under the policy `π` started at `p₀`: the law
of `(S_i, A_i, R_i)_{i ≥ h}` from the state `s` at step `h` for `p₀ = (s, h)`. -/
noncomputable def stepLaw (M : EpisodicMDP S A H) (π : Policy S A H) (p₀ : LayerState S H) :
    Measure (ℕ → Round (LayerState S H) A ℝ) :=
  (layerMDP M).policyMeasure π.layer π.measurable_layer p₀

lemma isProbabilityMeasure_stepLaw (M : EpisodicMDP S A H) (π : Policy S A H)
    (p₀ : LayerState S H) : IsProbabilityMeasure (stepLaw M π p₀) := by
  unfold stepLaw; infer_instance

instance (M : EpisodicMDP S A H) (π : Policy S A H) (p₀ : LayerState S H) :
    IsProbabilityMeasure (stepLaw M π p₀) :=
  isProbabilityMeasure_stepLaw M π p₀

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A]
  [Nonempty A] in
/-- The return `∑_{i < H} R_i` of a trajectory of the layered MDP (the rewards after the terminal
layer are `0`, so this is the return of the episode from any starting step). -/
def episodeReturn (H : ℕ) (traj : ℕ → Round (LayerState S H) A ℝ) : ℝ :=
  ∑ k ∈ range H, IT.feedback k traj

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A]
  [Nonempty A] in
lemma measurable_episodeReturn : Measurable (episodeReturn (S := S) (A := A) H) := by
  unfold episodeReturn; fun_prop

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A]
  [Nonempty A] in
/-- The states `s_1, …, s_{H+1}` of a trajectory of the layered MDP. -/
def episodeStates (H : ℕ) (traj : ℕ → Round (LayerState S H) A ℝ) : Traj S H :=
  fun h ↦ (IT.obs h traj).1

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A]
  [Nonempty A] in
lemma measurable_episodeStates : Measurable (episodeStates (S := S) (A := A) H) := by
  unfold episodeStates; fun_prop

/-- The occupancy measure `p^π_h(s, a) = P^π(S_h = s, A_h = a)` of the policy `π` from the
initial state `s₁`. -/
noncomputable def occupancy (M : EpisodicMDP S A H) (π : Policy S A H) (s₁ : S) (h : Fin H)
    (s : S) (a : A) : ℝ :=
  (stepLaw M π (s₁, startStep H)).real {traj | (IT.obs h traj).1 = s ∧ IT.action h traj = a}

/-! ### Episodes as rounds -/

variable (M : EpisodicMDP S A H)

/-- The law of the state sequence of the episode played with the policy `π` from `s₁`. -/
noncomputable def statesLaw (s₁ : S) (π : Policy S A H) : Measure (Traj S H) :=
  (stepLaw M π (s₁, startStep H)).map (episodeStates H)

lemma isProbabilityMeasure_statesLaw (s₁ : S) (π : Policy S A H) :
    IsProbabilityMeasure (statesLaw M s₁ π) := by
  unfold statesLaw; infer_instance

instance (s₁ : S) (π : Policy S A H) : IsProbabilityMeasure (statesLaw M s₁ π) :=
  isProbabilityMeasure_statesLaw M s₁ π

lemma measurable_statesLaw (s₁ : S) : Measurable (statesLaw M s₁) := measurable_of_countable _

/-- The kernel from policies to the law of the state sequence of the episode played with the
policy from `s₁`. -/
noncomputable def statesKernel (s₁ : S) : Kernel (Policy S A H) (Traj S H) :=
  ⟨statesLaw M s₁, measurable_statesLaw M s₁⟩

lemma statesKernel_apply (s₁ : S) (π : Policy S A H) : statesKernel M s₁ π = statesLaw M s₁ π :=
  rfl

lemma isProbabilityMeasure_statesKernel (s₁ : S) (π : Policy S A H) :
    IsProbabilityMeasure (statesKernel M s₁ π) :=
  isProbabilityMeasure_statesLaw M s₁ π

instance (s₁ : S) : IsMarkovKernel (statesKernel M s₁) :=
  ⟨isProbabilityMeasure_statesKernel M s₁⟩

/-- The episodic environment with the fixed initial state `s₁` in which the learner observes the
states of the episode only (the rewards being known): at each round, the learner plays a policy
and observes the states. -/
noncomputable def statesEnv (s₁ : S) : Environment Unit (Policy S A H) (Traj S H) :=
  stationaryEnv (statesKernel M s₁)

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A]
  [Nonempty A] in
/-- A best-policy identification algorithm: an identification algorithm playing a policy at each
episode, observing the states, and outputting a policy. -/
abbrev BPIAlg (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] (H : ℕ) :=
  IdentAlg Unit (Policy S A H) (Traj S H) (Policy S A H)

end Learning.MDP.Episodic
