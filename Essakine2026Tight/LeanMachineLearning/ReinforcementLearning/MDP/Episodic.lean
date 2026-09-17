/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Markov
public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Vec
public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import LeanMachineLearning.SequentialLearning.IdentificationAlg

/-!
# Finite-horizon (episodic) MDPs

A finite-horizon MDP `M : EpisodicMDP S A` on measurable state and action spaces is given by its
transition kernels `M.trans h : Kernel (S × A) S` and its reward kernels
`M.reward h : Kernel (S × A) ℝ` at every step `h : ℕ`, mirroring the stationary `Learning.MDP`.
The horizon `H` of the episodes is not part of the model: an MDP with horizon `H` only uses the
kernels of the steps `h < H`, and every quantity that depends on the horizon takes it as an
argument. Special cases: `EpisodicMDP.ofDet trans r` (transition kernels and a deterministic
reward function `r`). The transition probabilities `M.transVec h s a`, the mean reward
`M.meanReward h s a`, the conditions `M.RewardsIn I` (rewards almost surely in `I`) and
`M.HasRewardFn r` (the rewards are the deterministic function `r`) are derived.

## Policies

A (deterministic, Markov) policy is a function `π : ℕ → S → A`, playing the action `π h s` at the
step `h` in the state `s`; as for stochastic processes, it is not bundled with its measurability,
and the lemmas which need it take the hypothesis `hπ : ∀ h, Measurable (π h)`. The *H-step
policies* `Policy S A H = Fin H → S → A` of a finite-horizon problem are the paper's policies;
when the action space is nonempty, `Policy.extend π` extends an `H`-step policy by a fixed action
beyond the horizon (measurable when the state space is countable and discrete).

## Trajectory laws through the time-augmented MDP

The finite-horizon MDP is embedded in the stationary MDP `M.augmented : MDP (S × ℕ) A ℝ` on the
*time-augmented* state space: from `(s, h)`, the action `a` yields the reward
`R ∼ M.reward h (s, a)` and the next state `(s', h + 1)` with `s' ∼ M.trans h (s, a)`. The law of
the trajectory of the policy `π` from the augmented state `(s, h)` is `stepLaw M π (s, h)`, the
trajectory law of the stationary policy `augPolicy π` in `M.augmented` (and `0` if `π` is not
measurable, as `Measure.map` of a non-measurable function); as a kernel from the state `s` at the
step `h` it is `stepLawKernel M π h`. The return of `n` steps of a trajectory is
`episodeReturn n` and the states of an episode of horizon `H` are `episodeStates H`. The
occupancy measure `occupancyMeasure M π s₁ h` is the law of the state-action pair at the step `h`
from `s₁`, and `occupancy M π s₁ h s a = P^π(S_h = s, A_h = a)` its mass at a pair.

## Episodes as rounds

In the online interaction each round is an episode: the learner plays an `H`-step policy and
observes the states `Traj S H = Fin (H + 1) → S` of the episode (the rewards being known). With a
fixed initial state `s₁`, the law of the state sequence of the episode played with the policy
`π` is `statesLaw M H s₁ π`, the kernel from `H`-step policies to state sequences is
`statesKernel M H s₁`, and `statesEnv M H s₁ = stationaryEnv (statesKernel M H s₁)` is the
environment (no observation, action = policy, feedback = state sequence). A best-policy
identification algorithm is an identification algorithm `BPIAlg S A H` in this environment,
with output an `H`-step policy. This part needs a finite state space and a countable action space
(so that the `H`-step policies form a countable discrete type).

## Conventions

The steps are `0`-indexed (the paper's step `h` is `h - 1`). The kernels are built with explicit
measurability lemmas, and the definitions of this file are kept free of nested proofs, so that
the statements built on them can be compared across environments by `comparator`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP

namespace Learning.MDP.Episodic

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]

/-- A finite-horizon MDP: the transition kernels `trans h : Kernel (S × A) S` and the reward
kernels `reward h : Kernel (S × A) ℝ` at each step `h : ℕ`. -/
structure EpisodicMDP (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] where
  /-- The transition kernel at step `h`: the law of the next state. -/
  trans : ℕ → Kernel (S × A) S
  /-- The transition kernels are Markov kernels. -/
  [isMarkovKernel_trans : ∀ h, IsMarkovKernel (trans h)]
  /-- The reward kernel at step `h`: the law of the reward. -/
  reward : ℕ → Kernel (S × A) ℝ
  /-- The reward kernels are Markov kernels. -/
  [isMarkovKernel_reward : ∀ h, IsMarkovKernel (reward h)]

/-! ### Policies -/

omit [MeasurableSpace S] [MeasurableSpace A] in
/-- The stationary policy of the time-augmented state space `S × ℕ` associated with the policy
`π : ℕ → S → A`: the action `π h s` at the state `(s, h)`. -/
def augPolicy (π : ℕ → S → A) (p : S × ℕ) : A := π p.2 p.1

omit [MeasurableSpace S] [MeasurableSpace A] in
@[simp] lemma augPolicy_apply (π : ℕ → S → A) (s : S) (h : ℕ) : augPolicy π (s, h) = π h s := rfl

lemma measurable_augPolicy {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) :
    Measurable (augPolicy π) :=
  measurable_from_prod_countable_left hπ

/-- A deterministic `H`-step policy: the action `π h s` played at the step `h : Fin H` in the
state `s`. -/
abbrev Policy (S A : Type*) (H : ℕ) := Fin H → S → A

/-- The state sequence `s_0, …, s_H` of an episode of horizon `H`. -/
abbrev Traj (S : Type*) (H : ℕ) := Fin (H + 1) → S

instance [Nonempty A] : Nonempty {π : ℕ → S → A // ∀ h, Measurable (π h)} :=
  ⟨⟨fun _ _ ↦ Classical.arbitrary A, fun _ ↦ measurable_const⟩⟩

section Extend

variable [Nonempty A] {H : ℕ}

omit [MeasurableSpace S] [MeasurableSpace A] in
/-- The `H`-step policy `π` extended to all steps by a fixed action beyond the horizon. -/
noncomputable def Policy.extend (π : Policy S A H) (h : ℕ) (s : S) : A :=
  if hh : h < H then π ⟨h, hh⟩ s else Classical.arbitrary A

omit [MeasurableSpace S] [MeasurableSpace A] in
@[simp] lemma Policy.extend_of_lt (π : Policy S A H) {h : ℕ} (hh : h < H) (s : S) :
    π.extend h s = π ⟨h, hh⟩ s := by
  simp [Policy.extend, hh]

omit [MeasurableSpace S] [MeasurableSpace A] in
lemma Policy.extend_fin (π : Policy S A H) (h : Fin H) (s : S) :
    π.extend h s = π h s := by
  simp [Policy.extend, h.2]

omit [MeasurableSpace S] [MeasurableSpace A] in
@[simp] lemma Policy.extend_of_le (π : Policy S A H) {h : ℕ} (hh : H ≤ h) (s : S) :
    π.extend h s = Classical.arbitrary A := by
  simp [Policy.extend, not_lt.2 hh]

omit [MeasurableSpace S] [MeasurableSpace A] in
lemma Policy.extend_injective : Function.Injective (Policy.extend : Policy S A H → ℕ → S → A) := by
  intro π π' h
  funext k s
  rw [← π.extend_fin k s, ← π'.extend_fin k s, h]

lemma Policy.measurable_extend [Countable S] [MeasurableSingletonClass S] (π : Policy S A H)
    (h : ℕ) : Measurable (π.extend h) :=
  measurable_of_countable _

end Extend

/-! ### Derived objects of a finite-horizon MDP -/

namespace EpisodicMDP

variable (M : EpisodicMDP S A)

instance (h : ℕ) : IsMarkovKernel (M.trans h) := M.isMarkovKernel_trans h

instance (h : ℕ) : IsMarkovKernel (M.reward h) := M.isMarkovKernel_reward h

/-- The finite-horizon MDP with transition kernels `trans h` and the deterministic reward
function `r` (measurable in the state-action pair at every step). -/
noncomputable def ofDet (trans : ℕ → Kernel (S × A) S) [∀ h, IsMarkovKernel (trans h)]
    (r : ℕ → S → A → ℝ) (hr : ∀ h, Measurable fun p : S × A ↦ r h p.1 p.2) :
    EpisodicMDP S A where
  trans := trans
  reward h := Kernel.deterministic (fun p ↦ r h p.1 p.2) (hr h)

/-- Every function on a countable discrete state-action space is a measurable reward
function. -/
lemma measurable_rewardFn [Countable S] [Countable A] [MeasurableSingletonClass S]
    [MeasurableSingletonClass A] (r : ℕ → S → A → ℝ) (h : ℕ) :
    Measurable fun p : S × A ↦ r h p.1 p.2 :=
  measurable_of_countable _

/-- The transition probabilities `p_h(· | s, a)` as a vector. -/
noncomputable def transVec (h : ℕ) (s : S) (a : A) : S → ℝ := MDP.transVec (M.trans h) (s, a)

lemma transVec_nonneg (h : ℕ) (s : S) (a : A) (s' : S) : 0 ≤ M.transVec h s a s' :=
  MDP.transVec_nonneg _ _ _

/-- The transition probabilities `p_h(· | s, a)` form a probability vector. -/
lemma sum_transVec [Fintype S] [MeasurableSingletonClass S] (h : ℕ) (s : S) (a : A) :
    ∑ s', M.transVec h s a s' = 1 :=
  MDP.sum_transVec _ _

/-- The mean reward `r_h(s, a) = E[R]` at step `h`. -/
noncomputable def meanReward (h : ℕ) (s : S) (a : A) : ℝ := ∫ x, x ∂(M.reward h (s, a))

/-- The rewards of `M` all lie almost surely in the set `I`. -/
def RewardsIn (I : Set ℝ) : Prop := ∀ h s a, ∀ᵐ x ∂(M.reward h (s, a)), x ∈ I

/-- The rewards of `M` are the deterministic reward function `r`: the reward of `(s, a)` at step
`h` is `r h s a` almost surely. -/
def HasRewardFn (r : ℕ → S → A → ℝ) : Prop := ∀ h s a, M.reward h (s, a) = Measure.dirac (r h s a)

lemma hasRewardFn_ofDet (trans : ℕ → Kernel (S × A) S) [∀ h, IsMarkovKernel (trans h)]
    (r : ℕ → S → A → ℝ) (hr : ∀ h, Measurable fun p : S × A ↦ r h p.1 p.2) :
    (ofDet trans r hr).HasRewardFn r := by
  intro h s a
  simp [ofDet, Kernel.deterministic_apply]

lemma meanReward_eq_of_hasRewardFn {r : ℕ → S → A → ℝ} (hM : M.HasRewardFn r) (h : ℕ) (s : S)
    (a : A) : M.meanReward h s a = r h s a := by
  simp [meanReward, hM h s a]

/-! ### The time-augmented MDP -/

/-- The transition function of the time-augmented MDP: from `(s, h)` with action `a`, the next
augmented state is `(s', h + 1)` with `s' ∼ M.trans h (s, a)`. -/
noncomputable def augTransFun (p : (S × ℕ) × A) : Measure (S × ℕ) :=
  (M.trans p.1.2 (p.1.1, p.2)).map fun s' ↦ (s', p.1.2 + 1)

lemma measurable_augTransFun : Measurable M.augTransFun := by
  have h : Measurable fun q : (S × A) × ℕ ↦ (M.trans q.2 q.1).map fun s' ↦ (s', q.2 + 1) := by
    refine measurable_from_prod_countable_left fun h ↦ ?_
    have hm := ((M.trans h).map fun s' : S ↦ (s', h + 1)).measurable
    have heq : (⇑((M.trans h).map fun s' : S ↦ (s', h + 1)))
        = fun q ↦ (M.trans h q).map fun s' ↦ (s', h + 1) :=
      funext fun q ↦ Kernel.map_apply _ measurable_prodMk_right q
    rwa [heq] at hm
  exact h.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

/-- The transition kernel of the time-augmented MDP. -/
noncomputable def augTrans : Kernel ((S × ℕ) × A) (S × ℕ) :=
  ⟨M.augTransFun, M.measurable_augTransFun⟩

lemma augTrans_apply (p : (S × ℕ) × A) :
    M.augTrans p = (M.trans p.1.2 (p.1.1, p.2)).map fun s' ↦ (s', p.1.2 + 1) := rfl

lemma isProbabilityMeasure_augTrans (p : (S × ℕ) × A) : IsProbabilityMeasure (M.augTrans p) := by
  rw [augTrans_apply]; infer_instance

instance : IsMarkovKernel M.augTrans := ⟨M.isProbabilityMeasure_augTrans⟩

/-- The reward function of the time-augmented MDP: `M.reward h (s, a)` at `(s, h)`. -/
noncomputable def augRewardFun (p : (S × ℕ) × A) : Measure ℝ := M.reward p.1.2 (p.1.1, p.2)

lemma measurable_augRewardFun : Measurable M.augRewardFun := by
  have h : Measurable fun q : (S × A) × ℕ ↦ M.reward q.2 q.1 :=
    measurable_from_prod_countable_left fun h ↦ (M.reward h).measurable
  exact h.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

/-- The reward kernel of the time-augmented MDP. -/
noncomputable def augReward : Kernel ((S × ℕ) × A) ℝ :=
  ⟨M.augRewardFun, M.measurable_augRewardFun⟩

lemma augReward_apply (p : (S × ℕ) × A) : M.augReward p = M.reward p.1.2 (p.1.1, p.2) := rfl

lemma isProbabilityMeasure_augReward (p : (S × ℕ) × A) :
    IsProbabilityMeasure (M.augReward p) := by
  rw [augReward_apply]; infer_instance

instance : IsMarkovKernel M.augReward := ⟨M.isProbabilityMeasure_augReward⟩

/-- The stationary MDP on the time-augmented state space `S × ℕ` which embeds the finite-horizon
MDP `M`. -/
noncomputable def augmented : MDP (S × ℕ) A ℝ where
  P := M.augTrans
  R := M.augReward

@[simp] lemma augmented_P : M.augmented.P = M.augTrans := rfl

@[simp] lemma augmented_R : M.augmented.R = M.augReward := rfl

end EpisodicMDP

/-! ### Trajectory laws -/

open Classical in
/-- The law of the trajectory of the time-augmented MDP under the policy `π` started at the
augmented state `p₀ = (s, h)`: the law of `((S_{h+k}, h + k), A_{h+k}, R_{h+k})_{k ≥ 0}` from the
state `s` at the step `h`. It is `0` if `π` is not measurable at every step. -/
noncomputable def stepLaw (M : EpisodicMDP S A) (π : ℕ → S → A) (p₀ : S × ℕ) :
    Measure (ℕ → Round (S × ℕ) A ℝ) :=
  if hπ : ∀ k, Measurable (π k) then
    M.augmented.policyMeasure (augPolicy π) (measurable_augPolicy hπ) p₀
  else 0

section StepLaw

variable (M : EpisodicMDP S A) {π : ℕ → S → A}

lemma stepLaw_of_measurable (hπ : ∀ h, Measurable (π h)) (p₀ : S × ℕ) :
    stepLaw M π p₀ = M.augmented.policyMeasure (augPolicy π) (measurable_augPolicy hπ) p₀ := by
  rw [stepLaw, dite_eq_left hπ]

lemma stepLaw_of_not_measurable (hπ : ¬ ∀ h, Measurable (π h)) (p₀ : S × ℕ) :
    stepLaw M π p₀ = 0 := by
  rw [stepLaw, dite_eq_right hπ]

lemma isProbabilityMeasure_stepLaw (hπ : ∀ h, Measurable (π h)) (p₀ : S × ℕ) :
    IsProbabilityMeasure (stepLaw M π p₀) := by
  rw [stepLaw_of_measurable M hπ]
  exact isProbabilityMeasure_policyMeasure _ _ _ _

lemma stepLaw_univ (hπ : ∀ h, Measurable (π h)) (p₀ : S × ℕ) :
    stepLaw M π p₀ Set.univ = 1 :=
  (isProbabilityMeasure_stepLaw M hπ p₀).measure_univ

lemma isFiniteMeasure_stepLaw (π : ℕ → S → A) (p₀ : S × ℕ) :
    IsFiniteMeasure (stepLaw M π p₀) := by
  by_cases hπ : ∀ h, Measurable (π h)
  · have := isProbabilityMeasure_stepLaw M hπ p₀
    infer_instance
  · rw [stepLaw_of_not_measurable M hπ]
    infer_instance

instance (π : ℕ → S → A) (p₀ : S × ℕ) : IsFiniteMeasure (stepLaw M π p₀) :=
  isFiniteMeasure_stepLaw M π p₀

end StepLaw

open Classical in
/-- The trajectory law from the step `h` as a kernel from the state (`0` if `π` is not
measurable at every step). -/
noncomputable def stepLawKernel (M : EpisodicMDP S A) (π : ℕ → S → A) (h : ℕ) :
    Kernel S (ℕ → Round (S × ℕ) A ℝ) :=
  if hπ : ∀ k, Measurable (π k) then
    (policyKernel M.augmented (measurable_augPolicy hπ)).comap (fun s ↦ (s, h))
      measurable_prodMk_right
  else 0

@[simp] lemma stepLawKernel_apply (M : EpisodicMDP S A) (π : ℕ → S → A) (h : ℕ) (s : S) :
    stepLawKernel M π h s = stepLaw M π (s, h) := by
  by_cases hπ : ∀ k, Measurable (π k)
  · rw [stepLawKernel, dite_eq_left hπ, Kernel.comap_apply, policyKernel_apply,
      stepLaw_of_measurable M hπ]
  · rw [stepLawKernel, dite_eq_right hπ, stepLaw_of_not_measurable M hπ]
    rfl

lemma isMarkovKernel_stepLawKernel (M : EpisodicMDP S A) {π : ℕ → S → A}
    (hπ : ∀ h, Measurable (π h)) (h : ℕ) : IsMarkovKernel (stepLawKernel M π h) :=
  ⟨fun s ↦ by rw [stepLawKernel_apply]; exact isProbabilityMeasure_stepLaw M hπ _⟩

instance isFiniteKernel_stepLawKernel (M : EpisodicMDP S A) (π : ℕ → S → A) (h : ℕ) :
    IsFiniteKernel (stepLawKernel M π h) := by
  by_cases hπ : ∀ k, Measurable (π k)
  · have := isMarkovKernel_stepLawKernel M hπ h
    infer_instance
  · rw [stepLawKernel, dite_eq_right hπ]
    infer_instance

/-- The trajectory law from the step `h` is a measurable function of the state. -/
lemma measurable_stepLaw (M : EpisodicMDP S A) (π : ℕ → S → A) (h : ℕ) :
    Measurable fun s ↦ stepLaw M π (s, h) := by
  have : (fun s ↦ stepLaw M π (s, h)) = stepLawKernel M π h := funext fun s ↦ by simp
  rw [this]; exact (stepLawKernel M π h).measurable

omit [MeasurableSpace S] [MeasurableSpace A] in
/-- The return `∑_{k < n} R_k` of the first `n` rounds of a trajectory of the time-augmented
MDP. -/
def episodeReturn (n : ℕ) (traj : ℕ → Round (S × ℕ) A ℝ) : ℝ :=
  ∑ k ∈ range n, IT.feedback k traj

lemma measurable_episodeReturn (n : ℕ) : Measurable (episodeReturn (S := S) (A := A) n) := by
  unfold episodeReturn; fun_prop

omit [MeasurableSpace S] [MeasurableSpace A] in
@[simp] lemma episodeReturn_zero (traj : ℕ → Round (S × ℕ) A ℝ) : episodeReturn 0 traj = 0 := by
  simp [episodeReturn]

omit [MeasurableSpace S] [MeasurableSpace A] in
lemma episodeReturn_succ (n : ℕ) (traj : ℕ → Round (S × ℕ) A ℝ) :
    episodeReturn (n + 1) traj = episodeReturn n traj + IT.feedback n traj :=
  sum_range_succ _ _

omit [MeasurableSpace S] [MeasurableSpace A] in
/-- The return of `n + 1` rounds is the first reward plus the return of the shifted trajectory. -/
lemma episodeReturn_succ_eq_add_shiftRound (n : ℕ) (traj : ℕ → Round (S × ℕ) A ℝ) :
    episodeReturn (n + 1) traj = IT.feedback 0 traj + episodeReturn n (shiftRound traj) := by
  rw [episodeReturn, episodeReturn, sum_range_succ', add_comm]
  rfl

omit [MeasurableSpace S] [MeasurableSpace A] in
/-- The states `s_0, …, s_H` of a trajectory of the time-augmented MDP. -/
def episodeStates (H : ℕ) (traj : ℕ → Round (S × ℕ) A ℝ) : Traj S H :=
  fun h ↦ (IT.obs h traj).1

lemma measurable_episodeStates (H : ℕ) :
    Measurable (episodeStates (S := S) (A := A) H) := by
  unfold episodeStates; fun_prop

omit [MeasurableSpace S] [MeasurableSpace A] in
@[simp] lemma episodeStates_apply (H : ℕ) (traj : ℕ → Round (S × ℕ) A ℝ) (h : Fin (H + 1)) :
    episodeStates H traj h = (IT.obs h traj).1 := rfl

omit [MeasurableSpace S] [MeasurableSpace A] in
/-- The state and the action of the round `h` of a trajectory of the time-augmented MDP. -/
def stateAction (h : ℕ) (traj : ℕ → Round (S × ℕ) A ℝ) : S × A :=
  ((IT.obs h traj).1, IT.action h traj)

lemma measurable_stateAction (h : ℕ) : Measurable (stateAction (S := S) (A := A) h) := by
  unfold stateAction; fun_prop

/-- The occupancy measure at the step `h` of the policy `π` from the initial state `s₁`: the law
of the state-action pair `(S_h, A_h)`. -/
noncomputable def occupancyMeasure (M : EpisodicMDP S A) (π : ℕ → S → A) (s₁ : S)
    (h : ℕ) : Measure (S × A) :=
  (stepLaw M π (s₁, 0)).map (stateAction h)

instance (M : EpisodicMDP S A) (π : ℕ → S → A) (s₁ : S) (h : ℕ) :
    IsFiniteMeasure (occupancyMeasure M π s₁ h) := by
  unfold occupancyMeasure; infer_instance

/-- The occupancy `p^π_h(s, a) = P^π(S_h = s, A_h = a)` of the policy `π` from the initial state
`s₁`. -/
noncomputable def occupancy (M : EpisodicMDP S A) (π : ℕ → S → A) (s₁ : S) (h : ℕ) (s : S)
    (a : A) : ℝ :=
  (occupancyMeasure M π s₁ h).real {(s, a)}

/-! ### Episodes as rounds -/

section EpisodeEnv

variable (M : EpisodicMDP S A) (H : ℕ)

/-- The law of the state sequence of the episode of horizon `H` played with the policy `π`
from `s₁`. -/
noncomputable def statesLaw (s₁ : S) (π : ℕ → S → A) : Measure (Traj S H) :=
  (stepLaw M π (s₁, 0)).map (episodeStates H)

lemma isProbabilityMeasure_statesLaw (s₁ : S) {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) :
    IsProbabilityMeasure (statesLaw M H s₁ π) := by
  have := isProbabilityMeasure_stepLaw M hπ (s₁, 0)
  unfold statesLaw; infer_instance

variable [Finite S] [Countable A] [MeasurableSingletonClass S] [MeasurableSingletonClass A]
  [Nonempty A]

omit [MeasurableSingletonClass S] in
lemma measurable_statesLaw_extend (s₁ : S) :
    Measurable fun π : Policy S A H ↦ statesLaw M H s₁ π.extend :=
  measurable_of_countable _

/-- The kernel from `H`-step policies to the law of the state sequence of the episode played with
the policy from `s₁`. -/
noncomputable def statesKernel (s₁ : S) : Kernel (Policy S A H) (Traj S H) :=
  ⟨fun π ↦ statesLaw M H s₁ π.extend, measurable_statesLaw_extend M H s₁⟩

omit [MeasurableSingletonClass S] in
lemma statesKernel_apply (s₁ : S) (π : Policy S A H) :
    statesKernel M H s₁ π = statesLaw M H s₁ π.extend :=
  rfl

lemma isProbabilityMeasure_statesKernel (s₁ : S) (π : Policy S A H) :
    IsProbabilityMeasure (statesKernel M H s₁ π) :=
  isProbabilityMeasure_statesLaw M H s₁ π.measurable_extend

instance (s₁ : S) : IsMarkovKernel (statesKernel M H s₁) :=
  ⟨isProbabilityMeasure_statesKernel M H s₁⟩

/-- The episodic environment with horizon `H` and the fixed initial state `s₁`, in which the
learner observes the states of the episode only (the rewards being known): at each round, the
learner plays an `H`-step policy and observes the states. -/
noncomputable def statesEnv (s₁ : S) : Environment Unit (Policy S A H) (Traj S H) :=
  stationaryEnv (statesKernel M H s₁)

end EpisodeEnv

omit [MeasurableSpace S] [MeasurableSpace A] in
/-- A best-policy identification algorithm: an identification algorithm playing an `H`-step
policy at each episode, observing the states, and outputting an `H`-step policy. -/
abbrev BPIAlg (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] (H : ℕ) :=
  IdentAlg Unit (Policy S A H) (Traj S H) (Policy S A H)

end Learning.MDP.Episodic
