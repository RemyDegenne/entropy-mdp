/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace
public import LeanMachineLearning.SequentialLearning.Deterministic

/-!
# Markov decision processes

A Markov decision process `M : MDP 𝓢 𝓐 𝓡` with state space `𝓢`, action space `𝓐` and reward
space `𝓡` is given by a transition kernel `M.P : Kernel (𝓢 × 𝓐) 𝓢` and a reward kernel
`M.R : Kernel (𝓢 × 𝓐) 𝓡`. Its environment `M.env μ₀` (for an initial state distribution `μ₀`)
reveals the current state as the observation of each round and returns the reward as the
feedback. A stationary deterministic policy `π : 𝓢 → 𝓐` is the algorithm `policyAlg π hπ`; its
trajectory law from the state `s` is `M.policyMeasure π hπ s`, and the law of the state-action
trajectory alone is `M.stateLaw π hπ s`. The mean reward of a real reward kernel is
`meanReward R (s, a)`.

The definitions of this file are kept free of nested proofs and of pattern matching (the
measurability facts are named lemmas, the observation kernel is defined by `Nat.rec`), so that
the statements built on them can be compared across environments by `comparator`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning

/-- Markov decision process with state space `𝓢`, action space `𝓐`, and reward space `𝓡`, described
by a transition kernel `P : Kernel (𝓢 × 𝓐) 𝓢` and a reward kernel `R : Kernel (𝓢 × 𝓐) 𝓡`.
See `MDP.env` for the environment associated with the MDP. -/
structure MDP (𝓢 𝓐 𝓡 : Type*) [MeasurableSpace 𝓢] [MeasurableSpace 𝓐] [MeasurableSpace 𝓡] where
  /-- The transition kernel: the law of the next state given the current state and action. -/
  P : Kernel (𝓢 × 𝓐) 𝓢
  /-- The transition kernel is a Markov kernel. -/
  [hP : IsMarkovKernel P]
  /-- The reward kernel: the law of the reward given the current state and action. -/
  R : Kernel (𝓢 × 𝓐) 𝓡
  /-- The reward kernel is a Markov kernel. -/
  [hR : IsMarkovKernel R]

namespace Learning.MDP

variable {𝓢 𝓐 𝓡 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} {m𝓡 : MeasurableSpace 𝓡}

instance (M : MDP 𝓢 𝓐 𝓡) : IsMarkovKernel M.P := M.hP
instance (M : MDP 𝓢 𝓐 𝓡) : IsMarkovKernel M.R := M.hR

/-! ### The environment -/

/-- The state and the action of the last round of a history of `n + 1` rounds. -/
def lastObsAction (n : ℕ) (h : Hist 𝓢 𝓐 𝓡 (n + 1)) : 𝓢 × 𝓐 :=
  ((h (Fin.last n)).obs, (h (Fin.last n)).action)

lemma measurable_lastObsAction (n : ℕ) :
    Measurable (lastObsAction (𝓢 := 𝓢) (𝓐 := 𝓐) (𝓡 := 𝓡) n) := by
  unfold lastObsAction; fun_prop

/-- The current state and the action of a round, from the history, the observation and the
action. -/
def obsAction (n : ℕ) (p : (Hist 𝓢 𝓐 𝓡 n × 𝓢) × 𝓐) : 𝓢 × 𝓐 := (p.1.2, p.2)

lemma measurable_obsAction (n : ℕ) : Measurable (obsAction (𝓢 := 𝓢) (𝓐 := 𝓐) (𝓡 := 𝓡) n) := by
  unfold obsAction; fun_prop

/-- The observation kernel of the environment of `M` with initial state distribution `μ₀`: the
initial state is drawn from `μ₀`, and the state of round `n + 1` from `M.P` applied to the state
and action of round `n`. -/
noncomputable def envObs (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) (n : ℕ) : Kernel (Hist 𝓢 𝓐 𝓡 n) 𝓢 :=
  Nat.rec (motive := fun n ↦ Kernel (Hist 𝓢 𝓐 𝓡 n) 𝓢) (Kernel.const _ μ₀)
    (fun n _ ↦ M.P.comap (lastObsAction n) (measurable_lastObsAction n)) n

@[simp]
lemma envObs_zero (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) : envObs M μ₀ 0 = Kernel.const _ μ₀ := rfl

@[simp]
lemma envObs_succ (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) (n : ℕ) :
    envObs M μ₀ (n + 1) = M.P.comap (lastObsAction n) (measurable_lastObsAction n) := rfl

lemma isMarkovKernel_envObs (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) [IsProbabilityMeasure μ₀] (n : ℕ) :
    IsMarkovKernel (envObs M μ₀ n) := by
  cases n <;> simp only [envObs_zero, envObs_succ] <;> infer_instance

instance (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) [IsProbabilityMeasure μ₀] (n : ℕ) :
    IsMarkovKernel (envObs M μ₀ n) :=
  isMarkovKernel_envObs M μ₀ n

/-- The environment of the MDP `M` with initial state distribution `μ₀`: the observation of a
round is the current state (drawn from `μ₀` at the first round, then from `M.P (s, a)` for the
state `s` and action `a` of the previous round), and the feedback is the reward, drawn from
`M.R (s, a)`. -/
protected noncomputable def env (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) [IsProbabilityMeasure μ₀] :
    Environment 𝓢 𝓐 𝓡 where
  obs := envObs M μ₀
  feedback n := M.R.comap (obsAction n) (measurable_obsAction n)

/-! ### Stationary policies and their trajectory laws -/

lemma measurable_policyAlg_next {π : 𝓢 → 𝓐} (hπ : Measurable π) (n : ℕ) :
    Measurable fun p : Hist 𝓢 𝓐 𝓡 n × 𝓢 ↦ π p.2 :=
  hπ.comp measurable_snd

-- todo: this is a generic definition of a stationary policy, not specific to MDPs.
/-- The stationary deterministic policy `π` as an algorithm: it plays `π s` in the current
state `s`. -/
noncomputable def policyAlg (π : 𝓢 → 𝓐) (hπ : Measurable π) : Algorithm 𝓢 𝓐 𝓡 :=
  detAlgorithm (fun _ p ↦ π p.2) (measurable_policyAlg_next hπ)

/-- The law of the trajectory of the policy `π` started at the state `s`: `E^π_s`. -/
noncomputable def policyMeasure (M : MDP 𝓢 𝓐 𝓡) (π : 𝓢 → 𝓐) (hπ : Measurable π) (s : 𝓢) :
    Measure (ℕ → Round 𝓢 𝓐 𝓡) :=
  trajMeasure (policyAlg π hπ) (M.env (Measure.dirac s))

lemma isProbabilityMeasure_policyMeasure (M : MDP 𝓢 𝓐 𝓡) (π : 𝓢 → 𝓐) (hπ : Measurable π)
    (s : 𝓢) : IsProbabilityMeasure (M.policyMeasure π hπ s) := by
  unfold policyMeasure; infer_instance

instance (M : MDP 𝓢 𝓐 𝓡) (π : 𝓢 → 𝓐) (hπ : Measurable π) (s : 𝓢) :
    IsProbabilityMeasure (M.policyMeasure π hπ s) :=
  isProbabilityMeasure_policyMeasure M π hπ s

/-- The law of the state-action trajectory of the policy `π` from the state `s` (no rewards). -/
noncomputable def stateLaw (M : MDP 𝓢 𝓐 𝓡) (π : 𝓢 → 𝓐) (hπ : Measurable π) (s : 𝓢) :
    Measure (ℕ → 𝓢 × 𝓐) :=
  (policyMeasure M π hπ s).map (fun h n ↦ ((h n).obs, (h n).action))

lemma isProbabilityMeasure_stateLaw (M : MDP 𝓢 𝓐 𝓡) (π : 𝓢 → 𝓐) (hπ : Measurable π) (s : 𝓢) :
    IsProbabilityMeasure (stateLaw M π hπ s) := by
  unfold stateLaw; infer_instance

instance (M : MDP 𝓢 𝓐 𝓡) (π : 𝓢 → 𝓐) (hπ : Measurable π) (s : 𝓢) :
    IsProbabilityMeasure (stateLaw M π hπ s) :=
  isProbabilityMeasure_stateLaw M π hπ s

/-! ### Mean rewards -/

variable [NormedAddCommGroup 𝓡] [NormedSpace ℝ 𝓡]

/-- The mean reward `r(s, a) = 𝔼[R (s, a)]` of a state-action pair. -/
noncomputable def meanReward (R : Kernel (𝓢 × 𝓐) 𝓡) (p : 𝓢 × 𝓐) : 𝓡 := (R p)[id]

end Learning.MDP
