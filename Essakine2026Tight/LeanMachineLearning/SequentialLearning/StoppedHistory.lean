/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.StoppedHistory
public import Essakine2026Tight.Mathlib.Probability.Process.SigmaPrefix

/-!
# Stopped histories of algorithm-environment sequences

LML (`LeanMachineLearning.SequentialLearning.StoppedHistory`) introduces the process of
histories of variable length `sigmaHistory O X Y n = ⟨n, history O X Y n⟩`, the stopping time
`hittingAfter (sigmaHistory O X Y) S 0` of a *stopping rule* `S` (a measurable set of histories
of variable length: the interaction stops after `n` rounds if the history of these `n` rounds
belongs to `S`) and the *stopped history* `stoppedValue (sigmaHistory O X Y) τ`. These are the
prefixes of the process of rounds `step O X Y` (`sigmaHistory_eq_sigmaPrefix`,
`history_eq_finPrefix`), so the layer on prefixes of a process stopped at a stopping time
(`Essakine2026Tight.Mathlib.Probability.Process.SigmaPrefix`: characterizations of the stopping
time, stopped prefixes and their truncation, laws) applies to them. This file records the
specializations used downstream:

* `hittingAfter_sigmaHistory_eq_coe_iff`, `stoppedValue_sigmaHistory_of_eq`: the stopping rule
  fires after exactly `n` rounds iff the history of the first `n` rounds belongs to `S` and no
  shorter history does, and the history stopped at a time equal to `n` is the history of the
  first `n` rounds;
* `IsAlgEnvSeq.hasCondDistrib_step_restrict_lt_hittingAfter_sigmaHistory`,
  `IsAlgEnvSeq.hasCondDistrib_obs_restrict_lt_hittingAfter_sigmaHistory`,
  `IsAlgEnvSeq.hasCondDistrib_action_restrict_lt_hittingAfter_sigmaHistory`: on the event
  `{M < τ}`, which is determined by the first `M` rounds, the step, the observation and the
  action at round `M` keep their conditional laws.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {S : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)}
  {τ : Ω → WithTop ℕ} {ω : Ω} {n : ℕ}

/-- The history of the first `n` rounds is the prefix of length `n` of the process of rounds. -/
lemma history_eq_finPrefix (n : ℕ) : history O X Y n = finPrefix (step O X Y) n := rfl

/-- The history of the first `n` rounds, as a history of variable length, is the prefix of
length `n` of the process of rounds. -/
lemma sigmaHistory_eq_sigmaPrefix : sigmaHistory O X Y = sigmaPrefix (step O X Y) := rfl

/-- The stopping rule `S` fires after exactly `n` rounds iff the history of the first `n` rounds
belongs to `S` and no history of fewer rounds does. -/
lemma hittingAfter_sigmaHistory_eq_coe_iff :
    hittingAfter (sigmaHistory O X Y) S 0 ω = n ↔
      sigmaHistory O X Y n ω ∈ S ∧ ∀ j < n, sigmaHistory O X Y j ω ∉ S :=
  hittingAfter_sigmaPrefix_eq_coe_iff (Z := step O X Y)

/-- The history stopped at a time equal to `n` is the history of the first `n` rounds. -/
lemma stoppedValue_sigmaHistory_of_eq (h : τ ω = n) :
    stoppedValue (sigmaHistory O X Y) τ ω = ⟨n, history O X Y n ω⟩ :=
  stoppedValue_sigmaPrefix_of_eq (Z := step O X Y) h

section filtration

variable {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨} {P : Measure Ω} [IsFiniteMeasure P]
  {M : ℕ}

/-- On the event `{M < τ}`, for the stopping time `τ` of the stopping rule `S`, which is
determined by the first `M` rounds, the step at round `M` keeps its conditional law given the
first `M` rounds. -/
lemma IsAlgEnvSeq.hasCondDistrib_step_restrict_lt_hittingAfter_sigmaHistory
    (h : IsAlgEnvSeq O X Y alg env P) (hS : MeasurableSet S) (M : ℕ) :
    HasCondDistrib (step O X Y M) (history O X Y M) (stepKernel alg env M)
      (P.restrict {ω | (M : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω}) :=
  (h.hasCondDistrib_step M).restrict_lt_hittingAfter_sigmaPrefix (Z := step O X Y)
    h.measurable_step (h.measurable_step M) hS

/-- On the event `{M < τ}`, for the stopping time `τ` of the stopping rule `S`, which is
determined by the first `M` rounds, the observation at round `M` keeps its conditional law
given the first `M` rounds. -/
lemma IsAlgEnvSeq.hasCondDistrib_obs_restrict_lt_hittingAfter_sigmaHistory
    (h : IsAlgEnvSeq O X Y alg env P) (hS : MeasurableSet S) (M : ℕ) :
    HasCondDistrib (O M) (history O X Y M) (env.obs M)
      (P.restrict {ω | (M : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω}) :=
  (h.hasCondDistrib_obs M).restrict_lt_hittingAfter_sigmaPrefix (Z := step O X Y)
    h.measurable_step (h.measurable_obs M) hS

/-- On the event `{M < τ}`, for the stopping time `τ` of the stopping rule `S`, which is
determined by the first `M` rounds, the action at round `M` keeps its conditional law given the
first `M` rounds and the observation at round `M`. -/
lemma IsAlgEnvSeq.hasCondDistrib_action_restrict_lt_hittingAfter_sigmaHistory
    (h : IsAlgEnvSeq O X Y alg env P) (hS : MeasurableSet S) (M : ℕ) :
    HasCondDistrib (X M) (fun ω ↦ (history O X Y M ω, O M ω)) (alg.policy M)
      (P.restrict {ω | (M : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω}) :=
  (h.hasCondDistrib_action M).restrict_lt_hittingAfter_sigmaPrefix_prodMk (Z := step O X Y)
    h.measurable_step (h.measurable_action M) (h.measurable_obs M) hS

end filtration

end Learning
