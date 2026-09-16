# Upstreaming candidates

Material of this project written in library generality, with its intended destination. Phase 1
(statements) only; the list grows with phase 2.

## LML (`LeanMachineLearning/ReinforcementLearning/MDP/`)

* `MDP/Basic.lean` is the file of the `mdp` branch of LML (commit `ddfbff9`, "Merge branch
  'main' into mdp"), with the following changes, to be discussed before merging:
  - docstrings on the fields `P`, `R` of `MDP` and on `MDP.env`, and the unused instance
    argument `[IsMarkovKernel R]` of `MDP.meanReward` dropped (Mathlib linters);
  - `MDP.env M μ₀` requires `[IsProbabilityMeasure μ₀]` instead of replacing a non-probability
    `μ₀` by a Dirac mass (`open Classical in … if IsProbabilityMeasure μ₀ …`), so it no longer
    needs `[Nonempty 𝓢]`; the branch's lemma `measurable_env` (measurability of `μ₀ ↦ M.env μ₀`
    on all measures) is dropped with it. If measurability in `μ₀` is needed (random initial
    states in a Bayesian setting), the total-function design should be restored *with the
    conditional written through a named lemma* (see next item);
  - the observation kernel is `envObs M μ₀ n`, defined by `Nat.rec` (no pattern matching) with
    the measurability facts `measurable_lastObsAction`, `measurable_obsAction` and the Markov
    property `isMarkovKernel_envObs` as named lemmas, and `policyAlg` uses
    `measurable_policyAlg_next`: definitions in the closure of a `comparator` challenge must not
    contain nested proofs or matchers (their auxiliary declarations are named and deduplicated
    per module, so they differ between the project and the single-module challenge), see
    `notes/lean-design.md`.
* `MDP/Vec.lean`: `vecExp`, `vecVar`, `transVec` (expectation and variance of a function under a
  probability vector on a finite type; transition probabilities of a kernel as a vector).
* `MDP/Episodic.lean`: `EpisodicMDP` (transition and reward kernels per step, mirroring `MDP`),
  `Policy`, `Traj`, the layered stationary MDP `layerMDP` and the trajectory law `stepLaw`
  through `MDP.policyMeasure`, `episodeReturn`, `episodeStates`, `occupancy`, the episode
  environment `statesEnv` (stationary, action = policy, feedback = state sequence) and `BPIAlg`.
* `MDP/Entropic.lean`: exponential and entropic values, optimal values, entropic variances,
  `maxReturn`, `IsEntropicPAC` (an `IdentAlg.IsPAC` over the class of MDPs with a fixed reward
  function).
* `MDP/Empirical.lean`: `EmpiricalModel` (visit counts, reward sums, transition counts as an
  additive monoid), models of an episode and of a history of rounds.

## Mathlib (`Essakine2026Tight/Mathlib/`)

* `MeasureTheory/Measure/Weighted.lean`: `weightedMeasure p = ∑ i, ofReal (p i) • dirac i` on a
  finite type and its measurability in `p`.
* `MeasureTheory/MeasurableSpace/Sigma.lean`: `MeasurableSingletonClass (Σ i, α i)` when every
  fiber has it (next to LML's `measurableSet_sigma_iff`, itself a Mathlib candidate).
