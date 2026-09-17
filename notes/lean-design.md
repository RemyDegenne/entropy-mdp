# Lean design decisions

Decisions that are not derivable from the code, with their reasons. The mathematical deviations
from the paper are in `notes/blueprint-outline.md` (conventions and deviations list) and
`blueprint/src/content.tex`. The MDP library was generalized after phase 2 (2026-09-17, see the
last section); the comparator challenges were regenerated for the new statements.

* **MDPs come from LML's `mdp` branch.** `Learning.MDP 𝓢 𝓐 𝓡` (transition kernel `P`, reward
  kernel `R`, environment `MDP.env M μ₀` whose observation is the current state, stationary
  policies `policyAlg`, trajectory law `policyMeasure`) is the design of the `mdp` branch of
  LML, copied into `Essakine2026Tight/LeanMachineLearning/ReinforcementLearning/MDP/Basic.lean`
  with the changes listed in `upstreaming-candidates.md` (lint fixes, `[IsProbabilityMeasure μ₀]`,
  no nested proofs). The finite-horizon MDP `EpisodicMDP S A`
  mirrors it (transition and reward kernels `ℕ → Kernel (S × A) _`, independent given the
  state-action pair; the paper's rewards are deterministic) and is *embedded* in the stationary
  time-augmented `M.augmented : MDP (S × ℕ) A ℝ`, so that `stepLaw M π (s, h)` (the law of the
  trajectory of the policy `π : ℕ → S → A` from `s` at step `h`) is an `MDP.policyMeasure` and every
  trajectory fact comes from LML's `trajMeasure`/`IsAlgEnvSeq` theory (Markov property,
  conditional laws), not from a bespoke construction.
* **`Nonempty` instances.** `MDP.env` takes `[IsProbabilityMeasure μ₀]` (the `mdp` branch's
  version replaced a non-probability `μ₀` by a Dirac mass and needed `[Nonempty 𝓢]`), so no
  statement carries a `[Nonempty S]` hypothesis (Theorem 3 has `6 ≤ card S`). `[Nonempty A]` is
  needed by `Policy.extend` (the action played beyond the horizon) and by `argmax`/`argmin`,
  hence by everything downstream.
* **Episodes as rounds.** The interaction of a BPI algorithm is LML's `stationaryEnv` with
  action type `Policy S A H` and feedback type `Traj S H` (states only: the rewards are known);
  `BPIAlg S A H := IdentAlg Unit (Policy S A H) (Traj S H) (Policy S A H)` (LML main's
  `IdentAlg`: `stopSet` on `Σ n, Hist n`, `output` kernel on `Σ n, Hist n`). Entropic-BPI is a
  deterministic algorithm (`detAlgorithm`) with a deterministic output kernel; the
  measurability side conditions are `measurable_of_countable` on the finite/countable history
  types (`Σ n, Hist n` is countable and gets `MeasurableSingletonClass` from
  `Essakine2026Tight/Mathlib/MeasureTheory/MeasurableSpace/Sigma.lean`).
* **PAC as a property of the algorithm.** `IsEntropicPAC 𝒜 r β ε δ s₁` is LML's
  `IdentAlg.IsPAC` (about `outputMeasure`, hence no universe parameter and no quantification
  over probability spaces) for the class `{M // M.HasRewardFn r}`: the reward function is known
  to the algorithm and fixed, the transition kernels are arbitrary. Theorem 3's hypothesis is
  PAC for the reward function of the hard instances (existentially quantified with the
  instance), the weakest hypothesis of this form; Theorem 4's two conclusions are separate
  headline theorems (PAC; the stopping-time bound for every run, via `IdentAlg.IsRun`).
* **Backward recursions by steps-to-go.** `optZ`, `cert`, `ringZ` are `ℕ`-recursions indexed
  by the number `j` of steps to the end (`j = 0` terminal), evaluated at `H - h` for the
  `0`-indexed step `h : Fin (H + 1)`; the clips at a step with `k` steps after it are
  `e^{β (k + 1)}` (the range of `U*` there) and `1`. The `if 0 < β then … else …` branches
  handle the two signs in one definition. The algorithm-level quantities keep `Fin H` /
  `Fin (H + 1)` steps (they are what the algorithm computes for the horizon `H`), while the
  library values are `ℕ`-indexed; `TailCommon.lean` bridges them with `extendFin`
  (`starRateMin`, `klRateMin`: the rate terms of a history as functions of `h : ℕ`, `0` beyond
  the horizon) when a `Fin`-indexed quantity enters the unrolling lemmas of `UnrollBounds.lean`.
* **Pseudo-counts are random** (`pseudoCount M X s₁ h s a t = ∑_{i < t} occupancy M (X i) s₁ h s a`),
  hence `eventCnt` takes the MDP and the initial state, not the measure.
* **Constants.** `lowerBound` uses `1/5000` (non-full tree), `upperBound` is the two-term
  Lemma-29 bound with absolute constants `10^9`, `10^10` in `coeffSqrt`, `coeffLin`
  (`Constants.lean`); the blueprint tracks the exact values the proofs give.
* **Comparator hygiene: no nested proofs, no matchers, no numerals needing `NeZero`.** Lean
  abstracts every non-trivial nested proof of a definition into an auxiliary theorem
  `decl._proof_i` and deduplicates identical ones *within a module*; matchers (`decl.match_1`)
  are deduplicated likewise. Comparator compares constants structurally by name, and the
  challenge is a single module while the project is many: the auxiliary names then differ
  (`optZ.match_1` vs `Learning.MDP.env.match_1`, `maxReturn._proof_1` vs
  `statesKernel._proof_3`, …) and every headline statement fails the comparison. A nested
  proof is trivial (not abstracted) only if it is an atomic term or a constant applied to
  atomic arguments. Hence, in the closure of the headline statements:
  instances are `⟨lemma …⟩`; kernels are `⟨f, measurable_f …⟩` (never `Kernel.ofFunOfCountable`,
  whose `Countable`/`MeasurableSingletonClass` instance arguments are abstracted proofs);
  measurability arguments are named lemmas applied to variables; `Fin` indices are built with
  lemma applications (`⟨H - 1 - k, sub_one_sub_lt hk⟩`), and the steps of the headline statements
  are `ℕ` numerals (`optEntropicValue M H β 0 s₁`), which need no `NeZero` instance;
  recursions on `ℕ` (`optZ`, `cert`,
  `ringZ`, `envObs`) are written with `Nat.rec` and a step function (`optZStep`, …), with the
  equations `optZ_zero`, `optZ_succ` by `rfl`; `if`s use decidable instances that are data.
  The vendored LML block (`comparator/vendor/LML.lean.part`) is the sister project's block
  (all its chunks are still verbatim in LML `dde3322`) plus `IsAlgEnvSeq`,
  `IdentAlg.stoppingTime`, `stoppedHist`, `IsRun` and the `argmax`/`argmin` declarations
  (`to_dual` expanded by hand: `Function.min := univ.inf' univ_nonempty f`,
  `argmin := (exists_argmin f).choose`, the existence lemmas sorried and listed in
  `theorem_names`). Structures with `autoParam` fields (`IsAlgEnvSeq`) are fine: their
  `_auto_1` auxiliaries are named per declaration.
* **Tool caches.** `~/.cache/entropy-mdp/{referee,comparator-tools}` are symbolic links to the
  sister project's caches (`~/.cache/colt-2026-83/…`, same toolchain `v4.34.0-rc2`).

## Generalization of the MDP library (2026-09-17)

The MDP files of `Essakine2026Tight/LeanMachineLearning/ReinforcementLearning/MDP/` were rewritten
after phase 2 so that they are library material rather than paper-shaped, and the paper files
were adapted; the headline statements changed accordingly (the comparator challenges were
regenerated, and are true to the paper: the horizon `H` is now an explicit argument of
`entropicBPI`, the reward function is `r : ℕ → S → A → ℝ`, and the values of an `H`-step policy
`π` are those of `π.extend`).

* **Steps are `ℕ`, the horizon is an argument.** `EpisodicMDP S A` has kernels
  `trans reward : ℕ → Kernel (S × A) _` and `expValue M H β π h s`, `entropicValue`,
  `optEntropicValue M H β h s`, `entropicVarQ/V`, `maxReturn M H s₁`, `statesLaw M H s₁ π`,
  `statesEnv M H s₁` take the horizon `H`; the values are trivial from the step `H` on
  (`expValue_of_le`, `entropicVarV_of_le`) and the backward inductions are `horizon_induction H`
  (the case `H ≤ h`, then the step from `h + 1` to `h < H`). The return of `n` rounds is
  `episodeReturn n` (a plain sum over `range n`), the return from the step `h` being
  `episodeReturn (H - h)`. No terminal layer, no `Fin (H + 1)` casts in the library.
* **Policies are unbundled.** A policy is a plain `π : ℕ → S → A`, like a stochastic process
  in Mathlib: it is not bundled with its measurability (an earlier `MarkovPolicy` structure was
  removed on the user's request, 2026-09-17). The definitions are total: `stepLaw M π p` is
  `M.augmented.policyMeasure (augPolicy π) (measurable_augPolicy hπ) p` when
  `hπ : ∀ h, Measurable (π h)` holds and `0` otherwise (`open Classical in … if hπ : … then …
  else 0`, as `Measure.map` of a non-measurable function; `stepLaw_of_measurable`,
  `stepLawKernel` likewise), so the values `expValue M H β π h s`, `occupancy`, `statesLaw`, …
  need no proof argument, and the lemmas take `hπ` (explicit, with `π` implicit, so a call is
  `expValue_succ M H β hM hπ hh s`). Consequences: `IsProbabilityMeasure (stepLaw M π p)` is the
  lemma `isProbabilityMeasure_stepLaw M hπ p` (and `stepLaw_univ`), used as `have := …` in
  proofs, while `IsFiniteMeasure (stepLaw M π p)`, `IsFiniteKernel (stepLawKernel M π h)` and
  `IsFiniteMeasure (occupancyMeasure …)` are unconditional instances; lemmas true for every
  finite measure (`stepLawKernel_apply`, `measurable_stepLaw`, `measurable_expValue`,
  `integral_comp_obs_action_stepLaw`, …) take no `hπ`. Auxiliary kernels built with
  `Kernel.comap` along `s ↦ (s, π h s)` take the proof, as `Kernel.comap` does
  (`policyTransKernel M hπ h`, `rewardTransKernel M hπ h`, `histTransKernel`,
  `statesTransKernel`). The suprema `optEntropicValue` and `maxReturn` are over the subtype
  `{π : ℕ → S → A // ∀ k, Measurable (π k)}`, so that the zero measure of a non-measurable
  policy never enters them (a `Nonempty` instance for the subtype is provided); both are
  bounded for bounded rewards (`bddAbove_entropicValue`, `bddAbove_essSup_episodeReturn`) and
  the supremum is attained by the greedy policy `optPolicy M H β : ℕ → S → A` of the Bellman
  recursion `optExpValueRec` (`optEntropicValue_eq`, `measurable_optPolicy`), which is where
  `[Countable S] [Finite A]` enter. The learner's `H`-step policies
  `Policy S A H := Fin H → S → A` extend by `Policy.extend` (a fixed action beyond the horizon,
  `[Nonempty A]`; injective; `Policy.measurable_extend` on a countable discrete state space;
  values only depend on the first `H` steps, `expValue_congr`).
* **Time-augmented MDP.** `M.augmented : MDP (S × ℕ) A ℝ` (kernels `augTrans`, `augReward`
  written as `⟨f, measurable_f⟩`), the stationary policy `augPolicy π : S × ℕ → A`, and
  `stepLawKernel M π h` (the same law as a kernel from the state; `stepLawKernel_apply` is a
  `rw` lemma, not `rfl`, so whnf-heavy goals rewrite it explicitly).
* **General state and action spaces.** The trajectory theory (`Markov.lean`, `StepLaw.lean`)
  only assumes `MeasurableSingletonClass` on the state space (the Markov property is proved by
  comparing sections of the joint law rather than through a measurable diagonal), and
  `policyKernel` is Mathlib's `Kernel.traj` of the step kernels (`iicStepKernel`), which gives
  its measurability for free. Almost sure equalities of actions (`ae_action_eq_stepLaw`,
  `ae_feedback_eq_stepLaw`) need `[MeasurableEq A]` (a countable discrete action space);
  action-free variants (`ae_feedback_eq_policy_stepLaw`) are provided. Bounded rewards
  (`M.RewardsIn (Set.Icc a b)`) replace both the finite-sum arguments and the exponential-moment
  hypotheses (`integrable_exp_mul_episodeReturn`, `expValue_succ`, `entropicVarV_eq_variance`);
  `RewardsIn` follows from a bounded reward function (`rewardsIn_of_hasRewardFn`).
* **Occupancies and sums as measures first.** `occupancyMeasure M π s₁ h` (the law of `(S_h, A_h)`),
  `stateLawAt`, `policyTransKernel`, `occupancyMeasure_eq_map`, `stateLawAt_succ`, and the
  unrolling lemma `integral_prod_mul_le_of_backward` with general multiplicative nonnegative
  weights and integrals `∫ s', g (h + 1) s' ∂M.trans h (s, π h s)` (the exponential weights
  `le_sum_integral_of_backward_exp`, the Bellman recursion of the variances
  `entropicVarQ_eq_of_hasRewardFn` with `variance … (M.trans h (s, a))`) are the general forms;
  the tabular `vecExp`/`vecVar` forms are corollaries under `[Fintype S]`, and the sums
  `∑ s, ∑ a, occupancy …` appear only in lemmas whose statements have sums (`Fintype` binders
  there, `Finite` elsewhere, as the `unusedFintypeInType` linter asks).
* **The paper's finiteness hypotheses** are now in the statements that need them: `[Finite S]
  [Countable A] [Nonempty A]` for the episode environment (`statesKernel` is measurable on the
  countable discrete policy type), `[Countable S] [Finite A]` for the optimal policy, `[Fintype S]
  [Fintype A]` for the tabular sums, `[Finite S] [Finite A]` for the integrability of functions
  of the state-action process (`Fintype.ofFinite` inside proofs).
