# Lean design decisions (phase 1)

Decisions that are not derivable from the code, with their reasons. The mathematical deviations
from the paper are in `notes/blueprint-outline.md` (conventions and deviations list) and
`blueprint/src/content.tex`.

* **MDPs come from LML's `mdp` branch.** `Learning.MDP 𝓢 𝓐 𝓡` (transition kernel `P`, reward
  kernel `R`, environment `MDP.env M μ₀` whose observation is the current state, stationary
  policies `policyAlg`, trajectory law `policyMeasure`) is the design of the `mdp` branch of
  LML, copied into `Essakine2026Tight/LeanMachineLearning/ReinforcementLearning/MDP/Basic.lean`
  with the changes listed in `upstreaming-candidates.md` (lint fixes, `[IsProbabilityMeasure μ₀]`,
  no nested proofs). The finite-horizon MDP `EpisodicMDP`
  mirrors it (transition and reward kernels per step, independent given the state-action
  pair; the paper's rewards are deterministic) and is *embedded* in the stationary
  `layerMDP M : MDP (S × Fin (H + 1)) A ℝ`, so that `stepLaw M π (s, h)` (the law of the
  trajectory of `π` from `s` at step `h`) is an `MDP.policyMeasure` and every trajectory
  fact comes from LML's `trajMeasure`/`IsAlgEnvSeq` theory (Markov property, conditional
  laws), not from a bespoke construction.
* **`Nonempty` instances.** `MDP.env` takes `[IsProbabilityMeasure μ₀]` (the `mdp` branch's
  version replaced a non-probability `μ₀` by a Dirac mass and needed `[Nonempty 𝓢]`), so no
  statement carries a `[Nonempty S]` hypothesis (Theorem 3 has `6 ≤ card S`). `[Nonempty A]` is
  needed by `Policy.layer` (the policy at the terminal layer) and by `argmax`/`argmin`, hence by
  everything downstream.
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
  handle the two signs in one definition.
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
  lemma applications (`⟨p.1.2 + 1, Nat.succ_lt_succ hh⟩`, `⟨H - 1 - k, sub_one_sub_lt hk⟩`) and
  the first step is `startStep H = ⟨0, Nat.zero_lt_succ H⟩` rather than the numeral `0`
  (whose `NeZero (H + 1)` instance is an abstracted proof); recursions on `ℕ` (`optZ`, `cert`,
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
