# Upstreaming candidates

Material of this project written in library generality, with its intended destination. The
list grows with phase 2.

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
* `MDP/Episodic.lean`: `EpisodicMDP` (`ℕ`-indexed transition and reward kernels, mirroring
  `MDP`), unbundled policies `π : ℕ → S → A` (lemmas take `hπ : ∀ h, Measurable (π h)`), the
  `H`-step policies `Policy`, `Traj` and their extension `Policy.extend`, the time-augmented
  stationary MDP `augmented` with the stationary policy `augPolicy π`, and the total trajectory
  law `stepLaw` through `MDP.policyMeasure` (`0` for a non-measurable policy), `episodeReturn`,
  `episodeStates`, `occupancyMeasure`/`occupancy`, `statesLaw`, the episode environment
  `statesEnv` (stationary, action = policy, feedback = state sequence) and `BPIAlg`.
* `MDP/Entropic.lean`: exponential and entropic values with the horizon as an argument,
  optimal values (suprema over measurable policies), entropic variances, `maxReturn`,
  `IsEntropicPAC` (an `IdentAlg.IsPAC` over the class of MDPs with a fixed reward function).
* `MDP/Values.lean` (2026-09-17): `horizon_induction`, the exponential Bellman equation
  `expValue_succ` for bounded rewards, ranges, `expValue_congr` (the value of a policy only
  depends on its first `H` steps), the optimal Bellman recursion `optExpValueRec` and its greedy
  policy `optPolicy` attaining the supremum over all measurable policies
  (`optEntropicValue_eq`, `optExpValue_succ_eq`, `optExpQ_le_optExpValue`, …), `maxReturn` bounds.
* `MDP/StepLaw.lean`, `MDP/Occupancy.lean`, `MDP/StateSeq.lean` (2026-09-17): the Markov
  property of `stepLaw` along one step and along `k` steps (`hasLaw_stepLaw_succ`,
  `hasCondDistrib_shiftRounds_stepLaw`, `hasCondDistrib_obs_succ_hist_stepLaw`, …) on a state
  space with `MeasurableSingletonClass` only; occupancy measures and their recursion
  (`occupancyMeasure_eq_map`, `stateLawAt_succ`); the law of the state sequence
  (`stateSeqLaw_succ`, `stateSeqLaw_eq_dirac_of_absorbing`).
* `MDP/Unroll.lean`, `MDP/UnrollBounds.lean`, `MDP/EntropicVariance.lean` (2026-09-17): the
  Markov property with multiplicative weights along the trajectory
  (`integral_prod_mul_obs_succ`), the unrolling of backward recursive inequalities
  (`integral_prod_mul_le_of_backward`, `le_sum_integral_of_backward_exp`), measurability and
  bounds of the entropic variances, their Bellman recursion in integral form
  (`entropicVarQ_eq_of_hasRewardFn`) and their telescoping to the variance of the exponentiated
  return, and the Cauchy–Schwarz bound of the variance terms.
* `MDP/Empirical.lean`: `EmpiricalModel` (visit counts, reward sums, transition counts as an
  additive monoid), models of an episode and of a history of rounds.

* `MDP/Markov.lean` (phase 2, generalized 2026-09-17): the Markov property of the trajectory
  law of a stationary policy in an MDP whose state space has measurable singletons
  (`hasCondDistrib_shiftRound_trajMeasure`: the shifted trajectory has conditional law
  `policyMeasure` of the next state given the first round and the next state), the policy
  kernel `policyKernel` built with Mathlib's `Kernel.traj` from the step kernels
  (`iicStepKernel`, `Kernel.traj_congr`), the step kernels of `policyAlg` in `MDP.env`.
* `MDP/StepLaw.lean`, `MDP/Values.lean` (phase 2): the one-step law of the trajectory of a
  finite-horizon MDP (`hasLaw_stepLaw_castSucc`), terminal layer, return decomposition,
  exponential Bellman equations (Lebesgue and Bochner forms), ranges, optimal policy and optimal
  Bellman equation, value gap, maximal return; the episode-environment laws.
* `SequentialLearning/` (phase 2, copied and extended from the sister project `colt-2026-83`,
  none of it in LML `dde3322`):
  - `StoppedHistory.lean`: stopped histories and their laws;
  - `DivergenceDecomposition.lean`: chain rule of the KL divergence at a stopping time
    (`klDiv_map_hittingProcess_sigmaHistory…`, `klDiv_map_hittingValue_sigmaHistory…`) and the
    reindexing by action counts (`…_eq_sum_pullCount`);
  - `IdentificationAlg.lean`: canonical runs of an identification algorithm (`runMeasure`,
    `isRun_runMeasure`, `IsRun.comp_hasLaw`); the blueprint's `IdentAlg.isRun_canonical` does not
    exist upstream;
  - `ChangeOfMeasure.lean`: the one-sided change of measure at a stopping time
    (`IsRun.klBer_measureReal_le_sum_pullCount` and its forms with Bernoulli measures, real
    `klBerReal`, and the output law `outputMeasure` of the alternative environment).

## Mathlib (`Essakine2026Tight/Mathlib/`)

* `MeasureTheory/Measure/Weighted.lean`: `weightedMeasure p = ∑ i, ofReal (p i) • dirac i` on a
  finite type and its measurability in `p`.
* `MeasureTheory/MeasurableSpace/Sigma.lean`: `MeasurableSingletonClass (Σ i, α i)` when every
  fiber has it (next to LML's `measurableSet_sigma_iff`, itself a Mathlib candidate).
* Phase 2, chapter "Elementary inequalities": `Algebra/Order/Field/Basic.lean`
  (`two_sub_le_inv`, `sub_mul_sub_div_sq_le`), `Analysis/Real/Sqrt.lean` (`Real.sqrt_add_le`,
  weighted AM–GM `Real.sqrt_mul_le_add` and variants, `Real.le_add_sqrt_of_sq_le`),
  `Analysis/SpecialFunctions/Exp.lean` (`Real.one_add_div_pow_le_exp`),
  `Analysis/SpecialFunctions/Log/Basic.lean` (logarithmic sum bound),
  `Analysis/SpecialFunctions/Pow/Real.lean` (`Real.log_le_rpow_div_exp_one_mul`,
  `Real.log_le_of_le_mul_sq_log`), `Analysis/SpecialFunctions/Log/SelfBounding.lean` (the
  self-bounding inequality with the corrected constant), `Probability/Moments/Variance.lean`
  (`integral_mem_Icc_of_ae_mem_Icc`, normalized variance of an exponential transform).
* Phase 2: `Probability/HasCondDistrib.lean` (`hasCondDistrib_snd_compProd`,
  `HasCondDistrib.comp_hasLaw`, `HasCondDistrib.compProd_left`) and
  `Probability/CondDistrib.lean` (`HasCondDistrib.restrict_preimage`, `HasCondDistrib.of_comp_hasLaw`,
  `HasCondDistrib.comp_of_hasLaw`: the last two overlap with `HasCondDistrib.comp_hasLaw` and
  should be merged into one API before upstreaming).
* Phase 2, chapter "Change of measure" (copied and extended from the sister project):
  `Probability/Distributions/Bernoulli.lean`, `InformationTheory/KLBer.lean` (the binary
  divergence `klBer` in `[0, ∞]` and `klBerReal`, its bounds, unimodality in the second argument,
  lower semicontinuity), `InformationTheory/Pinsker.lean`, `InformationTheory/KLStoppedPrefix.lean`,
  `Probability/Process/{SigmaPrefix,HittingTime}.lean`,
  `MeasureTheory/MeasurableSpace/PiFinSuccProd.lean`.
* Phase 2, chapter "Concentration inequalities" (agent B):
  `Probability/Martingale/Ville.lean` (Ville's inequality `Supermartingale.measure_exists_ge_le`,
  the Bernoulli maximal inequality), `InformationTheory/KLBernstein.lean` (one-sided
  Donsker–Varadhan inequality `ofReal_integral_sub_log_integral_exp_le_klDiv`, KL–Bernstein,
  variance transport under a KL constraint), `InformationTheory/KullbackLeibler/Fintype.lean`
  (`toReal_klDiv_eq_sum`), `InformationTheory/MethodOfTypes.lean` (types, Sanov's bound),
  `Probability/Moments/{VarianceTransport,SelfNormalizedBernstein}.lean` (the self-normalized
  Bernstein inequality by mixtures; the last one is an LML candidate),
  `Analysis/SpecialFunctions/PoissonCramer.lean` (`Real.poissonCramer`, `Real.expSubOneSub`),
  `MeasureTheory/Measure/WeightedProbability.lean` (to be merged into `Weighted.lean`).
* Phase 2, main thread: `MDP/StateSeq.lean` (law of the state sequence of a trajectory, backward
  recursion), `MDP/EmpiricalCounts.lean` (consistent empirical models).
* Phase 2, chapter "Finite-horizon MDP theory" (agent D): Mathlib candidates
  `Probability/HasCondDistribIntegral.lean` (`HasCondDistrib.lintegral_prodMk`,
  `HasCondDistrib.integral_prodMk`, `hasCondDistrib_of_lintegral_eq`,
  `HasCondDistrib.compProd_left_of_sectR`, which generalizes `HasCondDistrib.compProd_left` of
  `Probability/HasCondDistrib.lean`: merge them), `MeasureTheory/Integral/CauchySchwarz.lean`
  (`MeasureTheory.integral_sum_mul_sqrt_mul_le`, `Real.le_sqrt_mul_sqrt_of_forall_two_mul_le`),
  and `measurable_finCons`, `measurable_finSnoc` (currently in `MDP/MarkovIter.lean`). LML
  candidates: `MDP/MarkovIter.lean` (`shiftRounds`, iterated Markov property), `MDP/Occupancy.lean`,
  `MDP/Unroll.lean`, `MDP/EntropicVariance.lean`, `MDP/Visits.lean` (episodic analogue of
  `RewardByCountMeasure` in dominated form) and the bookkeeping lemmas
  `exists_le_pullCount_iff_stepsUntil_ne_top`, `exists_pullCount_eq_iff_exists_le_pullCount`
  (for `SequentialLearning/FiniteActions.lean`).
* Phase 2, time-uniform KL concentration (agent F): `InformationTheory/KLTimeUniform.lean`
  (the Laplace-mixture supermartingale and the time-uniform bound
  `measure_exists_le_klDiv_empiricalFreq_le`), with Mathlib candidates
  `Stirling.factorial_le_exp_one_mul_sqrt_mul_div_pow` ($n! \le e\sqrt n (n/e)^n$; Mathlib only
  has the lower bound), `Nat.ascFactorial_le_factorial_mul_add_one_pow`,
  `Measure.absolutelyContinuous_of_forall_singleton`, and `measurableSet_exists_prefix`,
  `measure_exists_prefix_eq_infinitePi` (for `Probability/Independence/InfinitePi`).
* Phase 2, analysis on the good event (agent E, `EV2026/AnalysisCommon.lean`): helpers to move to
  library files after phase 2: `vecExp_sub_const`, `vecVar_sub_const`, `vecVar_const`,
  `vecExp_abs_sub_eq_of_le`, `integral_eq_vecExp_of_measureReal`,
  `variance_eq_vecVar_of_measureReal`, `sum_measureReal_eq_one` and the vector forms of
  KL–Bernstein and variance transport (`abs_vecExp_sub_le_of_klDiv_le`,
  `vecVar_le_two_mul_vecVar_add_of_klDiv_le`, `vecVar_le_mul_vecExp`) to `MDP/Vec.lean`;
  `measureReal_trans_singleton` to `MDP/Episodic.lean`; `mem_Icc_one_exp_of_pos`,
  `mem_Icc_exp_one_of_neg`, `rewardsIn_Icc_of_hasRewardFn` to `MDP/Values.lean`; `cert_sub_eq`,
  `ringZ_sub_eq`, `ringZ_zero`, `bonus_of_pos`, `bonus_of_not_pos` to `EV2026/Backups.lean`;
  `rateMin_nonneg`, `rateMin_eq_div`, `rateMin_eq_one` to `EV2026/RateBounds.lean`;
  `sqrt_le_add_of_le_sq_add_sq`, `four_mul_mul_le_sq_add` to `Mathlib/Analysis/Real/Sqrt.lean`.
* Phase 2, probabilities of the concentration events (agent G): Mathlib candidates
  `Probability/HasCondDistribCondExp.lean` (`HasCondDistrib.condExp_comap_ae_eq_integral`,
  without standard Borel assumption), `Probability/Independence/NaturalPast.lean`
  (`Filtration.naturalPast`, `iIndepFun.condExp_naturalPast_ae_eq`,
  `iIndepFun.measure_prefix_mem_eq_pi`: merge with `measure_typeCount_eq` of `MethodOfTypes.lean`
  and `measure_exists_prefix_eq_infinitePi` of `KLTimeUniform.lean`),
  `Probability/Process/FirstEntrance.lean` (first-entrance decomposition),
  `Probability/Moments/SelfNormalizedBernsteinIID.lean` (time-uniform Bernstein for i.i.d.
  sequences). LML candidates (with `MDP/Visits.lean`): `MDP/VisitConcentration.lean`
  (`condExp_visit_filtrationAction_ae_eq`, `measure_exists_pullCount_lt_le`,
  `measure_exists_le_pullCount_visitNextState_mem_le`).
* Phase 2, tail of the analysis and Theorem 4 (agent H): Mathlib candidate
  `Mathlib/Basic/Real/ENatENNReal.lean` (`ENat.toENNReal_le_ofReal_of_forall_natCast_le`); LML
  candidates `MDP/UnrollBounds.lean` (`le_exp_mul_sum_integral_of_backward`,
  `sum_integral_exp_mul_sqrt_vecVar_mul_le`, `sum_integral_exp_mul_mul_le`,
  `integrable_comp_obs_action`); for `SequentialLearning/IdentificationAlg.lean`, a lemma
  transferring a bound on `P.real bad` in one run to `outputMeasure` (done inline with
  `runMeasure`, `isRun_runMeasure`, `IsRun.hasLaw_output`), and the general pattern of
  `EV2026/TailCommon.lean` (`measureReal_bad_le`, `one_sub_le_measureReal_stoppingTime_le`: an event
  of probability at least `1 - δ` on which the algorithm stops in time and outputs a good answer
  gives PAC and a high-probability bound on the stopping time).
