# Phase 2 plan: proofs, blueprint-driven

Written 2026-09-16, after the first phase-2 chapter (`chap:pre_analysis`) was proved. This file
is the work breakdown for the remaining chapters and the briefs handed to the agents that work
on them in parallel. Every item refers to the labels of `blueprint/src/chapters/*.tex`.

## Status

**Phase 2 complete (2026-09-16): no `sorry` left; the three headline theorems use only the standard axioms.**

| Chapter | Labels | Status |
|---|---|---|
| `chap:pre_analysis` (elementary inequalities) | 16 lemmas | **done**: 7 files under `Essakine2026Tight/Mathlib/`, all `\leanok` |
| `chap:mdp` (model) | 10 lemmas | **done** (main thread): `MDP/{Markov,StepLaw,Values}.lean` |
| `chap:pre_concentration` | ~20 lemmas, 3 theorems | **done** (agent B) |
| `chap:pre_info` (change of measure) | 12 lemmas, 1 theorem | **done** (agent C) |
| `chap:pre_mdp` (finite-horizon MDP theory) | 15 lemmas | **done** (agent D) |
| `chap:empirical` (concentration events) | 8 lemmas | `lem:empirical_kl_time_uniform` **done** (agent F); `lem:rates_props` **done** (main thread); event probabilities **done** (agent G, `EV2026/Events.lean`) |
| `chap:algorithm` (backups, certificate, runs) | 3 lemmas | **done** (main thread): `EV2026/{Backups,EntropicBPIRun}.lean` |
| `chap:analysis_pos`, `chap:analysis_neg` | ~30 lemmas | **done**: good-event part (agent E, `EV2026/Analysis{Common,Pos,Neg}.lean`), tail (agent H, `EV2026/Tail{Common,Pos,Neg}.lean`) |
| `chap:sample_complexity` | ~10 lemmas + Theorem 4 | rate lemmas and Lemmas 27–28 **done** (main thread, `EV2026/RateBounds.lean`); Theorem 4 **done** (agent H) |
| `chap:lower_bound` | ~20 lemmas + Theorem 3 | **done** (main thread): Theorem 3 proved, `EV2026/{HardTree,HardParams,HardMDP,LowerBound}.lean` |

Dependency order: `chap:mdp` → {`chap:pre_mdp`, `chap:algorithm`} → `chap:empirical` (also needs
`chap:pre_concentration`) → analysis chapters → `chap:sample_complexity`;
`chap:pre_info` + `chap:mdp` → `chap:lower_bound`. The three prerequisite chapters B, C, D are
independent of each other; D needs the lemmas of `chap:mdp`.

## Standing rules for every agent

These are the rules of the `/formalize-paper` skill and of this repository; the agent's brief is
its only context, so they are repeated here.

* **Read first**: the blueprint chapter (its statements are the contract; its proofs are
  complete sketches naming Mathlib/LML lemmas), `notes/lean-design.md`, the existing Lean files
  named in the brief, and `~/.claude/skills/formalize-paper/tools.md` (gotchas). The paper is
  `source/colt_main_draft.tex`; the blueprint corrects it, follow the blueprint.
* **API lookup**: grep the pinned Mathlib and LML in `.lake/packages/mathlib` and
  `.lake/packages/LeanMachineLearning` (LML main `dde3322`; Mathlib `217ba069`; toolchain
  `v4.34.0-rc2`). Try statements in a scratch file compiled with `lake env lean File.lean`
  (in the scratchpad directory, never in the project tree).
* **File shape**: copyright header, `module`, `public import …`, module docstring,
  `@[expose] public section`, docstrings on every declaration, `lemma` for everything except
  the big classical theorems named `theorem` in the blueprint. Library-shaped material goes
  under `Essakine2026Tight/Mathlib/<Mathlib path>` or
  `Essakine2026Tight/LeanMachineLearning/<LML path>`, mirroring the upstream layout; nothing
  paper-specific there. Prove the general statement and derive the paper's form as a
  specialization. Laws are `HasLaw`/`HasCondDistrib`, not `Measure.map` equations.
* **Comparator hygiene** (only for *definitions* that end up in the closure of a headline
  statement, see `notes/lean-design.md`): no nested proofs, no `match`, no real numeral `≥ 2`,
  instances as `⟨lemma⟩`, kernels as `⟨f, measurable_f⟩`. Lemmas are unconstrained.
* **Build**: `lake build <Module.Name>` for the file being written (concurrent `lake build`
  invocations from several agents are fine), then, when the chapter is done,
  `lake exe mk_all --lib Essakine2026Tight` (regenerates the root module), `lake build
  Essakine2026Tight` (the only warnings allowed are the two `sorry` of Theorem 4 in `EV2026/UpperBound.lean`; Theorem 3 is proved)
  and `lake exe runLinter Essakine2026Tight` (fix everything it reports). Never `pkill -f`;
  long runs detached with `setsid nohup … &`.
* **No `sorry` in the deliverable.** If a lemma resists, leave it `sorry`-ed only as a last
  resort, and list every such declaration in the final report with what is missing; do not
  mark its proof `\leanok`.
* **Blueprint sync, in the chapter file only**: when a declaration compiles, add
  `\lean{Full.Name}` (several names comma-separated are allowed) and `\leanok` to the
  statement; add `\leanok` as the first line of the proof when the proof is complete;
  adjust the statement text to what Lean proves (dropped hypotheses, changed constants,
  indexing) and say so in a `\textbf{Lean remark.}`; keep every existing `\label` (other
  chapters `\uses` them); new auxiliary lemmas get new labels prefixed by the chapter's short
  name (`pconc_`, `pinfo_`, `pmdp_`). Run `python3 scripts/check-blueprint.py` (must print
  `OK`). Do not run `leanblueprint` (the main thread builds the PDF/web centrally).
* **Do not edit** `notes/paper-errata.md`, `formalization.yaml`, `README.md`,
  `notes/lean-design.md`, `notes/upstreaming-candidates.md`, other chapters' `.tex` files, or
  Lean files outside the brief's scope; report what those files should say instead. Never
  commit.
* **Final report** (the only thing the main thread sees): the list of files written, the list
  of blueprint labels now `\leanok` (statement and proof), every remaining `sorry`, every
  deviation from the blueprint statement (and why), findings about the paper or the blueprint
  (errors, slack in constants, unused hypotheses), Mathlib/LML lemmas that were missing or
  misnamed in the blueprint, and the exact commands run last with their results.

## Brief B: `chap:pre_concentration` (concentration inequalities)

Goal: prove every lemma and theorem of `blueprint/src/chapters/prereq_concentration.tex`
(Sanov's high-probability bound, Ville's inequality and the Bernoulli maximal inequality, the
self-normalized Bernstein inequality by the method of mixtures, the KL–Bernstein inequality and
the variance transport lemmas), in Mathlib generality, no MDP anywhere.

Scope and suggested files (all new, under `Essakine2026Tight/Mathlib/`):
* `InformationTheory/MethodOfTypes.lean`: `lem:type_prob_le`, `lem:num_types`, `thm:sanov_hp`.
  Probability vectors are `weightedMeasure` (`Essakine2026Tight/Mathlib/MeasureTheory/Measure/Weighted.lean`)
  or, if more convenient, `PMF`/measures on a `Fintype` with `MeasurableSingletonClass`; KL is
  `InformationTheory.klDiv` (valued in `ℝ≥0∞`); the i.i.d. sample is `iIndepFun` with
  `HasLaw`. Choose the formulation that makes `lem:empirical_visits_domination` and
  `lem:empirical_kl_time_uniform` of `chap:empirical` easy to state later (they compare
  `klDiv` of the empirical `weightedMeasure` with a real threshold via `ENNReal.ofReal`).
* `Probability/Martingale/Ville.lean`: `lem:ville` (nonnegative supermartingale, stopped at a
  hitting time, `Submartingale.expected_stoppedValue_mono` or `Supermartingale.stoppedProcess`),
  `lem:bernoulli_mgf_step`, `thm:bernoulli_concentration`.
* `Probability/Moments/SelfNormalizedBernstein.lean`: `lem:poisson_cramer`,
  `lem:pconc_exp_taylor_bound`, `lem:bernstein_exp_supermartingale`, `lem:pconc_mixture_lower`,
  `lem:pconc_bernstein_mixture`, `thm:bernstein_self_normalized`, `cor:bernstein_explicit`.
  This is the hardest part (Tonelli for the mixture); do it last.
* `InformationTheory/KLBernstein.lean`: `lem:donsker_varadhan_finite`,
  `lem:bernstein_mgf_bounded`, `lem:kl_bernstein`, `lem:kl_transport_var`,
  `lem:transport_var`, `lem:var_le_range_mean`.
Available already: `Real.sqrt_add_le`, `Real.sqrt_mul_le_add`, `Real.sqrt_mul_le_half_add_half`
(`Essakine2026Tight/Mathlib/Analysis/Real/Sqrt.lean`), `Real.one_add_div_pow_le_exp`,
`ProbabilityTheory.integral_mem_Icc_of_ae_mem_Icc` (`…/Probability/Moments/Variance.lean`),
Mathlib's `ProbabilityTheory.variance_le_sub_mul_sub` (Bhatia–Davis).
Order of work: KL section (finite sums, easiest) → Sanov → Ville/Bernoulli → Bernstein.

## Brief C: `chap:pre_info` (binary divergence, divergence decomposition, change of measure)

Goal: prove every lemma and the theorem of `blueprint/src/chapters/prereq_info.tex`: the binary
relative entropy lemmas, the divergence decomposition at a stopping time, and the change of
measure at a stopping time in its one-sided form (`thm:change_of_measure`, the paper's
Lemma 17), for LML's `IdentAlg` runs in two stationary environments.

Sources to reuse: the sister project `~/Documents/Lean/colt-2026-83` (same toolchain and
Mathlib, but LML pinned at `a6c27a7` while this project pins main `dde3322`: expect API
drift in `IdentAlg`, `sigmaHistory`, `stoppedHist`; adapt, do not downgrade). Copy and adapt,
keeping the upstream-mirroring layout:
* `Maiti2026Power/Mathlib/InformationTheory/{KLBer,Pinsker,KLMap,KLStoppedPrefix}.lean`,
  `Maiti2026Power/Mathlib/Probability/Process/{SigmaPrefix,HittingTime}.lean`,
  `Maiti2026Power/Mathlib/Probability/Distributions/Bernoulli.lean` →
  `Essakine2026Tight/Mathlib/…` (same relative paths). Take only what the chapter needs.
* `Maiti2026Power/LeanMachineLearning/{StoppedHistory,DivergenceDecomposition,RunDivergence}.lean`
  → `Essakine2026Tight/LeanMachineLearning/SequentialLearning/…`.
* New: `Essakine2026Tight/LeanMachineLearning/SequentialLearning/ChangeOfMeasure.lean` for
  `lem:kl_output_pair` (pair version) and `thm:change_of_measure` (one-sided: `τ` a.s. finite
  under the first environment only; truncation to `τ ∧ M` through the identification
  algorithm with `stopSet := A.stopSet ∪ {x | x.1 = M}`, then `lem:pinfo_klbin_lsc` and
  `lem:pinfo_klbin_convex_right`).
The statement shape of the theorem is fixed by the Lean remark after `thm:change_of_measure`
(`klDiv (bernoulliMeasure true false (P.real E)) (bernoulliMeasure true false (P'.real E')) ≤
∑ a, (∫⁻ ω, (pullCount X a (A.stoppingTime O X Y ω).toNat ω : ℝ≥0∞) ∂P) * klDiv (ν a) (ν' a)`);
check the names `Learning.pullCount`, `Learning.IdentAlg.stoppingTime`, `Learning.IdentAlg.IsRun`
in the pinned LML before writing it, and how `chap:lower_bound` (`blueprint/src/chapters/lower_bound.tex`,
`lem:hard_kl_episode` onwards) wants to consume it. The real-valued `klBin` is from
LMLPapers (`~/Documents/Lean/LMLPapers`, `LeanMachineLearning/ForMathlib/InformationTheory/Pinsker.lean`).
Order of work: klbin lemmas → copies (compile them) → stopped chain rule and decomposition →
output pair → theorem.

## Brief D: `chap:pre_mdp` (finite-horizon MDP theory), after `chap:mdp`

Goal: prove every lemma of `blueprint/src/chapters/prereq_mdp.tex`: iterated Markov property
of `stepLaw`, actions and rewards along a trajectory, the law of the next state within an
episode (`lem:pmdp_episode_env_step`, new), occupancy measures, unrolling of a backward
recursive inequality, Cauchy–Schwarz along a trajectory, entropic variances (Bellman
recursion, telescoping, normalized variance), counts and sampling at the visits of a
state-action pair.

What exists (read these files first; `chap:mdp` is fully proved, see the `\lean` tags of
`blueprint/src/chapters/mdp.tex`):
* `MDP/Markov.lean`: Markov property of the trajectory law of a stationary policy in LML
  generality (`hasCondDistrib_shiftRound_trajMeasure`, `firstRoundState`, `shiftRound`,
  `policyKernel`).
* `MDP/StepLaw.lean`: for the layered MDP, `hasLaw_stepLaw_castSucc` (law of (reward of round
  0, state of round 1, shifted trajectory) under `stepLaw M π (s, h.castSucc)`),
  `ae_stepLaw_castSucc_of_ae`, `lintegral_stepLaw_castSucc`, `stepLawKernel`, `ae_obs_zero_stepLaw`,
  `ae_action_zero_stepLaw`, terminal layer (`hasLaw_shiftRound_stepLaw_last`,
  `ae_feedback_eq_zero_stepLaw_last`), `ae_feedback_eq_zero_stepLaw`,
  `ae_episodeReturn_eq_add_shiftRound`, the episode-environment laws
  `hasCondDistrib_feedback_history_action_statesEnv`, `hasCondDistrib_feedback_statesEnv`.
* `MDP/Values.lean`: `lexpValue` (Lebesgue form), `expValue_castSucc` (Bellman, under finite
  exponential moments `hR`), `expValue_last`, `expValue_pos`, ranges (`expValue_mem_Icc`,
  `ae_episodeReturn_mem_Icc`, …), optimal values and `optPolicy`, `integral_eq_vecExp_transVec`,
  `rewardsIn_of_hasRewardFn`, `integrable_exp_mul_of_rewardsIn`, `maxReturn` bounds.
* `Mathlib/Probability/HasCondDistrib.lean` (`hasCondDistrib_snd_compProd`,
  `HasCondDistrib.comp_hasLaw`, `HasCondDistrib.compProd_left`) and
  `Mathlib/Probability/CondDistrib.lean` (`HasCondDistrib.restrict_preimage`,
  `HasCondDistrib.of_comp_hasLaw`, `HasCondDistrib.comp_of_hasLaw`, …).
* `Mathlib/Probability/Moments/Variance.lean`: `ProbabilityTheory.variance_exp_div_sq_integral_le`
  (Lemma 24) for `lem:variance_ratio_le`.
* Definitions (frozen: in the closure of the headline statements, never change them): `stepLaw`,
  `episodeReturn`, `episodeStates`, `occupancy`, `statesLaw`, `statesKernel`, `statesEnv`
  (`Episodic.lean`), `expValue`, `expQ`, `entropicVarQ` (a nested integral, not `variance`),
  `entropicVarV`, `maxReturn` (`Entropic.lean`), `EmpiricalModel` and friends (`Empirical.lean`),
  and the run quantities of `EV2026/Run.lean` (`visitCountAt`, `empTransAt`, …) which the
  counts/visits lemmas are about.

Files: new files under `Essakine2026Tight/LeanMachineLearning/ReinforcementLearning/MDP/`
(suggested `MarkovIter.lean`, `Occupancy.lean`, `Unroll.lean`, `EntropicVariance.lean`,
`Visits.lean`), and pure-probability lemmas (Cauchy–Schwarz along a trajectory) under
`Essakine2026Tight/Mathlib/`. Do not edit `Markov.lean`, `StepLaw.lean`, `Values.lean` or the
definitions of the existing files; add lemmas in new files (if an existing lemma needs a
generalization, write the general version in your file and report it).

Indexing: under `stepLaw M π (s, h)` the round `k` has layer `min (h + k) H` almost surely
(not yet stated: prove it with `ae_stepLaw_castSucc_of_ae` by backward induction if needed), so
the paper's step `i ≥ h` is the round `i - h`. The LML trajectory of LML's `trajMeasure` is
indexed by `ℕ`; the iterated Markov property is naturally stated for the shift by `k` rounds.
LML's trajectory theory: `.lake/packages/LeanMachineLearning/LeanMachineLearning/SequentialLearning/`
and `Online/Bandit/RewardByCountMeasure.lean` (model for `lem:visits_iid`).
Order of work: iterated Markov property and actions → within-episode law → occupancy →
unrolling and Cauchy–Schwarz → entropic variances → visits.

## Brief E: the analysis of Entropic-BPI on the good event (`chap:analysis_pos`, `chap:analysis_neg`)

Launched 2026-09-16 (Opus), after `chap:pre_analysis`, `chap:pre_concentration`, `chap:pre_info`,
`chap:mdp`, `chap:algorithm` and `chap:lower_bound` were proved (agent D on `chap:pre_mdp` still
running).

Goal: prove, for both signs of `β`, the lemmas of `blueprint/src/chapters/analysis_pos.tex` and
`analysis_neg.tex` that do not depend on `chap:pre_mdp`: `lem:concentration_pos/neg` (Lemmas 7, 12), `lem:optimism_pos/neg` (Lemmas 8, 13),
`lem:pos_ring_range`, `lem:neg_ring_range`, `lem:ring_pos/neg` (Lemmas 10, 15),
`lem:certificate_pos/neg` (Lemmas 11, 16), `lem:cert_dominates_gap_pos/neg`,
`lem:stopping_pos/neg` (Lemmas 9, 14), `lem:pac_at_stopping_pos/neg` and
`lem:cert_true_recursion_pos/neg`. Out of scope (they need `lem:unroll_recursion`,
`lem:cauchy_schwarz_traj`, `lem:entropic_variance_sum`, `lem:variance_ratio_le`, occupancy lemmas
of `chap:pre_mdp`): `lem:cert_unrolled_*`, `lem:ratio_bound_*`, `lem:progress_*`,
`lem:stopping_time_bound_*`, `lem:pac_*`.

What exists: `EV2026/Algorithm.lean` (definitions), `EV2026/Backups.lean` (`bonus_nonneg`,
`alphaKL_nonneg`, `alphaStar_nonneg`, `stepU_mem`, `optZ_mem`, `stepUAt_mem`, `optZ_eq`,
`optZ_fst_eq_stepUAt_greedy`, `stepUAt_fst_le_optZ`, `optZ_snd_eq_stepUAt_greedy`,
`optZ_snd_le_stepUAt`, `cert_mem`, `empTrans_nonneg`, `sum_empTrans`), `EV2026/EntropicBPIRun.lean`,
`EV2026/Run.lean` (run quantities and the events `eventKL`, `eventBern`, `eventCnt`,
`goodEvent`), `MDP/Values.lean` (Bellman equations, ranges, optimal values, `optPolicy`,
`optExpValue_castSucc_eq`, value gap), `MDP/Vec.lean` (`vecExp` lemmas, `vecVar_nonneg`,
`vecVar_eq_sum_sq`, `transVec_nonneg`, `sum_transVec`), the concentration library of agent B
(`Mathlib/InformationTheory/KLBernstein.lean`: `abs_integral_sub_integral_le_of_klDiv_le`,
`variance_le_two_mul_variance_add_of_klDiv_le`; `Mathlib/Probability/Moments/VarianceTransport.lean`:
`variance_le_two_mul_variance_add`, `variance_le_mul_integral`;
`Mathlib/MeasureTheory/Measure/WeightedProbability.lean`), `Mathlib/Analysis/Real/Sqrt.lean`.

The main thread proves the rate lemmas (`lem:rates_props`, `lem:sc_rates_real`,
`lem:sc_rate_min_arith`, `lem:pseudo_counts_bound`, `lem:sum_counts_bound`) in
`EV2026/RateBounds.lean` at the same time; if the analysis needs a rate fact that is not in
`EV2026/Backups.lean`, prove it locally in the analysis files. Suggested files: the analysis
in `EV2026/AnalysisPos.lean` and `EV2026/AnalysisNeg.lean` (shared lemmas in
`EV2026/AnalysisCommon.lean`). Formulate the core lemmas for a fixed history `hist` under the
deterministic consequences of the events at that history (the KL inequality for every pair, the
Bernstein inequality for `Z*`), then derive the run versions on `goodEvent`.

## Brief F: time-uniform KL concentration (`lem:empirical_kl_time_uniform`)

Launched 2026-09-16 (Opus). Independent of agents D and E.

Goal: prove `lem:empirical_kl_time_uniform` of `blueprint/src/chapters/empirical.tex` as library
material in `Essakine2026Tight/Mathlib/InformationTheory/KLTimeUniform.lean`, then move the
lemma (with its `\lean` tags) to `prereq_concentration.tex` or tag it in place. Statement: for a
probability vector `p` on a finite type `𝒳` with `m` elements, an i.i.d. sequence
`ξ : ℕ → Ω → 𝒳` of law `weightedMeasure p` (`iIndepFun` + `HasLaw`), and `δ' ∈ (0, 1)`,
`ℙ(∃ n ≥ 1, n KL(q̂ₙ ‖ p) ≥ log(1/δ') + (m - 1) log(n + 1) + 1 + ½ log n) ≤ δ'` with `q̂ₙ` the
empirical measure of `ξ 0, …, ξ (n-1)` (`weightedMeasure (empiricalFreq …)`), and the simplified
form with threshold `(log(1/δ') + m log(e(n + 1)))/n`. Also give the version for the coordinate
process of `Measure.infinitePi (fun _ : ℕ ↦ weightedMeasure p)`, which is the form
`lem:event_kl_prob` will combine with the domination lemma of agent D (`EV2026/VisitCounts.lean`).

Suggested route, simpler than the blueprint's Dirichlet integral: the Laplace (rule of succession)
mixture `Mₙ = ∏_{k<n} q̃ₖ(ξ k)/p(ξ k)` with `q̃ₖ(x) = (Nₖ(x) + 1)/(k + m)`. It is a nonnegative
supermartingale for the natural filtration (`𝔼[q̃ₖ(ξ)/p(ξ) | past] = ∑_{p x > 0} q̃ₖ(x) ≤ 1`, so no
reduction to the support is needed), `M₀ = 1`, and by induction on `n`
`∏_{k<n} q̃ₖ(ξ k) = (m - 1)! ∏ₓ Nₙ(x)! / (n + m - 1)!`, which is exactly the Dirichlet value, so
the lower bound of the blueprint proof applies verbatim. Update the blueprint proof to this route.

What exists: `Mathlib/Probability/Martingale/Ville.lean`
(`MeasureTheory.Supermartingale.measure_exists_ge_le`), `Mathlib/InformationTheory/MethodOfTypes.lean`
(`typeCount`, `sum_typeCount`, `empiricalFreq`, `prod_comp_eq_prod_pow_typeCount`,
`Nat.choose_add_le_add_one_pow`, `card_le_pow_of_sum_eq`), `Mathlib/InformationTheory/KullbackLeibler/Fintype.lean`
(`klDiv` of `weightedMeasure`s as a finite sum), `Mathlib/MeasureTheory/Measure/WeightedProbability.lean`.
Mathlib: `Real.pow_div_factorial_le_exp`, `Stirling.stirlingSeq'_antitone`,
`Stirling.stirlingSeq_one`, `Stirling.le_factorial_stirling`.

## Brief G: probabilities of the concentration events (`chap:empirical`)

Launched 2026-09-16 (Opus), after agent D. Depends on agent F only for
`lem:event_kl_prob` and `lem:good_event`.

Goal: prove the remaining lemmas of `blueprint/src/chapters/empirical.tex`:
`lem:pseudo_counts_increments`, `lem:empirical_visits_domination`, `lem:event_bern_prob`,
`lem:event_cnt_prob`, then `lem:event_kl_prob` and `lem:good_event` once agent F's
`Essakine2026Tight/Mathlib/InformationTheory/KLTimeUniform.lean` is complete (if it is not,
prove the reduction of `lem:event_kl_prob` to an explicit time-uniform hypothesis and report).
Files: `EV2026/Events.lean` (or one file per event), and library-shaped parts (the
first-entrance decomposition of `lem:empirical_visits_domination`(ii)) under
`Essakine2026Tight/Mathlib/` or `LeanMachineLearning/`.

What exists: agent D's `MDP/Visits.lean` and `EV2026/VisitCounts.lean`
(`visitNextState`, `measure_visitNextState_mem_le_pi`, `measure_exists_visitCountAt_eq_le_pi`,
`empTransAt_eq`, `transCount_eq_card`, `visitCountAt_eq_pullCount`, `visitCountAt_le`,
`sum_visitCountAt`), `MDP/Occupancy.lean` (`occupancy_nonneg`, `occupancy_le_one`,
`sum_occupancy`, `occupancy_eq`), `MDP/StepLaw.lean` (`hasCondDistrib_feedback_statesEnv`) and
`MDP/MarkovIter.lean` (`hasCondDistrib_feedback_succ_statesEnv`); agent B's
`Mathlib/Probability/Martingale/Ville.lean` (`measure_exists_sum_lt_half_mul_sum_sub_le`, the
Bernoulli maximal inequality) and `Mathlib/Probability/Moments/SelfNormalizedBernstein.lean`
(`measure_exists_sqrt_add_lt_abs_selfNormSum_le`, `…_le'`, the explicit Bernstein
corollary); the main thread's `EV2026/RateBounds.lean` (`alphaCnt_nonneg`, `one_lt_alphaCnt`,
`alphaStar_eq_rateReal`, `pseudoCount_nonneg`, `pseudoCount_le`); `EV2026/Run.lean` (the events).


## Brief H: tail of the analysis and Theorem 4 (after agents E and G)

Launched 2026-09-16 (Opus). Agent E is done: its run-level lemmas are in
`EV2026/AnalysisPos.lean` and `AnalysisNeg.lean` (read the `\lean` tags of `analysis_pos.tex` and
`analysis_neg.tex`): optimism `optExpValue_mem_Icc_ZlowerAt_ZtildeAt_of_pos/neg`, the certificate
recursion `certAt_le_of_pos/neg` (`lem:cert_true_recursion_*`), correctness at stopping
`optEntropicValue_sub_entropicValue_greedyAt_le_of_pos/neg`, each also at a fixed history under
the structure `HistConcentration` of `EV2026/AnalysisCommon.lean` (`histConcentration_histAt`
derives it from `goodEvent`). Still needed from agent G: `lem:good_event` (only for
`lem:pac_*` and Theorem 4; the other tail lemmas are pointwise on the event).

Goal: for both signs of `β`, `lem:cert_unrolled_*`, `lem:ratio_bound_*`, `lem:progress_*`,
`lem:stopping_time_bound_*`, `lem:pac_*` of `analysis_pos.tex`/`analysis_neg.tex`, then
Theorem 4 (`thm:upper_bound_pac`, `thm:upper_bound_complexity` of `sample_complexity.tex`), i.e.
remove the two `sorry` of `EV2026/UpperBound.lean` without changing the statements (they are
frozen by the comparator challenges).

What exists: agent D's `MDP/Unroll.lean` (`integral_exp_sum_mul_le_of_backward`,
`le_sum_integral_of_backward`), `Mathlib/MeasureTheory/Integral/CauchySchwarz.lean`
(`MeasureTheory.integral_sum_mul_sqrt_mul_le`), `MDP/EntropicVariance.lean`
(`sum_integral_exp_mul_vecVar_eq_variance`, `variance_exp_episodeReturn_div_sq_le_maxReturn`),
`MDP/Occupancy.lean` (`integral_sum_comp_obs_action_stepLaw`); `Mathlib/Analysis/SpecialFunctions/Exp.lean`
(`Real.one_add_div_pow_le_exp`); `Mathlib/Analysis/SpecialFunctions/Log/SelfBounding.lean`
(`le_of_le_sqrt_mul_add'`, Lemma 29 with `D ≥ 1`); the main thread's `EV2026/RateBounds.lean`
(`sum_occupancy_mul_klRateMinAt_le`, `sum_occupancy_mul_starRateMinAt_le`, `alphaKL_mono`);
`EV2026/EntropicBPIRun.lean` (`ae_action_eq_greedy`, `stopCond_histAt_stoppingTime`,
`not_stopCond_histAt_of_lt_stoppingTime`, `ae_output_eq_greedy`); for the PAC transfer,
`IdentAlg.runMeasure`, `IdentAlg.isRun_runMeasure`, `IdentAlg.IsRun.hasLaw_output`
(`LeanMachineLearning/SequentialLearning/IdentificationAlg.lean`; there is no
`IsPAC.of_forall_isRun` yet).
