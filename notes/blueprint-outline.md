# Blueprint outline (authoritative label list and proof routes)

This file is the contract between the chapter files of `blueprint/src/chapters/`. Every label
below is fixed: chapters may only `\uses{}` labels listed here (or labels they define
themselves). If a chapter needs a lemma that is not listed, define it locally with a new label
prefixed by the chapter's short name and do not reference it from other chapters.

Paper: Amer Essakine, Claire Vernade, *Tight Sample Complexity Bounds for Entropic Best Policy
Identification*, COLT 2026 (arXiv 2605.13717). Source: `source/colt_main_draft.tex` (single
file). Main text: Section 2 (setting, Definitions 1–2), Section 3 (Theorem 3, lower bound),
Section 4 (Algorithm 1 Entropic-BPI, Theorem 4), Section 5 (proof sketch). Appendix A
(concentration events, Lemma 5), Appendix B (algorithm analysis: B.1 `β > 0`, Lemmas 7–11 and the
sample complexity proof; B.2 `β < 0`, Lemmas 12–16), Appendix C (lower bound: Lemma 17,
Assumption 1, Condition A, proof of Theorem 3), Appendix E (concentration inequalities, Lemmas
19–22), Appendix F (technical results, Lemmas 23–29). The `colt2026` class numbers every
environment with one counter; the appendix restatements of Theorems 4 and 3 consume the numbers
6 and 18.

## Global conventions (all chapters)

* Style reference: `blueprint/src/chapters/mdp.tex` (read it first; it is written first). Each
  item is a `definition`/`lemma`/`proposition`/`theorem`/`corollary`/`remark` environment with a
  `\label{...}`, a `\uses{...}` line right after the label listing the labels of the definitions
  and lemmas the *statement* needs, and a `\begin{proof} ... \end{proof}` whose `\uses{...}`
  (first line inside the proof) lists what the *proof* needs. Proofs must be complete proof
  sketches at the level of detail of a careful paper, decomposed so that each lemma is a
  plausible single Lean declaration. Add `\textbf{Lean remark.}` paragraphs wherever the
  encoding is non-obvious (name Mathlib/LML declarations when known).
* `theorem` only for the paper's headline results (Theorems 3 and 4) and big classical theorems
  (Sanov, the self-normalized Bernstein inequality, the change of measure); everything else
  `lemma`/`proposition`/`corollary`.
* Cite the paper by section/appendix and lemma number, not by line. Bib keys (in
  `blueprint/src/bib.bib`): `essakine2026tight`, `menard2021fast`, `domingues2021episodic`,
  `kaufmann2016complexity`, `dann2017unifying`, `talebi2018variance`, `fei2021exponential`,
  `cover2006elements`, `bhatia2000better`, `borkar2001risk`.
* Macros (`blueprint/src/macros/common.tex`): `\R \N \E \Prob \Var \indic \abs{} \norm{}
  \Ss \As \eps \KL \klbin \Gmax \Zt \Zl \Ut \Ul \Zr \Ur \cert \phat \pbar \nbar \evKL \evBern
  \evCnt \evGood \argmax \argmin`. No `enumitem`; use `enumerate` with `\item[(i)]`. Wrap
  math in section headings with `\texorpdfstring`. Brace subscripts of macros (`_{\Ss}`).
* **Indexing.** The paper's steps are `h = 1, …, H` with terminal `H + 1`; Lean steps are
  `0`-indexed: `h : Fin H` for state-action steps, `h : Fin (H + 1)` for state values, so the
  paper's `h` is Lean's `h - 1`, and the paper's `e^{\beta (H - h)}` (the range of `Z^*_{h+1}`)
  is `e^{\beta k}` with `k = H - 1 - h` the number of steps *after* the Lean step `h`. The
  blueprint states everything with the paper's `1`-indexing and says so once in
  `chap:mdp`; Lean remarks give the translation. Episodes are indexed by `t = 0, 1, …`:
  `t` is the number of episodes already played, `\pi^{t+1}` the policy computed from them
  (LML rounds are `0`-indexed).
* **Backward recursions** (optimistic values, certificate, ring values) are indexed in Lean by
  the number `j` of steps to the end: `j = 0` is the terminal step `H + 1` (value `1`,
  certificate `0`), and the step `h` (paper) has `j = H + 1 - h`.
* **Two signs of `β`.** `β > 0` and `β < 0` are handled by the same Lean definitions with
  `if 0 < β then … else …`; the blueprint states the two cases as separate lemmas (as the
  paper does), with identical proof structure. Write the `β < 0` chapter by mirroring the
  `β > 0` chapter, changing min/max, the clips and the ranges.
* **Deviations from the paper** (decisions, listed in `content.tex`):
  1. Never-visited pairs: the paper's `α(0)/0 = ∞` is encoded by giving a pair with
     `n_h^t(s, a) = 0` the trivial bounds (`\Ut = e^{\beta (H - h)}`-type clip, `\Ul = 1`, and
     the certificate equal to its clip); Lean's `α(0)/0 = 0` never appears in a statement.
  2. The greedy policy for `β < 0` is `\argmin_a \Ul_h^t(s, a)` (Appendix B.2, consistent with
     the stopping rule and Lemma 16), not `\argmin_a \Ut` as written in the algorithm box.
  3. The clips: the optimistic backup `\Ut_h^t` and the certificate at step `h` are clipped at
     `e^{β (H + 1 - h)}` for `β > 0` (the paper writes `e^{β(H - h - 1)}` and `e^{β(H-h)}`:
     with its `1`-indexed `h`, `U^*_h` ranges in `[1, e^{β(H+1-h)}]`, lem:opt_exp_value_range,
     and optimism needs the clip to dominate `U^*_h`); the pessimistic backup is clipped at `1`.
     For `β < 0` the clips are exchanged (`\Ut` and the certificate at `1`, `\Ul` at
     `e^{β(H+1-h)}`). The exploration rates are the Appendix A definitions.
  4. Lemma 12's second term is `\alpha(n)/n` (the paper drops the `/n`); Lemma 14 is stated
     for `Z` at every step (its last sentence mixes `V` and `Z`); Lemma 27 assumes `α ≥ 0`.
  5. Theorem 3 is stated with Assumption 1 (`H ≥ 3d`, `d = ⌈\log_A((S-3)(A-1)+1)⌉`) and
     Condition A explicit, for `δ ∈ (0, 1/16]`. The tree of the hard instance is not required
     to be full (the paper proves the full-tree case and refers to
     \cite{domingues2021episodic} for the general one): the `S - 3` tree states are the first
     `S - 3` nodes of the infinite `A`-ary tree in breadth-first order (depth `≤ d - 1`), the
     *leaves* are the childless nodes (`L ≥ (S - 4)/2 ≥ S/6` of them, at depths `d - 2` or
     `d - 1`), and an action whose child is missing leads to the first child (lem:tree_leaves).
     The "arm" of an episode is the triple (exit step, leaf, leaf action); the leaf action is
     played on arrival at the leaf, at a step that depends on the leaf's depth. The constant
     `1/1650` becomes `1/5000` (lem:hard_count_lower, lem:tree_leaves).
  6. Theorem 4 is the detailed appendix version with `δ ∈ (0, 1)`, `ε ∈ (0, 2/(|β| H S)]`, and
     its two conclusions (PAC, and `τ ≤ bound` with probability `1 - δ`) as two separate
     headline statements. The bound is the *two-term* bound that the proof gives
     (Lemma 29 applied to the recursive inequality, def:upper_bound_const), not the paper's
     "in particular" simplification to a single term (which assumes that the first term
     dominates, which the hypothesis on `ε` does not guarantee, e.g. when `\Gmax` is small),
     and its absolute constants are generous (`10^9`, `10^{10}` in `C`, `D`) so that the
     formal proof has slack; the asymptotic form is the paper's. Lean: `upperBound`.
  7. The PAC property is a property of the algorithm (LML `IdentAlg.IsPAC`: the law of the
     output, in every environment of the class, gives probability at most `δ` to the bad
     outputs), for the class of MDPs with the *known* deterministic reward function `r` of the
     algorithm and arbitrary transition kernels. Theorem 3 quantifies over algorithms that are
     PAC for the class with the reward function of the hard instances (a weaker hypothesis than
     PAC for all reward functions, hence a stronger theorem).
  8. The change of measure (Lemma 17) is stated and proved in LML generality (two stationary
     environments, any algorithm, any almost surely finite stopping time of the history
     filtration), and the episodic environment of the hard instances is such a stationary
     environment (the action is the policy, the feedback the state sequence).
  9. Sanov's bound (Lemma 19) is used with `(m - 1) \log(n + 1)`; the union bound of Lemma 5
     over `(h, s, a)` and `t` uses `δ_{h,s,a} = δ/(3 S A H)` and the time-uniform form of the
     inequalities (the rates absorb the `\log(8 e (n + 1))`).
  10. Pseudo-counts are the *random* predictable sums `\nbar_h^t(s, a) := \sum_{i ≤ t}
     p^{π^i}_h(s, a)` (the conditional probabilities of the visits given the past), not
     `\E[n_h^t(s,a)]`: this is what Lemma 20 controls and what the counting argument
     telescopes (lem:pseudo_counts_increments). Policies being deterministic, the paper's
     `ν_{\hat π}(u) > 1/2` is "`\hat π` realizes `u`".
  11. The rate terms of the analysis are `ρ_h^t(s,a) := \min\{α(n)/n, 1\}` with the
     convention `ρ = 1` for `n = 0` (the paper's `α(n)/n ∧ 1` with `α(0)/0 = ∞`), and the
     additive term of lem:cert_true_recursion_pos is `84 H e^{β(H+1-h)} ρ` (the paper's
     `e^{β(H-h)}` would not dominate the clip of an unvisited pair); for `β < 0` it is `84 H ρ`
     (the paper's factor `1 - e^{β(H-h)}` vanishes at `h = H`). Both are bounded uniformly by
     `84 H e^{|β|(H+1)} ρ`; the progress per non-stopping episode is
     `κ(β, ε) := (e^{|β|ε} - 1) e^{-2|β|ε}/2` for both signs.
  12. The Bernstein event uses step-dependent ranges `b_h` (def:event_bern).
  13. Lemma 7 (and 12) is stated with `\phat|\Zt - Z^*|` (no sign assumption), and the
     optimism lemma removes the absolute value by its induction hypothesis; Lemma 11 (and 16)
     is stated for visited pairs, unvisited pairs being handled by the clip in
     lem:cert_dominates_gap_pos.

* **Library placement** (Lean remarks name the files). LML's `MDP` (from the `mdp` branch of
  LML, copied verbatim to `Essakine2026Tight/LeanMachineLearning/ReinforcementLearning/MDP/Basic.lean`):
  `Learning.MDP 𝓢 𝓐 𝓡` with transition kernel `P : Kernel (𝓢 × 𝓐) 𝓢` and reward kernel
  `R : Kernel (𝓢 × 𝓐) 𝓡`, the environment `MDP.env M μ₀ : Environment 𝓢 𝓐 𝓡` (observation =
  current state), stationary policies `MDP.policyAlg π`, their trajectory law
  `MDP.policyMeasure M π hπ s`. This project adds, in the same directory (library material,
  namespace `Learning.MDP`): finite-state vectors (`Vec.lean`: `vecExp`, `vecVar`, `transVec`),
  finite-horizon MDPs and their layered embedding, values and episodes as rounds
  (`Episodic.lean`), entropic values (`Entropic.lean`), empirical models (`Empirical.lean`).
  Mathlib-shaped material goes to `Essakine2026Tight/Mathlib/` (`weightedMeasure`, the binary
  divergence `klBin`, Bhatia–Davis, elementary inequalities). The paper's own objects
  (rates, Entropic-BPI, run quantities, events, constants, hard instances, the two theorems)
  are in `Essakine2026Tight/EV2026/`, namespace `Essakine2026Tight`.

---------------------------------------------------------------------------------------------

# Part I: the paper

## mdp.tex — `\chapter{Model: finite-horizon MDPs, entropic values and best-policy identification}\label{chap:mdp}`

Paper: Section 2 (and the exponential Bellman equation of Section 4). Style reference for all
other chapters. Every definition gets a Lean remark.

* def:mdp — (library) a finite MDP: finite state space `\Ss`, finite action space `\As`,
  transition kernel `P(· | s, a)`, reward kernel `R(· | s, a)` (law of the reward). Lean:
  `Learning.MDP S A ℝ` (kernels `M.P`, `M.R`), environment `MDP.env M μ₀`.
* def:episodic_mdp — finite-horizon MDP `\mathcal M = (\Ss, \As, H, (p_h)_{h ≤ H}, (r_h)_{h ≤ H})`:
  transition kernels `p_h : \Ss × \As → Δ(\Ss)` and reward kernels; the paper's MDPs have
  deterministic rewards `r_h : \Ss × \As → [0, 1]` (`def:reward_fn`). Lean:
  `EpisodicMDP S A H` with fields `trans : Fin H → Kernel (S × A) S`,
  `reward : Fin H → Kernel (S × A) ℝ` (Markov); `EpisodicMDP.ofDet trans r`;
  `M.HasRewardFn r` (`M.reward h (s, a) = dirac (r h s a)`); `M.transVec h s a : S → ℝ`
  the transition probabilities as a vector; `M.meanReward h s a`.
* def:reward_fn — a reward function `r : [H] × \Ss × \As → [0, 1]`; `\mathcal M` *has reward
  function `r`* if `R_h(· | s, a) = δ_{r_h(s, a)}`. The class `\mathcal M_r` of MDPs with reward
  function `r` (all transition kernels). Lean: `{M : EpisodicMDP S A H // M.HasRewardFn r}`.
* def:policy — deterministic non-stationary policy `π = (π_h)_{h ≤ H}`, `π_h : \Ss → \As`.
  Lean: `Policy S A H := Fin H → S → A`.
* def:layered_mdp — the stationary MDP on the layered state space `\Ss × \{1, …, H+1\}`: from
  `(s, h)` with `h ≤ H` and action `a`, reward `∼ R_h(s, a)` and next state `(s', h + 1)` with
  `s' ∼ p_h(· | s, a)`; the layer `H + 1` is absorbing with reward `0`. A policy `π` becomes the
  stationary policy `(s, h) ↦ π_h(s)` (arbitrary on the terminal layer). Lean:
  `layerMDP M : MDP (S × Fin (H + 1)) A ℝ`, `Policy.layer π`.
* def:step_law — the law `\Prob^π_{(s, h)}` of the trajectory `(S_i, A_i, R_i)_{i ≥ h}` of `π`
  started at state `s` at step `h`: the trajectory law of `π` in the layered MDP from
  `(s, h)`. `\E^π_{(s,h)}` the expectation. Lean: `stepLaw M π (s, h) :=
  (layerMDP M).policyMeasure π.layer _ (s, h)`, a measure on `ℕ → Round (S × Fin (H+1)) A ℝ`.
* def:episode_return — the return `R_h^π = \sum_{i = h}^H R_i` of a trajectory (the layered
  rewards after the terminal layer are `0`, so it is the sum of the first `H` rewards of the
  layered trajectory whatever the starting step). The state sequence `(S_1, …, S_{H+1})` of an
  episode. Lean: `episodeReturn H`, `episodeStates H`.
* lem:step_law_markov — (Markov property) for `h ≤ H`, `s`, and measurable `F` on trajectories,
  `\E^π_{(s,h)}[F((S_i, A_i, R_i)_{i ≥ h+1})] = \E_{(R, s') ∼ (R_h, p_h)(s, π_h(s))}
  \E^π_{(s', h+1)}[F]`, and `A_h = π_h(s)`, `(R_h, S_{h+1}) ∼ R_h(s, π_h(s)) ⊗ p_h(· | s, π_h(s))`
  under `\Prob^π_{(s,h)}`. Proof: the Ionescu-Tulcea construction of `MDP.policyMeasure`:
  the first round has observation `(s, h)`, action `π_h(s)`, feedback drawn from the layered
  step kernel, and the shifted trajectory is again the trajectory law from the next state
  (LML: `trajMeasure` shift / `IsAlgEnvSeq` of the canonical trajectory, `hasCondDistrib_feedback`).
  Lean remark: this is the one lemma about `stepLaw` that all recursions use; state it in
  the form "the law of the shifted trajectory given the first round is `stepLaw M π (s', h+1)`"
  (`HasCondDistrib`) and derive integral forms.
* def:eval_value — `\E^π[\sum_{i ≥ h} f_i(S_i, A_i) | S_h = s]` for `f : [H] × \Ss × \As → \R`.
  Lean: `evalValue M π f h s`.
* def:exp_value — exponential values, for `β ≠ 0`: `Z^π_h(s) := \E^π_{(s,h)}[e^{β R_h^π}]`
  (`Z^π_{H+1} = 1`), `U^π_h(s, a) := \E[e^{β R} Z^π_{h+1}(S')]` for `(R, S') ∼ R_h ⊗ p_h(· | s, a)`;
  with a deterministic reward `U^π_h(s, a) = e^{β r_h(s, a)} (p_h Z^π_{h+1})(s, a)` where
  `(p f)(s, a) := \E_{S' ∼ p(· | s, a)} f(S')`. Lean: `expValue M β π h s`, `expQ M β π h s a`,
  `vecExp (M.transVec h s a) f`.
* def:entropic_value — `V^π_h(s) := β^{-1} \log Z^π_h(s)`, `Q^π_h(s, a) := β^{-1} \log U^π_h(s, a)`.
  Lean: `entropicValue`, `entropicQ`.
* lem:exp_bellman — (exponential Bellman equation) `Z^π_h(s) = U^π_h(s, π_h(s))` for `h ≤ H`,
  i.e. `Z^π_h(s) = e^{β r_h(s, π_h(s))} (p_h Z^π_{h+1})(s, π_h(s))` for deterministic rewards.
  Proof: lem:step_law_markov with `F = e^{β R_{h+1}^π}` and `R_h^π = R_h + R_{h+1}^π`.
* lem:exp_value_range — for rewards in `[0, 1]`: `Z^π_h(s) ∈ [\min(1, e^{β (H + 1 - h)}),
  \max(1, e^{β (H + 1 - h)})]` and `U^π_h ∈ [\min(1, e^{β (H + 1 - h)}), \max(1, e^{β (H+1-h)})]`,
  `Z^π_h > 0`. Proof: `R_h^π ∈ [0, H + 1 - h]` a.s. and monotonicity of the integral.
* lem:exp_value_monotone — (monotonicity of the exponential Bellman operator) if `f ≤ g` on `\Ss`
  then `e^{β r}(p_h f) ≤ e^{β r}(p_h g)`; `p_h` is linear and positive; `p_h 1 = 1`.
* def:opt_value — `V^*_h(s) := \sup_π V^π_h(s)`, `Z^*_h(s) := e^{β V^*_h(s)}`,
  `U^*_h(s, a) := \E[e^{β R} Z^*_{h+1}(S')]` for `(R, S') ∼ R_h ⊗ p_h(· | s, a)`. Lean:
  `optEntropicValue`, `optExpValue`, `optExpQ` (the sup over the finite type of policies is a max).
* lem:opt_exp_value_eq — `Z^*_h(s) = \max_π Z^π_h(s)` if `β > 0`, `= \min_π Z^π_h(s)` if `β < 0`
  (`x ↦ e^{β x}` is increasing/decreasing, finitely many policies).
* lem:opt_bellman — (optimal exponential Bellman equation) for deterministic rewards,
  `Z^*_h(s) = \max_a U^*_h(s, a)` if `β > 0` and `Z^*_h(s) = \min_a U^*_h(s, a)` if `β < 0`;
  `Z^*_{H+1} = 1`; and `U^*_h(s, a) = e^{β r_h(s,a)} (p_h Z^*_{h+1})(s, a)`. Proof: backward
  induction using lem:exp_bellman, lem:exp_value_monotone and that the sup over policies
  decouples across steps (policies are non-stationary: the optimal continuation from `h + 1`
  does not depend on `π_h`). Lean remark: prove "`Z^*_h(s) = Z^{π^*}_h(s)` for the greedy
  policy `π^*` of `U^*`" and "`Z^π_h(s) ≤ Z^*_h(s)` (β > 0) for all π" separately.
* lem:opt_exp_value_range — `Z^*_h(s) ∈ [\min(1, e^{β(H+1-h)}), \max(1, e^{β(H+1-h)})]` and
  the same for `U^*_h` (from lem:exp_value_range, lem:opt_exp_value_eq).
* lem:value_gap_log — for `β ≠ 0` and every `π`, `V^*_1(s) - V^π_1(s) = β^{-1}\log(Z^*_1(s)/Z^π_1(s))
  = β^{-1} \log(1 + (Z^*_1(s) - Z^π_1(s))/Z^π_1(s))`; hence (`β > 0`) if
  `Z^*_1(s) - Z^π_1(s) ≤ (e^{β ε} - 1) Z^π_1(s)` then `V^*_1(s) - V^π_1(s) ≤ ε`, and (`β < 0`) if
  `Z^π_1(s) - Z^*_1(s) ≤ (e^{β ε} - 1)·(-1)·Z^π_1(s)`, i.e. `Z^π_1 - Z^*_1 ≤ (1 - e^{βε}) Z^π_1`,
  then `V^*_1(s) - V^π_1(s) ≤ ε`. (Section 4, "Stopping rule", and Appendix B.2.)
* def:gmax — `\Gmax(\mathcal M) := \sup_π \operatorname{ess\,sup} R_1^π` under `\Prob^π_{(s_1, 1)}`
  (Definition 1, with the fixed initial state `s_1`; the paper's sup over "all sources of
  randomness" is the essential supremum under the trajectory law). Lean:
  `maxReturn M s₁ := ⨆ π, essSup (episodeReturn H) (stepLaw M π (s₁, 0))`.
* lem:gmax_le_horizon — rewards in `[0, 1]` give `0 ≤ \Gmax(\mathcal M) ≤ H`, and `R_1^π ≤ \Gmax`
  a.s. under every `\Prob^π_{(s_1,1)}`.
* def:episode_env — episodes as rounds of the LML interaction: the learner plays a policy
  `π^{t+1}` (the action of round `t`), the environment draws the state sequence
  `(s^{t+1}_1, …, s^{t+1}_{H+1})` of the episode from the fixed initial state `s_1`
  (the feedback), there is no observation. The rewards are known (deterministic), so the
  state sequence determines the episode. This is the stationary environment (LML
  `stationaryEnv`) with feedback kernel `π ↦` law of `episodeStates` under `\Prob^π_{(s_1, 1)}`.
  Lean: `statesKernel M s₁ : Kernel (Policy S A H) (Traj S H)`, `statesEnv M s₁ :=
  stationaryEnv (statesKernel M s₁)`, `Traj S H := Fin (H + 1) → S`.
* lem:episode_env_law — in any algorithm-environment sequence `(X, Y)` for an algorithm and
  `statesEnv M s₁`, the conditional law of the episode `Y_t` given the past and `X_t = π` is the
  law of `episodeStates` under `\Prob^π_{(s_1,1)}` (LML `IsAlgEnvSeq.hasCondDistrib_feedback`
  + `feedback_stationaryEnv`); in particular the transition at step `h` of the episode, given
  the past and the states up to `h`, has law `p_h(· | s^t_h, π_h(s^t_h))` (lem:step_law_markov).
* def:bpi_alg — a BPI algorithm: an identification algorithm in the episode environment
  (sampling rule = policies, stopping rule, output = a policy). The number of episodes `τ` is
  its stopping time. Lean: `BPIAlg S A H := IdentAlg Unit (Policy S A H) (Traj S H) (Policy S A H)`,
  `IdentAlg.stoppingTime`, `IdentAlg.IsRun`.
* def:entropic_pac — (Definition 2) `\mathcal A` is `(ε, δ)`-PAC for entropic BPI with reward
  function `r`, parameter `β` and initial state `s_1` if for every MDP `\mathcal M ∈ \mathcal M_r`,
  the output `\hat π` of `\mathcal A` in the episode environment of `\mathcal M` satisfies
  `\Prob(V^*_1(s_1) - V^{\hat π}_1(s_1) > ε) ≤ δ`. Lean: `IsEntropicPAC 𝒜 r β ε δ s₁ :=
  𝒜.IsPAC (fun M : {M // M.HasRewardFn r} ↦ statesEnv M.1 s₁) (fun M π ↦ ε < V* - V^π) δ`.
  Lean remark: LML's `IsPAC` is about the law `outputMeasure` of the output; for a run
  `(X, Y, out)` on `(Ω, P)`, `IsPAC.measureReal_bad_of_isRun` gives `P(bad) ≤ δ`.

---------------------------------------------------------------------------------------------

## empirical.tex — `\chapter{Empirical transitions and concentration events}\label{chap:empirical}`

Paper: Section 2 ("Empirical MDP"), Appendix A (Lemma 5). Everything is for a run `(X, Y)` of
an arbitrary algorithm in the episode environment of `\mathcal M` (def:episode_env), on a
probability space `(Ω, \Prob)`: `X_t = π^{t+1}` and `Y_t = (s^{t+1}_1, …, s^{t+1}_{H+1})`.

* def:counts — `n_h^t(s, a) := \sum_{i ≤ t} \indic\{(s_h^i, a_h^i) = (s, a)\}`,
  `n_h^t(s, a, s') := \sum_{i ≤ t} \indic\{(s_h^i, a_h^i, s_{h+1}^i) = (s, a, s')\}` with
  `a^i_h = π^i_h(s^i_h)`, as functions of the history of the first `t` episodes. Lean:
  `EmpiricalModel S A` (visit counts, reward sums, transition counts; an additive monoid),
  `EmpiricalModel.ofEpisodeAt π τ r h`, `stepModel hist h := ∑ i, ofEpisodeAt …`,
  `visitCount hist h s a`; on a run, `histAt X Y t ω`, `visitCountAt X Y h s a t ω`.
* def:emp_trans — `\phat_h^t(s' | s, a) := n_h^t(s, a, s')/n_h^t(s, a)` if `n_h^t(s, a) > 0`,
  `1/S` otherwise; `\phat_h^t(s, a) ∈ Σ_{\Ss}` (probability vector). Lean: `empTrans hist h s a`,
  `empTransAt`.
* lem:emp_trans_simplex — `\phat_h^t(· | s, a)` is a probability vector; `\phat f` is
  linear in `f` and `|\phat f| ≤ \max |f|`.
* def:pseudo_counts — `\nbar_h^t(s, a) := \E[n_h^t(s, a)]`. Lean: `pseudoCount X Y P h s a t`.
* lem:pseudo_counts_increments — `\nbar_h^{t+1}(s, a) - \nbar_h^t(s, a) = \Prob(s^{t+1}_h = s,
  π^{t+1}_h(s) = a) = \E[p^{π^{t+1}}_h(s, a)]` where `p^π_h(s, a) := \Prob^π_{(s_1,1)}(S_h = s,
  A_h = a)` is the occupancy measure (def:occupancy in `chap:pre_mdp`); `\nbar_h^t ≤ t`.
  Proof: lem:episode_env_law and the tower rule.
* def:rates — exploration rates (Appendix A, eq. (5)): `α(n, δ) := \log(3 S A H/δ) + S\log(8e(n+1))`,
  `α^*(n, δ) := \log(3 S A H/δ) + \log(8e(n+1))`, `α^{cnt}(δ) := \log(3SAH/δ)`. Lean: `alphaKL`,
  `alphaStar`, `alphaCnt` (functions of the cardinalities `S`, `A` and of `H`).
* lem:rates_props — `α^* ≤ α`, both nondecreasing in `n`, `n ↦ α(n)/n` and `α^*(n)/n`
  nonincreasing on `n ≥ 1`, `α, α^* ≥ 0`, `α(n)/n ≤ α(n')/n'` for `n ≥ n' ≥ 1`;
  `α(n, δ) ≤ \log(3SAH/δ) + S \log(8 e (n+1))`.
* def:event_kl — `\evKL := \{∀ t, h, (s, a) : \KL(\phat_h^t(s, a) ‖ p_h(s, a)) ≤ α(n_h^t(s,a), δ)/n_h^t(s,a)\}`
  (the threshold is `+∞` for `n = 0`). Lean: `eventKL X Y M δ`, with
  `klDiv (weightedMeasure (empTransAt …)) (M.trans h (s, a))` and `klThreshold`.
* def:event_bern — for `f = (f_h)_{h ≤ H+1}` and ranges `b = (b_h)_{h ≤ H}` with `b_h ≥ 0`
  (`b_h` bounds the oscillation `\max f_{h+1} - \min f_{h+1}` of `f_{h+1}` in the lemmas
  that use the event; the paper takes a single `b`):
  `\evBern(f, b) := \{∀ t, h, (s, a) with n_h^t(s,a) > 0 : |(\phat_h^t - p_h) f_{h+1}(s, a)| <
  \sqrt{2 \Var_{p_h}(f_{h+1})(s,a) α^*(n)/n} + 3 b_h α^*(n)/n\}`, `n = n_h^t(s, a)`.
  Lean: `eventBern X Y M δ f b` with `b : Fin H → ℝ`. Deviation 12 (record in `content.tex`):
  step-dependent ranges, needed because the paper's Lemmas 7 and 12 use the range
  `e^{β(H-h)}` (resp. `1 - e^{β(H-h)}`) of `Z^*_{h+1}` at step `h`, not a uniform `b`.
* def:event_cnt — `\evCnt := \{∀ t, h, (s, a) : n_h^t(s, a) ≥ \nbar_h^t(s, a)/2 - α^{cnt}(δ)\}`.
  Lean: `eventCnt X Y δ P`.
* def:good_event — `\evGood^+ := \evKL ∩ \evBern(Z^*, b) ∩ \evCnt` with `b_h = e^{β (H - h)}`
  (`β > 0`), `\evGood^- := \evKL ∩ \evBern(Z^*, b) ∩ \evCnt` with `b_h = 1 - e^{β (H - h)}`
  (`β < 0`); `Z^* = (Z^*_h)_{h ≤ H+1}`, and `Z^*_{h+1}` takes values in `[1, e^{β(H-h)}]`
  (resp. `[e^{β(H-h)}, 1]`) by lem:opt_exp_value_range, an interval of length `≤ b_h`.
  Lean: `goodEvent X Y M β δ P` (in Lean `b h = Real.exp (β * k)` resp. `1 - Real.exp (β * k)`
  with `k = H - 1 - h`).
* lem:event_kl_prob — `\Prob(\evKL) ≥ 1 - δ/3`. Proof: for fixed `(h, s, a)`, the
  transitions observed at the visits of `(s, a)` at step `h` are i.i.d. `p_h(· | s, a)`
  (lem:visits_iid in `chap:pre_mdp`: the `k`-th observed next state, conditionally on the
  past, has law `p_h(s, a)`), so thm:sanov_hp with `δ_{h,s,a} = δ/(3SAH)` and a union bound over
  `n ≥ 1` (the `\log(8e(n+1))` of `α` absorbs `\sum_n δ/(8e(n+1)^2)`-type terms; use
  `\sum_{n ≥ 1} 1/(8e(n+1)^2) ≤ 1`) give the bound uniformly in `t` since the event at time
  `t` only depends on `n = n_h^t(s, a)` and the first `n` observed transitions; then a union
  bound over `(h, s, a)`. Lean remark: the reindexing "the empirical distribution after `t`
  episodes is the empirical distribution of the first `n_h^t(s,a)` observed transitions"
  is lem:emp_trans_reindex (`chap:pre_mdp`).
* lem:event_bern_prob — for every `f` and `b` with `\max f_{h+1} - \min f_{h+1} ≤ b_h`,
  `\Prob(\evBern(f, b)) ≥ 1 - δ/3`.
  Proof (Appendix A): fix `(h, s, a)`; `w_i := \indic\{(s^i_h, a^i_h) = (s, a)\}` is
  predictable (determined by the history of `i - 1` episodes and the states of episode `i` up
  to step `h`), `Y_i := f_{h+1}(s^i_{h+1}) - (p_h f_{h+1})(s, a)` on `\{w_i = 1\}` is centered
  with conditional variance `\Var_{p_h}(f_{h+1})(s,a)` (lem:episode_env_law), `|Y_i| ≤ b_h`;
  `S_t/W_t = (\phat_h^t - p_h) f_{h+1}(s, a)` and `V_t = n_h^t(s,a) \Var_{p_h}(f_{h+1})(s,a)`;
  thm:bernstein_self_normalized with `δ_{h,s,a} = δ/(3SAH)` and `\log(4e(2t+1)/δ') ≤ α^*(n, δ)`
  when... note `4e(2t+1)` is in `t`, not `n`: use the filtration of the visits (the
  `k`-th visit) so that the time index is the number of visits `n` (lem:visits_iid), and
  `\log(4e(2n+1)) ≤ \log(8e(n+1))`. Union bound over `(h, s, a)`.
* lem:event_cnt_prob — `\Prob(\evCnt) ≥ 1 - δ/3`. Proof: thm:bernoulli_concentration applied,
  for fixed `(h, s, a)`, to `X_i := \indic\{(s^i_h, a^i_h) = (s, a)\}` with the filtration of
  the histories of episodes, `P_i = \Prob(X_i = 1 | \mathcal F_{i-1})`, so that
  `\sum_{i ≤ t} P_i` has expectation `\nbar_h^t(s,a)`... the paper's event compares `n_h^t` to
  `\nbar_h^t/2 - α^{cnt}`; thm:bernoulli_concentration gives `n_h^t ≥ \frac12 \sum_{i ≤ t} P_i - \log(1/δ')`.
  Lean remark: the paper (following Ménard et al.) identifies `\nbar_h^t = \E n_h^t` with
  `\sum_{i ≤ t} P_i`; these differ in general (the latter is random). **Decision:** define the
  pseudo-counts as `\nbar_h^t(s, a) := \sum_{i ≤ t} \Prob(s^i_h = s, a^i_h = a | \mathcal F_{i-1})
  = \sum_{i ≤ t} p^{π^i}_h(s, a)` (random, `\mathcal F_{t-1}`-measurable), which is what both
  Lemma 5 (through Lemma 20) and the counting argument (lem:sum_counts_bound, through
  lem:pseudo_counts_increments) actually use. Record this in the Lean remark of
  def:pseudo_counts and in `content.tex` (deviation 10).
* lem:good_event — (Lemma 5) `\Prob(\evGood^+) ≥ 1 - δ` and `\Prob(\evGood^-) ≥ 1 - δ`
  (union bound of the three events).

---------------------------------------------------------------------------------------------

## algorithm.tex — `\chapter{The Entropic-BPI algorithm}\label{chap:algorithm}`

Paper: Section 4 (Algorithm 1), Appendix B (equations (bonus positive),
(optimism_equation_positive), (width_certificate_positive) and their negative versions).
All quantities are computed from the history of the first `t` episodes (def:counts,
def:emp_trans) and the known reward function `r`. Lean remark: they are defined as functions
of a history `hist : Hist Unit (Policy S A H) (Traj S H) t` (`Essakine2026Tight/EV2026/Algorithm.lean`)
and evaluated on a run through `histAt X Y t ω` (`Run.lean`); the backward recursions are
indexed by the number `j` of steps to the end.

* def:bonus — (`β > 0`, eq. (bonus positive)) for a pair with `n = n_h^t(s, a) ≥ 1`:
  `b_h^t(s, a) := 2\sqrt2 \sqrt{\Var_{\phat_h^t}(\Zt^t_{h+1})(s,a) α^*(n)/n} + 5 e^{β(H-h)} α(n)/n
  + 4 H e^{β(H-h)} α^*(n)/n`; (`β < 0`, eq. (bonus_negative)) the same with `\Zl` in the
  variance and `(1 - e^{β(H-h)})` in place of `e^{β(H-h)}`. Lean: `bonus nA H β δ k n phat Zt Zl`
  with `k = H - h` the number of steps after `h`.
* def:backups — (eq. (optimism_equation_positive)) for `β > 0`, with `\Zt^t_{H+1} = \Zl^t_{H+1} = 1`:
  `\Ut_h^t(s,a) := \min\{e^{β(H-h)}, e^{β r_h(s,a)}[\phat \Zt^t_{h+1} + b + \frac1H \phat(\Zt^t_{h+1} - \Zl^t_{h+1})](s,a)\}`,
  `\Ul_h^t(s,a) := \max\{1, e^{β r_h(s,a)}[\phat \Zl^t_{h+1} - b - \frac1H \phat(\Zt^t_{h+1} - \Zl^t_{h+1})](s,a)\}`,
  `\Zt^t_h(s) := \max_a \Ut_h^t(s,a)`, `\Zl^t_h(s) := \max_a \Ul_h^t(s,a)`; for a never-visited
  pair `\Ut_h^t(s,a) := e^{β(H-h)}`, `\Ul_h^t(s,a) := 1` (deviation 1). For `β < 0`
  (eq. (optimism_equation_negative)): clips `1` (for `\Ut`) and `e^{β(H-h)}` (for `\Ul`),
  `\Zt^t_h(s) := \min_a \Ut`, `\Zl^t_h(s) := \min_a \Ul`. Note: the paper writes the range
  `e^{β(H-h-1)}` in the min at step `h` for `\Ut`; with the paper's `1`-indexing the value
  `U^*_h` lies in `[1, e^{β(H+1-h)}]` (lem:opt_exp_value_range), and the recursion is
  consistent with the clip `e^{β(H+1-h)}`: **use the clip `e^{β(H + 1 - h)}` at step `h`**
  (Lean: `Real.exp (β * (k + 1))` for `k = H - h` steps after `h`... check: Lean step `h`
  (0-indexed) has `k = H - 1 - h` steps after it and `U` at that step ranges in
  `[1, e^{β (k + 1)}]`; the clip is `e^{β (k+1)}`). Record as deviation 11 (the paper's
  exponent `H - h - 1` is a typo for the `1`-indexed `H + 1 - h`). Lean: `stepU`, `optZ`,
  `stepUAt`, on a run `UtildeAt`, `UlowerAt`, `ZtildeAt`, `ZlowerAt`.
* lem:backups_range — `\Ul ≤ \Ut`, `\Zl ≤ \Zt`, `1 ≤ \Ul_h^t ≤ \Ut_h^t ≤ e^{β(H+1-h)}` (`β > 0`),
  `e^{β(H+1-h)} ≤ \Ul ≤ \Ut ≤ 1` (`β < 0`), same for `\Zl, \Zt` at every step; `b_h^t ≥ 0`.
  Proof: backward induction; the bonus is nonnegative; `\phat(\Zt - \Zl) ≥ 0`.
* def:greedy — `π^{t+1}_h(s) := \argmax_a \Ut_h^t(s, a)` (`β > 0`), `:= \argmin_a \Ul_h^t(s,a)`
  (`β < 0`) (deviation 2); so `\Zt^t_h(s) = \Ut_h^t(s, π^{t+1}_h(s))` (`β > 0`) and
  `\Zl^t_h(s) = \Ul_h^t(s, π^{t+1}_h(s))` (`β < 0`). Lean: `greedy r β δ hist`, `greedyAt`
  (LML `argmax`/`argmin` on a finite type).
* def:certificate — (eq. (width_certificate_positive)) `G^t_{H+1} := 0` and, for
  `a = π^{t+1}_h(s)` with `n = n_h^t(s,a) ≥ 1`:
  `(π^{t+1}_h G^t_h)(s) := \min\{c_h, e^{β r_h(s,a)}[3 b_h^t(s,a) + (1 + \frac3H) \phat_h^t (π^{t+1}_{h+1} G^t_{h+1})(s,a)]\}`
  with the clip `c_h = e^{β(H+1-h)}` (`β > 0`; the paper writes `e^{β(H-h)}`, same typo as
  in def:backups) or `c_h = 1` (`β < 0`); `:= c_h` for a never-visited pair. Lean: `cert r β δ hist j`,
  `certAt`.
* lem:certificate_range — `0 ≤ (π^{t+1}_h G^t_h)(s) ≤ c_h`.
* def:stopping_rule — stop after `t` episodes if `(π^{t+1}_1 G^t_1)(s_1) ≤ \frac{e^{βε} - 1}{e^{βε}} \Zt^t_1(s_1)`
  (`β > 0`, eq. (computable_stopping_condition)) or `(π^{t+1}_1 G^t_1)(s_1) ≤ (1 - e^{βε}) \Zl^t_1(s_1)`
  (`β < 0`, eq. (true_optimality_condition_negative)). Lean: `stopCond r β δ ε s₁ hist`.
* def:entropic_bpi — (Algorithm 1) the BPI algorithm with sampling rule "play `π^{t+1}`
  after `t` episodes" (deterministic), stopping rule def:stopping_rule, output `π^{t+1}` at the
  stopping time `τ = t`. Lean: `entropicBPI r β δ ε s₁ : BPIAlg S A H`, built with `detAlgorithm`,
  `stopSet := {h | stopCond … h.2}`, `output := Kernel.deterministic (fun h ↦ greedy … h.2)`.
* lem:entropic_bpi_run — in a run `(X, Y, out)` of Entropic-BPI: `X_t = π^{t+1}` computed from
  the history of the first `t` episodes (LML `IsAlgEnvSeq` with a deterministic algorithm:
  `hasCondDistrib_action` with a deterministic kernel gives `X_t = greedy(histAt t)` a.s.),
  at the stopping time `τ < ∞` the stopping condition holds for the history of `τ` episodes
  and fails for every `t < τ`, and `out = π^{τ+1}` a.s. on `\{τ < ∞\}` (the output kernel is
  deterministic). Lean remark: `IdentAlg.stoppedHist_mem_stopSet_of_ne_top`,
  `hittingAfter` characterization, `HasCondDistrib` with a deterministic kernel.
* def:ring — auxiliary (analysis-only) values, `\Zr^t_{H+1} := 1` and backward, for
  `a = π^{t+1}_h(s)`: (`β > 0`, Appendix B.1 "Stopping rule")
  `\Ur^t_{h,pes}(s,a) := \max\{1, e^{β r}[\phat \Zr^t_{h+1} - b - \frac1H \phat(\Zt^t_{h+1} - \Zr^t_{h+1})](s,a)\}`,
  `\Ur^t_h(s,a) := \min\{e^{β r}(p_h \Zr^t_{h+1})(s,a), \Ur^t_{h,pes}(s,a)\}`, `\Zr^t_h(s) := \Ur^t_h(s, π^{t+1}_h(s))`;
  for a never-visited pair `\Ur^t_h(s, a) := \min\{e^{β r}(p_h \Zr^t_{h+1})(s,a), 1\}`
  (`\Ul = 1` there). (`β < 0`, Appendix B.2)
  `\Ur^t_{h,opt}(s,a) := \min\{1, e^{β r}[\phat \Zr^t_{h+1} + b + \frac1H \phat(\Zr^t_{h+1} - \Zl^t_{h+1})](s,a)\}`,
  `\Ur^t_h := \max\{e^{β r}(p_h \Zr^t_{h+1}), \Ur^t_{h,opt}\}`; never visited: `\max\{e^{βr} p_h \Zr, 1\}`.
  Lean: `ringUAux`, `ringZ M β δ hist j`, `ringU`, `ringZAt`, `ringUAt`.

---------------------------------------------------------------------------------------------

## analysis_pos.tex — `\chapter{Analysis of Entropic-BPI for \texorpdfstring{$\beta > 0$}{beta > 0}}\label{chap:analysis_pos}`

Paper: Appendix B.1 (Lemmas 7–11 and the sample complexity proof). Standing setting: `β > 0`,
`\mathcal M` with reward function `r` with values in `[0, 1]`, `δ ∈ (0,1)`, `ε > 0`, a run
`(X, Y, out)` of Entropic-BPI (def:entropic_bpi) in the episode environment of `\mathcal M`
from `s_1`, on `(Ω, \Prob)`; all quantities at episode `t` are those of def:backups,
def:greedy, def:certificate, def:ring for the history of the first `t` episodes, and
`π := π^{t+1}`. "On `\evGood^+`" means: for every `ω ∈ \evGood^+`. Abbreviations: `n = n_h^t(s,a)`,
`\phat = \phat_h^t(s,a)`, `b = b_h^t(s,a)`.

* lem:concentration_pos — (Lemma 7) on `\evGood^+`, for all `t, h, (s,a)` with `n ≥ 1`:
  `|(p_h - \phat) Z^*_{h+1}(s,a)| ≤ 2\sqrt2 \sqrt{\Var_{\phat}(\Zt^t_{h+1})(s,a) α^*(n)/n}
  + 5 e^{β(H-h)} α(n)/n + 4 H e^{β(H-h)} α^*(n)/n + \frac1H \phat|\Zt^t_{h+1} - Z^*_{h+1}|(s,a)`.
  Proof: def:good_event gives the Bernstein bound with `b_h = e^{β(H-h)}`; lem:kl_transport_var
  with `f = Z^*_{h+1} - 1 ∈ [0, e^{β(H-h)}]` and `\KL(\phat ‖ p_h) ≤ α(n)/n` (def:event_kl):
  `\Var_{p_h}(Z^*) ≤ 2\Var_{\phat}(Z^*) + 4 e^{2β(H-h)} α/n`; lem:transport_var (first part)
  with `f = Z^*_{h+1} - 1`, `g = \Zt^t_{h+1} - 1` (in `[0, e^{β(H-h)}]` by lem:backups_range):
  `\Var_{\phat}(Z^*) ≤ 2\Var_{\phat}(\Zt) + 2 e^{β(H-h)} \phat|Z^* - \Zt|`; then lem:sqrt_add_le,
  lem:sqrt_mul_le with `η = H`, and `α^* ≤ α` (lem:rates_props). **Verify every constant**;
  if a constant of the paper is wrong, use a correct one and say so in a remark (the constants
  of the bonus, def:bonus, must then be changed consistently: the bonus is *defined* as the
  right-hand side minus the last term).
* lem:optimism_pos — (Lemma 8) on `\evGood^+`, for all `t, h, (s, a)`:
  `\Ul_h^t(s,a) ≤ U^*_h(s,a) ≤ \Ut_h^t(s,a)` and `\Zl^t_h ≤ Z^*_h ≤ \Zt^t_h`. Proof: backward
  induction on `h` (terminal: all equal to `1`); step `h`: unvisited pairs by
  lem:opt_exp_value_range and the clips; visited: if the min in `\Ut` is the clip,
  `U^* ≤ e^{β(H+1-h)}`; else `\Ut - U^* = e^{β r}[\phat(\Zt - Z^*) + (\phat - p_h)Z^* + b + \frac1H\phat(\Zt - \Zl)]`
  and lem:concentration_pos with the induction hypothesis (`|\Zt - Z^*| = \Zt - Z^*`) gives
  `(\phat - p_h) Z^* ≥ -b - \frac1H \phat(\Zt - Z^*)`, hence
  `\Ut - U^* ≥ e^{βr}[(1 - \frac1H)\phat(\Zt - Z^*) + \frac1H \phat(Z^* - \Zl)] ≥ 0`
  (lem:emp_trans_simplex, `H ≥ 1`). Pessimism symmetric. `Z`: lem:opt_bellman and the max
  over `a`.
* lem:ring_pos — (Lemma 10) for all `t, h, (s,a)` (no event needed):
  `\Ur^t_h(s,a) ≤ \min\{\Ul_h^t(s,a), U^π_h(s,a)\}` and `\Zr^t_h(s) ≤ \min\{\Zl^t_h(s), Z^π_h(s)\}`.
  Proof: backward induction; `\Ur ≤ e^{βr} p_h \Zr_{h+1} ≤ e^{βr} p_h Z^π_{h+1} = U^π_h`
  (lem:exp_value_monotone, lem:exp_bellman); `\Ul - \Ur_{pes} ≥ 0` since `\max\{1, ·\}` is
  monotone and the arguments differ by `e^{βr}(1 - \frac1H)\phat(\Zl - \Zr) ≥ 0` (unvisited:
  `\Ur ≤ 1 = \Ul`); `Z`: `\Zr_h(s) = \Ur_h(s, π_h(s)) ≤ \Ul_h(s, π_h(s)) ≤ \Zl_h(s)` and
  `≤ U^π_h(s, π_h(s)) = Z^π_h(s)`.
* lem:certificate_pos — (Lemma 11) on `\evGood^+`, for all `t, h, (s,a)` with `n ≥ 1`:
  `\Ut_h^t(s,a) - \Ur^t_h(s,a) ≤ e^{βr}[3b + (1 + \frac3H)\phat(\Zt^t_{h+1} - \Zr^t_{h+1})(s,a)]`.
  Proof: two cases on the min defining `\Ur`. Case `\Ur = e^{βr} p_h \Zr_{h+1}`: drop the clip
  of `\Ut`, decompose `\phat\Zt - p_h\Zr = \phat(\Zt - \Zr) + (\phat - p_h)Z^* + (p_h - \phat)(Z^* - \Zr)`;
  second term by lem:concentration_pos and `\Zt - Z^* ≤ \Zt - \Zr` (lem:optimism_pos,
  lem:ring_pos: `\Zr ≤ \Zl ≤ Z^* ≤ \Zt`); third term by lem:kl_bernstein with `f = Z^* - \Zr ∈ [0, e^{β(H-h)}]`
  and `\Var_{\phat}(f) ≤ \phat f^2 ≤ e^{β(H-h)} \phat f`, then lem:sqrt_mul_le with `η = H`:
  `≤ \frac1H\phat(\Zt - \Zr) + 2 H e^{β(H-h)} α/n + \frac23 e^{β(H-h)} α/n ≤ \frac1H \phat(\Zt - \Zr) + b`;
  and `\phat(\Zt - \Zl) ≤ \phat(\Zt - \Zr)`. Case `\Ur = \Ur_{pes}`: direct algebra plus
  lem:ring_pos. Check the constants `3` and `3/H`.
* lem:cert_dominates_gap_pos — on `\evGood^+`, for all `t, h, s`:
  `\Zt^t_h(s) - \Zr^t_h(s) ≤ (π_h G^t_h)(s)`. Proof: backward induction; `a = π_h(s)`; if
  `n = 0`, `\Zt - \Zr ≤ e^{β(H+1-h)} - 1 ≤ c_h`; else lem:certificate_pos, the induction
  hypothesis inside `\phat` (lem:emp_trans_simplex) and the min with the clip
  (`\Zt - \Zr ≤ e^{β(H+1-h)} - 1 ≤ c_h`, lem:backups_range, lem:ring_pos).
* lem:stopping_pos — (Lemma 9) on `\evGood^+`, for all `t, h, s`:
  `Z^*_h(s) - Z^π_h(s) ≤ (π_h G^t_h)(s)`. Proof: lem:optimism_pos, lem:ring_pos,
  lem:cert_dominates_gap_pos.
* lem:pac_at_stopping_pos — on `\evGood^+`, if the stopping condition (def:stopping_rule)
  holds after `t` episodes then `V^*_1(s_1) - V^π_1(s_1) ≤ ε` for `π = π^{t+1}`. Proof:
  the condition is `πG ≤ (e^{βε} - 1)(\Zt_1 - πG)(s_1)`; `\Zt_1 - πG ≤ \Zr_1 ≤ Z^π_1`
  (lem:cert_dominates_gap_pos, lem:ring_pos); `Z^*_1 - Z^π_1 ≤ πG` (lem:stopping_pos);
  lem:value_gap_log.
* lem:cert_true_recursion_pos — on `\evGood^+`, for all `t, h, s`, with `a = π_h(s)`:
  `(π_h G^t_h)(s) ≤ e^{β r_h(s,a)}[36\sqrt{\Var_{p_h}(Z^π_{h+1})(s,a) ρ^{*t}_h(s,a)} + (1 + \frac{13}H)(p_h π_{h+1}G^t_{h+1})(s,a) + 84 H e^{β(H+1-h)} ρ^t_h(s,a)]`
  (def:rate_min). Proof (Appendix B.1, "Sample complexity"): if `n = 0` or `α(n)/n ≥ 1`,
  the clip `c_h = e^{β(H+1-h)} ≤ 84 H e^{β(H+1-h)} ρ` (`ρ = 1`). Otherwise `ρ = α/n`,
  `ρ^* = α^*/n`: (i) lem:kl_bernstein for `f = π_{h+1}G^t_{h+1} ∈ [0, e^{β(H-h)}]`
  (lem:certificate_range) on `\evKL`: `|(\phat - p_h) f| ≤ \sqrt{2\Var_{p_h}(f) α/n} + \frac23 e^{β(H-h)} α/n`,
  `\Var_{p_h}(f) ≤ e^{β(H-h)} p_h f`, lem:sqrt_mul_le: `≤ \frac1H p_h f + 3 H e^{β(H-h)} α/n`;
  (ii) the bonus under the true kernel: lem:kl_transport_var (`\Var_{\phat}(\Zt) ≤ 2\Var_{p_h}(\Zt) + 4e^{2β(H-h)}α/n`),
  lem:transport_var (`\Var_{p_h}(\Zt) ≤ 2\Var_{p_h}(Z^π) + 2e^{β(H-h)} p_h(\Zt - Z^π)`, as
  `Z^π ≤ Z^* ≤ \Zt`, lem:opt_exp_value_eq, lem:optimism_pos), `\Zt_{h+1} - Z^π_{h+1} ≤ \Zt - \Zr ≤ π_{h+1}G_{h+1}`
  (lem:ring_pos, lem:cert_dominates_gap_pos), lem:sqrt_add_le, lem:sqrt_mul_le, `α^* ≤ α`:
  `b ≤ 6\sqrt{\Var_{p_h}(Z^π_{h+1}) α^*/n} + \frac{2\sqrt2}{H} p_h π G_{h+1} + 27 H e^{β(H-h)} α/n`;
  (iii) combine in `G ≤ e^{βr}[3b + (1 + \frac3H)(\phat πG_{h+1})]` and simplify with
  `H ≥ 1`, `e^{β(H-h)} ≤ e^{β(H+1-h)}`. Verify the constants `36`, `13`, `84`.
* lem:cert_unrolled_pos — on `\evGood^+`, for all `t`:
  `(π_1 G^t_1)(s_1) ≤ e^{13}\E^π_{(s_1,1)}[\sum_{h=1}^H e^{β\sum_{i ≤ h} r_i(S_i,A_i)}(36\sqrt{\Var_{p_h}(Z^π_{h+1})(S_h,A_h)ρ^{*t}_h(S_h,A_h)} + 84 H e^{β(H+1-h)} ρ^t_h(S_h,A_h))]`.
  Proof: lem:unroll_recursion with `κ = 1 + 13/H`, `g_h = π_h G^t_h`, `g_{H+1} = 0`, and
  lem:one_add_div_pow_le_exp (`κ^{h-1} ≤ e^{13}`).
* lem:ratio_bound_pos — on `\evGood^+`, for all `t`:
  `(π_1 G^t_1)(s_1)/\Zt^t_1(s_1) ≤ e^{13}[36\sqrt{V_G · x_t} + 84 H e^{β(H+1)} y_t]` where
  `V_G := (e^{β\Gmax} - 1)^2/e^{β\Gmax}`, `x_t := \sum_h \sum_{s,a} p^π_h(s,a) ρ^{*t}_h(s,a)`,
  `y_t := \sum_h\sum_{s,a} p^π_h(s,a) ρ^t_h(s,a)` (def:occupancy). Proof: `\Zt_1 ≥ Z^*_1 ≥ Z^π_1 > 0`
  (lem:optimism_pos, lem:opt_exp_value_eq, lem:exp_value_range); divide lem:cert_unrolled_pos
  by `Z^π_1(s_1)`; lem:cauchy_schwarz_traj; lem:entropic_variance_sum and lem:variance_ratio_le
  for the first term; `e^{β\sum_{i≤h} r_i} ≤ e^{βh}` for the second; lem:occupancy_expectation.
* lem:progress_pos — on `\evGood^+`, for every `t` at which the stopping condition fails,
  `κ(β, ε) ≤ (π_1 G^t_1)(s_1)/\Zt^t_1(s_1)` with `κ(β,ε) := (e^{|β|ε} - 1)e^{-2|β|ε}/2`
  (def:upper_bound_const; `(e^{βε}-1)/e^{βε} ≥ κ`).
* lem:stopping_time_bound_pos — on `\evGood^+`, `τ ≤ \mathrm{upperBound}(S, A, H, β, ε, δ, \Gmax)`
  (def:upper_bound_const); in particular `τ < ∞`. Proof: let `T ≥ 1` with `T ≤ τ` (the
  condition fails for all `t < T`); sum lem:progress_pos and lem:ratio_bound_pos over
  `t < T`; Cauchy–Schwarz `\sum_{t<T}\sqrt{x_t} ≤ \sqrt{T}\sqrt{\sum_{t<T} x_t}`;
  lem:sum_counts_bound (on `\evCnt`) for `\sum_{t<T} x_t` and `\sum_{t<T} y_t` with
  `α^*(T-1) ≤ A_0 + L`, `α(T-1) ≤ A_0 + S L`, `\log(T+1) ≤ L := \log(8eT)`, `A_0 := \log(3SAH/δ)`;
  this gives `T ≤ C\sqrt{T(A_0 L + L^2)} + D(A_0 L + S L^2)` with the `C, D` of
  def:upper_bound_const; lem:self_bounding gives `T ≤ \mathrm{upperBound}`. If `τ = ∞` every
  `T` qualifies, contradiction; so `τ ≤ \mathrm{upperBound}`.
* lem:pac_pos — `\Prob(V^*_1(s_1) - V^{out}_1(s_1) > ε) ≤ δ` (and `\Prob(τ ≤ \mathrm{upperBound}) ≥ 1-δ`).
  Proof: on `\evGood^+`, `τ < ∞` (lem:stopping_time_bound_pos), the stopping condition holds
  after `τ` episodes and `out = π^{τ+1}` (lem:entropic_bpi_run), so lem:pac_at_stopping_pos
  applies; lem:good_event.

---------------------------------------------------------------------------------------------

## analysis_neg.tex — `\chapter{Analysis of Entropic-BPI for \texorpdfstring{$\beta < 0$}{beta < 0}}\label{chap:analysis_neg}`

Paper: Appendix B.2 (Lemmas 12–16, the sample complexity proof). Mirror of chap:analysis_pos
with `β < 0`: ranges `[e^{β(H-h)}, 1]`, `b_h = 1 - e^{β(H-h)}`, `\Zt = \min_a \Ut`,
`\Zl = \min_a \Ul`, `π = \argmin_a \Ul`, `\Ur = \max\{e^{βr}p_h\Zr, \Ur_{opt}\}`, the
certificate clip `1`, optimism `\Zl ≤ Z^* ≤ \Zt` still, and the bridge goes the other way
(`\Zr ≥ \max\{\Zt, Z^π\}`, `\Zr - \Zl ≤ πG`). Labels (same proofs, mirrored):
* lem:concentration_neg — (Lemma 12) `|(p_h - \phat)Z^*_{h+1}| ≤ 2\sqrt2\sqrt{\Var_{\phat}(\Zl^t_{h+1})α^*/n} + 5(1 - e^{β(H-h)})α/n + 4H(1 - e^{β(H-h)})α^*/n + \frac1H\phat|Z^*_{h+1} - \Zl^t_{h+1}|`
  (transport with `f = Z^* - e^{β(H-h)}`, `g = \Zl - e^{β(H-h)}` in `[0, 1 - e^{β(H-h)}]`).
* lem:optimism_neg — (Lemma 13) `\Ul ≤ U^* ≤ \Ut`, `\Zl ≤ Z^* ≤ \Zt` (min over `a`,
  lem:opt_bellman for `β < 0`).
* lem:ring_neg — (Lemma 15) `\Ur ≥ \max\{\Ut, U^π\}`, `\Zr ≥ \max\{\Zt, Z^π\}`.
* lem:certificate_neg — (Lemma 16) for `n ≥ 1`: `\Ur - \Ul ≤ e^{βr}[3b + (1 + \frac3H)\phat(\Zr_{h+1} - \Zl_{h+1})]`.
* lem:cert_dominates_gap_neg — `\Zr^t_h - \Zl^t_h ≤ π_h G^t_h` (unvisited: `≤ 1 - e^{β(H+1-h)} ≤ 1`).
* lem:stopping_neg — (Lemma 14) `Z^π_h(s) - Z^*_h(s) ≤ (π_h G^t_h)(s)`.
* lem:pac_at_stopping_neg — stopping condition `πG ≤ (1 - e^{βε})\Zl_1(s_1)` and
  `\Zl_1 ≤ Z^*_1 ≤ Z^π_1`... careful: for `β < 0`, `Z^π_1 ≤ Z^*_1` (lem:opt_exp_value_eq);
  the argument: `Z^π_1 - Z^*_1 ≤ πG ≤ (1 - e^{βε})\Zl_1 ≤ (1 - e^{βε}) Z^π_1`?? — no:
  `\Zl_1 ≤ Z^*_1` and we need a lower bound on `Z^π_1`; use `Z^π_1 ≥ \Zr_1 - πG`... the paper
  (end of B.2) uses `Z^π_1 ≥ \Zl_1`, which follows from `Z^π_1 ≥ ?`. Derive it correctly:
  lem:ring_neg gives `Z^π_1 ≤ \Zr_1`, not a lower bound. Instead use lem:value_gap_log for
  `β < 0`: `V^* - V^π = |β|^{-1}\log(Z^π_1/Z^*_1) ≤ |β|^{-1}\log(1 + (Z^π_1 - Z^*_1)/Z^*_1)` and
  `Z^π_1 - Z^*_1 ≤ πG ≤ (1 - e^{βε})\Zl_1 ≤ (1 - e^{βε}) Z^*_1` (lem:optimism_neg), so
  `Z^π_1/Z^*_1 ≤ 2 - e^{βε} ≤ e^{-βε} = e^{|β|ε}` (`2 - x ≤ 1/x` for `x ∈ (0,1]`), giving
  `V^* - V^π ≤ ε`. Record this correction in a remark.
* lem:cert_true_recursion_neg — additive term `84 H ρ` (deviation 11), `Z^π_{h+1} - \Zl_{h+1} ≤ \Zr - \Zl ≤ πG_{h+1}`.
* lem:cert_unrolled_neg, lem:ratio_bound_neg (with `e^{β\sum r} ≤ 1`, `V_G = (e^{|β|\Gmax}-1)^2/e^{|β|\Gmax}`,
  denominator `Z^π_1 ≤ \Zr_1 ≤ \Zl_1 + πG`), lem:progress_neg (`πG > (1 - e^{βε})\Zl_1`
  implies `πG/(\Zl_1 + πG) ≥ (e^{|β|ε} - 1)/(2e^{|β|ε} - 1) ≥ κ(β,ε)`, and
  `πG/Z^π_1 ≥ πG/(\Zl_1 + πG)`), lem:stopping_time_bound_neg, lem:pac_neg.

---------------------------------------------------------------------------------------------

## sample_complexity.tex — `\chapter{Sample complexity of Entropic-BPI}\label{chap:sample_complexity}`

Paper: Theorem 4 (Section 4 and its appendix restatement), the counting argument of Appendix
B.1, Lemma 27. Combines the two sign chapters.

* def:rate_min — `ρ^t_h(s,a) := \min\{α(n_h^t(s,a))/n_h^t(s,a), 1\}` (`:= 1` if `n = 0`),
  `ρ^{*t}_h(s,a)` with `α^*`. Lean: `rateMin`, `klRateMinAt`, `starRateMinAt`.
* lem:pseudo_counts_bound — (Lemma 27) on `\evCnt`, for `α ≥ 0` nondecreasing with `x ↦ α(x)/x`
  nonincreasing on `[1, ∞)`, for all `t ≥ 1, h, (s,a)`:
  `\min\{α(n)/n, 1\} ≤ 4 α(\nbar)/\max\{\nbar, 1\}` with `n = n_h^t(s,a)`, `\nbar = \nbar_h^t(s,a)`
  (def:pseudo_counts, deviation 10), and `= 1 ≤ 4α(\nbar)/\max\{\nbar,1\}` when `n = 0` needs
  `α(\nbar) ≥ \max\{\nbar,1\}/4`: on `\evCnt`, `n = 0` gives `\nbar ≤ 2α^{cnt}`, and `α ≥ α^{cnt}`
  for the rates of def:rates... **state the lemma for the two rates `α, α^*` of def:rates**
  (which satisfy `α(x) ≥ α^{cnt} ≥ \max\{\nbar, 1\}/4`-type bounds only if `α^{cnt} ≥ 1/4`...).
  Write the proof of Ménard et al. (Lemma 7): case `\nbar ≤ 4α^{cnt}`... Do the case analysis
  fully and fix the hypotheses so that the statement is true; the version used later is
  `ρ^t_h(s,a) ≤ 4 α(t)/\max\{\nbar_h^t(s,a), 1\}` (`α` nondecreasing, `\nbar ≤ t`), which is what
  lem:sum_counts_bound needs; note `α(n, δ) ≥ \log 3 > 1` for `δ ≤ 1`.
* lem:sum_counts_bound — on `\evCnt`, for `T ≥ 1` and `α ∈ \{α(·,δ), α^*(·,δ)\}`:
  `\sum_{t=0}^{T-1}\sum_h\sum_{s,a} p^{π^{t+1}}_h(s,a)\min\{α(n_h^t(s,a))/n_h^t(s,a), 1\} ≤ 16 S A H α(T) \log(T + 1)`.
  Proof: lem:pseudo_counts_bound, `\nbar_h^{t+1} - \nbar_h^t = p^{π^{t+1}}_h(s,a) ∈ [0,1]`
  (lem:pseudo_counts_increments), lem:log_sum_bound per `(h, s, a)`, `\nbar_h^T ≤ T`.
* def:upper_bound_const — `κ(β,ε) := (e^{|β|ε} - 1)e^{-2|β|ε}/2`,
  `V_G := (e^{|β|G} - 1)^2/e^{|β|G}`, `A_0 := \log(3SAH/δ)`,
  `C := 10^9\sqrt{V_G S A H}/κ`, `D := 10^{10} e^{|β|(H+1)} H^2 S A/κ`,
  `C_1 := \frac85\log(11 (8e)^2 (A_0 + S)(C + D))`,
  `\mathrm{upperBound} := C^2(A_0 + 1)C_1^2 + (D + 2\sqrt D C)(A_0 + S)C_1^2 + 1`.
  Remark: `= \tilde O(e^{2|β|ε}(e^{|β|ε}-1)^{-2} V_G S A H)` + lower-order term, the paper's
  Theorem 4 form. Lean: `upperBound S A H β ε δ G`.
* lem:self_bounding — (Lemma 29, in chap:pre_analysis); used here.
* thm:upper_bound_pac — (Theorem 4, PAC) for `β ≠ 0`, `r` with values in `[0,1]`, `δ ∈ (0,1)`,
  `ε ∈ (0, 2/(|β| H S)]`, Entropic-BPI is `(ε,δ)`-PAC for entropic BPI with reward function
  `r` (def:entropic_pac). Proof: lem:pac_pos / lem:pac_neg for every `\mathcal M ∈ \mathcal M_r`,
  through the run-to-law translation of def:entropic_pac (the output law is the law of `out`
  in any run; runs exist: LML's canonical run). Lean:
  `Essakine2026Tight.isEntropicPAC_entropicBPI`. Lean remark: `IsPAC` is about
  `outputMeasure`; prove `P(bad) ≤ δ` for the canonical run (`IdentAlg.IsRun` on the
  Ionescu-Tulcea space, LML) and transfer by `IsRun.hasLaw_output`.
* thm:upper_bound_complexity — (Theorem 4, sample complexity) same hypotheses, `\mathcal M ∈ \mathcal M_r`:
  in every run, `\Prob(τ ≤ \mathrm{upperBound}(S,A,H,β,ε,δ,\Gmax(\mathcal M))) ≥ 1 - δ`.
  Proof: lem:stopping_time_bound_pos / _neg and lem:good_event. Lean:
  `Essakine2026Tight.probReal_stoppingTime_entropicBPI_le_ge`.

---------------------------------------------------------------------------------------------

## lower_bound.tex — `\chapter{Lower bound}\label{chap:lower_bound}`

Paper: Section 3 (Theorem 3) and Appendix C. Target: thm:lower_bound.

* def:tree_depth — `d := ⌈\log_A((S-3)(A-1) + 1)⌉`; Assumption 1: `H ≥ 3d`. Lean: `treeDepth S A`.
* lem:tree_depth_props — `d ≥ 1`, `A^{d-1} < (S-3)(A-1) + 1 ≤ A^d` (for `S ≥ 6`, `A ≥ 2`), so the
  full tree of depth `d - 2` has fewer than `S - 3` nodes and the first `S - 3` nodes of the
  `A`-ary tree in breadth-first order have depth `≤ d - 1`.
* def:condition_a — Condition A (Appendix C): `c := e^{|β|H} - 1`; `e^{|β|ε} < \min\{4(c+1)^2/(2c^2+7c+4), 16/13\}`
  (`β > 0`), `e^{|β|ε} < \min\{(11c+8)/(10c+8), 11/10\}` (`β < 0`). Lean: `ConditionA β H ε`.
  Remark: the condition uses `c` with `H`, while the construction uses `c' = e^{|β|H'} - 1`
  with `H' ≤ H`; check that the admissibility `0 < p_- < p_+ < 1` (lem:hard_params_valid)
  holds with `c'` under Condition A stated with `c` (`c' ≤ c`; the functions of `c` in
  Condition A are monotone in the right direction — verify; if not, state Condition A with
  `H'` in place of `H`, `H' := H - ⌊H/3⌋ - d`, and record it).
* def:hard_tree — the tree: nodes `x_0` (root), `x_1, …, x_{S-4}` in breadth-first order of
  the `A`-ary tree (`x_i`'s children are `x_{Ai+1}, …, x_{Ai+A}` when they exist), depth
  `\mathrm{dep}(x_i) ≤ d - 1` (lem:tree_depth_props); `\mathrm{child}(x, a) := x_{A i + a}` if
  `A i + a ≤ S - 4`, `:= x_{A i + 1}` if that exists, else `x` is a leaf. Leaves
  `\mathcal L :=` childless nodes, `L := |\mathcal L|`. Lean: the states are
  `Fin S` (or an equivalent explicit type `HardState S`), the three special states and the
  tree nodes by index arithmetic.
* lem:tree_leaves — `L = (S-3) - ⌈(S-4)/A⌉ ≥ (S-4)/2 ≥ S/6` for `S ≥ 6`, `A ≥ 2` (every
  non-leaf has all `A` children except at most one; count internal nodes `= ⌈(S-4)/A⌉`).
* def:hard_params — `\bar H := ⌊H/3⌋ ≥ 1`, `\tilde H := \bar H + d + 1`, `H' := H - \bar H - d ≥ H/3`,
  `c := e^{|β|H'} - 1 > 0`; `β > 0`: `p_- := 1/(2(c+1))`, `Δ := (3c+2)(e^{βε}-1)/(c(c+1)(2 - e^{βε}))`;
  `β < 0`: `p_- := 1 - 1/(2(c+1))`, `Δ := (3c+2)(e^{|β|ε}-1)/(c(c+1)(e^{|β|ε} - 1/2))`;
  `p_+ := p_- + Δ`.
* lem:hard_params_valid — under Condition A, `0 < p_- < p_+ < 1` (both signs).
* def:hard_mdp — the instances `\mathcal M_0`, `\mathcal M_u` (`u ∈ \mathcal U := [\bar H] × \mathcal L × \As`)
  with horizon `H`, states `\{s_w, s_g, s_b\} ∪ \{x_0, …, x_{S-4}\}`, initial state `s_w`;
  transitions at step `h`: from `s_w`, `a_w` (a fixed action) keeps `s_w` if `h < \bar H`, any
  other action (or `h = \bar H`) leads to `x_0`; from an internal node `x`, action `a` leads to
  `\mathrm{child}(x,a)`; from a leaf `ℓ`, action `a` leads to `s_g` with probability
  `p_h(s_g | ℓ, a)` and to `s_b` otherwise, where `p_h(s_g|ℓ,a) = p_-` in `\mathcal M_0`, and
  in `\mathcal M_u`, `u = (h_e, ℓ^*, a^*)`: `= p_+` iff `(h, ℓ, a) = (h_e + 1 + \mathrm{dep}(ℓ^*), ℓ^*, a^*)`,
  `p_-` otherwise; `s_g`, `s_b` absorbing. Rewards `r_h(s,a) := \indic\{s = s_g\}\indic\{h ≥ \tilde H\}`
  (deterministic, in `[0,1]`); `r_0` denotes this reward function. Lean: `hardMDP S A H β ε (u : Option 𝒰)`.
* def:hard_triple — the triple `u(π) = (h_e(π), ℓ(π), a(π))` realized by a policy `π`: the exit
  step `h_e(π) := \min\{h ≤ \bar H : π_h(s_w) ≠ a_w\} ∧ \bar H`, the leaf reached by following
  `\mathrm{child}(·, π_h(·))` from `x_0` at step `h_e + 1`, the action `π_{h'}(ℓ)` at the
  arrival step `h' = h_e + 1 + \mathrm{dep}(ℓ)`. `π` *realizes* `u` iff `u(π) = u`.
* lem:hard_trajectory — under any instance and any `π`, from `s_w` at step `1`: the trajectory
  is deterministic up to the arrival at the leaf `ℓ(π)` at step `h'(π) ≤ \bar H + d`, then
  `S_{h'+1} ∈ \{s_g, s_b\}` with `\Prob(S_{h'+1} = s_g) = p_h(s_g | ℓ(π), a(π))`, and
  `S_h = S_{h'+1}` for all `h ≥ h' + 1`; in particular `S_{\tilde H} ∈ \{s_g, s_b\}` a.s. and
  `R_1^π = H'\indic\{S_{\tilde H} = s_g\}` a.s.
* lem:hard_success — `p^{\mathcal M}(π) := \Prob^{\mathcal M, π}(S_{\tilde H} = s_g)`;
  `p^{\mathcal M_0}(π) = p_-`, `p^{\mathcal M_u}(π) = p_+` if `π` realizes `u`, `p_-` otherwise.
* lem:hard_exp_value — `Z^π_1(s_w) = 1 + c\,p^{\mathcal M}(π)` (`β > 0`),
  `Z^π_1(s_w) = e^{βH'}(1 + c(1 - p^{\mathcal M}(π)))` (`β < 0`), `c = e^{|β|H'} - 1`.
* lem:hard_opt_value — `Z^*_1(s_w)` in `\mathcal M_u` is `1 + c p_+` (`β > 0`), resp.
  `e^{βH'}(1 + c(1 - p_+))` (`β < 0`): a policy realizing `u` exists, and lem:opt_exp_value_eq.
* lem:hard_eps_suboptimal — (eq. (hardness)) in `\mathcal M_u`, if `π` does not realize `u`
  then `V^*_1(s_w) - V^π_1(s_w) ≥ ε`. Proof: the choice of `Δ` (`β > 0`:
  `β^{-1}\log((1 + c(p_- + Δ))/(1 + c(p_- + Δ/2))) = ε` and `p_- ≤ p_- + Δ/2`; `β < 0` similarly).
* lem:hard_gmax — `\Gmax(\mathcal M_0) = H'` (a policy realizing any `u` reaches `s_g` with
  probability `p_- > 0`, and `R_1 ≤ H'`).
* lem:hard_pac_event — if `\mathcal A` is `(ε,δ)`-PAC for reward function `r_0` (def:entropic_pac),
  then for every run in `\mathcal M_u`, `\Prob_u(E_u) ≥ 1 - δ` where `E_u := \{out \text{ realizes } u\}`;
  and `\sum_u \Prob_0(E_u) ≤ 1` (the `E_u` are pairwise disjoint: `out` realizes exactly one triple).
* lem:hard_kl_episode — for every policy `π`, the state-sequence laws of the episode under
  `\mathcal M_0` and `\mathcal M_u` satisfy `\KL(ν_0(π) ‖ ν_u(π)) = \klbin(p_-, p_+)` if `π`
  realizes `u` and `= 0` otherwise. Proof: lem:hard_trajectory (the laws are images of the
  Bernoulli laws `Ber(p_-)`, `Ber(p_+)` under the same deterministic map; lem:klbin_bernoulli,
  data processing/injectivity — the map is injective on the support).
* lem:hard_change_of_measure — for every run of any `\mathcal A` and `u`, with `N_u(τ) :=
  \sum_{t < τ}\indic\{π^{t+1} \text{ realizes } u\}` (number of episodes with triple `u`):
  `\klbin(\Prob_0(E_u), \Prob_u(E_u)) ≤ \E_0[N_u(τ)]\,\klbin(p_-, p_+)` whenever `\E_0[τ] < ∞`.
  Proof: thm:change_of_measure (chap:pre_info) for the stationary environments
  `\mathrm{statesEnv}(\mathcal M_0)`, `\mathrm{statesEnv}(\mathcal M_u)` (def:episode_env),
  the algorithm `\mathcal A.\mathrm{alg}`, its stopping time `τ` (a.s. finite since
  `\E_0 τ < ∞`) and the event `E_u` (an event of the pair (stopped history, output),
  lem:kl_output_pair), with `\sum_a \E_0[N_a(τ)]\KL(ν_0(a)‖ν_u(a)) = \E_0[N_u(τ)]\klbin(p_-,p_+)`
  (lem:hard_kl_episode).
* lem:hard_kl_params — under Condition A: `\klbin(p_-, p_+) ≤ \frac{1521}{100}\frac{c+1}{c^2}(e^{βε}-1)^2`
  (`β > 0`), `≤ \frac{81}{4}\frac{c+1}{c^2}e^{2|β|ε}(e^{|β|ε}-1)^2` (`β < 0`). Proof:
  lem:klbin_upper (`≤ (p_+ - p_-)^2/(p_-(1-p_-))`), `p_-(1 - p_-) ≥ 1/(4(c+1))`... compute:
  `β > 0`: `p_-(1-p_-) = (2c+1)/(4(c+1)^2) ≥ 1/(4(c+1))`; then `Δ^2 ≤ ((3c+2)/(c(c+1)))^2 (e^{βε}-1)^2/(2 - e^{βε})^2`
  and `2 - e^{βε} ≥ 10/13`, `(3c+2)/(c+1) ≤ 3`. Verify the paper's constants and correct if
  needed (record).
* lem:hard_count_sum — `\sum_u N_u(τ) = τ` on `\{τ < ∞\}`; `\E_0[τ] = \sum_u \E_0[N_u(τ)]`.
* lem:hard_count_lower — for `δ ≤ 1/16`, `|\mathcal U| ≥ 2`, `x_u := \Prob_0(E_u)` with `\sum_u x_u ≤ 1`
  and `y_u := \Prob_u(E_u) ≥ 1 - δ`: `\sum_u \klbin(x_u, y_u) ≥ \sum_u[(1 - x_u)\log(1/δ) - \log 2] ≥ |\mathcal U|\log(1/δ)/4`
  (lem:klbin_lower; `\sum_u(1 - x_u) ≥ |\mathcal U| - 1 ≥ |\mathcal U|/2`, `\log(1/δ) ≥ 4\log 2`).
* def:lower_bound_const — `\mathrm{lowerBound}(S,A,H,β,ε,δ,G) := \frac{1}{5000}\frac{(e^{|β|G}-1)^2}{e^{|β|G}}\frac{e^{2\min\{β,0\}ε} S A H}{(e^{|β|ε}-1)^2}\log\frac1δ`.
  Lean: `lowerBound`.
* thm:lower_bound — (Theorem 3) `S ≥ 6`, `A ≥ 2`, `H ≥ 3d`, `β ≠ 0`, `δ ∈ (0, 1/16]`, `ε > 0`
  with Condition A: there are a reward function `r_0` with values in `[0,1]`, an MDP
  `\mathcal M_0` with reward function `r_0` and an initial state `s_1` such that every
  algorithm `\mathcal A` which is `(ε,δ)`-PAC for reward function `r_0` satisfies, in every run
  in the episode environment of `\mathcal M_0` from `s_1`,
  `\E_0[τ] ≥ \mathrm{lowerBound}(S,A,H,β,ε,δ,\Gmax(\mathcal M_0))`. Proof: if `\E_0 τ = ∞`
  done; else lem:hard_change_of_measure summed over `u` with lem:hard_count_sum,
  lem:hard_count_lower, lem:hard_pac_event: `\E_0[τ]\klbin(p_-,p_+) ≥ |\mathcal U|\log(1/δ)/4`;
  lem:hard_kl_params; `|\mathcal U| = \bar H L A ≥ (H/6)(S/6)A` (lem:tree_leaves,
  `\bar H = ⌊H/3⌋ ≥ H/6` for `H ≥ 3`); lem:hard_gmax (`c = e^{|β|\Gmax(\mathcal M_0)} - 1`);
  arithmetic to `1/5000` (verify: `β > 0`: `(100/1521)/(4·36) ≥ 1/2200`; `β < 0`:
  `(4/81)/(4·36) = 1/2916`). Lean: `Essakine2026Tight.exists_hardMDP_lowerBound_le_lintegral_stoppingTime`.

---------------------------------------------------------------------------------------------

# Part II: prerequisites to be added to Mathlib and LML

## prereq_mdp.tex — `\chapter{Finite-horizon MDPs: trajectories, occupancy measures and variances}\label{chap:pre_mdp}`

Library material (`Learning.MDP`), stated for an arbitrary finite-horizon MDP (def:episodic_mdp),
policy `π`, initial state `s_1`, and `\E^π := \E^π_{(s_1, 1)}`.
* def:occupancy — `p^π_h(s,a) := \Prob^π(S_h = s, A_h = a)` for `h ≤ H`. Lean: `occupancy M π s₁ h s a`.
* lem:occupancy_sum_one — `\sum_{s,a} p^π_h(s,a) = 1`; `p^π_h(s,a) = \indic\{a = π_h(s)\}\Prob^π(S_h = s)`.
* lem:occupancy_expectation — `\E^π[\sum_{h ≤ H} f_h(S_h, A_h)] = \sum_h\sum_{s,a} p^π_h(s,a) f_h(s,a)`.
* lem:occupancy_recursion — `p^π_{h+1}(s', a') = \indic\{a' = π_{h+1}(s')\}\sum_{s,a} p^π_h(s,a) p_h(s'|s,a)`.
* lem:unroll_recursion — if `g_h : \Ss → \R`, `h ≤ H + 1`, `g_{H+1} = 0`, `u_h : \Ss × \As → [0, ∞)`,
  `κ ≥ 1`, rewards `r_h ≥ 0`, and for all `h ≤ H`, `s`, with `a = π_h(s)`:
  `g_h(s) ≤ e^{β r_h(s,a)}[u_h(s,a) + κ (p_h g_{h+1})(s,a)]`, then
  `g_1(s_1) ≤ \sum_{h=1}^H κ^{h-1}\E^π[e^{β\sum_{i ≤ h} r_i(S_i,A_i)} u_h(S_h,A_h)]`
  (for `β` of either sign; only `e^{βr} > 0` and monotonicity are used). Proof: backward
  induction on the statement "for all `h`, `\E^π[e^{β\sum_{i<h} r_i} g_h(S_h)] ≤ \sum_{h' ≥ h} κ^{h'-h}\E^π[e^{β\sum_{i≤h'} r_i} u_{h'}]`"
  using lem:step_law_markov (Markov property at step `h`).
* lem:cauchy_schwarz_traj — for `w_h ≥ 0`, `v_h, u_h ≥ 0` functions of `(S_h, A_h)`:
  `\E^π[\sum_h w_h\sqrt{v_h u_h}] ≤ \sqrt{\E^π[\sum_h w_h^2 v_h]}\sqrt{\E^π[\sum_h u_h]}`
  (Cauchy–Schwarz on `\sum_h \E^π`).
* def:entropic_variance — (paper, Lemma 23) `σQ^π_h(s,a) := \E^π[(e^{βR_h^π} - U^π_h(s,a))^2 | S_h = s, A_h = a]`
  (the variance of `e^{βR_h^π}` from `(s, a)` at step `h`), `σV^π_h(s) := σQ^π_h(s, π_h(s))`,
  `σV^π_{H+1} := 0`. Lean: `entropicVarQ`, `entropicVarV` (defined through `stepLaw` from
  `(x.2, h+1)` after the first transition, as in LMLPapers).
* lem:entropic_variance_recursion — (Lemma 23) for deterministic rewards:
  `σQ^π_h(s,a) = e^{2βr_h(s,a)}\Var_{S' ∼ p_h(s,a)}(Z^π_{h+1}(S')) + e^{2βr_h(s,a)}(p_h σV^π_{h+1})(s,a)`.
  Proof: `e^{βR_h} = e^{βr_h}e^{βR_{h+1}}`, law of total variance conditioning on `S_{h+1}`
  (lem:step_law_markov), `\E[e^{βR_{h+1}} | S_{h+1} = s'] = Z^π_{h+1}(s')`.
* lem:entropic_variance_sum — `\sum_{h=1}^H \E^π[e^{2β\sum_{i≤h} r_i(S_i,A_i)}\Var_{p_h}(Z^π_{h+1})(S_h,A_h)] = σV^π_1(s_1) = \Var_{\Prob^π}(e^{βR_1^π})`.
  Proof: multiply lem:entropic_variance_recursion by `e^{2β\sum_{i<h} r_i}`, take `\E^π`,
  telescope over `h` (lem:occupancy_expectation, lem:step_law_markov), `σV_{H+1} = 0`.
* lem:variance_ratio_le — `\Var_{\Prob^π}(e^{βR_1^π})/(Z^π_1(s_1))^2 ≤ (e^{|β|G} - 1)^2/e^{|β|G}`
  whenever `R_1^π ∈ [0, G]` a.s. (lem:normalized_variance_bound); in particular with `G = \Gmax`
  (lem:gmax_le_horizon).
* lem:visits_iid — (sampling at visits) in a run `(X, Y)` of any algorithm in the episode
  environment of `\mathcal M` (def:episode_env), for fixed `(h, s, a)`: let `T_k` be the
  episode of the `k`-th visit of `(s, a)` at step `h` and `W_k := s^{T_k}_{h+1}` the observed
  next state; then conditionally on `k ≤ n_h^t(s,a)`-type events... precisely: the sequence
  `(W_k)_{k ≥ 1}` (on the event that the `k`-th visit happens) is i.i.d. with law
  `p_h(· | s, a)`, and independent of `T_k`... **State the form actually needed**: (i) for
  the KL event: the empirical distribution `\phat_h^t(· | s,a)` is the empirical distribution
  of `W_1, …, W_{n}` with `n = n_h^t(s,a)` (lem:emp_trans_reindex), and for every `n ≥ 1`,
  `\Prob(\KL(\hat q_n ‖ p_h(s,a)) > x, \text{the } n\text{-th visit happens}) ≤ \Prob_{iid}(\KL(\hat q_n‖p) > x)`
  (the law of `(W_1,…,W_n)` on the event of `n` visits is dominated by the i.i.d. law:
  `\Prob(W_1 ∈ B_1, …, W_n ∈ B_n, T_n < ∞) ≤ \prod_i p_h(B_i | s,a)` — proved by induction with
  lem:episode_env_law and the optional-sampling structure); (ii) for the Bernstein and counts
  events: the martingale-difference structure `\E[f(s^{t+1}_{h+1}) | \mathcal F_t, s^{t+1}_{≤ h}] = (p_h f)(s^{t+1}_h, a^{t+1}_h)`
  (lem:episode_env_law), which is what thm:bernstein_self_normalized and
  thm:bernoulli_concentration consume with the filtration of episodes. Lean remark: LML's
  `Online/Bandit/RewardByCountMeasure.lean` proves the i.i.d. law of "the reward of the `k`-th
  pull of arm `a`" for bandits; the episodic version is its analogue with the "arm" `(h,s,a)`
  and the "reward" `s_{h+1}` — a candidate for LML.
* lem:emp_trans_reindex — `\phat_h^t(· | s,a)` is the empirical distribution of the next
  states observed at the first `n_h^t(s,a)` visits.
* lem:count_le_episodes — `n_h^t(s,a) ≤ t`, `\sum_{s,a} n_h^t(s,a) = t`.

## prereq_concentration.tex — `\chapter{Concentration inequalities}\label{chap:pre_concentration}`

Paper: Appendix E (Lemmas 19–22), Appendix F (Lemmas 25, 26). Mathlib-shaped statements.
* lem:type_prob_le — `X_1..X_n` i.i.d. with law `p` on a finite set of size `m`, `\hat p_n` the
  empirical distribution; for every probability vector `q` which is a type (`n q_i ∈ \N`):
  `\Prob(\hat p_n = q) ≤ e^{-n \KL(q‖p)}` (method of types, Cover–Thomas 11.1.4).
* lem:num_types — the number of types is at most `(n+1)^{m-1}`... (`\binom{n+m-1}{m-1} ≤ (n+1)^{m-1}`).
* thm:sanov_hp — (Lemma 19) with probability at least `1 - δ`,
  `\KL(\hat p_n ‖ p) ≤ ((m-1)\log(n+1) + \log(1/δ))/n`. Proof: union over types with
  `\KL(q‖p) > x`: `\Prob(\KL(\hat p_n‖p) > x) ≤ (n+1)^{m-1}e^{-nx}`. Lean remark: `klDiv` of
  `weightedMeasure`s on `Fin m`; the sample `X : Fin n → Ω → Fin m` with `iIndepFun` and `HasLaw`.
* lem:bernoulli_mgf_step — for `X ∈ \{0,1\}` with `\Prob(X = 1 | \mathcal G) = P`:
  `\E[e^{P/2 - X} | \mathcal G] ≤ 1` (`1 - P + P/e ≤ e^{-P/2}`).
* lem:ville — (Ville's maximal inequality) a nonnegative supermartingale `M` with `M_0 ≤ 1`
  satisfies `\Prob(\exists n, M_n ≥ 1/δ) ≤ δ`. Lean remark: check Mathlib's
  `MeasureTheory.Supermartingale`/`maximal_ineq` API; otherwise derive from Doob's maximal
  inequality for the stopped process.
* thm:bernoulli_concentration — (Lemma 20, Dann et al. 2017, F.4) adapted Bernoulli `X_i`,
  predictable `P_i = \Prob(X_i = 1 | \mathcal F_{i-1})`:
  `\Prob(\exists n, \sum_{t ≤ n} X_t < \sum_{t ≤ n} P_t/2 - \log(1/δ)) ≤ δ`. Proof:
  `M_n := \exp(\sum_{t ≤ n}(P_t/2 - X_t))` is a nonnegative supermartingale (lem:bernoulli_mgf_step);
  lem:ville.
* lem:poisson_cramer — `h(x) := (x+1)\log(x+1) - x`; `h ≥ 0`, `h(x) ≥ \frac{x^2}{2(1 + x/3)}`;
  and the inversion `(v + 1)h(s/(v+1)) ≥ ℓ ⟹ s ≤ \sqrt{2(v+1)ℓ} + ℓ`-type bound used for
  cor:bernstein_explicit (make the statement precise; Ménard et al. Lemma 9's proof).
* lem:bernstein_exp_supermartingale — for `λ ∈ \R`: `\E[\exp(λ w_t Y_t - w_t^2(e^{λ b} - 1 - λ b)/b^2 \E[Y_t^2|\mathcal F_{t-1}]) | \mathcal F_{t-1}] ≤ 1`
  under `|Y_t| ≤ b`, `\E[Y_t|\mathcal F_{t-1}] = 0`, `w_t ∈ [0,1]` predictable; hence
  `\exp(λ S_t - φ(λ) V_t/b^2)` with `φ(λ) = e^{λb} - 1 - λb` is a supermartingale.
* thm:bernstein_self_normalized — (Lemma 21, Ménard et al. 2021, Lemma 9)
  `\Prob(\exists t ≥ 1, (V_t/b^2 + 1) h(b|S_t|/(V_t + b^2)) ≥ \log(1/δ) + \log(4e(2t+1))) ≤ δ`.
  Proof: for each `t`, the peeling/mixture argument over `λ` (the paper of Ménard et al.:
  a "stitching" with `λ` chosen from `V_t`, union bound over `t` with weights `1/(4e(2t+1))`...
  follow their proof and decompose into named steps).
* cor:bernstein_explicit — with probability `≥ 1 - δ`, for all `t ≥ 1`:
  `|S_t| ≤ \sqrt{2V_t\log(4e(2t+1)/δ)} + 3b\log(4e(2t+1)/δ)` (lem:poisson_cramer).
* lem:donsker_varadhan_finite — for probability vectors `p, q` on a finite set and `g`:
  `\KL(p‖q) ≥ p g - \log(q e^{g})` (Gibbs variational principle; Mathlib may have
  `klDiv` variational forms — check `Mathlib.InformationTheory.KullbackLeibler`).
* lem:bernstein_mgf_bounded — for `f ∈ [0, b]` and a probability vector `q`, `λ ≥ 0`:
  `\log(q e^{λ(f - qf)}) ≤ \Var_q(f)(e^{λb} - 1 - λb)/b^2`.
* lem:kl_bernstein — (Lemma 22, Talebi–Maillard 2018) `\KL(p‖q) ≤ α`, `f ∈ [0, b]`:
  `|pf - qf| ≤ \sqrt{2\Var_q(f)α} + \frac23 bα`. Proof: lem:donsker_varadhan_finite with
  `g = λ(f - qf)`, lem:bernstein_mgf_bounded, optimize `λ` (both signs of `f - qf`).
* lem:kl_transport_var — (Lemma 25, Ménard et al. Lemma 11) `\KL(p‖q) ≤ α`, `f ∈ [0,b]`:
  `\Var_q(f) ≤ 2\Var_p(f) + 4b^2α` and `\Var_p(f) ≤ 2\Var_q(f) + 4b^2α`. Proof: lem:kl_bernstein
  applied to `f^2` and to `f` (or to `(f - pf)^2`), `\sqrt{ab} ≤ a/2 + b/2`.
* lem:transport_var — (Lemma 26, Ménard et al. Lemma 12) `f, g ∈ [0, b]`:
  `\Var_p(f) ≤ 2\Var_p(g) + 2b\,p|f - g|` and `\Var_q(f) ≤ \Var_p(f) + 3b^2\norm{p - q}_1`.
* lem:var_le_range_mean — for `f ∈ [0, b]`: `\Var_p(f) ≤ p f^2 ≤ b\,p f`.

## prereq_info.tex — `\chapter{Change of measure}\label{chap:pre_info}`

Paper: Lemma 17 (Kaufmann, Cappé, Garivier 2016, Lemma 1). LML-shaped statements.
* def:klbin — `\klbin(x, y) := x\log(x/y) + (1-x)\log((1-x)/(1-y))` for `x, y ∈ [0,1]`
  (`\klbin(0,0) = \klbin(1,1) = 0`; `+∞` when `y ∈ \{0,1\}` and `x ≠ y`, or state the
  inequalities below only for `y ∈ (0,1)`). Lean: `klBin` (LMLPapers `Pinsker.lean`).
* lem:klbin_bernoulli — `\KL(\mathrm{Ber}(x) ‖ \mathrm{Ber}(y)) = \klbin(x,y)` for `y ∈ (0,1)`
  (Mathlib `bernoulliMeasure`/`PMF.bernoulli`; colt-2026-83 `KLBer.lean`).
* lem:klbin_le_kl — (data processing to an event) for probability measures `μ, ν` and a
  measurable set `E`: `\klbin(μ(E), ν(E)) ≤ \KL(μ‖ν)` (Mathlib `klDiv_map_le` with the map
  `\indic_E`, lem:klbin_bernoulli).
* lem:klbin_lower — for `x ∈ [0,1]`, `y ∈ (0,1)`: `\klbin(x,y) ≥ (1-x)\log(1/(1-y)) - \log 2`.
* lem:klbin_upper — for `x ∈ [0,1]`, `y ∈ (0,1)`: `\klbin(x, y) ≤ (x-y)^2/(y(1-y))`
  (`\log u ≤ u - 1`).
* lem:kl_history_le — (divergence decomposition, finite horizon) for stationary environments
  `\mathrm{stationaryEnv}(ν)`, `\mathrm{stationaryEnv}(ν')` with `ν, ν' : \As → Δ(\mathcal Y)`
  Markov kernels on a finite action set, any algorithm and `n ∈ \N`:
  `\KL(\mathrm{law}_ν(\hist_n) ‖ \mathrm{law}_{ν'}(\hist_n)) = \sum_a \E_ν[N_a(n)]\KL(ν_a‖ν'_a)`
  where `N_a(n)` is the number of rounds `t < n` with `A_t = a`. LML: `SequentialLearning/DivergenceDecomposition.lean`
  (`IsAlgEnvSeq.klDiv_map_history` or the current name — check and cite).
* lem:kl_stopped_hist_le — (divergence decomposition at a stopping time) same setting, `τ` a
  stopping time of the history filtration with `\E_ν[τ] < ∞` (or a.s. finite): the laws of the
  stopped history (LML `stoppedHistMeasure alg env stopSet`) satisfy
  `\KL(\mathrm{law}_ν(\hist_τ) ‖ \mathrm{law}_{ν'}(\hist_τ)) ≤ \sum_a \E_ν[N_a(τ)]\KL(ν_a‖ν'_a)`.
  Proof: the stopped history is the image of `\hist_n` truncated... route: for the finite
  truncations `τ ∧ n`, the stopped history at `τ ∧ n` is a measurable function of `\hist_n`, so
  data processing and lem:kl_history_le give `\KL_n ≤ \sum_a\E_ν[N_a(τ ∧ n)]\KL(ν_a‖ν'_a)`;
  as `n → ∞` the laws of `\hist_{τ ∧ n}` converge (they agree with the law of `\hist_τ` on
  `\{τ ≤ n\}`) and lower semicontinuity of `\KL` (or the monotone convergence of the
  restrictions, `klDiv` of restricted measures: colt-2026-83 `KLStoppedPrefix.lean`,
  `Maiti2026Power/Mathlib/InformationTheory/KLStoppedPrefix.lean`) gives the bound. Lean
  remark: look at LML's `StoppedHistory.lean` (`stoppedHistMeasure`, `sigmaHistory`) and
  `DivergenceDecomposition.lean` before designing; the `τ ∧ n` truncations are the stopping
  times of the `IdentAlg` with stopping set `stopSet ∪ \{|h| = n\}`.
* lem:kl_output_pair — if the output is drawn from the same Markov kernel `ρ` of the stopped
  history under both environments, `\KL(\mathrm{law}_ν(\hist_τ, out) ‖ \mathrm{law}_{ν'}(\hist_τ, out)) = \KL(\mathrm{law}_ν(\hist_τ)‖\mathrm{law}_{ν'}(\hist_τ))`
  (chain rule for `μ ⊗ₘ ρ`, LML `ForMathlib/InformationTheory/KullbackLeibler/CompProd.lean`).
* thm:change_of_measure — (Lemma 17) same setting, every event `E` of `(\hist_τ, out)`:
  `\klbin(\Prob_ν(E), \Prob_{ν'}(E)) ≤ \sum_a\E_ν[N_a(τ)]\KL(ν_a‖ν'_a)` (lem:klbin_le_kl,
  lem:kl_output_pair, lem:kl_stopped_hist_le); the paper's `\sup_E` form is the same statement.
  Lean: the `Essakine2026Tight/LeanMachineLearning/SequentialLearning/ChangeOfMeasure.lean` file.

## prereq_analysis.tex — `\chapter{Elementary inequalities}\label{chap:pre_analysis}`

Paper: Appendix F (Lemmas 24, 28, 29) and the inequalities used in the proofs.
* lem:sqrt_add_le — `\sqrt{a + b} ≤ \sqrt a + \sqrt b` for `a, b ≥ 0`.
* lem:sqrt_mul_le — `\sqrt{ab} ≤ \frac{ηa}{2} + \frac{b}{2η}` for `a, b ≥ 0`, `η > 0`
  (hence `≤ ηa + b/η`).
* lem:one_add_div_pow_le_exp — `(1 + a/H)^{h} ≤ e^{a}` for `a ≥ 0`, `0 ≤ h ≤ H`, `H ≥ 1`.
* lem:bhatia_davis — `Y ∈ [m, M]` a.s. with mean `μ`: `\Var(Y) ≤ (M - μ)(μ - m)`.
* lem:normalized_variance_bound — (Lemma 24) `f ∈ [0, R]`, `Y = e^{βf}`, `m = \min(1, e^{βR})`,
  `M = \max(1, e^{βR})`: `Y ∈ [m, M]`, `\E Y ∈ [m, M]`, `\Var(Y)/(\E Y)^2 ≤ (e^{|β|R} - 1)^2/(4e^{|β|R})`
  (lem:bhatia_davis and the maximization of `(M-μ)(μ-m)/μ^2` over `[m, M]`).
* lem:log_sum_bound — (Lemma 28) `u_t ∈ [0,1]`, `U_t := \sum_{i ≤ t} u_i`:
  `\sum_{t=0}^{T} u_{t+1}/\max\{U_t, 1\} ≤ 4\log(U_{T+1} + 1)`.
* lem:self_bounding — (Lemma 29, Ménard et al. Lemma 13) positive `A, B, C, D, E, α` with
  `1 ≤ B ≤ E`, `α ≥ e`, `τ ≥ 0` with `τ ≤ C\sqrt{τ(A\log(ατ) + B\log(ατ)^2)} + D(A\log(ατ) + E\log(ατ)^2)`:
  `τ ≤ C^2(A+B)C_1^2 + (D + 2\sqrt D C)(A+E)C_1^2 + 1`, `C_1 := \frac85\log(11α^2(A+E)(C+D))`.
  Proof: follow Ménard et al.; decompose (e.g. lem:log_le_sqrt: `\log(αx) ≤ ...`).
* lem:two_sub_le_inv — `2 - x ≤ 1/x` for `x ∈ (0, 1]`.
* lem:klbin bounds are in chap:pre_info.


---------------------------------------------------------------------------------------------

# Amendments after the chapters were written (2026-09-16)

The chapter authors found the following errors in the paper or in the outline above; the
chapters and the Lean statements follow the amended versions, which supersede the text above.

* **Bonus (def:bonus, `bonus`).** The third term is `4 H e^{β(H-h)} α(n)/n` (KL rate `α`, as in
  the statement of the paper's Lemma 7), not `α*`: with `α*` (as small as `α/S`) the certificate
  lemmas 11/16 cannot be proved (`rem:pos_constants_bonus`).
* **Lemma 29 (lem:self_bounding).** False as stated in the paper (counterexample in
  `prereq_analysis.tex`): the factor `(C + D)` in `C_1` must be squared. `def:upper_bound_const`
  and `logFactor` use `C_1 = (8/5) log(11 (8e)² (A_0 + S)(C + D)²)`; the lemma is proved for
  `A, B, C, D ≥ 0`, `E ≥ B`, `α ≥ e` (`D ≥ 1` for the `(C + D)²` form). Lemma 28 holds with the
  constant `3` (stated with `4`).
* **Lemma 27 (lem:pseudo_counts_bound).** Needs `α ≥ α^cnt ≥ 1` (the paper's monotonicity
  hypotheses alone are false); stated for the two rates of def:rates, all `t`, including
  `n = 0`. The counting argument (lem:sum_counts_bound) has constant `16`, not `3`.
* **Bernstein event (def:event_bern).** Non-strict inequality `≤` (the strict one gives an
  empty event for `β < 0` at `h = H`). Lean: `eventBern` with `≤`.
* **KL event (lem:event_kl_prob).** Proved through a time-uniform mixture-martingale bound
  (`lem:empirical_kl_time_uniform`, uses `lem:ville`, `lem:num_types`), not through
  `thm:sanov_hp` + a union bound over `n` (which diverges with the rate `α`).
* **Lower bound (chap:lower_bound).** The paper's bound `d(p₋, p₊) ≤ (p₊ - p₋)²/(p₋(1 - p₋))`
  is false (wrong argument of the χ²-type bound; `d(p₋,p₊) → ∞` as `p₊ → 1`). Condition A is
  restated for the *effective horizon* `H' = H - ⌊H/3⌋ - d` (the thresholds are increasing in
  `c`, so the paper's condition with `H` does not imply admissibility with `H'`) and with the
  margin `p₊ ≤ (1 + p₋)/2`: `e^{|β|ε} - 1 ≤ c(2c+1)/(4(3c+2))` (`β > 0`),
  `e^{|β|ε} - 1 ≤ c/(10c+8)` (`β < 0`), `c = e^{|β|H'} - 1`. `Δ = (q-1)(3c+2)/(c(c+1))`
  (`β > 0`), `(q-1)(3c+2)/(c(c+1)(2q-1))` (`β < 0`), `q = e^{|β|ε}`, so that non-realizing
  policies are strictly more than `ε`-suboptimal. `d(p₋,p₊) ≤ 72 (c+1)(q-1)²/c²` (both signs);
  `L ≥ (S-3)/2 ≥ S/4`, `|𝒰| ≥ 4`, `lem:hard_count_lower` with constant `1/2`; the final constant
  is `1/3456`, stated as `1/5000`. Lean: `ConditionA β (effHorizon S A H) ε`,
  `treeDepth S A = Nat.clog A ((S-3)(A-1)+1)`, `effHorizon S A H = H - H/3 - treeDepth S A`.
* **Analysis (chap:analysis_pos/neg).** Lemma 10/15: the difference of the two max/min
  arguments is `e^{βr}(1 + 1/H) p̂(Z̲ - Z̊)` (sign only matters). For `β < 0` the additive term
  of `lem:cert_true_recursion_neg` sits outside the factor `e^{βr}` (`e^{βr} ≤ 1` cannot absorb
  the clip `1`); the certificate range for `β < 0` is `1`. The progress `κ` is common to both
  signs; the final coefficients are `144 e^{13} √(V_G SAH)/κ ≤ 10^9` and
  `1344 e^{13} e^{|β|(H+1)} H² SA/κ ≤ 10^{10}`. The hypothesis `ε ≤ 2/(|β| H S)` is not used.
* **Miscellaneous.** `lem:unroll_recursion` holds for `κ ≥ 0` and arbitrary real `r`, `u`;
  `lem:cauchy_schwarz_traj` for general nonnegative bounded random variables; the filtration of
  the empirical chapter is `𝓕_t = σ(hist_t, X_t)`.
* **Concentration (chap:pre_concentration).** Lemma 21 proved by the method of mixtures
  (threshold `log(1/δ) + log(8(1+√(2t)))`, the paper's form as a corollary);
  `lem:bernstein_exp_supermartingale` for `λ ≥ 0` only; `lem:poisson_cramer` inversion with
  `2/3`; `thm:sanov_hp` is a fixed-`n` result referenced only in remarks; `lem:ville` for
  `E[M_0] ≤ 1`, any level `c`; Lemmas 22, 25 for `α ≥ 0`; Lemma 25 with `10/3`, `5/3` (stated
  `4`), Lemma 26 second part with `1` (stated `3`).
* **Change of measure (chap:pre_info).** `def:klbin` valued in `[0, ∞]`; `lem:kl_history_le`
  and `lem:kl_stopped_hist_le` are equalities (LML `IsAlgEnvSeq.klDiv_map_history`; stopped
  version two-sided, via `τ ∧ M` truncations as in the sister project's `KLStoppedPrefix.lean`);
  `thm:change_of_measure` is one-sided (a.s. finiteness under the first environment only) for
  every event of (stopped history, output), through `lem:pinfo_stopped_chain_rule`, lower
  semicontinuity and convexity of `klbin`; stopping times are taken as stopping rules.
