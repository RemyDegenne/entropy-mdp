# Errors in the paper and notable findings of the formalization

Paper: Essakine, Vernade, *Tight Sample Complexity Bounds for Entropic Best Policy
Identification*, COLT 2026 (arXiv 2605.13717 v1, `source/colt_main_draft.tex`). Lemma numbers
are the paper's (one counter for all environments; the appendix restatements of Theorems 4 and 3
are Theorems 6 and 18).

Each entry says what the paper states, why it is wrong or insufficient, and what the
formalization does instead (blueprint label and Lean name). "Blueprint" refers to
`blueprint/src/chapters/`. Entries marked *(statement)* change the meaning of a formalized
statement; the others only change proofs or constants. This file is maintained as the
formalization progresses.

## Errors that change the statements

1. **Theorem 3: the bound on the binary divergence is false.** *(statement)* Appendix C bounds
   $d(p_-, p_+) \le (p_+ - p_-)^2 / (p_-(1 - p_-))$. The elementary bound
   $d(x, y) \le (x - y)^2 / (y (1 - y))$ has the *second* argument in the denominator, so this is a
   bound on $d(p_+, p_-)$, not on $d(p_-, p_+)$; and $d(p_-, p_+) \to \infty$ as $p_+ \to 1$
   while Condition A only guarantees $p_+ < 1$ with no margin. Counterexample (admissible for
   the paper's Condition A): $c = 1$, $e^{\beta\varepsilon} = 1.23$, $p_- = 1/4$, $p_+ \approx 0.99675$,
   $d(p_-, p_+) \approx 3.7 > 1.61$ (the paper's bound). *Fix:* Condition A is restated with a
   margin equivalent to $p_+ \le (1 + p_-)/2$: $e^{|\beta|\varepsilon} - 1 \le c(2c+1)/(4(3c+2))$ for
   $\beta > 0$ and $e^{|\beta|\varepsilon} - 1 \le c/(10c + 8)$ for $\beta < 0$ (for $\beta < 0$ this is
   exactly the paper's $e^{|\beta|\varepsilon} \le (11c+8)/(10c+8)$; the paper's caps $16/13$ and
   $11/10$ are not needed). Then $d(p_-, p_+) \le \Delta^2 / (p_+(1-p_+)) \le 72 (c+1)(e^{|\beta|\varepsilon}-1)^2 / c^2$
   for both signs. Blueprint `def:condition_a`, `lem:hard_params_valid`, `lem:hard_kl_params`,
   `rem:lb_kl_paper`; Lean `ConditionA`.
2. **Theorem 3: Condition A is stated with the wrong horizon.** *(statement)* The paper states
   Condition A with $c = e^{|\beta| H} - 1$, but the construction uses
   $c' = e^{|\beta| H'} - 1$ with the effective horizon $H' = H - \bar H - d \le H$. The
   admissibility thresholds ($0 < p_- < p_+ < 1$) are increasing in $c$, so the condition with
   $H$ does not imply admissibility with $H'$. *Fix:* Condition A is assumed for
   $H' = H - \lfloor H/3 \rfloor - d$. Lean `effHorizon`, hypothesis
   `ConditionA β (effHorizon S A H) ε` of `exists_hardMDP_lowerBound_le_lintegral_stoppingTime`.
3. **Theorem 3: the gap $\Delta$ for $\beta < 0$ is off by a factor 2** from the equation
   $V^{\mathcal M_u,*} - V^{\mathcal M_u}(\pi) = \varepsilon$ it is supposed to solve, and for both
   signs the exact-$\varepsilon$ choice does not give the *strict* suboptimality that the PAC bad event
   ($V^* - V^{\hat\pi} > \varepsilon$) requires. *Fix:* $\Delta = (q-1)(3c+2)/(c(c+1))$ for
   $\beta > 0$ and $(q-1)(3c+2)/(c(c+1)(2q-1))$ for $\beta < 0$, $q = e^{|\beta|\varepsilon}$, so that a
   non-realizing policy is $|\beta|^{-1}\log(2q-1) > \varepsilon$ suboptimal. Blueprint
   `def:hard_params`, `lem:hard_eps_suboptimal`, `rem:lb_params`.
4. **Exploration bonus: the third term must carry the KL rate $\alpha$, not $\alpha^*$.**
   *(statement)* Equations (bonus positive) and (bonus_negative) have $4H e^{\beta(H-h)}\alpha^*(n)/n$,
   while the statement of Lemma 7 has $\alpha$. The proof of Lemma 11 needs
   $(2H + 2/3) e^{\beta(H-h)} \alpha(n)/n \le b_h^t$, which fails with $\alpha^*$ (as small as
   $\alpha/S$). *Fix:* the bonus uses $\alpha$ in its third term. Blueprint `def:bonus`,
   `rem:pos_constants_bonus`; Lean `bonus`.
5. **Clips of the optimistic backups and of the certificate are off by one (or two).**
   *(statement)* Section 4 and eq. (optimism_equation_positive) clip $\widetilde U_h^t$ at
   $e^{\beta(H-h-1)}$; with the paper's 1-indexed $h$, $U^*_h$ ranges in $[1, e^{\beta(H+1-h)}]$,
   so optimism $U^* \le \widetilde U$ fails at $h = H$ ($e^{-\beta} < 1 \le U^*_H$). The
   certificate clip $e^{\beta(H-h)}$ (Appendix B) does not dominate
   $\widetilde Z_H - \mathring Z_H \le e^{\beta} - 1$ when $\beta > \log 2$. *Fix:* clip
   $e^{\beta(H+1-h)}$ for both (Lean `Real.exp (β * (k + 1))` with $k = H - h$ steps after the
   step). Blueprint `def:backups`, `def:certificate`, `rem:algorithm_clips`,
   `rem:algorithm_cert_clip`; Lean `stepU`, `certStep`.
6. **Greedy policy for $\beta < 0$.** *(statement)* Algorithm 1 writes $\argmin_a \widetilde U$;
   the appendix analysis (Lemmas 14, 16) needs $\argmin_a \underline U$. *Fix:* $\argmin_a \underline U$.
   Blueprint `def:greedy`, `rem:algorithm_greedy_neg`; Lean `greedy`.
7. **Stopping condition for $\beta < 0$.** Appendix B.2 writes the threshold
   $(e^{\beta\varepsilon} - 1)\underline Z_1$, which is negative (the algorithm would never stop); the
   algorithm box's $(1 - e^{\beta\varepsilon})\underline Z_1$ is the intended one. Lean `stopCond`.
8. **Lemma 29 (self-bounding inequality, from Ménard et al. 2021) is false as stated.**
   *(statement, through the constant of Theorem 4)* Counterexample: $\alpha = e$, $B = E = 1$,
   $C = 1000$, $A = D = 10^{-6}$, $\tau = 4\cdot 10^8$ satisfies the hypothesis but violates the
   conclusion with $C_1 = \frac85\log(11\alpha^2(A+E)(C+D))$. *Fix:* the factor $(C + D)$ in
   $C_1$ must be squared: $C_1 = \frac85 \log(11 \alpha^2 (A+E)(C+D)^2)$ (proved for
   $A, B, C, D \ge 0$, $E \ge B$, $\alpha \ge e$, $D \ge 1$; the form with $(C + \sqrt D)^2$
   holds without $D \ge 1$). Blueprint `lem:self_bounding`, `lem:pana_self_bounding_core`,
   `rem:pana_self_bounding_paper`; Lean `logFactor`, `upperBound`.
9. **Theorem 4's final bound.** *(statement)* The "in particular" single-term form assumes that
   the first term of the two-term bound dominates, which the hypothesis
   $\varepsilon \le 2/(|\beta| H S)$ does not guarantee (the second term can dominate when
   $G_{\max}$ is small); the displayed two-term bound omits the absolute constants of its own
   $C$, $D$ (e.g. $(36 e^{13})^2$), and its $C_1$ is not Lemma 29's $C_1$ at its $C$, $D$. Its
   constant $C_2$ contains the typos $e^{\beta\varepsilon}$ (for $e^{|\beta|\varepsilon}$) and $e^{|\beta H}$.
   *Fix:* the formalized bound is the two-term bound obtained by applying (the corrected)
   Lemma 29 to the recursive inequality, with generous absolute constants ($10^9$, $10^{10}$ in
   $C$, $D$; the proof gives $144 e^{13}$ and $1344 e^{13}$). The hypothesis
   $\varepsilon \le 2/(|\beta| H S)$ is not used by the proof (kept for fidelity). Blueprint
   `def:upper_bound_const`, `rem:sc_constants`, `rem:sc_hypotheses`; Lean `coeffSqrt`,
   `coeffLin`, `upperBound`.
10. **Bernstein concentration event must be non-strict.** *(statement of the event)* With the
    paper's strict inequality, the event $\mathcal E^-$ is empty: at $h = H$,
    $Z^*_{H+1} \equiv 1$ and the range factor $1 - e^{\beta(H - H)} = 0$ make both sides $0$.
    *Fix:* "$\le$", which is what the Bernstein inequality gives anyway. Blueprint
    `def:event_bern`, `rem:empirical_bern_event`; Lean `eventBern`.

## Errors in proofs, fixed without changing the statements

11. **Lemma 27 (pseudo-counts):** its two monotonicity hypotheses do not suffice
    ($\alpha \equiv 1/8$, $n = 0$, $\bar n = 1/2$ is a counterexample); the proof needs
    $\alpha \ge \alpha^{\mathrm{cnt}} \ge 1$, which the rates of the paper satisfy
    ($\log(3SAH/\delta) \ge \log 3 > 1$). Also stated with the *random* pseudo-counts
    $\bar n_h^t = \sum_{i \le t} p^{\pi^i}_h(s,a)$ (conditional visit probabilities), which is
    what Lemma 20 controls and what the counting argument telescopes; the paper's
    $\bar n = \mathbb E[n]$ is a different (deterministic) quantity. Blueprint
    `lem:pseudo_counts_bound`, `def:pseudo_counts`, `rem:sc_lemma27`.
12. **Counting argument** (Appendix B.1): the constant is $16$ ($4$ from Lemma 27 and $4$ from
    Lemma 28), not $3$; the paper also writes $\alpha(\tilde n \vee 1)$ for
    $4\alpha(\tilde n)/(\tilde n \vee 1)$. Blueprint `lem:sum_counts_bound`.
13. **Lemma 5 (good event):** (a) the KL event cannot be obtained from Sanov's bound (Lemma 19)
    by a union bound over $n$: with the rate $\alpha(n) = \log(3SAH/\delta) + S\log(8e(n+1))$
    the terms $(n+1)^{S-1} e^{-\alpha(n)}$ form a harmonic series. The blueprint proves the
    time-uniform bound by a uniform-Dirichlet mixture martingale (Ville's inequality), with a
    threshold below $\alpha(n)/n$. (b) The Bernstein inequality is applied with the episode index
    $t$ while the rate is in the number of visits $n$; the blueprint indexes by visits. (c) The
    union bound needs $\delta_{h,s,a} = \delta/(3SAH)$, not $\delta/(SAH)$, to get $\delta/3$.
    Blueprint `lem:event_kl_prob`, `lem:empirical_kl_time_uniform`, `rem:empirical_sanov_union`,
    `rem:empirical_bernstein_index`.
14. **Lemma 11 (and 16):** the proof applies the KL-Bernstein inequality with the variance under
    $\hat p$, but $\mathrm{KL}(\hat p \| p_h) \le \alpha/n$ controls $|(\hat p - p_h) f|$ with the
    variance under $p_h$; a transport step (Lemmas 25, 26) is needed. Together with item 4 the
    constants $3$ and $3/H$ are then correct. Blueprint `lem:certificate_pos`,
    `rem:pos_constants_certificate`.
15. **Lemmas 7 and 12:** the proof takes $\sqrt{\mathrm{Var}\,\alpha^*/n}$ instead of
    $\sqrt{2\,\mathrm{Var}\,\alpha^*/n}$ (a $\sqrt2$ is dropped twice); the constants
    $2\sqrt2$, $5$, $4H$ are nevertheless correct via $\sqrt{\alpha\alpha^*} \le (\alpha+\alpha^*)/2$
    and a different AM–GM weight. Lemma 12's statement misses a $/n$ and has the exponent
    $H - hH$. Blueprint `lem:concentration_pos`, `lem:concentration_neg`.
16. **Lemmas 10 and 15:** the difference of the two max/min arguments is
    $e^{\beta r}(1 + 1/H)\hat p(\underline Z - \mathring Z)$, not $(1 - 1/H)$ (only the sign
    matters).
17. **True-kernel recursion** (Appendix B.1, "Sample complexity"): the paper's steps give
    $1 + 15.5/H$ (not $13/H$) and $81H + (1 + 3/H)3H \ne 84H$; the constants $36$, $13$, $84$
    do hold with a sharper AM–GM step. For $\beta < 0$, the additive term $84H(1 - e^{\beta(H-h)})$
    vanishes at $h = H$ and $e^{\beta r} \le 1$ cannot absorb the clip $1$ of an unvisited pair:
    the term is $84 H\,\rho$ outside the factor $e^{\beta r}$. Unvisited pairs (the paper's
    $\alpha(0)/0 = \infty$, "$\alpha(n) \wedge 1$") need the term $84H e^{\beta(H+1-h)}\rho$ to
    dominate the clip. Blueprint `lem:cert_true_recursion_pos/_neg`, `rem:neg_additive_term`.
18. **$\varepsilon$-optimality at stopping for $\beta < 0$:** the paper uses $Z^\pi_1 \ge \underline Z_1$
    without proof (true via $Z^\pi_1 \ge Z^*_1 \ge \underline Z_1$ for $\beta < 0$) and its last
    display has a sign error. Blueprint `lem:pac_at_stopping_neg`, `rem:neg_stopping`.
19. **Lemma 28:** holds with the constant $3$ (the paper's $4$ is stated).
20. **Theorem 3, counting:** $L \ge S/4$ is proved only for full trees ($S - 3 = (A^d - 1)/(A-1)$);
    for the first $S - 3$ nodes of the $A$-ary tree in breadth-first order (leaves = childless
    nodes) $L = (S-3) - \lceil (S-4)/A \rceil \ge (S-3)/2 \ge S/4$. $\bar H = H/3$ is not an
    integer ($\bar H = \lfloor H/3 \rfloor \ge H/6$). The factor $e^{2\min\{\beta,0\}\varepsilon}$ is an
    artifact of a loose bound and is not needed (kept, it is $\le 1$). With the corrected KL
    bound the constant is $1/3456$, stated as $1/5000$; the paper's $1/1650$ is not derivable.
    Blueprint `lem:tree_leaves`, `thm:lower_bound`, `rem:lb_constant`.
21. **Appendix A:** the KL event is written with the threshold $\alpha(n)$ instead of
    $\alpha(n)/n$. **Lemma 14:** its last sentence mixes $V$ and $Z$. **Definition 2:** does not
    require $\tau < \infty$ (the formalization's PAC property is about the output law; the
    sample complexity theorem gives $\tau < \infty$ with probability $1 - \delta$).

22. **Lemma 19 (Sanov):** the proof writes $(n+1)^m$ where the method of types gives
    $(n+1)^{m-1}$ (harmless). Blueprint `thm:sanov_hp`, `rem:pconc_sanov_paper`.
23. **Lemma 21 (self-normalized Bernstein):** the exponential-supermartingale lemma holds for
    $\lambda \ge 0$ only (not all real $\lambda$; the negative side is obtained from $-Y$); the
    inversion of the Poisson Cramér transform gives $s \le \sqrt{2c\ell} + \frac23\ell$ (constant
    $2/3$, not $1/3$). The blueprint proves the inequality by the method of mixtures, with the
    sharper threshold $\log(1/\delta) + \log(8(1 + \sqrt{2t}))$, from which the paper's
    $\log(4e(2t+1))$ form follows; the explicit form has $\frac53 b L_t$, stated with $3b$.
    Blueprint `thm:bernstein_self_normalized`, `cor:bernstein_explicit`,
    `rem:pconc_bernstein_constants`.
24. **Lemmas 25 and 26 (transportation of variances):** proved with the constants $10/3$, $5/3$
    (stated with $4$) and $1$ (stated with $3$) respectively; Lemma 22 and 25 hold for
    $\alpha \ge 0$. Blueprint `lem:kl_transport_var`, `lem:transport_var`.
25. **Lemma 17 (change of measure, Kaufmann–Cappé–Garivier):** the cited proof silently needs
    the event to lie in $\{\sigma < \infty\}$ under the second model too; the blueprint proves a
    one-sided version (almost sure finiteness under the first environment only, which is all
    the lower bound has: $\mathbb E_0[\tau] < \infty$), through the bounded stopping rules
    $\tau \wedge M$, lower semicontinuity and convexity of the binary divergence. Blueprint
    `thm:change_of_measure`, `rem:pinfo_one_sided`.

## Other notable findings

* The concentration events of Lemma 5 hold for *any* algorithm, not only Entropic-BPI (used
  as such in the blueprint).
* The bonus with the KL rate $\alpha$ (item 4) does not change the order of the sample
  complexity: the $\alpha$-term is absorbed by the additive $84H$ term, which is already in $\alpha$.
* The asymptotic form of the corrected Theorem 4 has $e^{4|\beta|\varepsilon}$ instead of the paper's
  $e^{2\max\{\beta,0\}\varepsilon}$, because a single progress constant
  $\kappa = (e^{|\beta|\varepsilon}-1)e^{-2|\beta|\varepsilon}/2$ is used for both signs; under
  $\varepsilon \le 2/(|\beta|HS)$ this factor is at most $e^8$.
* The Lean model needs no conditioning on null events: the entropic variance
  $\sigma Q^\pi_h(s,a)$ is defined through the law "play $a$ at $(s,h)$, then $\pi$", and the
  filtration of the empirical chapter is $\sigma(\mathrm{hist}_t, \pi^{t+1})$.
* Comparator (the tool that checks the headline statements) forced a coding discipline on the
  definitions: no nested proofs, no matchers, no real numerals $\ge 2$ (see
  `notes/lean-design.md`); this is a property of Lean's auxiliary declarations, not of the paper.

## Findings of phase 2 (proofs)

* **Chapter "Elementary inequalities" (2026-09-16).** Mathlib already has the Bhatia–Davis
  inequality (`ProbabilityTheory.variance_le_sub_mul_sub`), so the paper's Lemma 24 reduces to
  the algebraic maximization `sub_mul_sub_div_sq_le`, which needs no restriction of the mean to
  $[m, M]$. The root of the quadratic inequality $x^2 \le bx + c$ needs no sign assumption on
  $x$. The self-bounding inequality (Lemma 29) is proved in the sharp form
  $\tau \le K(\tfrac85\log M)^2 + 1$ for every $M \ge 4\alpha K$, from which both the
  $(C + \sqrt D)^2$ and the $(C + D)^2$ forms of $C_1$ follow; the bound
  $\log y \le y^\gamma/(e\gamma)$ used for it sharpens Mathlib's `Real.log_le_rpow_div` by a
  factor $e$. The logarithmic sum bound (Lemma 28) is stated for sums over $t < T$ with the
  bound $3\log(U_T + 1)$ (and $4\log(U_T + 1)$).
* **Chapter "Model" (`chap:mdp`, 2026-09-16).** The exponential Bellman equation
  $Z^\pi_h(s) = U^\pi_h(s, \pi_h(s))$ is *false* for general reward kernels when the value is a
  Bochner integral: if the exponential return is not integrable its integral is $0$ while the
  right-hand side can be positive. The formalization proves the identity for the Lebesgue
  integrals without hypothesis and for the values under the hypothesis that the rewards have
  finite exponential moments of order $\beta$ (automatic for the paper's deterministic rewards in
  $[0, 1]$). The ranges of $Z^\pi$, $U^\pi$, $Z^*$, $U^*$ follow analytically from the Bellman
  equation; the optimal Bellman equation and the optimality of the greedy policy need only finite
  exponential moments (not a reward function in $[0, 1]$), and the value-gap identities only
  $Z^\pi_h(s) > 0$. The Markov property of the trajectory law of a stationary policy
  (not in LML) is proved by uniqueness of the Ionescu–Tulcea measure.
* **Chapter "Change of measure" (`chap:pre_info`, 2026-09-16).** The one-sided change of measure
  (the paper's Lemma 17 with $\tau$ almost surely finite under the first environment only) is
  proved; mutual absolute continuity of the arm distributions is not needed ($0 \cdot \infty = 0$
  in $[0, \infty]$). The convexity step of the proof only needs the bound
  $\klbin(x, y) \le \max\{\klbin(x, y_1), \klbin(x, y_2)\}$ for $y \in [y_1, y_2]$, proved by
  unimodality ($\partial_y \klbin(x, y) = (y - x)/(y(1 - y))$), and the lower bound
  $\klbin(x, y) \ge (1 - x)\log\frac1{1 - y} - \log 2$ does not need $x \le 1$. The proof avoids
  auxiliary truncated algorithms: the stopping rule itself separates $\{\tau \le M\}$ from
  $\{\tau > M\}$ on the law of the history stopped at $M$. The lower bound needs the form of the
  theorem in which the alternative instance appears only through the law of the output
  (`IdentAlg.outputMeasure`), since PAC is a property of that law and no run in the alternative
  instance is given.
* **Chapter "Concentration inequalities" (`chap:pre_concentration`, 2026-09-16).** Lemma 19
  (Sanov) is proved with $(n+1)^{m-1}$, confirming the correction of item 22. Lemma 20 (Bernoulli
  maximal inequality) and Lemma 21 (self-normalized Bernstein, with the smaller term
  $\log(8(1+\sqrt{2t}))$) hold for every $\delta > 0$ and all $t \ge 0$; the explicit form of
  Lemma 21 already holds at $t = 0$ ($L_0 = \log(4e/\delta) > 2$). Lemma 22 (KL–Bernstein) and
  Lemmas 25–26 (variance transport) hold for arbitrary probability measures, not only on finite
  sets, and the second inequality of Lemma 26 holds with the constant $1$ in place of $3$. The
  inequality $h(x) \ge x^2/(2(1+x/3))$ for the Poisson Cramér transform follows from the Padé
  bound $\log(1+x) \ge (6x + 5x^2)/(6 + 8x + 2x^2)$ with a single derivative; Ville's inequality
  holds with the bound $\mathbb E[M_0]/c$.
* **Chapter "Algorithm" (`chap:algorithm`, 2026-09-16).** The ranges of the backups and of the
  certificate need $\delta \le 1$ (for the nonnegativity of the rates $\log(3SAH/\delta)$) and
  hold uniformly in the sign of $\beta$ when written between $\min\{1, e^{\beta j}\}$ and
  $\max\{1, e^{\beta j}\}$; the run properties of Entropic-BPI hold in any environment.
* **Chapter "Finite-horizon MDP theory" (`chap:pre_mdp`, agent D, 2026-09-16).** No error in the
  paper for this chapter. The entropic-variance identities (the Bellman recursion of the entropic
  variance and its telescoping sum) need finite exponential moments of order $2\beta$ of the
  rewards, automatic for a reward function in $[0, 1]$. The bound on the normalized variance of
  the exponential return by $G_{\max}$ needs only rewards in $[0, 1]$ (not deterministic rewards)
  and holds at every starting pair $(s, h)$. The Cauchy–Schwarz inequality along a trajectory
  holds for weights of any sign, under integrability in place of boundedness, and the unrolling
  of a backward recursive inequality only needs a nonnegative multiplier. The visits of a
  state-action pair are dominated by an i.i.d. sample in the form used by the concentration
  events (probability of a set of next-state sequences at the first $n$ visits at most its
  product-measure probability); the independence statement with a general test function is not
  needed.
* **Rates and counting argument (`chap:sample_complexity`, main thread, 2026-09-16).** The
  monotonicity of $x \mapsto \alpha(x)/x$ holds on $(0, \infty)$, with a proof by
  $\log(1 + u) \le u$ instead of derivatives. Lemma 27 holds on the counts event under the
  corrected hypotheses of `rem:sc_lemma27` (the rate dominates $\alpha^{\mathrm{cnt}}(\delta) > 1$,
  i.e.\ $\delta \le 1$), and the counting argument (Lemma 28 summed over the triples) holds with
  the constant $16$ of `rem:sc_counting_constant` for every $T \ge 0$.
* **Time-uniform KL concentration (`lem:empirical_kl_time_uniform`, agent F, 2026-09-16).** The
  bound $\Prob(\exists n \ge 1, n\KL(\hat q_n \| p) \ge \log(1/\delta') + (m-1)\log(n+1) + 1 +
  \frac12\log n) \le \delta'$ is proved with the exact constants of the blueprint, for an arbitrary
  law on a finite set and every $\delta' > 0$. The Dirichlet mixture over the simplex is replaced
  by the Laplace (rule of succession) product
  $M_n = \prod_{k<n} \frac{(N_k(\xi_k) + 1)/(k + m)}{p(\xi_k)}$, which has the same value
  $(m-1)!\prod_x N_n(x)!/(n + m - 1)!$ and is a nonnegative supermartingale without restricting
  to the support of $p$; no integral over the simplex is needed. This confirms that the rate
  $\alpha(n, \delta) = \log(3SAH/\delta) + S\log(8e(n+1))$ of the paper is valid time-uniformly,
  while a union bound over $n$ of Sanov's bound is not (`rem:empirical_sanov_union`).
* **Analysis on the good event (`chap:analysis_pos`, `chap:analysis_neg`, agent E, 2026-09-16).**
  No new error: the blueprint statements (with the corrected bonus, whose third term carries the
  KL rate $\alpha$, the clips, and the constants $3$, $3/H$, $36$, $13$, $84$) are proved for both
  signs of $\beta$. The proofs have slack: the concentration lemma gives
  $(2H + 2\sqrt2 + 3)B\alpha \le (4H + 5)B\alpha$, the third term of Lemmas 11 and 16 gives
  $(H + 2\sqrt2 + 2/3)B\alpha$, and the certificate recursion holds with $1 + 10/H$ and $77H$ in
  place of $1 + 13/H$ and $84H$. All the lemmas hold for $\delta \in (0, 1]$ and are statements
  about a fixed history satisfying the pointwise consequences of the good event: they need no
  run hypothesis. The ranges of the auxiliary values $\mathring Z$, $\mathring U$ hold for every
  number of remaining steps without any event. The KL–Bernstein and variance-transport
  inequalities are used in vector form for functions with values in $[c, c + b]$, $b \ge 0$, so
  the case of a zero range needs no special treatment.
* **Probabilities of the concentration events (`chap:empirical`, agent G, 2026-09-16).** The
  three events of the analysis and the good event have the probabilities of the paper's
  Lemma 5, in every run of every algorithm, with the corrected union bound
  $\delta/(3SAH)$ per triple (`rem:empirical_bernstein_index`) and the Bernstein inequality
  indexed by the number of visits. The KL and counts events hold for every $\delta > 0$, the
  Bernstein event for $\delta \in (0, 1]$, and the good event for every $\beta$ (including
  $\beta = 0$). The Bernoulli maximal inequality already covers $t = 0$, so the counts event
  needs no separate case. The KL event only needs the rate $\log(3SAH/\delta) + S\log(e(n+1))$:
  the factor $8$ of the paper's $\alpha(n, \delta)$ is slack there, and is used only by
  $\alpha^*$ (through $4e(2n+1) \le 8e(n+1)$). No measurability of the events is needed: the
  proofs are countable union bounds on complements.
* **Tail of the analysis and Theorem 4 (agent H, 2026-09-16).** Both conclusions of Theorem 4
  are proved for the frozen statements. Neither uses the hypothesis $\eps \le 2/(|\beta|HS)$ nor
  $\delta < 1$: $\delta \in (0, 1]$ and $\eps > 0$ suffice (`rem:sc_hypotheses`). The constants
  $10^9$ and $10^{10}$ of the upper bound have a slack of a factor about $16$; even the crude
  bound $e^{13} \le 3^{13}$ suffices. The claim that the stopping-time bound holds pointwise on the
  good event silently uses that the policy played in each episode is the greedy policy of the
  history, which holds almost surely in a run: the counting argument is about the policies
  played, the certificate bound about the greedy policies. The degenerate horizon $H = 0$, where
  the blueprint's $D \ge 1$ fails, is handled separately (the progress hypothesis is then
  contradictory). The PAC property is transferred from one run to the law of the output with
  LML's canonical run.
