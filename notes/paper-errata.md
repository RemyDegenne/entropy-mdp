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
