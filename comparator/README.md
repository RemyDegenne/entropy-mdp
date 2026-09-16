# Comparator setup

Machine-checkable verification, with [leanprover/comparator](https://github.com/leanprover/comparator),
that this repository proves the headline results claimed in [`formalization.yaml`](../formalization.yaml)
without having to read or trust the Lean development in `Essakine2026Tight/`.

**Status.** Phase 1 (2026-09-16): the three challenges are stated and `scripts/comparator-verify.sh
--insecure` was run on all of them: the statements and every definition they rest on are
identical in the challenges and in the project, and each run fails only on the `sorryAx` axiom
of the project's `sorry`-ed proofs. The script will pass once phase 2 proves them.

Each challenge is one self-contained file whose transitive imports resolve to Mathlib and Lean
core only, the shape the [Palomar registry](https://palomar-registry.org/) enforces: no LML, no
project modules, no sibling helpers.

## The trust story

For each headline theorem `Essakine2026Tight.<name>` there is a challenge file `Challenge_<name>.lean` and a
config `<name>.json`; the list is `targets.txt`:

| paper result | challenge(s) |
|---|---|
| Theorem 3 (lower bound on the expected number of episodes of every PAC algorithm on the hard instance) | `exists_hardMDP_lowerBound_le_lintegral_stoppingTime` |
| Theorem 4, PAC (Entropic-BPI is (ε, δ)-PAC) | `isEntropicPAC_entropicBPI` |
| Theorem 4, sample complexity (Entropic-BPI stops within `upperBound` episodes with probability 1 - δ) | `probReal_stoppingTime_entropicBPI_le_ge` |

Each challenge states the theorem with `sorry`, with every definition the statement rests on
inlined verbatim: the project's definitions and the LML declarations they build on, copied from
LML in `vendor/LML.lean.part`. A reader checks the *statement* (the challenge file) by hand and
lets comparator check that the project proves exactly it, with no axioms beyond `propext`,
`Classical.choice` and `Quot.sound`, the proofs replayed through the kernel.

## Regenerating and running

`scripts/make-challenges.py` regenerates every challenge and config from `targets.txt`;
`lake build Comparator` checks that they compile; `scripts/comparator-verify.sh [--insecure]`
runs comparator on every config (see the script header for the sandbox requirements).
