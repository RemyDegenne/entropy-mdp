/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Entropic
public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Empirical
public import Essakine2026Tight.EV2026.Rates
public import LeanMachineLearning.ForMathlib.MeasureTheory.Order.MeasurableArg
public import LeanMachineLearning.SequentialLearning.Deterministic
public import Essakine2026Tight.Mathlib.MeasureTheory.MeasurableSpace.Sigma

/-!
# The Entropic-BPI algorithm (Essakine, Vernade 2026, Algorithm 1)

This file defines the **Entropic-BPI** algorithm `entropicBPI H r β δ ε s₁ : BPIAlg S A H` for
the horizon `H`, the known reward function `r`, the risk parameter `β`, the confidence `δ`, the
accuracy `ε` and the initial state `s₁`, and the quantities of its analysis, as functions of the
history `hist : Hist Unit (Policy S A H) (Traj S H) t` of the first `t` episodes.

Steps are `0`-indexed (`h : Fin H`, the paper's `h + 1`), and the backward recursions are indexed
by the number `j` of steps from the current step to the end: `optZ r β δ hist j` is the pair
`(Z̃, Z̲)` of optimistic and pessimistic exponential values at the step `H - j` (`j = 0`: terminal
values `1`), `cert r β δ hist j` the certificate `π^{t+1} G` at that step (`j = 0`: `0`), and
`ringZ M β δ hist j` the auxiliary value `Z̊` of the analysis. At a step `h : Fin H`,
`k = H - 1 - h` is the number of steps after `h`, which is the paper's `H - h` (for its
`1`-indexed `h`); the backups at that step are clipped at `e^{β (k + 1)}` (the range of `U*`).

* Empirical counts of a history of episodes: `stepModel`, `visitCount` (`n_h^t(s, a)`), `empTrans`
  (`p̂_h^t(· | s, a)`, uniform for never-visited pairs).
* The bonus `bonus` (`b_h^t(s, a)`), the optimistic/pessimistic backups `stepU` (`(Ũ, U̲)` from the
  next-step values), the greedy policy `greedy` (`π^{t+1}`, `argmax_a Ũ` if `β > 0`,
  `argmin_a U̲` if `β < 0`), the certificate `cert` and the stopping rule `stopCond`. Pairs never
  visited get the trivial bounds (the paper's `α(0)/0 = ∞`).
* The auxiliary quantities `ringZ`, `ringU` (`Z̊`, `Ů`) of the analysis, which depend on the true
  MDP.

The recursions are written with `Nat.rec` and step functions (`optZStep`, `certStep`,
`ringZStep`), the measurability facts are named lemmas and real numerals are casts of natural
numerals: the definitions must be free of nested proofs and matchers to be compared across
environments by `comparator` (see `notes/lean-design.md`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP.Episodic Learning.MDP

namespace Essakine2026Tight

section Helpers

variable {S : Type*} [Fintype S]

lemma sub_one_sub_lt {H k : ℕ} (hk : k < H) : H - 1 - k < H := by omega

/-- The `0`-indexed step with `k` steps after it. -/
def stepOf (H k : ℕ) (hk : k < H) : Fin H := ⟨H - 1 - k, sub_one_sub_lt hk⟩

/-- The bonus `b_h^t(s, a)` of a pair visited `n` times with empirical transitions `phat`, from
the next-step optimistic and pessimistic values `Zt`, `Zl`, with `k` steps after `h`, for `nS`
states, `nA` actions and horizon `H`:
`2 √2 √(Var_p̂(Z̃) α*(n)/n) + 5 e^{β k} α(n)/n + 4 H e^{β k} α(n)/n` for `β > 0` (with `Z̲` and
`1 - e^{β k}` for `β < 0`). The third term carries the KL rate `α`, as in the statement of the
paper's Lemma 7 (its bonus (bonus positive) has `α*` there, which does not suffice for Lemma 11;
blueprint, chapter "Analysis for β > 0", `rem:pos_constants_bonus`). -/
noncomputable def bonus (nS nA H : ℕ) (β δ : ℝ) (k n : ℕ) (phat Zt Zl : S → ℝ) : ℝ :=
  let αn := alphaKL nS nA H δ n / n
  let αs := alphaStar nS nA H δ n / n
  if 0 < β then
    (2 : ℕ) * √(2 : ℕ) * √(vecVar phat Zt * αs) + (5 : ℕ) * Real.exp (β * k) * αn
      + (4 * H : ℕ) * Real.exp (β * k) * αn
  else
    (2 : ℕ) * √(2 : ℕ) * √(vecVar phat Zl * αs) + (5 : ℕ) * (1 - Real.exp (β * k)) * αn
      + (4 * H : ℕ) * (1 - Real.exp (β * k)) * αn

/-- The optimistic and pessimistic backups `(Ũ, U̲)(s, a)` of a pair with reward `r`, visited `n`
times with empirical transitions `phat`, from the next-step values `Zt`, `Zl`, with `k` steps
after the current step, clipped at `e^{β (k + 1)}` and `1`; a pair never visited gets the trivial
bounds. -/
noncomputable def stepU (nS nA H : ℕ) (β δ : ℝ) (k n : ℕ) (r : ℝ) (phat Zt Zl : S → ℝ) :
    ℝ × ℝ :=
  let b := bonus nS nA H β δ k n phat Zt Zl
  let w := (1 / H : ℝ) * vecExp phat (Zt - Zl)
  let up := if 0 < β then Real.exp (β * (k + 1)) else 1
  let low := if 0 < β then 1 else Real.exp (β * (k + 1))
  if n = 0 then (up, low) else
    (min up (Real.exp (β * r) * (vecExp phat Zt + b + w)),
      max low (Real.exp (β * r) * (vecExp phat Zl - b - w)))

/-- The auxiliary backup `Ů(s, a)` of the analysis (Lemmas 10 and 15): the exponential Bellman
backup of `Z̊` under the true transitions `p`, clipped by the pessimistic (`β > 0`) or optimistic
(`β < 0`) empirical backup. -/
noncomputable def ringUAux (nS nA H : ℕ) (β δ : ℝ) (k n : ℕ) (r : ℝ) (p phat Zr Zt Zl : S → ℝ) :
    ℝ :=
  let b := bonus nS nA H β δ k n phat Zt Zl
  if 0 < β then
    if n = 0 then min (Real.exp (β * r) * vecExp p Zr) 1 else
      min (Real.exp (β * r) * vecExp p Zr)
        (max 1 (Real.exp (β * r) * (vecExp phat Zr - b - (1 / H) * vecExp phat (Zt - Zr))))
  else
    if n = 0 then max (Real.exp (β * r) * vecExp p Zr) 1 else
      max (Real.exp (β * r) * vecExp p Zr)
        (min 1 (Real.exp (β * r) * (vecExp phat Zr + b + (1 / H) * vecExp phat (Zr - Zl))))

end Helpers

section Algorithm

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]
  {H : ℕ}

/-! ### Empirical counts of a history of episodes -/

omit [Nonempty A] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- The empirical model of the step `h` of a history of episodes (states only, rewards `0`). -/
def stepModel {t : ℕ} (hist : Hist Unit (Policy S A H) (Traj S H) t) (h : Fin H) :
    EmpiricalModel S A :=
  ∑ i, EmpiricalModel.ofEpisodeAt (hist i).action (hist i).feedback 0 h

omit [Nonempty A] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- The number of episodes of the history `hist` in which `(s, a)` was visited at step `h`
(`n_h^t(s, a)`). -/
def visitCount {t : ℕ} (hist : Hist Unit (Policy S A H) (Traj S H) t) (h : Fin H) (s : S)
    (a : A) : ℕ :=
  (stepModel hist h).count (s, a)

omit [Nonempty A] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- The empirical transition probabilities `p̂_h^t(· | s, a)` (uniform if `(s, a)` was never
visited at step `h`). -/
noncomputable def empTrans {t : ℕ} (hist : Hist Unit (Policy S A H) (Traj S H) t) (h : Fin H)
    (s : S) (a : A) : S → ℝ :=
  if visitCount hist h s a = 0 then fun _ ↦ (Fintype.card S : ℝ)⁻¹
  else (stepModel hist h).empTrans (s, a)

/-! ### Optimistic planning -/

/-- One backward step of the optimistic planning: the values `(Z̃, Z̲)` at the step with `k`
steps after it, from the values `prev` at the next step (`stepU` for every pair, then the max
(`β > 0`) or the min (`β < 0`) over the actions); the identity if `k ≥ H`. -/
noncomputable def optZStep (r : ℕ → S → A → ℝ) (β δ : ℝ) {t : ℕ}
    (hist : Hist Unit (Policy S A H) (Traj S H) t) (k : ℕ) (prev : (S → ℝ) × (S → ℝ)) :
    (S → ℝ) × (S → ℝ) :=
  if hk : k < H then
    let h := stepOf H k hk
    let U := fun s a ↦ stepU (Fintype.card S) (Fintype.card A) H β δ k (visitCount hist h s a)
      (r h s a) (empTrans hist h s a) prev.1 prev.2
    (fun s ↦ if 0 < β then (fun a ↦ (U s a).1).max else (fun a ↦ (U s a).1).min,
      fun s ↦ if 0 < β then (fun a ↦ (U s a).2).max else (fun a ↦ (U s a).2).min)
  else prev

/-- The optimistic and pessimistic exponential values `(Z̃, Z̲)` at the step `H - j` computed
from the history `hist` (backward recursion; `j = 0` is the terminal step, with values `1`). -/
noncomputable def optZ (r : ℕ → S → A → ℝ) (β δ : ℝ) {t : ℕ}
    (hist : Hist Unit (Policy S A H) (Traj S H) t) (j : ℕ) : (S → ℝ) × (S → ℝ) :=
  Nat.rec (motive := fun _ ↦ (S → ℝ) × (S → ℝ)) (fun _ ↦ 1, fun _ ↦ 1) (optZStep r β δ hist) j

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma optZ_zero (r : ℕ → S → A → ℝ) (β δ : ℝ) {t : ℕ}
    (hist : Hist Unit (Policy S A H) (Traj S H) t) : optZ r β δ hist 0 = (fun _ ↦ 1, fun _ ↦ 1) :=
  rfl

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma optZ_succ (r : ℕ → S → A → ℝ) (β δ : ℝ) {t : ℕ}
    (hist : Hist Unit (Policy S A H) (Traj S H) t) (k : ℕ) :
    optZ r β δ hist (k + 1) = optZStep r β δ hist k (optZ r β δ hist k) := rfl

/-- The backups `(Ũ, U̲)(s, a)` at the step `h` computed from the history `hist`. -/
noncomputable def stepUAt (r : ℕ → S → A → ℝ) (β δ : ℝ) {t : ℕ}
    (hist : Hist Unit (Policy S A H) (Traj S H) t) (h : Fin H) (s : S) (a : A) : ℝ × ℝ :=
  let prev := optZ r β δ hist (H - 1 - h)
  stepU (Fintype.card S) (Fintype.card A) H β δ (H - 1 - h) (visitCount hist h s a) (r h s a)
    (empTrans hist h s a) prev.1 prev.2

/-- The greedy policy `π^{t+1}` computed from the history `hist`: `argmax_a Ũ(s, a)` if `β > 0`,
`argmin_a U̲(s, a)` if `β < 0`. -/
noncomputable def greedy (r : ℕ → S → A → ℝ) (β δ : ℝ) {t : ℕ}
    (hist : Hist Unit (Policy S A H) (Traj S H) t) : Policy S A H :=
  fun h s ↦ if 0 < β then argmax fun a ↦ (stepUAt r β δ hist h s a).1
    else argmin fun a ↦ (stepUAt r β δ hist h s a).2

/-- One backward step of the certificate: `π^{t+1} G` at the step with `k` steps after it, from
the certificate `prev` at the next step; the identity if `k ≥ H`. -/
noncomputable def certStep (r : ℕ → S → A → ℝ) (β δ : ℝ) {t : ℕ}
    (hist : Hist Unit (Policy S A H) (Traj S H) t) (k : ℕ) (prev : S → ℝ) : S → ℝ :=
  fun s ↦
    if hk : k < H then
      let h := stepOf H k hk
      let a := greedy r β δ hist h s
      let n := visitCount hist h s a
      let Z := optZ r β δ hist k
      let b := bonus (Fintype.card S) (Fintype.card A) H β δ k n (empTrans hist h s a) Z.1 Z.2
      let clip := if 0 < β then Real.exp (β * (k + 1)) else 1
      if n = 0 then clip else
        min clip (Real.exp (β * r h s a) *
          ((3 : ℕ) * b + (1 + (3 : ℕ) / H) * vecExp (empTrans hist h s a) prev))
    else prev s

/-- The certificate `π^{t+1} G` at the step `H - j` computed from the history `hist` (backward
recursion; `j = 0` is the terminal step, with value `0`), clipped at `e^{β (k + 1)}` (`β > 0`)
or `1` (`β < 0`) where `k` is the number of steps after the current step. -/
noncomputable def cert (r : ℕ → S → A → ℝ) (β δ : ℝ) {t : ℕ}
    (hist : Hist Unit (Policy S A H) (Traj S H) t) (j : ℕ) : S → ℝ :=
  Nat.rec (motive := fun _ ↦ S → ℝ) (fun _ ↦ 0) (certStep r β δ hist) j

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma cert_zero (r : ℕ → S → A → ℝ) (β δ : ℝ) {t : ℕ}
    (hist : Hist Unit (Policy S A H) (Traj S H) t) : cert r β δ hist 0 = fun _ ↦ 0 := rfl

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma cert_succ (r : ℕ → S → A → ℝ) (β δ : ℝ) {t : ℕ}
    (hist : Hist Unit (Policy S A H) (Traj S H) t) (k : ℕ) :
    cert r β δ hist (k + 1) = certStep r β δ hist k (cert r β δ hist k) := rfl

/-- The stopping rule of Entropic-BPI: `π^{t+1} G_1(s₁) ≤ (e^{βε} - 1) e^{-βε} Z̃_1(s₁)` if
`β > 0`, `π^{t+1} G_1(s₁) ≤ (1 - e^{βε}) Z̲_1(s₁)` if `β < 0`. -/
noncomputable def stopCond (r : ℕ → S → A → ℝ) (β δ ε : ℝ) (s₁ : S) {t : ℕ}
    (hist : Hist Unit (Policy S A H) (Traj S H) t) : Prop :=
  if 0 < β then
    cert r β δ hist H s₁ ≤ (Real.exp (β * ε) - 1) / Real.exp (β * ε) * (optZ r β δ hist H).1 s₁
  else cert r β δ hist H s₁ ≤ (1 - Real.exp (β * ε)) * (optZ r β δ hist H).2 s₁

lemma measurable_greedy_fst (r : ℕ → S → A → ℝ) (β δ : ℝ) (n : ℕ) :
    Measurable fun p : Hist Unit (Policy S A H) (Traj S H) n × Unit ↦ greedy r β δ p.1 :=
  measurable_of_countable _

lemma measurable_greedy_snd (r : ℕ → S → A → ℝ) (β δ : ℝ) :
    Measurable fun h : Σ n : ℕ, Hist Unit (Policy S A H) (Traj S H) n ↦ greedy r β δ h.2 :=
  measurable_of_countable _

lemma measurableSet_stopCond (r : ℕ → S → A → ℝ) (β δ ε : ℝ) (s₁ : S) :
    MeasurableSet {h : Σ n : ℕ, Hist Unit (Policy S A H) (Traj S H) n | stopCond r β δ ε s₁ h.2} :=
  (Set.to_countable _).measurableSet

variable (H) in
/-- **Algorithm 1** (Entropic-BPI) with horizon `H`, known rewards `r`, risk parameter `β`,
confidence `δ`, accuracy `ε` and initial state `s₁`: at each episode, play the greedy policy of
the optimistic backups computed from the past episodes; stop when the certificate of the greedy
policy is small enough, and output the greedy policy. -/
noncomputable def entropicBPI (r : ℕ → S → A → ℝ) (β δ ε : ℝ) (s₁ : S) : BPIAlg S A H where
  alg := detAlgorithm (fun _ p ↦ greedy r β δ p.1) (measurable_greedy_fst r β δ)
  stopSet := {h | stopCond r β δ ε s₁ h.2}
  measurableSet_stopSet := measurableSet_stopCond r β δ ε s₁
  output := Kernel.deterministic (fun h ↦ greedy r β δ h.2) (measurable_greedy_snd r β δ)

/-! ### Auxiliary quantities of the analysis -/

/-- One backward step of the auxiliary value `Z̊` of the analysis, for the MDP `M`. -/
noncomputable def ringZStep (M : EpisodicMDP S A) (r : ℕ → S → A → ℝ) (β δ : ℝ) {t : ℕ}
    (hist : Hist Unit (Policy S A H) (Traj S H) t) (k : ℕ) (prev : S → ℝ) : S → ℝ :=
  fun s ↦
    if hk : k < H then
      let h := stepOf H k hk
      let a := greedy r β δ hist h s
      let Z := optZ r β δ hist k
      ringUAux (Fintype.card S) (Fintype.card A) H β δ k (visitCount hist h s a) (r h s a)
        (M.transVec h s a) (empTrans hist h s a) prev Z.1 Z.2
    else prev s

/-- The auxiliary value `Z̊` of the analysis at the step `H - j`, for the MDP `M` with reward
function `r` and the history `hist`. -/
noncomputable def ringZ (M : EpisodicMDP S A) (r : ℕ → S → A → ℝ) (β δ : ℝ) {t : ℕ}
    (hist : Hist Unit (Policy S A H) (Traj S H) t) (j : ℕ) : S → ℝ :=
  Nat.rec (motive := fun _ ↦ S → ℝ) (fun _ ↦ 1) (ringZStep M r β δ hist) j

/-- The auxiliary backup `Ů(s, a)` of the analysis at the step `h`. -/
noncomputable def ringU (M : EpisodicMDP S A) (r : ℕ → S → A → ℝ) (β δ : ℝ) {t : ℕ}
    (hist : Hist Unit (Policy S A H) (Traj S H) t) (h : Fin H) (s : S) (a : A) : ℝ :=
  let prev := optZ r β δ hist (H - 1 - h)
  ringUAux (Fintype.card S) (Fintype.card A) H β δ (H - 1 - h) (visitCount hist h s a) (r h s a)
    (M.transVec h s a) (empTrans hist h s a) (ringZ M r β δ hist (H - 1 - h)) prev.1 prev.2

end Algorithm

end Essakine2026Tight
