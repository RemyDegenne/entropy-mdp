/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.EV2026.Algorithm
public import Essakine2026Tight.Mathlib.MeasureTheory.Measure.Weighted
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Run quantities and concentration events of the analysis of Entropic-BPI

For a run `(X, Y)` of an algorithm in the episode environment of an MDP `M` from `s₁`
(`X t ω : Policy S A H` the policy of episode `t`, `Y t ω : Traj S H` its states), on a
probability space `Ω`:

* `histAt X Y t` is the history of the first `t` episodes and `visitCountAt`, `empTransAt`,
  `ZtildeAt`, `ZlowerAt`, `UtildeAt`, `UlowerAt`, `bonusAt`, `greedyAt`, `certAt`, `ringZAt`,
  `ringUAt` are the quantities
  `n_h^t, p̂_h^t, Z̃^t, Z̲^t, Ũ^t, U̲^t, b^t, π^{t+1}, π^{t+1} G^t, Z̊^t, Ů^t` at episode `t`
  (`EV2026/Algorithm.lean`);
* `pseudoCount M X s₁ h s a t` is the pseudo-count `n̄_h^t(s, a) = ∑_{i < t} p^{π^{i+1}}_h(s, a)`,
  the sum of the conditional probabilities of the visits given the past (a predictable
  process; the paper writes `E[n_h^t(s, a)]`);
* `klRateAt`, `starRateAt` are the rates `α(n_h^t(s, a)) / n_h^t(s, a)`,
  `α*(n_h^t(s, a)) / n_h^t(s, a)`, and `klRateMinAt`, `starRateMinAt` their minima with `1`
  (`1` for unvisited pairs);
* the events `eventKL` (`𝓔_KL`), `eventBern` (`𝓔_f`, with step-dependent ranges `b h`),
  `eventCnt` (`𝓔^cnt`) and the good event `goodEvent` (`𝓔^+` / `𝓔^-`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP.Episodic Learning.MDP
  InformationTheory
open scoped ENNReal

namespace Essakine2026Tight

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]
  {H : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} (X : ℕ → Ω → Policy S A H) (Y : ℕ → Ω → Traj S H)

/-- The history of the first `t` episodes of the run `(X, Y)`. -/
def histAt (t : ℕ) (ω : Ω) : Hist Unit (Policy S A H) (Traj S H) t :=
  history (fun _ _ ↦ ()) X Y t ω

omit [Nonempty A] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- The visitation count `n_h^t(s, a)` after the first `t` episodes of the run. -/
def visitCountAt (h : Fin H) (s : S) (a : A) (t : ℕ) (ω : Ω) : ℕ :=
  visitCount (histAt X Y t ω) h s a

omit [Nonempty A] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- The empirical transition probabilities `p̂_h^t(· | s, a)` after the first `t` episodes of the
run. -/
noncomputable def empTransAt (h : Fin H) (s : S) (a : A) (t : ℕ) (ω : Ω) : S → ℝ :=
  empTrans (histAt X Y t ω) h s a

/-- The optimistic exponential value `Z̃_h^t` at episode `t`. -/
noncomputable def ZtildeAt (r : ℕ → S → A → ℝ) (β δ : ℝ) (t : ℕ) (ω : Ω) (h : Fin (H + 1)) :
    S → ℝ :=
  (optZ r β δ (histAt X Y t ω) (H - h)).1

/-- The pessimistic exponential value `Z̲_h^t` at episode `t`. -/
noncomputable def ZlowerAt (r : ℕ → S → A → ℝ) (β δ : ℝ) (t : ℕ) (ω : Ω) (h : Fin (H + 1)) :
    S → ℝ :=
  (optZ r β δ (histAt X Y t ω) (H - h)).2

/-- The optimistic backup `Ũ_h^t(s, a)` at episode `t`. -/
noncomputable def UtildeAt (r : ℕ → S → A → ℝ) (β δ : ℝ) (t : ℕ) (ω : Ω) (h : Fin H) (s : S)
    (a : A) : ℝ :=
  (stepUAt r β δ (histAt X Y t ω) h s a).1

/-- The pessimistic backup `U̲_h^t(s, a)` at episode `t`. -/
noncomputable def UlowerAt (r : ℕ → S → A → ℝ) (β δ : ℝ) (t : ℕ) (ω : Ω) (h : Fin H) (s : S)
    (a : A) : ℝ :=
  (stepUAt r β δ (histAt X Y t ω) h s a).2

/-- The bonus `b_h^t(s, a)` at episode `t`. -/
noncomputable def bonusAt (r : ℕ → S → A → ℝ) (β δ : ℝ) (t : ℕ) (ω : Ω) (h : Fin H) (s : S)
    (a : A) : ℝ :=
  bonus (Fintype.card S) (Fintype.card A) H β δ (H - 1 - h) (visitCountAt X Y h s a t ω)
    (empTransAt X Y h s a t ω) (ZtildeAt X Y r β δ t ω h.succ) (ZlowerAt X Y r β δ t ω h.succ)

/-- The greedy policy `π^{t+1}` computed after the first `t` episodes. -/
noncomputable def greedyAt (r : ℕ → S → A → ℝ) (β δ : ℝ) (t : ℕ) (ω : Ω) : Policy S A H :=
  greedy r β δ (histAt X Y t ω)

/-- The certificate `π^{t+1} G_h^t` at episode `t`. -/
noncomputable def certAt (r : ℕ → S → A → ℝ) (β δ : ℝ) (t : ℕ) (ω : Ω) (h : Fin (H + 1)) :
    S → ℝ :=
  cert r β δ (histAt X Y t ω) (H - h)

/-- The auxiliary value `Z̊_h^t` at episode `t`. -/
noncomputable def ringZAt (M : EpisodicMDP S A) (r : ℕ → S → A → ℝ) (β δ : ℝ) (t : ℕ)
    (ω : Ω) (h : Fin (H + 1)) : S → ℝ :=
  ringZ M r β δ (histAt X Y t ω) (H - h)

/-- The auxiliary backup `Ů_h^t(s, a)` at episode `t`. -/
noncomputable def ringUAt (M : EpisodicMDP S A) (r : ℕ → S → A → ℝ) (β δ : ℝ) (t : ℕ)
    (ω : Ω) (h : Fin H) (s : S) (a : A) : ℝ :=
  ringU M r β δ (histAt X Y t ω) h s a

/-- The rate `α(n_h^t(s, a), δ) / n_h^t(s, a)` at episode `t`. -/
noncomputable def klRateAt (δ : ℝ) (h : Fin H) (s : S) (a : A) (t : ℕ) (ω : Ω) : ℝ :=
  alphaKL (Fintype.card S) (Fintype.card A) H δ (visitCountAt X Y h s a t ω)
    / visitCountAt X Y h s a t ω

/-- The rate `α*(n_h^t(s, a), δ) / n_h^t(s, a)` at episode `t`. -/
noncomputable def starRateAt (δ : ℝ) (h : Fin H) (s : S) (a : A) (t : ℕ) (ω : Ω) : ℝ :=
  alphaStar (Fintype.card S) (Fintype.card A) H δ (visitCountAt X Y h s a t ω)
    / visitCountAt X Y h s a t ω

/-- The rate term `min {α(n_h^t(s, a), δ) / n_h^t(s, a), 1}` at episode `t` (`1` if the pair was
never visited). -/
noncomputable def klRateMinAt (δ : ℝ) (h : Fin H) (s : S) (a : A) (t : ℕ) (ω : Ω) : ℝ :=
  rateMin (alphaKL (Fintype.card S) (Fintype.card A) H δ) (visitCountAt X Y h s a t ω)

/-- The rate term `min {α*(n_h^t(s, a), δ) / n_h^t(s, a), 1}` at episode `t` (`1` if the pair was
never visited). -/
noncomputable def starRateMinAt (δ : ℝ) (h : Fin H) (s : S) (a : A) (t : ℕ) (ω : Ω) : ℝ :=
  rateMin (alphaStar (Fintype.card S) (Fintype.card A) H δ) (visitCountAt X Y h s a t ω)

/-- The pseudo-count `n̄_h^t(s, a) = ∑_{i < t} p^{π^{i+1}}_h(s, a)`: the sum over the first `t`
episodes of the probability, given the past, of visiting `(s, a)` at step `h`. -/
noncomputable def pseudoCount (M : EpisodicMDP S A) (s₁ : S) (h : Fin H) (s : S) (a : A)
    (t : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ range t, occupancy M (X i ω).extend s₁ h s a

/-- The KL concentration threshold `α(n, δ) / n` (`∞` for `n = 0`). -/
noncomputable def klThreshold (S A H : ℕ) (δ : ℝ) (n : ℕ) : ℝ≥0∞ :=
  if n = 0 then ⊤ else ENNReal.ofReal (alphaKL S A H δ n / n)

/-- The KL concentration event `𝓔_KL`: for all episodes `t`, steps `h` and pairs `(s, a)`,
`KL(p̂_h^t(s, a) ‖ p_h(s, a)) ≤ α(n_h^t(s, a), δ) / n_h^t(s, a)`. -/
def eventKL (M : EpisodicMDP S A) (δ : ℝ) : Set Ω :=
  {ω | ∀ t h s a, klDiv (weightedMeasure (empTransAt X Y h s a t ω)) (M.trans h (s, a)) ≤
    klThreshold (Fintype.card S) (Fintype.card A) H δ (visitCountAt X Y h s a t ω)}

/-- The Bernstein concentration event `𝓔_f` for the functions `f_h` with ranges `b h` at step
`h`: for all `t`, `h`, `(s, a)` with `n_h^t(s, a) > 0`,
`|(p̂_h^t - p_h) f_{h+1}(s, a)| ≤ √(2 Var_{p_h}(f_{h+1})(s, a) α*(n) / n) + 3 b_h α*(n) / n`. -/
def eventBern (M : EpisodicMDP S A) (δ : ℝ) (f : ℕ → S → ℝ) (b : ℕ → ℝ) : Set Ω :=
  {ω | ∀ t (h : Fin H) s a, 0 < visitCountAt X Y h s a t ω →
    |vecExp (empTransAt X Y h s a t ω) (f (h + 1)) - vecExp (M.transVec h s a) (f (h + 1))| ≤
      √(2 * vecVar (M.transVec h s a) (f (h + 1)) * starRateAt X Y δ h s a t ω)
      + 3 * b h * starRateAt X Y δ h s a t ω}

/-- The counts concentration event `𝓔^cnt`: `n_h^t(s, a) ≥ n̄_h^t(s, a) / 2 - α^cnt(δ)`. -/
def eventCnt (M : EpisodicMDP S A) (s₁ : S) (δ : ℝ) : Set Ω :=
  {ω | ∀ t h s a, pseudoCount X M s₁ h s a t ω / 2 - alphaCnt (Fintype.card S) (Fintype.card A) H δ
    ≤ (visitCountAt X Y h s a t ω : ℝ)}

/-- The good event `𝓔^+` (`β > 0`) or `𝓔^-` (`β < 0`): the KL event, the Bernstein event for the
optimal exponential values `Z*` (with the range `e^{β k}` at the step with `k` steps after it
for `β > 0`, `1 - e^{β k}` for `β < 0`) and the counts event. -/
def goodEvent (M : EpisodicMDP S A) (s₁ : S) (β δ : ℝ) : Set Ω :=
  eventKL X Y M δ ∩ eventBern X Y M δ (optExpValue M H β)
      (fun h ↦ if 0 < β then Real.exp (β * (H - 1 - h : ℕ)) else 1 - Real.exp (β * (H - 1 - h : ℕ)))
    ∩ eventCnt X Y M s₁ δ

end Essakine2026Tight
