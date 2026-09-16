/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Entropic
public import Essakine2026Tight.EV2026.Constants

/-!
# Theorem 3: lower bound on the sample complexity of entropic best-policy identification

For `S ≥ 6` states, `A ≥ 2` actions, a horizon `H ≥ 3 d` (Assumption 1), `β ≠ 0`, `δ ≤ 1/16` and
`ε` small enough (Condition A for the effective horizon `H - ⌊H/3⌋ - d`), there are a reward
function `r₀` with values in `[0, 1]`, an MDP
`M₀` with reward function `r₀` and an initial state `s₁` such that every `(ε, δ)`-PAC algorithm
for the class of MDPs with reward function `r₀` uses in expectation at least
`(1/5000) (e^{|β| G_max} - 1)² e^{-|β| G_max} e^{2 min(β, 0) ε} S A H log(1/δ) / (e^{|β| ε} - 1)²`
episodes in every run on `M₀`. Theorem 18 is the restatement of this theorem in the appendix.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Learning.MDP.Episodic
open scoped ENNReal

universe u v

namespace Essakine2026Tight

/-- **Theorem 3** (Essakine, Vernade 2026). For finite state and action spaces with `S ≥ 6`,
`A ≥ 2`, a horizon `H ≥ 3 d` with `d = ⌈log_A((S - 3)(A - 1) + 1)⌉` (Assumption 1), `β ≠ 0`,
`δ ∈ (0, 1/16]` and `ε > 0` satisfying Condition A for the effective horizon
`H' = H - ⌊H/3⌋ - d`, there are a reward function `r₀` with
values in `[0, 1]`, an MDP `M₀` with reward function `r₀` and an initial state `s₁` such that
every algorithm which is `(ε, δ)`-PAC for entropic best-policy identification with reward
function `r₀` satisfies, in every run on `M₀`,
`E[τ] ≥ (1/5000) (e^{|β| G_max(M₀)} - 1)² e^{-|β| G_max(M₀)} e^{2 min(β, 0) ε} S A H log(1/δ) /
(e^{|β| ε} - 1)²`. -/
theorem exists_hardMDP_lowerBound_le_lintegral_stoppingTime
    {S A : Type u} [Fintype S] [Fintype A] [Nonempty A]
    [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
    [MeasurableSingletonClass A] (H : ℕ)
    (hS : 6 ≤ Fintype.card S) (hA : 2 ≤ Fintype.card A)
    (hH : 3 * treeDepth (Fintype.card S) (Fintype.card A) ≤ H)
    {β : ℝ} (hβ : β ≠ 0) {δ : ℝ} (hδ : δ ∈ Set.Ioc 0 (1 / 16)) {ε : ℝ} (hε : 0 < ε)
    (hcond : ConditionA β (effHorizon (Fintype.card S) (Fintype.card A) H) ε) :
    ∃ (r₀ : Fin H → S → A → ℝ) (M₀ : EpisodicMDP S A H) (s₁ : S),
      (∀ h s a, r₀ h s a ∈ Set.Icc 0 1) ∧ M₀.HasRewardFn r₀ ∧
      ∀ 𝒜 : BPIAlg S A H, IsEntropicPAC 𝒜 r₀ β ε δ s₁ →
        ∀ {Ω : Type v} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
          (X : ℕ → Ω → Policy S A H) (Y : ℕ → Ω → Traj S H) (out : Ω → Policy S A H),
          𝒜.IsRun (statesEnv M₀ s₁) (fun _ _ ↦ ()) X Y out P →
          ENNReal.ofReal (lowerBound (Fintype.card S) (Fintype.card A) H β ε δ
              (maxReturn M₀ s₁)) ≤
            ∫⁻ ω, (𝒜.stoppingTime (fun _ _ ↦ ()) X Y ω : ℝ≥0∞) ∂P := by
  sorry

end Essakine2026Tight
