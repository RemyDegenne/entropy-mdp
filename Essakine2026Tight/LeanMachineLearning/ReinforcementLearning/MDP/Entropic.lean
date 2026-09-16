/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Episodic
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Entropic (risk-sensitive) values of an episodic MDP

For a risk parameter `β ≠ 0` and a finite-horizon MDP `M` (see `MDP/Episodic.lean`):
* `expValue M β π h s = E[exp(β R_h) | S_h = s]` (`Z^π_h`, with `R_h` the return from step `h`)
  and the entropic value `entropicValue M β π h s = β⁻¹ log Z^π_h(s)` (`V^π_h`);
* `expQ M β π h s a = E[exp(β R) Z^π_{h+1}(S')]` for `R ∼ M.reward h (s, a)` and
  `S' ∼ M.trans h (s, a)` (`U^π_h`, the exponential Bellman equation) and `entropicQ` (`Q^π_h`);
* `optEntropicValue M β h s = ⨆ π, V^π_h(s)` (`V*_h`), `optExpValue` (`Z*_h = exp(β V*_h)`),
  `optExpQ` (`U*_h`);
* `entropicVarQ M β π h s a = E[(exp(β R_h) - U^π_h(s, a))² | S_h = s, A_h = a]` (`σQ^π_h`) and
  `entropicVarV` (`σV^π_h`);
* `maxReturn M s₁ = ⨆ π, ess sup R_1` (`G_max(M)`), the maximal achievable return.

A best-policy identification algorithm is `(ε, δ)`-PAC for the entropic criterion with the
known reward function `r` (`IsEntropicPAC 𝒜 r β ε δ s₁`) if, for every MDP with reward function
`r`, its output `π̂` satisfies `V*_1(s₁) - V^π̂_1(s₁) > ε` with probability at most `δ`
(`IdentAlg.IsPAC`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP

namespace Learning.MDP.Episodic

variable {S A : Type*} [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] {H : ℕ}

/-- The exponential value `Z^π_h(s) = E[exp(β R_h) | S_h = s]`. -/
noncomputable def expValue (M : EpisodicMDP S A H) (β : ℝ) (π : Policy S A H) (h : Fin (H + 1))
    (s : S) : ℝ :=
  ∫ traj, Real.exp (β * episodeReturn H traj) ∂(stepLaw M π (s, h))

/-- The entropic value `V^π_h(s) = β⁻¹ log E[exp(β R_h) | S_h = s]`. -/
noncomputable def entropicValue (M : EpisodicMDP S A H) (β : ℝ) (π : Policy S A H)
    (h : Fin (H + 1)) (s : S) : ℝ :=
  β⁻¹ * Real.log (expValue M β π h s)

/-- The exponential state-action value `U^π_h(s, a) = E[exp(β R) Z^π_{h+1}(S')]` for
`R ∼ M.reward h (s, a)` and `S' ∼ M.trans h (s, a)`. -/
noncomputable def expQ (M : EpisodicMDP S A H) (β : ℝ) (π : Policy S A H) (h : Fin H) (s : S)
    (a : A) : ℝ :=
  (∫ x, Real.exp (β * x) ∂(M.reward h (s, a))) * ∫ s', expValue M β π h.succ s' ∂(M.trans h (s, a))

/-- The entropic state-action value `Q^π_h(s, a) = β⁻¹ log U^π_h(s, a)`. -/
noncomputable def entropicQ (M : EpisodicMDP S A H) (β : ℝ) (π : Policy S A H) (h : Fin H)
    (s : S) (a : A) : ℝ :=
  β⁻¹ * Real.log (expQ M β π h s a)

/-- The optimal entropic value `V*_h(s) = ⨆ π, V^π_h(s)`. -/
noncomputable def optEntropicValue (M : EpisodicMDP S A H) (β : ℝ) (h : Fin (H + 1)) (s : S) :
    ℝ :=
  ⨆ π : Policy S A H, entropicValue M β π h s

/-- The optimal exponential value `Z*_h(s) = exp(β V*_h(s))`. -/
noncomputable def optExpValue (M : EpisodicMDP S A H) (β : ℝ) (h : Fin (H + 1)) (s : S) : ℝ :=
  Real.exp (β * optEntropicValue M β h s)

/-- The optimal exponential state-action value `U*_h(s, a) = E[exp(β R) Z*_{h+1}(S')]`. -/
noncomputable def optExpQ (M : EpisodicMDP S A H) (β : ℝ) (h : Fin H) (s : S) (a : A) : ℝ :=
  (∫ x, Real.exp (β * x) ∂(M.reward h (s, a))) * ∫ s', optExpValue M β h.succ s' ∂(M.trans h (s, a))

/-- The entropic variance `σQ^π_h(s, a) = E[(exp(β R_h) - U^π_h(s, a))² | S_h = s, A_h = a]`:
the variance of the exponential return from `(s, a)` at step `h`, the first reward being drawn
from `M.reward h (s, a)`, the next state from `M.trans h (s, a)` and the rest of the trajectory
following `π` from step `h + 1`. -/
noncomputable def entropicVarQ (M : EpisodicMDP S A H) (β : ℝ) (π : Policy S A H) (h : Fin H)
    (s : S) (a : A) : ℝ :=
  ∫ x, ∫ s', ∫ traj, (Real.exp (β * (x + episodeReturn H traj)) - expQ M β π h s a) ^ 2
    ∂(stepLaw M π (s', h.succ)) ∂(M.trans h (s, a)) ∂(M.reward h (s, a))

/-- The entropic variance `σV^π_h(s) = σQ^π_h(s, π_h(s))`, `0` at the terminal step. -/
noncomputable def entropicVarV (M : EpisodicMDP S A H) (β : ℝ) (π : Policy S A H)
    (h : Fin (H + 1)) (s : S) : ℝ :=
  if hh : (h : ℕ) < H then entropicVarQ M β π ⟨h, hh⟩ s (π ⟨h, hh⟩ s) else 0

/-- The maximal achievable return `G_max(M) = ⨆ π, ess sup R_1` from the initial state `s₁`. -/
noncomputable def maxReturn (M : EpisodicMDP S A H) (s₁ : S) : ℝ :=
  ⨆ π : Policy S A H, essSup (episodeReturn H) (stepLaw M π (s₁, startStep H))

/-- `𝒜` is `(ε, δ)`-PAC for best-policy identification under the entropic risk measure with
parameter `β`, for the known reward function `r`, from the initial state `s₁`: for every MDP
with reward function `r`, the output `π̂` of `𝒜` in its states-only environment satisfies
`V*_1(s₁) - V^π̂_1(s₁) > ε` with probability at most `δ`. -/
def IsEntropicPAC (𝒜 : BPIAlg S A H) (r : Fin H → S → A → ℝ) (β ε δ : ℝ) (s₁ : S) : Prop :=
  𝒜.IsPAC (fun M : {M : EpisodicMDP S A H // M.HasRewardFn r} ↦ statesEnv M.1 s₁)
    (fun M π ↦
      ε < optEntropicValue M.1 β (startStep H) s₁ - entropicValue M.1 β π (startStep H) s₁) δ

end Learning.MDP.Episodic
