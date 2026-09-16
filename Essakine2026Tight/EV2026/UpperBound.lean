/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.EV2026.Algorithm
public import Essakine2026Tight.EV2026.Constants
public import Essakine2026Tight.EV2026.TailNeg
public import Essakine2026Tight.EV2026.TailPos
public import Essakine2026Tight.LeanMachineLearning.SequentialLearning.IdentificationAlg

/-!
# Theorem 4: sample complexity of Entropic-BPI

For every reward function `r` with values in `[0, 1]`, `β ≠ 0`, `δ ∈ (0, 1)` and
`ε ∈ (0, 2 / (|β| H S)]`, Entropic-BPI is `(ε, δ)`-PAC for entropic best-policy identification
on the class of MDPs with reward function `r` (`isEntropicPAC_entropicBPI`), and in every run
on such an MDP `M`, with probability at least `1 - δ`, it stops after at most
`upperBound S A H β ε δ (G_max M)` episodes (`probReal_stoppingTime_entropicBPI_le_ge`), which is
`Õ(e^{2 |β| ε} (e^{|β| ε} - 1)⁻² (e^{|β| G_max} - 1)² e^{-|β| G_max} S A H)`. This is the
detailed version of the theorem (restated in the appendix as Theorem 6), with its two
conclusions as two statements.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Learning.MDP.Episodic
open scoped ENNReal

namespace Essakine2026Tight

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]
  {H : ℕ}

/-- **Theorem 4, first part** (Essakine, Vernade 2026; PAC property). For every reward function
`r` with values in `[0, 1]`, `β ≠ 0`, `δ ∈ (0, 1)` and `ε ∈ (0, 2 / (|β| H S)]`, Entropic-BPI
with parameters `r, β, δ, ε` and initial state `s₁` is `(ε, δ)`-PAC for entropic best-policy
identification on the class of MDPs with reward function `r`. -/
theorem isEntropicPAC_entropicBPI (r : Fin H → S → A → ℝ) (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    {β δ ε : ℝ} (hβ : β ≠ 0) (hδ : δ ∈ Set.Ioo 0 1)
    (hε : ε ∈ Set.Ioc 0 (2 / (|β| * H * Fintype.card S))) (s₁ : S) :
    IsEntropicPAC (entropicBPI r β δ ε s₁) r β ε δ s₁ := by
  intro M
  have hrun := (entropicBPI r β δ ε s₁).isRun_runMeasure (statesEnv M.1 s₁)
  rw [← hrun.hasLaw_output.measureReal_eq (Set.to_countable _).measurableSet]
  rcases hβ.lt_or_gt with hneg | hpos
  · exact measureReal_bad_le_of_neg M.2 hr hneg hδ.1 hδ.2.le hε.1 hrun
  · exact measureReal_bad_le_of_pos M.2 hr hpos hδ.1 hδ.2.le hε.1 hrun

/-- **Theorem 4, second part** (Essakine, Vernade 2026; sample complexity). For every reward
function `r` with values in `[0, 1]`, `β ≠ 0`, `δ ∈ (0, 1)`, `ε ∈ (0, 2 / (|β| H S)]` and every
MDP `M` with reward function `r`, in every run of Entropic-BPI on `M` from `s₁`, with
probability at least `1 - δ` its number of episodes `τ` is at most
`upperBound S A H β ε δ G_max(M)`. -/
theorem probReal_stoppingTime_entropicBPI_le_ge (r : Fin H → S → A → ℝ)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) {β δ ε : ℝ} (hβ : β ≠ 0) (hδ : δ ∈ Set.Ioo 0 1)
    (hε : ε ∈ Set.Ioc 0 (2 / (|β| * H * Fintype.card S))) (s₁ : S)
    (M : EpisodicMDP S A H) (hM : M.HasRewardFn r)
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → Policy S A H) (Y : ℕ → Ω → Traj S H) (out : Ω → Policy S A H)
    (h : (entropicBPI r β δ ε s₁).IsRun (statesEnv M s₁) (fun _ _ ↦ ()) X Y out P) :
    1 - δ ≤ P.real {ω |
      ((entropicBPI r β δ ε s₁).stoppingTime (fun _ _ ↦ ()) X Y ω : ℝ≥0∞) ≤
        ENNReal.ofReal
          (upperBound (Fintype.card S) (Fintype.card A) H β ε δ (maxReturn M s₁))} := by
  rcases hβ.lt_or_gt with hneg | hpos
  · exact one_sub_le_measureReal_stoppingTime_le_of_neg hM hr hneg hδ.1 hδ.2.le hε.1 h
  · exact one_sub_le_measureReal_stoppingTime_le_of_pos hM hr hpos hδ.1 hδ.2.le hε.1 h

end Essakine2026Tight
