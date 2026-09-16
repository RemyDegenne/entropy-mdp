/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.EV2026.Run

/-!
# Runs of Entropic-BPI

In a run of Entropic-BPI in any environment, almost surely: the policy played at every episode is
the greedy policy of the history (`ae_action_eq_greedy`); the stopping time is the first number
of episodes after which the stopping condition holds (`stopCond_histAt_stoppingTime`,
`not_stopCond_histAt_of_lt_stoppingTime`, `stoppingTime_le_of_stopCond`); and the output is the
greedy policy of the history at the stopping time (`ae_output_eq_greedy`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Learning.MDP.Episodic

namespace Essakine2026Tight

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]
  {H : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {r : Fin H → S → A → ℝ} {β δ ε : ℝ} {s₁ : S} {env : Environment Unit (Policy S A H) (Traj S H)}
  {X : ℕ → Ω → Policy S A H} {Y : ℕ → Ω → Traj S H} {out : Ω → Policy S A H}

/-- In a run of Entropic-BPI, the policy of every episode is the greedy policy of the history of
the previous episodes. -/
lemma ae_action_eq_greedy
    (h : (entropicBPI r β δ ε s₁).IsRun env (fun _ _ ↦ ()) X Y out P) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = greedy r β δ (histAt X Y t ω) :=
  IsAlgEnvSeq.action_detAlgorithm_ae_all_eq h.isAlgEnvSeq

/-- If Entropic-BPI stops, the stopping condition holds for the history at the stopping time. -/
lemma stopCond_histAt_stoppingTime {ω : Ω}
    (hτ : (entropicBPI r β δ ε s₁).stoppingTime (fun _ _ ↦ ()) X Y ω ≠ ⊤) :
    stopCond r β δ ε s₁
      (histAt X Y ((entropicBPI r β δ ε s₁).stoppingTime (fun _ _ ↦ ()) X Y ω).untopA ω) :=
  IdentAlg.stoppedHist_mem_stopSet_of_ne_top hτ

/-- Before the stopping time, the stopping condition fails. -/
lemma not_stopCond_histAt_of_lt_stoppingTime {ω : Ω} {t : ℕ}
    (ht : (t : ℕ∞) < (entropicBPI r β δ ε s₁).stoppingTime (fun _ _ ↦ ()) X Y ω) :
    ¬ stopCond r β δ ε s₁ (histAt X Y t ω) :=
  notMem_of_lt_hittingAfter (k := t) ht (Nat.zero_le t)

/-- The stopping time is at most any number of episodes after which the condition holds. -/
lemma stoppingTime_le_of_stopCond {ω : Ω} {t : ℕ} (ht : stopCond r β δ ε s₁ (histAt X Y t ω)) :
    (entropicBPI r β δ ε s₁).stoppingTime (fun _ _ ↦ ()) X Y ω ≤ t :=
  hittingAfter_le_of_mem (Nat.zero_le t) ht

/-- In a run of Entropic-BPI, the output is the greedy policy of the history at the stopping
time. -/
lemma ae_output_eq_greedy
    (h : (entropicBPI r β δ ε s₁).IsRun env (fun _ _ ↦ ()) X Y out P) :
    ∀ᵐ ω ∂P, out ω = greedy r β δ
      (histAt X Y ((entropicBPI r β δ ε s₁).stoppingTime (fun _ _ ↦ ()) X Y ω).untopA ω) := by
  have hout : HasCondDistrib out ((entropicBPI r β δ ε s₁).stoppedHist (fun _ _ ↦ ()) X Y)
      (Kernel.deterministic (fun h ↦ greedy r β δ h.2) (measurable_greedy_snd r β δ)) P :=
    h.hasCondDistrib_output
  have hae := ae_eq_of_hasCondDistrib_deterministic (measurable_greedy_snd r β δ)
    hout.aemeasurable_fst hout.aemeasurable_snd hout
  filter_upwards [hae] with ω hω
  exact hω

end Essakine2026Tight
