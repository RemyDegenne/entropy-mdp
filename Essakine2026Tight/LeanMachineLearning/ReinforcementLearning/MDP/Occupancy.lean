/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.MarkovIter

/-!
# Occupancy measures of a finite-horizon MDP

The occupancy measure `occupancy M π s₁ h s a = P^π(S_h = s, A_h = a)` of a policy `π` from the
initial state `s₁` (`MDP/Episodic.lean`) is a probability vector on `S × A` concentrated on the
graph of `π h` (`occupancy_nonneg`, `sum_occupancy`, `occupancy_eq`), the expectation of a sum of
functions of the state-action pairs along the trajectory is a sum against the occupancy measures
(`integral_sum_comp_obs_action_stepLaw`), and the occupancy measures satisfy the forward
recursion `p_{h+1}(s', a') = 1{a' = π_{h+1}(s')} ∑_{s, a} p_h(s, a) p_h(s' | s, a)`
(`occupancy_succ`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP
open scoped ENNReal

namespace Learning.MDP.Episodic

variable {S A : Type*} [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] {H : ℕ} (M : EpisodicMDP S A H)
  (π : Policy S A H) (s₁ : S)

/-- Occupancy measures are nonnegative. -/
lemma occupancy_nonneg (h : Fin H) (s : S) (a : A) : 0 ≤ occupancy M π s₁ h s a :=
  measureReal_nonneg

/-- Occupancy measures are at most `1`. -/
lemma occupancy_le_one (h : Fin H) (s : S) (a : A) : occupancy M π s₁ h s a ≤ 1 :=
  measureReal_le_one

/-- The occupancy measure of `(s, a)` is the probability of visiting `s` if `a = π_h(s)`, and `0`
otherwise. -/
lemma occupancy_eq [DecidableEq A] (h : Fin H) (s : S) (a : A) :
    occupancy M π s₁ h s a = if a = π h s
      then (stepLaw M π (s₁, startStep H)).real {x | (IT.obs h x).1 = s} else 0 := by
  have hae := ae_action_eq_stepLaw M π s₁ (h₀ := startStep H) (h := h) (k := h) (by simp)
  rw [occupancy, measureReal_congr (t := {x | (IT.obs h x).1 = s ∧ π h (IT.obs h x).1 = a})]
  · split_ifs with ha
    · congr 1
      ext x
      simp only [Set.mem_ofPred_eq, and_iff_left_iff_imp]
      intro hx
      rw [hx, ha]
    · rw [← measureReal_empty (μ := stepLaw M π (s₁, startStep H))]
      congr 1
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hx
      rw [hx]
      exact Ne.symm ha
  · filter_upwards [hae] with x hx
    simp only [hx]

/-- The expectation of a function of the state-action pair of the step `h` is its integral against
the occupancy measure. -/
lemma integral_comp_obs_action_stepLaw (h : Fin H) (f : S → A → ℝ) :
    ∫ x, f (IT.obs h x).1 (IT.action h x) ∂stepLaw M π (s₁, startStep H)
      = ∑ s, ∑ a, occupancy M π s₁ h s a * f s a := by
  have hZ : Measurable fun x : ℕ → Round (LayerState S H) A ℝ ↦ ((IT.obs h x).1, IT.action h x) :=
    by fun_prop
  calc ∫ x, f (IT.obs h x).1 (IT.action h x) ∂stepLaw M π (s₁, startStep H)
      = ∫ z, f z.1 z.2 ∂(stepLaw M π (s₁, startStep H)).map
          (fun x ↦ ((IT.obs h x).1, IT.action h x)) :=
        (integral_map (f := fun z : S × A ↦ f z.1 z.2) hZ.aemeasurable
          (measurable_of_countable _).aestronglyMeasurable).symm
    _ = _ := by
        rw [integral_fintype Integrable.of_finite, Fintype.sum_prod_type]
        refine sum_congr rfl fun s _ ↦ sum_congr rfl fun a _ ↦ ?_
        rw [smul_eq_mul, map_measureReal_apply hZ (measurableSet_singleton _), occupancy]
        congr 2
        ext x
        simp [Prod.ext_iff]

/-- Occupancy measures are probability vectors. -/
lemma sum_occupancy (h : Fin H) : ∑ s, ∑ a, occupancy M π s₁ h s a = 1 := by
  simpa using (integral_comp_obs_action_stepLaw M π s₁ h (fun _ _ ↦ 1)).symm

/-- **Expectations of sums along the trajectory**: the expectation of `∑_h f_h(S_h, A_h)` is
`∑_h ∑_{s, a} p^π_h(s, a) f_h(s, a)`. -/
lemma integral_sum_comp_obs_action_stepLaw (f : Fin H → S → A → ℝ) :
    ∫ x, ∑ h : Fin H, f h (IT.obs h x).1 (IT.action h x) ∂stepLaw M π (s₁, startStep H)
      = ∑ h, ∑ s, ∑ a, occupancy M π s₁ h s a * f h s a := by
  rw [integral_finsetSum _ fun h _ ↦ ?_]
  · exact sum_congr rfl fun h _ ↦ integral_comp_obs_action_stepLaw M π s₁ h (f h)
  · have hZ : Measurable fun x : ℕ → Round (LayerState S H) A ℝ ↦
        ((IT.obs h x).1, IT.action h x) := by fun_prop
    exact (Integrable.of_finite (f := fun z : S × A ↦ f h z.1 z.2)).comp_measurable hZ

/-- **Forward recursion of the occupancy measures**. -/
lemma occupancy_succ [DecidableEq A] {h h' : Fin H} (hh : (h' : ℕ) = h + 1) (s' : S)
    (a' : A) :
    occupancy M π s₁ h' s' a' = if a' = π h' s'
      then ∑ s, ∑ a, occupancy M π s₁ h s a * M.transVec h s a s' else 0 := by
  classical
  rw [occupancy_eq]
  by_cases ha : a' = π h' s'
  swap; · simp [ha]
  rw [ite_eq_left ha, ite_eq_left ha]
  have hind := integral_mul_obs_succ_stepLaw M π s₁ (h₀ := startStep H) (h := h) (k := h)
    (by simp) (Ψ := fun _ ↦ 1) measurable_const (C := 1) (fun _ ↦ by simp)
    (fun s'' ↦ if s'' = s' then 1 else 0)
  simp only [one_mul] at hind
  have hmeas : MeasurableSet {x : ℕ → Round (LayerState S H) A ℝ | (IT.obs h' x).1 = s'} :=
    (measurableSet_singleton s').preimage (measurable_fst.comp (IT.measurable_obs _))
  calc (stepLaw M π (s₁, startStep H)).real {x | (IT.obs h' x).1 = s'}
      = ∫ x, {x : ℕ → Round (LayerState S H) A ℝ | (IT.obs h' x).1 = s'}.indicator 1 x
          ∂stepLaw M π (s₁, startStep H) := (integral_indicator_one hmeas).symm
    _ = ∫ x, (if (IT.obs (h + 1) x).1 = s' then 1 else 0) ∂stepLaw M π (s₁, startStep H) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply, hh]
    _ = ∫ x, M.transVec h (IT.obs h x).1 (π h (IT.obs h x).1) s'
          ∂stepLaw M π (s₁, startStep H) := by
        rw [hind]
        simp [vecExp]
    _ = ∑ s, ∑ a, occupancy M π s₁ h s a * M.transVec h s (π h s) s' :=
        integral_comp_obs_action_stepLaw M π s₁ h (fun s _ ↦ M.transVec h s (π h s) s')
    _ = _ := by
        refine sum_congr rfl fun s _ ↦ sum_congr rfl fun a _ ↦ ?_
        rw [occupancy_eq]
        split_ifs with has
        · rw [has]
        · simp

end Learning.MDP.Episodic
