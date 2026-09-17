/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.StepLaw

/-!
# Occupancy measures of a finite-horizon MDP

For a finite-horizon MDP `M`, a policy `π : ℕ → S → A` (measurable at every step, `hπ`) and an
initial state `s₁`:

* `stateLawAt M π s₁ h` is the law of the state `S_h` of the step `h` and
  `occupancyMeasure M π s₁ h` the law of the state-action pair `(S_h, A_h)`
  (`MDP/Episodic.lean`); the action is the policy's (`hasCondDistrib_action_obs_stepLaw`), so the
  occupancy measure is the image of the state law by `s ↦ (s, π h s)`
  (`occupancyMeasure_eq_map`), and the state laws satisfy the **forward recursion**
  `stateLawAt (h + 1) = policyTransKernel h ∘ₘ stateLawAt h` (`stateLawAt_succ`) with the
  transition kernel `policyTransKernel M hπ h : Kernel S S` of the policy;
* the expectation of a function of `(S_h, A_h)` is its integral against the occupancy measure
  (`integral_comp_stateAction_stepLaw`);
* on finite state and action spaces, the occupancy `occupancy M π s₁ h s a = P^π(S_h = s, A_h = a)`
  is a probability vector concentrated on the graph of `π h` (`occupancy_nonneg`,
  `sum_occupancy`, `occupancy_eq`), the expectation of a sum of functions of the state-action
  pairs along the trajectory is a sum against the occupancies
  (`integral_sum_comp_obs_action_stepLaw`), and the forward recursion reads
  `p_{h+1}(s', a') = 1{a' = π_{h+1}(s')} ∑_{s, a} p_h(s, a) p_h(s' | s, a)` (`occupancy_succ`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP
open scoped ENNReal

namespace Learning.MDP.Episodic

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : EpisodicMDP S A)

section NoMeasurability

variable (π : ℕ → S → A) (s₁ : S)

/-- The law of the state `S_h` of the step `h` of the trajectory of `π` from `s₁`. -/
noncomputable def stateLawAt (h : ℕ) : Measure S :=
  (stepLaw M π (s₁, 0)).map fun x ↦ (IT.obs h x).1

lemma hasLaw_fst_obs_stateLawAt (h : ℕ) :
    HasLaw (fun x ↦ (IT.obs h x).1) (stateLawAt M π s₁ h) (stepLaw M π (s₁, 0)) :=
  ⟨(measurable_fst.comp (IT.measurable_obs h)).aemeasurable, rfl⟩

lemma hasLaw_stateAction_occupancyMeasure (h : ℕ) :
    HasLaw (stateAction h) (occupancyMeasure M π s₁ h) (stepLaw M π (s₁, 0)) :=
  ⟨(measurable_stateAction h).aemeasurable, rfl⟩

/-- The expectation of an integrable function of the state-action pair of the step `h` is its
integral against the occupancy measure. -/
lemma integral_comp_stateAction_stepLaw (h : ℕ) {f : S × A → ℝ}
    (hf : AEStronglyMeasurable f (occupancyMeasure M π s₁ h)) :
    ∫ x, f (stateAction h x) ∂stepLaw M π (s₁, 0) = ∫ z, f z ∂occupancyMeasure M π s₁ h :=
  (integral_map (measurable_stateAction h).aemeasurable hf).symm

lemma lintegral_comp_stateAction_stepLaw (h : ℕ) {f : S × A → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f (stateAction h x) ∂stepLaw M π (s₁, 0) = ∫⁻ z, f z ∂occupancyMeasure M π s₁ h :=
  (lintegral_map hf (measurable_stateAction h)).symm

lemma occupancy_nonneg (h : ℕ) (s : S) (a : A) : 0 ≤ occupancy M π s₁ h s a :=
  measureReal_nonneg

variable [MeasurableSingletonClass S] [MeasurableSingletonClass A] [Fintype S] [Fintype A]

/-- The expectation of a function of the state-action pair of the step `h` is its sum against
the occupancies. -/
lemma integral_comp_obs_action_stepLaw (h : ℕ) (f : S → A → ℝ) :
    ∫ x, f (IT.obs h x).1 (IT.action h x) ∂stepLaw M π (s₁, 0)
      = ∑ s, ∑ a, occupancy M π s₁ h s a * f s a := by
  have h1 := integral_comp_stateAction_stepLaw M π s₁ h (f := fun z ↦ f z.1 z.2)
    (measurable_of_countable _).aestronglyMeasurable
  simp only [stateAction] at h1
  rw [h1, integral_fintype Integrable.of_finite, Fintype.sum_prod_type]
  rfl

/-- **Expectations of sums along the trajectory**: the expectation of `∑_{h < n} f_h(S_h, A_h)`
is `∑_{h < n} ∑_{s, a} p^π_h(s, a) f_h(s, a)`. -/
lemma integral_sum_comp_obs_action_stepLaw (n : ℕ) (f : ℕ → S → A → ℝ) :
    ∫ x, ∑ h ∈ range n, f h (IT.obs h x).1 (IT.action h x) ∂stepLaw M π (s₁, 0)
      = ∑ h ∈ range n, ∑ s, ∑ a, occupancy M π s₁ h s a * f h s a := by
  rw [integral_finsetSum _ fun h _ ↦ ?_]
  · exact sum_congr rfl fun h _ ↦ integral_comp_obs_action_stepLaw M π s₁ h (f h)
  · exact (Integrable.of_finite (f := fun z : S × A ↦ f h z.1 z.2)).comp_measurable
      (measurable_stateAction h)

end NoMeasurability

/-- The transition kernel of the policy `π` at the step `h`: `s ↦ p_h(· | s, π_h(s))`. -/
noncomputable def policyTransKernel {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) (h : ℕ) :
    Kernel S S :=
  (M.trans h).comap (fun s ↦ (s, π h s)) (measurable_id.prodMk (hπ h))

variable {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h)) (s₁ : S)

lemma policyTransKernel_apply (h : ℕ) (s : S) :
    policyTransKernel M hπ h s = M.trans h (s, π h s) := rfl

instance (h : ℕ) : IsMarkovKernel (policyTransKernel M hπ h) := by
  unfold policyTransKernel; infer_instance

include hπ

lemma isProbabilityMeasure_stateLawAt (h : ℕ) : IsProbabilityMeasure (stateLawAt M π s₁ h) := by
  have := isProbabilityMeasure_stepLaw M hπ (s₁, 0)
  unfold stateLawAt; infer_instance

lemma isProbabilityMeasure_occupancyMeasure (h : ℕ) :
    IsProbabilityMeasure (occupancyMeasure M π s₁ h) := by
  have := isProbabilityMeasure_stepLaw M hπ (s₁, 0)
  unfold occupancyMeasure; infer_instance

lemma occupancy_le_one (h : ℕ) (s : S) (a : A) : occupancy M π s₁ h s a ≤ 1 := by
  have := isProbabilityMeasure_occupancyMeasure M hπ s₁ h
  exact measureReal_le_one

variable [MeasurableSingletonClass S] [MeasurableSingletonClass A]

/-- The action of the round `k` is the action of the policy at its state: conditional-law
form, valid without a measurable diagonal on the action space. -/
lemma hasCondDistrib_action_obs_stepLaw (s : S) (h k : ℕ) :
    HasCondDistrib (IT.action k) (fun x ↦ (IT.obs k x).1)
      (Kernel.deterministic (π (h + k)) (hπ (h + k))) (stepLaw M π (s, h)) := by
  have hc := (hasCondDistrib_shiftRounds_stepLaw M hπ s h k).comp_left (IT.measurable_action 0)
  have hK : (Kernel.prodMkLeft (Hist (S × ℕ) A ℝ k) (stepLawKernel M π (h + k))).map
      (IT.action 0) = Kernel.prodMkLeft (Hist (S × ℕ) A ℝ k)
        (Kernel.deterministic (π (h + k)) (hπ (h + k))) := by
    ext q : 1
    rw [Kernel.map_apply _ (IT.measurable_action 0), Kernel.prodMkLeft_apply,
      Kernel.prodMkLeft_apply, stepLawKernel_apply, Kernel.deterministic_apply]
    exact (hasLaw_action_zero_stepLaw M hπ q.2 (h + k)).map_eq
  rw [hK] at hc
  refine hc.comp_right.congr (Filter.Eventually.of_forall fun _ ↦ rfl)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  simp [shiftRounds, IT.action]

/-- The state of the round `k + 1` has conditional law `p_{h+k}(· | S_k, π(S_k))` given the state
of the round `k`. -/
lemma hasCondDistrib_fst_obs_succ_stepLaw (s : S) (h k : ℕ) :
    HasCondDistrib (fun x ↦ (IT.obs (k + 1) x).1) (fun x ↦ (IT.obs k x).1)
      (policyTransKernel M hπ (h + k)) (stepLaw M π (s, h)) :=
  HasCondDistrib.comp_right (Z := IT.hist (k + 1)) (κ := policyTransKernel M hπ (h + k))
    (f := fun p : Hist (S × ℕ) A ℝ (k + 1) ↦ (p (Fin.last k)).obs.1)
    (hf := measurable_fst.comp (Round.measurable_obs.comp (measurable_pi_apply (Fin.last k))))
    (hasCondDistrib_obs_succ_hist_stepLaw M hπ s h k)

/-- The occupancy measure is the image of the state law by `s ↦ (s, π h s)`. -/
lemma occupancyMeasure_eq_map (h : ℕ) :
    occupancyMeasure M π s₁ h = (stateLawAt M π s₁ h).map fun s ↦ (s, π h s) := by
  have hc := hasCondDistrib_action_obs_stepLaw M hπ s₁ 0 h
  rw [Nat.zero_add] at hc
  unfold occupancyMeasure stateAction stateLawAt
  rw [← Measure.compProd_deterministic (hπ h)]
  exact hc.map_eq

/-- **Forward recursion of the state laws**: the law of `S_{h+1}` is the law of `S_h` pushed
through the transition kernel of the policy. -/
lemma stateLawAt_succ (h : ℕ) :
    stateLawAt M π s₁ (h + 1) = policyTransKernel M hπ h ∘ₘ stateLawAt M π s₁ h := by
  have hc := hasCondDistrib_fst_obs_succ_stepLaw M hπ s₁ 0 h
  rw [Nat.zero_add] at hc
  unfold stateLawAt
  rw [← Measure.snd_compProd, ← hc.map_eq, Measure.snd,
    Measure.map_map measurable_snd (by fun_prop)]
  rfl

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
lemma stateLawAt_zero : stateLawAt M π s₁ 0 = Measure.dirac s₁ := by
  rw [stateLawAt]
  change (stepLaw M π (s₁, 0)).map (Prod.fst ∘ IT.obs 0) = _
  rw [← Measure.map_map measurable_fst (IT.measurable_obs 0),
    (hasLaw_obs_zero_stepLaw M hπ (s₁, 0)).map_eq]
  exact Measure.map_dirac' measurable_fst (s₁, 0)

/-- The occupancy of `(s, a)` is the probability of visiting `s` if `a = π_h(s)`, and `0`
otherwise. -/
lemma occupancy_eq [DecidableEq A] (h : ℕ) (s : S) (a : A) :
    occupancy M π s₁ h s a = if a = π h s then (stateLawAt M π s₁ h).real {s} else 0 := by
  rw [occupancy, occupancyMeasure_eq_map M hπ, map_measureReal_apply (f := fun s ↦ (s, π h s))
    (measurable_id.prodMk (hπ h)) (measurableSet_singleton _)]
  split_ifs with ha
  · congr 1
    ext s'
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.ext_iff]
    constructor
    · rintro ⟨rfl, -⟩; rfl
    · rintro rfl; exact ⟨rfl, ha.symm⟩
  · rw [← measureReal_empty (μ := stateLawAt M π s₁ h)]
    congr 1
    ext s'
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.ext_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl
    exact Ne.symm ha

variable [Fintype S] [Fintype A]

/-- Occupancies are probability vectors. -/
lemma sum_occupancy (h : ℕ) : ∑ s, ∑ a, occupancy M π s₁ h s a = 1 := by
  have := isProbabilityMeasure_stepLaw M hπ (s₁, 0)
  simpa using (integral_comp_obs_action_stepLaw M π s₁ h (fun _ _ ↦ 1)).symm

/-- **Forward recursion of the occupancies**. -/
lemma occupancy_succ [DecidableEq A] (h : ℕ) (s' : S) (a' : A) :
    occupancy M π s₁ (h + 1) s' a' = if a' = π (h + 1) s'
      then ∑ s, ∑ a, occupancy M π s₁ h s a * M.transVec h s a s' else 0 := by
  classical
  rw [occupancy_eq M hπ]
  by_cases ha : a' = π (h + 1) s'
  swap; · simp [ha]
  simp only [ha, ↓reduceIte]
  have hind := integral_mul_obs_succ_stepLaw M hπ s₁ 0 h (Ψ := fun _ ↦ 1) measurable_const (C := 1)
    (fun _ ↦ by simp) (g := fun s'' ↦ if s'' = s' then 1 else 0) (measurable_of_countable _)
    (D := 1) (fun _ ↦ by split_ifs <;> simp)
  simp only [one_mul, Nat.zero_add] at hind
  have hmeas : MeasurableSet {x : ℕ → Round (S × ℕ) A ℝ | (IT.obs (h + 1) x).1 = s'} :=
    (measurableSet_singleton s').preimage (measurable_fst.comp (IT.measurable_obs _))
  calc (stateLawAt M π s₁ (h + 1)).real {s'}
      = (stepLaw M π (s₁, 0)).real {x | (IT.obs (h + 1) x).1 = s'} := by
        rw [stateLawAt, map_measureReal_apply (f := fun x : ℕ → Round (S × ℕ) A ℝ ↦
          (IT.obs (h + 1) x).1) (measurable_fst.comp (IT.measurable_obs _))
          (measurableSet_singleton _)]
        rfl
    _ = ∫ x, {x : ℕ → Round (S × ℕ) A ℝ | (IT.obs (h + 1) x).1 = s'}.indicator 1 x
          ∂stepLaw M π (s₁, 0) := (integral_indicator_one hmeas).symm
    _ = ∫ x, (if (IT.obs (h + 1) x).1 = s' then 1 else 0) ∂stepLaw M π (s₁, 0) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    _ = ∫ x, M.transVec h (IT.obs h x).1 (π h (IT.obs h x).1) s' ∂stepLaw M π (s₁, 0) := by
        rw [hind]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        simp only
        rw [integral_fintype Integrable.of_finite]
        simp [EpisodicMDP.transVec, MDP.transVec, Finset.sum_ite_eq']
    _ = ∑ s, ∑ a, occupancy M π s₁ h s a * M.transVec h s (π h s) s' :=
        integral_comp_obs_action_stepLaw M π s₁ h (fun s _ ↦ M.transVec h s (π h s) s')
    _ = _ := by
        refine sum_congr rfl fun s _ ↦ sum_congr rfl fun a _ ↦ ?_
        rw [occupancy_eq M hπ]
        split_ifs with has
        · rw [has]
        · simp

end Learning.MDP.Episodic
