/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Episodic
public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Markov

/-!
# The Markov property of the trajectory laws of a finite-horizon MDP

For a finite-horizon MDP `M`, a policy `π`, a step `h : Fin H` and a state `s`, the trajectory
law `stepLaw M π (s, h.castSucc)` of `π` from `s` at step `h` satisfies
(`hasLaw_stepLaw_castSucc`): the reward of the first round, the state of the second round and
the shifted trajectory have law
`(M.reward h (s, π h s)).prod (M.trans h (s, π h s)) ⊗ₘ Kernel.prodMkLeft ℝ K` with
`K = stepLawKernel M π h.succ`: the reward and the next state `s'` are independent with the
laws of the MDP, and given them the rest of the trajectory is the trajectory of `π` from `s'` at
step `h + 1`. At the terminal layer the trajectory is constant: its rewards vanish and its shift
has the same law (`hasLaw_shiftRound_stepLaw_last`, `ae_feedback_eq_zero_stepLaw_last`).

Consequences: the rewards of the rounds after the terminal layer vanish almost surely
(`ae_feedback_eq_zero_stepLaw`), hence the return of a trajectory is the first reward plus the
return of the shifted trajectory (`ae_episodeReturn_eq_add_shiftRound`), and almost sure
properties and integrals of functions of (first reward, next state, shifted trajectory) are
computed step by step (`ae_stepLaw_castSucc_of_ae`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP

namespace Learning.MDP.Episodic

variable {S A : Type*} [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] {H : ℕ} (M : EpisodicMDP S A H)

/-! ### The kernels of the layered MDP at a non-terminal and at the terminal layer -/

lemma layerReward_castSucc (h : Fin H) (s : S) (a : A) :
    layerReward M ((s, h.castSucc), a) = M.reward h (s, a) := by
  simp [layerReward_apply, layerRewardFun]

lemma layerReward_last (s : S) (a : A) :
    layerReward M ((s, Fin.last H), a) = Measure.dirac 0 := by
  simp [layerReward_apply, layerRewardFun]

lemma layerTrans_castSucc (h : Fin H) (s : S) (a : A) :
    layerTrans M ((s, h.castSucc), a) = (M.trans h (s, a)).map fun s' ↦ (s', h.succ) := by
  simp only [layerTrans_apply, layerTransFun, Fin.val_castSucc, h.is_lt, ↓reduceDIte]
  rfl

lemma layerTrans_last (s : S) (a : A) :
    layerTrans M ((s, Fin.last H), a) = Measure.dirac (s, Fin.last H) := by
  simp [layerTrans_apply, layerTransFun]

variable [Nonempty A]

omit [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
lemma Policy.layer_castSucc (π : Policy S A H) (h : Fin H) (s : S) :
    π.layer (s, h.castSucc) = π h s := by
  simp [Policy.layer]

variable (π : Policy S A H)

/-! ### The trajectory laws as kernels -/

lemma stepLaw_eq_trajMeasure (p : LayerState S H) :
    stepLaw M π p
      = trajMeasure (policyAlg π.layer π.measurable_layer) ((layerMDP M).env (Measure.dirac p)) :=
  rfl

lemma measurable_stepLaw_state (h : Fin (H + 1)) : Measurable fun s ↦ stepLaw M π (s, h) :=
  measurable_of_countable _

/-- The trajectory laws of `π` from the states at the step `h`, as a kernel. -/
noncomputable def stepLawKernel (h : Fin (H + 1)) : Kernel S (ℕ → Round (LayerState S H) A ℝ) :=
  ⟨fun s ↦ stepLaw M π (s, h), measurable_stepLaw_state M π h⟩

@[simp]
lemma stepLawKernel_apply (h : Fin (H + 1)) (s : S) : stepLawKernel M π h s = stepLaw M π (s, h) :=
  rfl

instance (h : Fin (H + 1)) : IsMarkovKernel (stepLawKernel M π h) :=
  ⟨fun s ↦ isProbabilityMeasure_stepLaw M π (s, h)⟩

lemma policyKernel_layerMDP_apply (p : LayerState S H) :
    policyKernel (layerMDP M) π.measurable_layer p = stepLaw M π p :=
  rfl

/-! ### The first round -/

lemma hasLaw_obs_zero_stepLaw (p : LayerState S H) :
    HasLaw (IT.obs 0) (Measure.dirac p) (stepLaw M π p) :=
  IT.hasLaw_obs_zero (policyAlg π.layer π.measurable_layer) ((layerMDP M).env (Measure.dirac p))

lemma ae_obs_zero_stepLaw (p : LayerState S H) : ∀ᵐ x ∂stepLaw M π p, IT.obs 0 x = p :=
  (hasLaw_obs_zero_stepLaw M π p).ae_eq_of_dirac

lemma ae_action_zero_stepLaw (p : LayerState S H) :
    ∀ᵐ x ∂stepLaw M π p, IT.action 0 x = π.layer p := by
  have h := IsAlgEnvSeq.action_zero_detAlgorithm
    (IT.isAlgEnvSeq_trajMeasure (policyAlg π.layer π.measurable_layer)
      ((layerMDP M).env (Measure.dirac p)))
  filter_upwards [h, ae_obs_zero_stepLaw M π p] with x hx hx0
  rw [hx]
  exact congrArg π.layer hx0

lemma hasLaw_feedback_zero_stepLaw (p : LayerState S H) :
    HasLaw (IT.feedback 0) (layerReward M (p, π.layer p)) (stepLaw M π p) := by
  have h := IT.hasCondDistrib_feedback_zero (policyAlg π.layer π.measurable_layer)
    ((layerMDP M).env (Measure.dirac p))
  have hae : (fun _ ↦ (p, π.layer p)) =ᵐ[stepLaw M π p] fun x ↦ (IT.obs 0 x, IT.action 0 x) := by
    filter_upwards [ae_obs_zero_stepLaw M π p, ae_action_zero_stepLaw M π p] with x h0 h1
    rw [h0, h1]
  have h' := hasCondDistrib_const_iff.1 (h.congr hae (Filter.EventuallyEq.refl _ _))
  rwa [ν0_env] at h'

lemma hasCondDistrib_obs_one_feedback_zero_stepLaw (p : LayerState S H) :
    HasCondDistrib (IT.obs 1) (IT.feedback 0) (Kernel.const ℝ (layerTrans M (p, π.layer p)))
      (stepLaw M π p) := by
  have h := hasCondDistrib_obs_one_trajMeasure (layerMDP M) π.measurable_layer (Measure.dirac p)
  have hψ : MeasurableEmbedding fun r : ℝ ↦ ((p, π.layer p, r) : Round (LayerState S H) A ℝ) :=
    (measurableEmbedding_prodMk_left p).comp (measurableEmbedding_prodMk_left (π.layer p))
  have hae : (fun r : ℝ ↦ ((p, π.layer p, r) : Round (LayerState S H) A ℝ)) ∘ IT.feedback 0
      =ᵐ[stepLaw M π p] fun x ↦ x 0 := by
    filter_upwards [ae_obs_zero_stepLaw M π p, ae_action_zero_stepLaw M π p] with x h0 h1
    exact Prod.ext h0.symm (Prod.ext h1.symm rfl)
  have h3 := (h.congr hae (Filter.EventuallyEq.refl _ _)).of_measurableEmbedding_comp_right hψ
  convert h3 using 1
  · exact Kernel.ext fun _ ↦ rfl
  · rfl

lemma hasLaw_obs_one_stepLaw (p : LayerState S H) :
    HasLaw (IT.obs 1) (layerTrans M (p, π.layer p)) (stepLaw M π p) :=
  (hasCondDistrib_obs_one_feedback_zero_stepLaw M π p).hasLaw_of_const

/-! ### The Markov property at a non-terminal step -/

lemma ae_obs_one_snd_stepLaw_castSucc (h : Fin H) (s : S) :
    ∀ᵐ x ∂stepLaw M π (s, h.castSucc), (IT.obs 1 x).2 = h.succ := by
  have hl := hasLaw_obs_one_stepLaw M π (s, h.castSucc)
  rw [Policy.layer_castSucc, layerTrans_castSucc] at hl
  refine ae_of_ae_map (p := fun q : LayerState S H ↦ q.2 = h.succ) hl.aemeasurable ?_
  rw [hl.map_eq, ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) measurable_const)]
  exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- **Markov property** of the trajectory law of a finite-horizon MDP at a non-terminal step:
the reward of the first round, the state of the second round and the shifted trajectory have law
`(M.reward h (s, π h s)).prod (M.trans h (s, π h s)) ⊗ₘ Kernel.prodMkLeft ℝ K` with
`K = stepLawKernel M π h.succ`. -/
lemma hasLaw_stepLaw_castSucc (h : Fin H) (s : S) :
    HasLaw (fun x ↦ ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x))
      ((M.reward h (s, π h s)).prod (M.trans h (s, π h s))
        ⊗ₘ Kernel.prodMkLeft ℝ (stepLawKernel M π h.succ))
      (stepLaw M π (s, h.castSucc)) := by
  set p : LayerState S H := (s, h.castSucc) with hp
  -- the law of the first reward and the next state
  have hf : HasLaw (IT.feedback 0) (M.reward h (s, π h s)) (stepLaw M π p) := by
    have := hasLaw_feedback_zero_stepLaw M π p
    rwa [hp, Policy.layer_castSucc, layerReward_castSucc] at this
  have ho : HasCondDistrib (fun x ↦ (IT.obs 1 x).1) (IT.feedback 0)
      (Kernel.const ℝ (M.trans h (s, π h s))) (stepLaw M π p) := by
    have := (hasCondDistrib_obs_one_feedback_zero_stepLaw M π p).comp_left (f := Prod.fst)
      measurable_fst
    have hk : (Kernel.const ℝ (layerTrans M (p, π.layer p))).map Prod.fst
        = Kernel.const ℝ (M.trans h (s, π h s)) := by
      ext r : 1
      rw [Kernel.map_apply _ measurable_fst, Kernel.const_apply, Kernel.const_apply, hp,
        Policy.layer_castSucc, layerTrans_castSucc, Measure.map_map measurable_fst (by fun_prop)]
      exact Measure.map_id
    rw [hk] at this
    exact this
  have hG : HasLaw (fun x ↦ (IT.feedback 0 x, (IT.obs 1 x).1))
      ((M.reward h (s, π h s)).prod (M.trans h (s, π h s))) (stepLaw M π p) := by
    have := hf.prod_of_hasCondDistrib ho
    rwa [Measure.compProd_const] at this
  -- the conditional law of the shifted trajectory
  have hgen := hasCondDistrib_shiftRound_trajMeasure (layerMDP M) π.measurable_layer
    (Measure.dirac p)
  set φ : ℝ × S → Round (LayerState S H) A ℝ × LayerState S H :=
    fun q ↦ ((p, π.layer p, q.1), (q.2, h.succ)) with hφ_def
  have hφ : MeasurableEmbedding φ :=
    ((measurableEmbedding_prodMk_left p).comp (measurableEmbedding_prodMk_left (π.layer p))).prodMap
      (measurableEmbedding_prod_mk_right h.succ)
  have hae : φ ∘ (fun x ↦ (IT.feedback 0 x, (IT.obs 1 x).1)) =ᵐ[stepLaw M π p] firstRoundState := by
    filter_upwards [ae_obs_zero_stepLaw M π p, ae_action_zero_stepLaw M π p,
      ae_obs_one_snd_stepLaw_castSucc M π h s] with x h0 h1 h2
    exact Prod.ext (Prod.ext h0.symm (Prod.ext h1.symm rfl)) (Prod.ext rfl h2.symm)
  have hC := (hgen.congr hae (Filter.EventuallyEq.refl _ _)).of_measurableEmbedding_comp_right hφ
  have hC' : HasCondDistrib shiftRound (fun x ↦ (IT.feedback 0 x, (IT.obs 1 x).1))
      (Kernel.prodMkLeft ℝ (stepLawKernel M π h.succ)) (stepLaw M π p) := by
    convert hC using 1
    · exact Kernel.ext fun _ ↦ rfl
    · rfl
  exact hG.prod_of_hasCondDistrib hC'

lemma hasLaw_feedback_zero_stepLaw_castSucc (h : Fin H) (s : S) :
    HasLaw (IT.feedback 0) (M.reward h (s, π h s)) (stepLaw M π (s, h.castSucc)) := by
  have := hasLaw_feedback_zero_stepLaw M π (s, h.castSucc)
  rwa [Policy.layer_castSucc, layerReward_castSucc] at this

/-- Almost sure properties of (first reward, next state, shifted trajectory) at a non-terminal
step. -/
lemma ae_stepLaw_castSucc_of_ae {h : Fin H} {s : S}
    {P : ℝ → S → (ℕ → Round (LayerState S H) A ℝ) → Prop}
    (hP : MeasurableSet {z : (ℝ × S) × (ℕ → Round (LayerState S H) A ℝ) | P z.1.1 z.1.2 z.2})
    (hae : ∀ᵐ r ∂M.reward h (s, π h s), ∀ s', ∀ᵐ y ∂stepLaw M π (s', h.succ), P r s' y) :
    ∀ᵐ x ∂stepLaw M π (s, h.castSucc), P (IT.feedback 0 x) (IT.obs 1 x).1 (shiftRound x) := by
  have hlaw := hasLaw_stepLaw_castSucc M π h s
  refine ae_of_ae_map (p := fun z : (ℝ × S) × (ℕ → Round (LayerState S H) A ℝ) ↦
    P z.1.1 z.1.2 z.2) hlaw.aemeasurable ?_
  rw [hlaw.map_eq]
  refine Measure.ae_compProd_of_ae_ae (p := fun z : (ℝ × S) × (ℕ → Round (LayerState S H) A ℝ) ↦
    P z.1.1 z.1.2 z.2) hP ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hae] with q hq
  exact hq q.2

/-- Lebesgue integrals of functions of (first reward, next state, shifted trajectory) at a
non-terminal step. -/
lemma lintegral_stepLaw_castSucc (h : Fin H) (s : S)
    {f : (ℝ × S) × (ℕ → Round (LayerState S H) A ℝ) → ENNReal} (hf : Measurable f) :
    ∫⁻ x, f ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x) ∂stepLaw M π (s, h.castSucc)
      = ∫⁻ q, ∫⁻ y, f (q, y) ∂stepLaw M π (q.2, h.succ)
          ∂((M.reward h (s, π h s)).prod (M.trans h (s, π h s))) := by
  rw [(hasLaw_stepLaw_castSucc M π h s).lintegral_comp hf.aemeasurable,
    Measure.lintegral_compProd hf]
  rfl

/-! ### The terminal layer -/

lemma ae_feedback_zero_stepLaw_last (s : S) :
    ∀ᵐ x ∂stepLaw M π (s, Fin.last H), IT.feedback 0 x = 0 := by
  have hl := hasLaw_feedback_zero_stepLaw M π (s, Fin.last H)
  rw [layerReward_last] at hl
  exact hl.ae_eq_of_dirac

lemma ae_obs_one_stepLaw_last (s : S) :
    ∀ᵐ x ∂stepLaw M π (s, Fin.last H), IT.obs 1 x = (s, Fin.last H) := by
  have hl := hasLaw_obs_one_stepLaw M π (s, Fin.last H)
  rw [layerTrans_last] at hl
  exact hl.ae_eq_of_dirac

/-- At the terminal layer, the shifted trajectory has the same law as the trajectory. -/
lemma hasLaw_shiftRound_stepLaw_last (s : S) :
    HasLaw shiftRound (stepLaw M π (s, Fin.last H)) (stepLaw M π (s, Fin.last H)) := by
  set p : LayerState S H := (s, Fin.last H)
  have hgen := hasCondDistrib_shiftRound_trajMeasure (layerMDP M) π.measurable_layer
    (Measure.dirac p)
  have hae : (fun _ ↦ ((p, π.layer p, (0 : ℝ)), p)) =ᵐ[stepLaw M π p] firstRoundState := by
    filter_upwards [ae_obs_zero_stepLaw M π p, ae_action_zero_stepLaw M π p,
      ae_feedback_zero_stepLaw_last M π s, ae_obs_one_stepLaw_last M π s] with x h0 h1 h2 h3
    exact Prod.ext (Prod.ext h0.symm (Prod.ext h1.symm h2.symm)) h3.symm
  exact hasCondDistrib_const_iff.1 (hgen.congr hae (Filter.EventuallyEq.refl _ _))

lemma ae_feedback_eq_zero_stepLaw_last (s : S) :
    ∀ᵐ x ∂stepLaw M π (s, Fin.last H), ∀ k, IT.feedback k x = 0 := by
  rw [ae_all_iff]
  intro k
  induction k with
  | zero => exact ae_feedback_zero_stepLaw_last M π s
  | succ k ih =>
    have hl := hasLaw_shiftRound_stepLaw_last M π s
    refine ae_of_ae_map (p := fun y ↦ IT.feedback k y = 0) hl.aemeasurable ?_
    rwa [hl.map_eq]

lemma ae_episodeReturn_eq_zero_stepLaw_last (s : S) :
    ∀ᵐ x ∂stepLaw M π (s, Fin.last H), episodeReturn H x = 0 := by
  filter_upwards [ae_feedback_eq_zero_stepLaw_last M π s] with x hx
  simp [episodeReturn, hx]

/-! ### Rewards after the terminal layer and the return -/

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A]
  [Nonempty A] in
lemma measurableSet_feedback_eq_zero (i : ℕ) :
    MeasurableSet {z : (ℝ × S) × (ℕ → Round (LayerState S H) A ℝ) |
      ∀ k, H ≤ i + (k + 1) → IT.feedback k z.2 = 0} := by
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun k ↦ MeasurableSet.iInter fun _ ↦
    measurableSet_eq_fun (g := fun _ ↦ (0 : ℝ)) ((IT.measurable_feedback k).comp measurable_snd)
      measurable_const

/-- The rewards of the rounds at the terminal layer vanish almost surely. -/
lemma ae_feedback_eq_zero_stepLaw (h : Fin (H + 1)) (s : S) :
    ∀ᵐ x ∂stepLaw M π (s, h), ∀ k, H ≤ h + k → IT.feedback k x = 0 := by
  induction h using Fin.reverseInduction generalizing s with
  | last => filter_upwards [ae_feedback_eq_zero_stepLaw_last M π s] with x hx k _ using hx k
  | cast i ih =>
    have h0 : ∀ᵐ x ∂stepLaw M π (s, i.castSucc),
        ∀ k, H ≤ i + (k + 1) → IT.feedback k (shiftRound x) = 0 := by
      refine ae_stepLaw_castSucc_of_ae M π
        (P := fun _ _ y ↦ ∀ k, H ≤ i + (k + 1) → IT.feedback k y = 0)
        (measurableSet_feedback_eq_zero i) (Filter.Eventually.of_forall fun _ s' ↦ ?_)
      filter_upwards [ih s'] with y hy k hk
      exact hy k (by rw [Fin.val_succ]; omega)
    filter_upwards [h0] with x hx k hk
    cases k with
    | zero => exact absurd hk (by simp)
    | succ k => exact hx k (by simpa using hk)

omit [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Nonempty A] in
lemma episodeReturn_add_feedback (x : ℕ → Round (LayerState S H) A ℝ) :
    episodeReturn H x + IT.feedback H x = IT.feedback 0 x + episodeReturn H (shiftRound x) := by
  simp only [episodeReturn]
  rw [← Finset.sum_range_succ (fun k ↦ IT.feedback k x), Finset.sum_range_succ', add_comm]
  rfl

/-- The return is the first reward plus the return of the shifted trajectory. -/
lemma ae_episodeReturn_eq_add_shiftRound (h : Fin (H + 1)) (s : S) :
    ∀ᵐ x ∂stepLaw M π (s, h),
      episodeReturn H x = IT.feedback 0 x + episodeReturn H (shiftRound x) := by
  filter_upwards [ae_feedback_eq_zero_stepLaw M π h s] with x hx
  rw [← episodeReturn_add_feedback, hx H (by omega), add_zero]

/-! ### The episode environment -/

section EpisodeEnv

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {alg : Algorithm Unit (Policy S A H) (Traj S H)} {O : ℕ → Ω → Unit} {X : ℕ → Ω → Policy S A H}
  {Y : ℕ → Ω → Traj S H}

omit π

/-- **Law of an episode given the past**: in an interaction with the episode environment of `M`
from `s₁`, the state sequence of the episode `t` has conditional law `statesKernel M s₁` given
the history of the first `t` episodes and the policy of the episode `t`. -/
lemma hasCondDistrib_feedback_history_action_statesEnv (s₁ : S)
    (h : IsAlgEnvSeq O X Y alg (statesEnv M s₁) P) (t : ℕ) :
    HasCondDistrib (Y t) (fun ω ↦ ((history O X Y t ω, O t ω), X t ω))
      ((statesKernel M s₁).prodMkLeft _) P := by
  have h' : IsAlgEnvSeq O X Y alg (stationaryEnv (statesKernel M s₁)) P := h
  have := IsObliviousEnv.hasCondDistrib_feedback_history_action h' t
  rwa [feedbackCondAction_stationaryEnv] at this

/-- In an interaction with the episode environment of `M` from `s₁`, the state sequence of the
episode `t` has conditional law `statesKernel M s₁` given the policy of the episode `t`. -/
lemma hasCondDistrib_feedback_statesEnv (s₁ : S) (h : IsAlgEnvSeq O X Y alg (statesEnv M s₁) P)
    (t : ℕ) : HasCondDistrib (Y t) (X t) (statesKernel M s₁) P :=
  (hasCondDistrib_feedback_history_action_statesEnv M s₁ h t).comp_right

end EpisodeEnv

end Learning.MDP.Episodic
