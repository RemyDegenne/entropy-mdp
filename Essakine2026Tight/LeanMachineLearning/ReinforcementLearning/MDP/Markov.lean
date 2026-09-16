/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Basic
public import Essakine2026Tight.Mathlib.Probability.HasCondDistrib

/-!
# The Markov property of the trajectory law of a stationary policy

For a stationary policy `π` in the MDP `M`, the step kernels of the pair `(policyAlg π, M.env μ₀)`
only depend on the last state-action pair: at round `0` the state has law `μ₀`, and at round
`n + 1` it has law `M.P (s, a)` for the state `s` and action `a` of round `n`; the action is `π s`
and the reward has law `M.R (s, π s)` (`actionRewardKernel`). The trajectory law of `π` from a
state is the kernel `policyKernel M hπ`, and the **Markov property**
(`hasCondDistrib_shift_trajMeasure`) states that, under `trajMeasure (policyAlg π hπ) (M.env μ₀)`,
the trajectory shifted by one round has conditional law `policyKernel M hπ s'` given the first
round and the state `s'` of the second round. Its integral form is
`integral_trajMeasure_eq_integral_policyMeasure`.

The proof is by uniqueness of the trajectory law (`Kernel.hasLaw_trajMeasureFin`): the process
obtained by prepending a round to a trajectory drawn from the policy kernel of the next state
has the same conditional laws as the canonical trajectory. The state space is assumed countable
with measurable singletons, which makes the policy kernel measurable for free; the general case
follows from the measurability of `Kernel.traj` in its initial condition.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning

namespace Learning.MDP

variable {𝓢 𝓐 𝓡 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓡 : MeasurableSpace 𝓡} (M : MDP 𝓢 𝓐 𝓡) {π : 𝓢 → 𝓐} (hπ : Measurable π)

/-! ### The step kernels of a stationary policy in an MDP -/

/-- The action and the reward of a round given the state `s`: the action `π s` and the reward
drawn from `M.R (s, π s)`. -/
noncomputable def actionRewardKernel : Kernel 𝓢 (𝓐 × 𝓡) := Kernel.deterministic π hπ ⊗ₖ M.R

instance : IsMarkovKernel (actionRewardKernel M hπ) := by
  unfold actionRewardKernel; infer_instance

lemma p0_policyAlg : (policyAlg (m𝓡 := m𝓡) π hπ).p0 = Kernel.deterministic π hπ :=
  Kernel.ext fun _ ↦ rfl

lemma ν0_env (μ₀ : Measure 𝓢) [IsProbabilityMeasure μ₀] : (M.env μ₀).ν0 = M.R :=
  Kernel.ext fun _ ↦ rfl

lemma stepKernel_policyAlg_env_zero (μ₀ : Measure 𝓢) [IsProbabilityMeasure μ₀]
    (h : Hist 𝓢 𝓐 𝓡 0) :
    stepKernel (policyAlg π hπ) (M.env μ₀) 0 h = μ₀ ⊗ₘ actionRewardKernel M hπ := by
  rw [stepKernel_zero, p0_policyAlg, ν0_env]
  rfl

lemma stepKernel_policyAlg_env_succ (μ₀ : Measure 𝓢) [IsProbabilityMeasure μ₀] (n : ℕ)
    (h : Hist 𝓢 𝓐 𝓡 (n + 1)) :
    stepKernel (policyAlg π hπ) (M.env μ₀) (n + 1) h
      = M.P (lastObsAction n h) ⊗ₘ actionRewardKernel M hπ := by
  rw [stepKernel_def, Kernel.compProd_apply_eq_compProd_sectR]
  congr 1
  ext s : 1
  rw [Kernel.sectR_apply, Kernel.compProd_apply_eq_compProd_sectR, actionRewardKernel,
    Kernel.compProd_apply_eq_compProd_sectR]
  rfl

/-- The step kernels at rounds `n + 1` do not depend on the initial state distribution. -/
lemma stepKernel_policyAlg_env_succ_eq (μ₀ μ₁ : Measure 𝓢) [IsProbabilityMeasure μ₀]
    [IsProbabilityMeasure μ₁] (n : ℕ) :
    stepKernel (policyAlg π hπ) (M.env μ₀) (n + 1)
      = stepKernel (policyAlg π hπ) (M.env μ₁) (n + 1) :=
  rfl

/-- The law of the first round of the trajectory of `π` from `s`. -/
lemma hasLaw_step_zero_policyMeasure (s : 𝓢) :
    HasLaw (IT.step 0) (Measure.dirac s ⊗ₘ actionRewardKernel M hπ) (M.policyMeasure π hπ s) := by
  have h := IT.hasLaw_step_zero (policyAlg π hπ) (M.env (Measure.dirac s))
  rwa [← stepKernel_zero _ _ default, stepKernel_policyAlg_env_zero] at h

/-! ### Rounds and reconstructed trajectories -/

/-- The state and the action of a round. -/
def roundObsAction (r : Round 𝓢 𝓐 𝓡) : 𝓢 × 𝓐 := (r.obs, r.action)

lemma measurable_roundObsAction :
    Measurable (roundObsAction (𝓢 := 𝓢) (𝓐 := 𝓐) (𝓡 := 𝓡)) :=
  Round.measurable_obs.prodMk Round.measurable_action

/-- The transition kernel of `M` as a kernel from the last round. -/
noncomputable def roundKernel : Kernel (Round 𝓢 𝓐 𝓡) 𝓢 :=
  M.P.comap roundObsAction measurable_roundObsAction

lemma roundKernel_apply (r : Round 𝓢 𝓐 𝓡) : M.roundKernel r = M.P (r.obs, r.action) := rfl

instance : IsMarkovKernel M.roundKernel := by unfold roundKernel; infer_instance

/-- A round as a history of one round. -/
def roundFinOne : Round 𝓢 𝓐 𝓡 ≃ᵐ (Fin 1 → Round 𝓢 𝓐 𝓡) where
  toFun r := fun _ ↦ r
  invFun x := x 0
  left_inv _ := rfl
  right_inv x := funext fun i ↦ by rw [Unique.eq_default i]; rfl
  measurable_toFun := Measurable.of_eval fun _ ↦ measurable_id
  measurable_invFun := measurable_pi_apply 0

/-- The first round and the state of the second round of a trajectory. -/
def firstRoundState (x : ℕ → Round 𝓢 𝓐 𝓡) : Round 𝓢 𝓐 𝓡 × 𝓢 := (x 0, IT.obs 1 x)

lemma measurable_firstRoundState :
    Measurable (firstRoundState (𝓢 := 𝓢) (𝓐 := 𝓐) (𝓡 := 𝓡)) :=
  (measurable_pi_apply 0).prodMk (IT.measurable_obs 1)

/-- The shift of a trajectory by one round. -/
def shiftRound (x : ℕ → Round 𝓢 𝓐 𝓡) (n : ℕ) : Round 𝓢 𝓐 𝓡 := x (n + 1)

lemma measurable_shiftRound : Measurable (shiftRound (𝓢 := 𝓢) (𝓐 := 𝓐) (𝓡 := 𝓡)) :=
  Measurable.of_eval fun _ ↦ measurable_pi_apply _

/-- A trajectory reconstructed from a first round and a trajectory (its shift). -/
def consRound (p : (Round 𝓢 𝓐 𝓡 × 𝓢) × (ℕ → Round 𝓢 𝓐 𝓡)) (n : ℕ) : Round 𝓢 𝓐 𝓡 :=
  Nat.rec p.1.1 (fun m _ ↦ p.2 m) n

lemma measurable_consRound_apply (n : ℕ) :
    Measurable fun p : (Round 𝓢 𝓐 𝓡 × 𝓢) × (ℕ → Round 𝓢 𝓐 𝓡) ↦ consRound p n := by
  cases n with
  | zero => exact measurable_fst.comp measurable_fst
  | succ m => exact (measurable_pi_apply m).comp measurable_snd

lemma measurable_consRound : Measurable (consRound (𝓢 := 𝓢) (𝓐 := 𝓐) (𝓡 := 𝓡)) :=
  measurable_pi_iff.2 measurable_consRound_apply

/-- The first `n + 1` rounds of a reconstructed trajectory. -/
lemma consRound_fin (n : ℕ) :
    (fun (p : (Round 𝓢 𝓐 𝓡 × 𝓢) × (ℕ → Round 𝓢 𝓐 𝓡)) (i : Fin (n + 1)) ↦ consRound p i)
      = (MeasurableEquiv.piFinSuccAbove (fun _ ↦ Round 𝓢 𝓐 𝓡) 0).symm
        ∘ fun p ↦ (p.1.1, fun i : Fin n ↦ p.2 i) := by
  funext p
  simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply]
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp only [Fin.val_zero]
    rfl
  · simp only [Fin.val_succ]
    rfl

lemma consRound_firstRoundState_shiftRound (x : ℕ → Round 𝓢 𝓐 𝓡) :
    consRound (firstRoundState x, shiftRound x) = x := by
  funext n
  cases n with
  | zero => rfl
  | succ m => rfl

/-! ### The policy kernel -/

variable [Countable 𝓢] [MeasurableSingletonClass 𝓢]

lemma measurable_policyMeasure : Measurable (M.policyMeasure π hπ) := measurable_of_countable _

/-- The trajectory law of the policy `π` as a kernel from the initial state. -/
noncomputable def policyKernel : Kernel 𝓢 (ℕ → Round 𝓢 𝓐 𝓡) :=
  ⟨M.policyMeasure π hπ, measurable_policyMeasure M hπ⟩

@[simp] lemma policyKernel_apply (s : 𝓢) : policyKernel M hπ s = M.policyMeasure π hπ s := rfl

instance : IsMarkovKernel (policyKernel M hπ) :=
  ⟨fun s ↦ isProbabilityMeasure_policyMeasure M π hπ s⟩

lemma map_step_zero_policyKernel :
    (policyKernel M hπ).map (IT.step 0)
      = Kernel.id ⊗ₖ Kernel.prodMkLeft 𝓢 (actionRewardKernel M hπ) := by
  ext s : 1
  rw [Kernel.map_apply _ (IT.measurable_step 0), policyKernel_apply,
    (hasLaw_step_zero_policyMeasure M hπ s).map_eq, Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.id_apply, Kernel.sectR_prodMkLeft]

/-! ### The Markov property -/

variable (μ₀ : Measure 𝓢) [IsProbabilityMeasure μ₀]

/-- Auxiliary measure of the proof of the Markov property: the law of the first round and the
state of the second round, followed by an independent trajectory from that state. -/
noncomputable def shiftMeasure : Measure ((Round 𝓢 𝓐 𝓡 × 𝓢) × (ℕ → Round 𝓢 𝓐 𝓡)) :=
  (trajMeasure (policyAlg π hπ) (M.env μ₀)).map firstRoundState
    ⊗ₘ Kernel.prodMkLeft (Round 𝓢 𝓐 𝓡) (policyKernel M hπ)

instance : IsProbabilityMeasure ((trajMeasure (policyAlg π hπ) (M.env μ₀)).map firstRoundState) :=
  ⟨by rw [Measure.map_apply measurable_firstRoundState MeasurableSet.univ, Set.preimage_univ,
    measure_univ]⟩

instance : IsProbabilityMeasure (shiftMeasure M hπ μ₀) := by
  unfold shiftMeasure; infer_instance

lemma hasLaw_fst_shiftMeasure :
    HasLaw Prod.fst ((trajMeasure (policyAlg π hπ) (M.env μ₀)).map firstRoundState)
      (shiftMeasure M hπ μ₀) :=
  ⟨measurable_fst.aemeasurable, Measure.fst_compProd _ _⟩

/-- Round `0` of the reconstructed process: the law of the first round. -/
lemma hasLaw_consRound_zero :
    HasLaw (fun p ↦ consRound p 0) (stepKernel (policyAlg π hπ) (M.env μ₀) 0 default)
      (shiftMeasure M hπ μ₀) := by
  refine ⟨(measurable_consRound_apply 0).aemeasurable, ?_⟩
  calc (shiftMeasure M hπ μ₀).map (fun p ↦ consRound p 0)
      = ((shiftMeasure M hπ μ₀).map Prod.fst).map Prod.fst := by
        rw [Measure.map_map measurable_fst measurable_fst]; rfl
    _ = ((trajMeasure (policyAlg π hπ) (M.env μ₀)).map firstRoundState).map Prod.fst := by
        rw [(hasLaw_fst_shiftMeasure M hπ μ₀).map_eq]
    _ = (trajMeasure (policyAlg π hπ) (M.env μ₀)).map (fun x ↦ x 0) := by
        rw [Measure.map_map measurable_fst measurable_firstRoundState]; rfl
    _ = _ := (Kernel.hasLaw_eval_zero_trajMeasureFin (X := fun _ ↦ Round 𝓢 𝓐 𝓡)
        (κ' := stepKernel (policyAlg π hπ) (M.env μ₀))).map_eq

omit [Countable 𝓢] [MeasurableSingletonClass 𝓢] in
/-- The state of the second round given the first round, under the trajectory law. -/
lemma hasCondDistrib_obs_one_trajMeasure :
    HasCondDistrib (IT.obs 1) (fun x ↦ x 0) M.roundKernel
      (trajMeasure (policyAlg π hπ) (M.env μ₀)) := by
  have h := IT.hasCondDistrib_obs (policyAlg π hπ) (M.env μ₀) 1
  rw [show IT.hist (𝓞 := 𝓢) (𝓐 := 𝓐) (𝓨 := 𝓡) 1 = roundFinOne ∘ fun x ↦ x 0 from by
        funext x i
        rw [Unique.eq_default i]
        rfl,
    hasCondDistrib_measurableEquiv_comp_right_iff] at h
  convert h using 1
  exact Kernel.ext fun _ ↦ rfl

/-- The state of the second round given the first round, under the auxiliary measure. -/
lemma hasCondDistrib_snd_fst_shiftMeasure :
    HasCondDistrib (fun p ↦ p.1.2) (fun p ↦ p.1.1) M.roundKernel (shiftMeasure M hπ μ₀) := by
  refine HasCondDistrib.comp_hasLaw (hasLaw_fst_shiftMeasure M hπ μ₀) measurable_fst
    measurable_snd ?_
  refine ⟨by fun_prop, ?_⟩
  rw [show (fun q : Round 𝓢 𝓐 𝓡 × 𝓢 ↦ (q.1, q.2)) = id from rfl, Measure.map_id,
    Measure.map_map measurable_fst measurable_firstRoundState]
  exact (hasCondDistrib_obs_one_trajMeasure M hπ μ₀).map_eq

/-- The first round of the trajectory part of the auxiliary measure, given the pair. -/
lemma hasCondDistrib_snd_zero_shiftMeasure :
    HasCondDistrib (fun p ↦ p.2 0) Prod.fst
      (Kernel.prodMkLeft (Round 𝓢 𝓐 𝓡) (Kernel.id ×ₖ actionRewardKernel M hπ))
      (shiftMeasure M hπ μ₀) := by
  have h : HasCondDistrib (fun p ↦ p.2 0) Prod.fst
      ((Kernel.prodMkLeft (Round 𝓢 𝓐 𝓡) (policyKernel M hπ)).map (IT.step 0))
      (shiftMeasure M hπ μ₀) :=
    (hasCondDistrib_snd_compProd ((trajMeasure (policyAlg π hπ) (M.env μ₀)).map
      firstRoundState) (Kernel.prodMkLeft (Round 𝓢 𝓐 𝓡) (policyKernel M hπ))).comp_left
      (IT.measurable_step 0)
  convert h using 1
  ext q : 1
  rw [Kernel.map_apply _ (IT.measurable_step 0), Kernel.prodMkLeft_apply, Kernel.prodMkLeft_apply,
    ← Kernel.map_apply _ (IT.measurable_step 0), map_step_zero_policyKernel,
    Kernel.compProd_prodMkLeft_eq_comp, Kernel.comp_id]

/-- Round `1` of the reconstructed process. -/
lemma hasCondDistrib_consRound_one :
    HasCondDistrib (fun p ↦ p.2 0) (fun p (i : Fin 1) ↦ consRound p i)
      (stepKernel (policyAlg π hπ) (M.env μ₀) 1) (shiftMeasure M hπ μ₀) := by
  rw [consRound_fin 0]
  refine HasCondDistrib.comp_right (hf := (MeasurableEquiv.piFinSuccAbove _ 0).symm.measurable) ?_
  rw [hasCondDistrib_prodMk_right_unique_iff]
  have hpair : HasCondDistrib (fun p ↦ p.2 0) (fun p ↦ p.1.1)
      ((M.roundKernel ⊗ₖ
        Kernel.prodMkLeft (Round 𝓢 𝓐 𝓡) (Kernel.id ×ₖ actionRewardKernel M hπ)).snd)
      (shiftMeasure M hπ μ₀) :=
    ((hasCondDistrib_snd_fst_shiftMeasure M hπ μ₀).prod
      (hasCondDistrib_snd_zero_shiftMeasure M hπ μ₀)).snd
  convert hpair using 1
  rw [Kernel.snd_compProd_prodMkLeft, ← Kernel.compProd_prodMkLeft_eq_comp]
  ext r : 1
  rw [Kernel.compProd_apply_eq_compProd_sectR, Kernel.sectR_prodMkLeft, Kernel.sectL_apply,
    Kernel.comap_apply, stepKernel_policyAlg_env_succ, roundKernel_apply]
  congr 2

/-- Rounds `m + 2` of the reconstructed process. -/
lemma hasCondDistrib_consRound_succ_succ (m : ℕ) :
    HasCondDistrib (fun p ↦ p.2 (m + 1)) (fun p (i : Fin (m + 2)) ↦ consRound p i)
      (stepKernel (policyAlg π hπ) (M.env μ₀) (m + 2)) (shiftMeasure M hπ μ₀) := by
  rw [consRound_fin (m + 1)]
  refine HasCondDistrib.comp_right (hf := (MeasurableEquiv.piFinSuccAbove _ 0).symm.measurable) ?_
  have hcp : HasCondDistrib (fun p ↦ p.2 (m + 1))
      (fun p ↦ (p.1, fun i : Fin (m + 1) ↦ p.2 i))
      (Kernel.prodMkLeft (Round 𝓢 𝓐 𝓡 × 𝓢) (stepKernel (policyAlg π hπ) (M.env μ₀) (m + 1)))
      (shiftMeasure M hπ μ₀) := by
    refine HasCondDistrib.compProd_left (Measurable.of_eval fun i ↦ measurable_pi_apply _)
      (measurable_pi_apply _) fun q ↦ ?_
    rw [Kernel.prodMkLeft_apply, policyKernel_apply]
    exact Kernel.hasCondDistrib_trajMeasureFin (X := fun _ ↦ Round 𝓢 𝓐 𝓡)
      (κ' := stepKernel (policyAlg π hπ) (M.env (Measure.dirac q.2))) (m + 1)
  rw [show (fun p : (Round 𝓢 𝓐 𝓡 × 𝓢) × (ℕ → Round 𝓢 𝓐 𝓡) ↦
      (p.1.1, fun i : Fin (m + 1) ↦ p.2 i))
      = (fun q : (Round 𝓢 𝓐 𝓡 × 𝓢) × (Fin (m + 1) → Round 𝓢 𝓐 𝓡) ↦ (q.1.1, q.2))
        ∘ fun p ↦ (p.1, fun i : Fin (m + 1) ↦ p.2 i) from rfl]
  refine HasCondDistrib.comp_right (hf := by fun_prop) ?_
  convert hcp using 1
  ext q : 1
  rw [Kernel.comap_apply, Kernel.comap_apply, Kernel.prodMkLeft_apply,
    stepKernel_policyAlg_env_succ, stepKernel_policyAlg_env_succ]
  congr 2

/-- The reconstructed process has the trajectory law. -/
lemma map_consRound_shiftMeasure :
    (shiftMeasure M hπ μ₀).map consRound = trajMeasure (policyAlg π hπ) (M.env μ₀) := by
  have hlaw : HasLaw (fun p n ↦ consRound p n)
      (Kernel.trajMeasureFin (stepKernel (policyAlg π hπ) (M.env μ₀))) (shiftMeasure M hπ μ₀) := by
    refine Kernel.hasLaw_trajMeasureFin (X := fun _ ↦ Round 𝓢 𝓐 𝓡) measurable_consRound_apply
      fun n ↦ ?_
    rcases n with _ | _ | m
    · rw [show (fun (p : (Round 𝓢 𝓐 𝓡 × 𝓢) × (ℕ → Round 𝓢 𝓐 𝓡)) (i : Fin 0) ↦ consRound p i)
          = fun _ ↦ (default : Hist 𝓢 𝓐 𝓡 0) from funext fun _ ↦ Unique.eq_default _,
        hasCondDistrib_const_iff]
      exact hasLaw_consRound_zero M hπ μ₀
    · exact hasCondDistrib_consRound_one M hπ μ₀
    · exact hasCondDistrib_consRound_succ_succ M hπ μ₀ m
  exact hlaw.map_eq

/-- Almost surely under the auxiliary measure, the trajectory part starts from the given state. -/
lemma ae_obs_zero_shiftMeasure :
    ∀ᵐ p ∂(shiftMeasure M hπ μ₀), (p.2 0).obs = p.1.2 := by
  rw [shiftMeasure, Measure.ae_compProd_iff (measurableSet_eq_fun
    (f := fun p : (Round 𝓢 𝓐 𝓡 × 𝓢) × (ℕ → Round 𝓢 𝓐 𝓡) ↦ (p.2 0).obs) (g := fun p ↦ p.1.2)
    (by fun_prop) (by fun_prop))]
  refine Filter.Eventually.of_forall fun q ↦ ?_
  rw [Kernel.prodMkLeft_apply, policyKernel_apply]
  have h0 : HasLaw (IT.obs 0) (Measure.dirac q.2) (M.policyMeasure π hπ q.2) :=
    IT.hasLaw_obs_zero (policyAlg π hπ) (M.env (Measure.dirac q.2))
  filter_upwards [h0.ae_eq_of_dirac] with x hx
  exact hx

/-- **Markov property** of the trajectory law of a stationary policy: under
`trajMeasure (policyAlg π hπ) (M.env μ₀)`, the trajectory shifted by one round has conditional
law `M.policyMeasure π hπ s'` given the first round and the state `s'` of the second round. -/
lemma hasCondDistrib_shiftRound_trajMeasure :
    HasCondDistrib shiftRound firstRoundState
      (Kernel.prodMkLeft (Round 𝓢 𝓐 𝓡) (policyKernel M hπ))
      (trajMeasure (policyAlg π hπ) (M.env μ₀)) := by
  refine ⟨(measurable_firstRoundState.prodMk measurable_shiftRound).aemeasurable, ?_⟩
  have hae : ∀ᵐ p ∂(shiftMeasure M hπ μ₀),
      (firstRoundState (consRound p), shiftRound (consRound p)) = p := by
    filter_upwards [ae_obs_zero_shiftMeasure M hπ μ₀] with p hp
    exact Prod.ext (Prod.ext rfl hp) (funext fun _ ↦ rfl)
  calc (trajMeasure (policyAlg π hπ) (M.env μ₀)).map (fun x ↦ (firstRoundState x, shiftRound x))
      = ((shiftMeasure M hπ μ₀).map consRound).map
          (fun x ↦ (firstRoundState x, shiftRound x)) := by
        rw [map_consRound_shiftMeasure]
    _ = (shiftMeasure M hπ μ₀).map
          (fun p ↦ (firstRoundState (consRound p), shiftRound (consRound p))) :=
        Measure.map_map (measurable_firstRoundState.prodMk measurable_shiftRound)
          measurable_consRound
    _ = (shiftMeasure M hπ μ₀).map id := Measure.map_congr hae
    _ = shiftMeasure M hπ μ₀ := Measure.map_id
    _ = _ := by rw [shiftMeasure]

end Learning.MDP
