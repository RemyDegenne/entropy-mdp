/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Episodic
public import Essakine2026Tight.Mathlib.Probability.CondDistrib
public import Essakine2026Tight.Mathlib.Probability.HasCondDistribIntegral

/-!
# Trajectory laws of a finite-horizon MDP: the Markov property

For a finite-horizon MDP `M`, a policy `π : ℕ → S → A` measurable at every step
(`hπ : ∀ h, Measurable (π h)`) and the trajectory law `stepLaw M π (s, h)` from the state `s` at
the step `h` (`MDP/Episodic.lean`), the round `k` of the trajectory is the paper's step `h + k`.

* **The first round**: its state is `(s, h)` (`ae_obs_zero_stepLaw`), its action `π h s`
  (`ae_action_zero_stepLaw`), its reward has law `M.reward h (s, π h s)`
  (`hasLaw_feedback_zero_stepLaw`) and the next state has law `M.trans h (s, π h s)`
  (`hasLaw_fst_obs_one_stepLaw`).
* **One-step Markov property** (`hasLaw_stepLaw_succ`): the reward of the first round, the
  state of the second round and the trajectory shifted by one round have the law
  `R_h(· | s, π_h(s)) ⊗ p_h(· | s, π_h(s)) ⊗ stepLaw M π (·, h + 1)`; consequences
  `ae_stepLaw_succ_of_ae`, `lintegral_stepLaw_succ`, `integral_stepLaw_succ`.
* **Iterated Markov property** (`hasCondDistrib_shiftRounds_stepLaw`): the trajectory shifted by
  `k` rounds has conditional law `stepLaw M π (s', h + k)` given the first `k` rounds and the
  state `s'` of the round `k`; consequences for the round `k` (`ae_obs_eq_stepLaw`,
  `ae_action_eq_stepLaw`, `ae_feedback_eq_stepLaw`), for the reward of the round `k` and the
  state of the round `k + 1` (`hasCondDistrib_feedback_obs_succ_stepLaw`,
  `hasCondDistrib_obs_succ_hist_stepLaw`, `integral_mul_obs_succ_stepLaw`).
* **Episodes**: under the law of the state sequence of an episode, the state of the step `h + 1`
  has conditional law `p_h(· | s_h, π_h(s_h))` given `s_0, …, s_h` (`hasCondDistrib_statesLaw`);
  in the episode environment `statesEnv`, the state sequence of an episode has conditional law
  `statesKernel` given the past (`hasCondDistrib_feedback_history_action_statesEnv`,
  `hasCondDistrib_feedback_statesEnv`) and the state of the step `h + 1` of an episode has
  conditional law `p_h(· | s_h, π_h(s_h))` given the past and `s_0, …, s_h`
  (`hasCondDistrib_feedback_succ_statesEnv`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP
open scoped ENNReal

namespace Learning.MDP.Episodic

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : EpisodicMDP S A)
  {π : ℕ → S → A} (hπ : ∀ h, Measurable (π h))

include hπ

lemma stepLaw_eq_trajMeasure (p : S × ℕ) :
    stepLaw M π p = trajMeasure (policyAlg (augPolicy π) (measurable_augPolicy hπ))
      (M.augmented.env (Measure.dirac p)) :=
  stepLaw_of_measurable M hπ p

lemma policyKernel_augmented_apply (p : S × ℕ) :
    policyKernel M.augmented (measurable_augPolicy hπ) p = stepLaw M π p := by
  rw [policyKernel_apply, stepLaw_of_measurable M hπ]

omit hπ in
lemma augTrans_apply' (s : S) (h : ℕ) (a : A) :
    M.augTrans ((s, h), a) = (M.trans h (s, a)).map fun s' ↦ (s', h + 1) := rfl

omit hπ in
lemma augReward_apply' (s : S) (h : ℕ) (a : A) : M.augReward ((s, h), a) = M.reward h (s, a) := rfl

/-! ### The first round -/

lemma hasLaw_obs_zero_stepLaw (p : S × ℕ) :
    HasLaw (IT.obs 0) (Measure.dirac p) (stepLaw M π p) := by
  rw [stepLaw_eq_trajMeasure M hπ]
  exact IT.hasLaw_obs_zero (policyAlg (augPolicy π) (measurable_augPolicy hπ))
    (M.augmented.env (Measure.dirac p))

variable [MeasurableSingletonClass S] [MeasurableSingletonClass A]

omit [MeasurableSingletonClass A] in
lemma ae_obs_zero_stepLaw (p : S × ℕ) : ∀ᵐ x ∂stepLaw M π p, IT.obs 0 x = p :=
  (hasLaw_obs_zero_stepLaw M hπ p).ae_eq_of_dirac

omit [MeasurableSingletonClass A] in
/-- The action of the first round is `π h s`. -/
lemma hasLaw_action_zero_stepLaw (s : S) (h : ℕ) :
    HasLaw (IT.action 0) (Measure.dirac (π h s)) (stepLaw M π (s, h)) := by
  have := isProbabilityMeasure_stepLaw M hπ (s, h)
  have h' := IT.hasCondDistrib_action_zero (policyAlg (augPolicy π) (measurable_augPolicy hπ))
    (M.augmented.env (Measure.dirac (s, h)))
  rw [p0_policyAlg, ← stepLaw_eq_trajMeasure M hπ] at h'
  have hae : (fun _ ↦ ((s, h) : S × ℕ)) =ᵐ[stepLaw M π (s, h)] IT.obs 0 :=
    (ae_obs_zero_stepLaw M hπ (s, h)).mono fun x hx ↦ hx.symm
  have h'' := hasCondDistrib_const_iff.1 (h'.congr hae (Filter.EventuallyEq.refl _ _))
  rwa [Kernel.deterministic_apply] at h''

lemma ae_action_zero_stepLaw (s : S) (h : ℕ) :
    ∀ᵐ x ∂stepLaw M π (s, h), IT.action 0 x = π h s :=
  (hasLaw_action_zero_stepLaw M hπ s h).ae_eq_of_dirac

lemma hasLaw_feedback_zero_stepLaw (s : S) (h : ℕ) :
    HasLaw (IT.feedback 0) (M.reward h (s, π h s)) (stepLaw M π (s, h)) := by
  have := isProbabilityMeasure_stepLaw M hπ (s, h)
  have h' := IT.hasCondDistrib_feedback_zero (policyAlg (augPolicy π) (measurable_augPolicy hπ))
    (M.augmented.env (Measure.dirac (s, h)))
  rw [← stepLaw_eq_trajMeasure M hπ] at h'
  have hae : (fun _ ↦ ((s, h), π h s)) =ᵐ[stepLaw M π (s, h)]
      fun x ↦ (IT.obs 0 x, IT.action 0 x) := by
    filter_upwards [ae_obs_zero_stepLaw M hπ (s, h), ae_action_zero_stepLaw M hπ s h] with x h0 h1
    rw [h0, h1]
  have h'' := hasCondDistrib_const_iff.1 (h'.congr hae (Filter.EventuallyEq.refl _ _))
  rwa [ν0_env] at h''

lemma hasCondDistrib_obs_one_feedback_zero_stepLaw (s : S) (h : ℕ) :
    HasCondDistrib (IT.obs 1) (IT.feedback 0)
      (Kernel.const ℝ ((M.trans h (s, π h s)).map fun s' ↦ (s', h + 1))) (stepLaw M π (s, h)) := by
  have h' := hasCondDistrib_obs_one_trajMeasure M.augmented (measurable_augPolicy hπ)
    (Measure.dirac (s, h))
  rw [← stepLaw_eq_trajMeasure M hπ] at h'
  have hψ : MeasurableEmbedding fun r : ℝ ↦ (((s, h), π h s, r) : Round (S × ℕ) A ℝ) :=
    (measurableEmbedding_prodMk_left (s, h)).comp (measurableEmbedding_prodMk_left (π h s))
  have hae : (fun r : ℝ ↦ (((s, h), π h s, r) : Round (S × ℕ) A ℝ)) ∘ IT.feedback 0
      =ᵐ[stepLaw M π (s, h)] fun x ↦ x 0 := by
    filter_upwards [ae_obs_zero_stepLaw M hπ (s, h), ae_action_zero_stepLaw M hπ s h] with x h0 h1
    exact Prod.ext h0.symm (Prod.ext h1.symm rfl)
  have h3 := (h'.congr hae (Filter.EventuallyEq.refl _ _)).of_measurableEmbedding_comp_right hψ
  convert h3 using 1
  exact Kernel.ext fun _ ↦ rfl

lemma hasLaw_obs_one_stepLaw (s : S) (h : ℕ) :
    HasLaw (IT.obs 1) ((M.trans h (s, π h s)).map fun s' ↦ (s', h + 1)) (stepLaw M π (s, h)) := by
  have := isProbabilityMeasure_stepLaw M hπ (s, h)
  exact (hasCondDistrib_obs_one_feedback_zero_stepLaw M hπ s h).hasLaw_of_const

/-- The state of the second round has law `p_h(· | s, π_h(s))`. -/
lemma hasLaw_fst_obs_one_stepLaw (s : S) (h : ℕ) :
    HasLaw (fun x ↦ (IT.obs 1 x).1) (M.trans h (s, π h s)) (stepLaw M π (s, h)) := by
  refine ⟨(measurable_fst.comp (IT.measurable_obs 1)).aemeasurable, ?_⟩
  calc (stepLaw M π (s, h)).map (fun x ↦ (IT.obs 1 x).1)
      = ((stepLaw M π (s, h)).map (IT.obs 1)).map Prod.fst :=
        (Measure.map_map measurable_fst (IT.measurable_obs 1)).symm
    _ = ((M.trans h (s, π h s)).map (fun s' ↦ (s', h + 1))).map Prod.fst := by
        rw [(hasLaw_obs_one_stepLaw M hπ s h).map_eq]
    _ = M.trans h (s, π h s) := by
        rw [Measure.map_map measurable_fst measurable_prodMk_right]; exact Measure.map_id

/-- The step of the second round is `h + 1`. -/
lemma ae_obs_one_snd_stepLaw (s : S) (h : ℕ) :
    ∀ᵐ x ∂stepLaw M π (s, h), (IT.obs 1 x).2 = h + 1 := by
  have hl := hasLaw_obs_one_stepLaw M hπ s h
  refine ae_of_ae_map (p := fun q : S × ℕ ↦ q.2 = h + 1) hl.aemeasurable ?_
  rw [hl.map_eq, ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) measurable_const)]
  exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- The first round is `((s, h), π h s, R_0)`. -/
lemma ae_round_zero_stepLaw (s : S) (h : ℕ) :
    ∀ᵐ x ∂stepLaw M π (s, h), x 0 = ((s, h), π h s, IT.feedback 0 x) := by
  filter_upwards [ae_obs_zero_stepLaw M hπ (s, h), ae_action_zero_stepLaw M hπ s h] with x h0 h1
  exact Prod.ext h0 (Prod.ext h1 rfl)

/-! ### The one-step Markov property -/

/-- The reward of the first round and the state of the second round are independent, with laws
`R_h(· | s, π_h(s))` and `p_h(· | s, π_h(s))`. -/
lemma hasLaw_feedback_zero_fst_obs_one_stepLaw (s : S) (h : ℕ) :
    HasLaw (fun x ↦ (IT.feedback 0 x, (IT.obs 1 x).1))
      ((M.reward h (s, π h s)).prod (M.trans h (s, π h s))) (stepLaw M π (s, h)) := by
  have ho : HasCondDistrib (fun x ↦ (IT.obs 1 x).1) (IT.feedback 0)
      (Kernel.const ℝ (M.trans h (s, π h s))) (stepLaw M π (s, h)) := by
    have := (hasCondDistrib_obs_one_feedback_zero_stepLaw M hπ s h).comp_left (f := Prod.fst)
      measurable_fst
    have hk : (Kernel.const ℝ ((M.trans h (s, π h s)).map fun s' ↦ (s', h + 1))).map Prod.fst
        = Kernel.const ℝ (M.trans h (s, π h s)) := by
      ext r : 1
      rw [Kernel.map_apply _ measurable_fst, Kernel.const_apply, Kernel.const_apply,
        Measure.map_map measurable_fst measurable_prodMk_right]
      exact Measure.map_id
    rwa [hk] at this
  have := (hasLaw_feedback_zero_stepLaw M hπ s h).prod_of_hasCondDistrib ho
  rwa [Measure.compProd_const] at this

/-- **One-step Markov property**: under `stepLaw M π (s, h)`, the reward of the first round,
the state of the second round and the trajectory shifted by one round have the law
`R_h(· | s, π_h(s)) ⊗ p_h(· | s, π_h(s)) ⊗ stepLaw M π (·, h + 1)`. -/
lemma hasLaw_stepLaw_succ (s : S) (h : ℕ) :
    HasLaw (fun x ↦ ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x))
      ((M.reward h (s, π h s)).prod (M.trans h (s, π h s))
        ⊗ₘ Kernel.prodMkLeft ℝ (stepLawKernel M π (h + 1)))
      (stepLaw M π (s, h)) := by
  have hgen := hasCondDistrib_shiftRound_trajMeasure M.augmented (measurable_augPolicy hπ)
    (Measure.dirac (s, h))
  rw [← stepLaw_eq_trajMeasure M hπ] at hgen
  set φ : ℝ × S → Round (S × ℕ) A ℝ × (S × ℕ) :=
    fun q ↦ (((s, h), π h s, q.1), (q.2, h + 1)) with hφ_def
  have hφ : MeasurableEmbedding φ :=
    ((measurableEmbedding_prodMk_left (s, h)).comp
      (measurableEmbedding_prodMk_left (π h s))).prodMap (measurableEmbedding_prod_mk_right (h + 1))
  have hae : φ ∘ (fun x ↦ (IT.feedback 0 x, (IT.obs 1 x).1))
      =ᵐ[stepLaw M π (s, h)] firstRoundState := by
    filter_upwards [ae_obs_zero_stepLaw M hπ (s, h), ae_action_zero_stepLaw M hπ s h,
      ae_obs_one_snd_stepLaw M hπ s h] with x h0 h1 h2
    exact Prod.ext (Prod.ext h0.symm (Prod.ext h1.symm rfl)) (Prod.ext rfl h2.symm)
  have hC := (hgen.congr hae (Filter.EventuallyEq.refl _ _)).of_measurableEmbedding_comp_right hφ
  have hK : (Kernel.prodMkLeft (Round (S × ℕ) A ℝ)
        (policyKernel M.augmented (measurable_augPolicy hπ))).comap φ hφ.measurable
      = Kernel.prodMkLeft ℝ (stepLawKernel M π (h + 1)) := by
    ext q : 1
    rw [Kernel.comap_apply, Kernel.prodMkLeft_apply, Kernel.prodMkLeft_apply, stepLawKernel_apply,
      policyKernel_augmented_apply M hπ]
  rw [hK] at hC
  exact (hasLaw_feedback_zero_fst_obs_one_stepLaw M hπ s h).prod_of_hasCondDistrib hC

/-- Almost sure properties of (first reward, next state, shifted trajectory). -/
lemma ae_stepLaw_succ_of_ae {s : S} {h : ℕ} {P : ℝ → S → (ℕ → Round (S × ℕ) A ℝ) → Prop}
    (hP : MeasurableSet {z : (ℝ × S) × (ℕ → Round (S × ℕ) A ℝ) | P z.1.1 z.1.2 z.2})
    (hae : ∀ᵐ r ∂M.reward h (s, π h s), ∀ s', ∀ᵐ y ∂stepLaw M π (s', h + 1), P r s' y) :
    ∀ᵐ x ∂stepLaw M π (s, h), P (IT.feedback 0 x) (IT.obs 1 x).1 (shiftRound x) := by
  have hlaw := hasLaw_stepLaw_succ M hπ s h
  refine ae_of_ae_map (p := fun z : (ℝ × S) × (ℕ → Round (S × ℕ) A ℝ) ↦
    P z.1.1 z.1.2 z.2) hlaw.aemeasurable ?_
  rw [hlaw.map_eq]
  refine Measure.ae_compProd_of_ae_ae (p := fun z : (ℝ × S) × (ℕ → Round (S × ℕ) A ℝ) ↦
    P z.1.1 z.1.2 z.2) hP ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hae] with q hq
  rw [Kernel.prodMkLeft_apply, stepLawKernel_apply]
  exact hq q.2

/-- Lebesgue integrals of functions of (first reward, next state, shifted trajectory). -/
lemma lintegral_stepLaw_succ (s : S) (h : ℕ)
    {f : (ℝ × S) × (ℕ → Round (S × ℕ) A ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x) ∂stepLaw M π (s, h)
      = ∫⁻ q, ∫⁻ y, f (q, y) ∂stepLaw M π (q.2, h + 1)
          ∂((M.reward h (s, π h s)).prod (M.trans h (s, π h s))) := by
  rw [(hasLaw_stepLaw_succ M hπ s h).lintegral_comp hf.aemeasurable, Measure.lintegral_compProd hf]
  simp only [Kernel.prodMkLeft_apply, stepLawKernel_apply]

/-- Bochner integrals of functions of (first reward, next state, shifted trajectory). -/
lemma integral_stepLaw_succ (s : S) (h : ℕ) {f : (ℝ × S) × (ℕ → Round (S × ℕ) A ℝ) → ℝ}
    (hf : Integrable f ((M.reward h (s, π h s)).prod (M.trans h (s, π h s))
      ⊗ₘ Kernel.prodMkLeft ℝ (stepLawKernel M π (h + 1)))) :
    ∫ x, f ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x) ∂stepLaw M π (s, h)
      = ∫ q, ∫ y, f (q, y) ∂stepLaw M π (q.2, h + 1)
          ∂((M.reward h (s, π h s)).prod (M.trans h (s, π h s))) := by
  have h1 := (hasLaw_stepLaw_succ M hπ s h).integral_comp hf.aestronglyMeasurable
  simp only [Function.comp_apply] at h1
  rw [h1, Measure.integral_compProd hf]
  simp only [Kernel.prodMkLeft_apply, stepLawKernel_apply]

/-! ### The iterated Markov property -/

/-- **Iterated Markov property**, Lebesgue integral form: integrating a function of (the first
`k` rounds, the state `S_k` of the round `k`, the trajectory shifted by `k` rounds) amounts to
integrating the shifted trajectory against `stepLaw M π (S_k, h + k)`. -/
lemma lintegral_stepLaw_hist_shiftRounds (k : ℕ) :
    ∀ (s : S) (h : ℕ) (f : Hist (S × ℕ) A ℝ k × S × (ℕ → Round (S × ℕ) A ℝ) → ℝ≥0∞),
      Measurable f →
    ∫⁻ x, f (IT.hist k x, (IT.obs k x).1, shiftRounds k x) ∂stepLaw M π (s, h)
      = ∫⁻ x, ∫⁻ y, f (IT.hist k x, (IT.obs k x).1, y) ∂stepLaw M π ((IT.obs k x).1, h + k)
          ∂stepLaw M π (s, h) := by
  induction k with
  | zero =>
    intro s h f hf
    simp only [Nat.add_zero]
    have hae : ∀ᵐ x ∂stepLaw M π (s, h), (IT.obs 0 x).1 = s := by
      filter_upwards [ae_obs_zero_stepLaw M hπ (s, h)] with x hx
      rw [hx]
    calc ∫⁻ x, f (IT.hist 0 x, (IT.obs 0 x).1, shiftRounds 0 x) ∂stepLaw M π (s, h)
        = ∫⁻ x, f (default, s, x) ∂stepLaw M π (s, h) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with x hx
          rw [hx, Unique.eq_default (IT.hist 0 x), shiftRounds_zero]
      _ = ∫⁻ x, ∫⁻ y, f (default, s, y) ∂stepLaw M π (s, h) ∂stepLaw M π (s, h) := by
          rw [lintegral_const, stepLaw_univ M hπ, mul_one]
      _ = _ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with x hx
          rw [hx, Unique.eq_default (IT.hist 0 x)]
  | succ k ih =>
    intro s h f hf
    set r0 : ℝ → Round (S × ℕ) A ℝ := fun r ↦ ((s, h), π h s, r) with hr0
    have hr0m : Measurable r0 := by fun_prop
    have hae : ∀ᵐ x ∂stepLaw M π (s, h), IT.hist (k + 1) x
        = Fin.cons (r0 (IT.feedback 0 x)) (IT.hist k (shiftRound x)) := by
      filter_upwards [ae_round_zero_stepLaw M hπ s h] with x hx
      rw [hist_succ_eq_cons, hx]
    -- the integrand of the right-hand side
    set G : Hist (S × ℕ) A ℝ (k + 1) × S → ℝ≥0∞ :=
      fun p ↦ ∫⁻ z, f (p.1, p.2, z) ∂stepLawKernel M π (h + (k + 1)) p.2 with hG
    have hGm : Measurable G :=
      Measurable.lintegral_kernel_prod_right'
        (κ := Kernel.prodMkLeft (Hist (S × ℕ) A ℝ (k + 1)) (stepLawKernel M π (h + (k + 1))))
        (f := fun q ↦ f (q.1.1, q.1.2, q.2)) (by fun_prop)
    have hGeq : ∀ p : Hist (S × ℕ) A ℝ (k + 1) × S,
        G p = ∫⁻ z, f (p.1, p.2, z) ∂stepLaw M π (p.2, h + (k + 1)) := fun p ↦ by
      simp only [hG, stepLawKernel_apply]
    have hcons : Measurable fun q : (ℝ × S) × (ℕ → Round (S × ℕ) A ℝ) ↦
        (Fin.cons (r0 q.1.1) (IT.hist k q.2) : Hist (S × ℕ) A ℝ (k + 1)) :=
      measurable_finCons.comp ((hr0m.comp measurable_fst.fst).prodMk
        ((IT.measurable_hist k).comp measurable_snd))
    have hcons' (r : ℝ) : Measurable fun p : Hist (S × ℕ) A ℝ k ↦
        (Fin.cons (r0 r) p : Hist (S × ℕ) A ℝ (k + 1)) :=
      measurable_finCons.comp (measurable_const.prodMk measurable_id)
    have hk1 : h + 1 + k = h + (k + 1) := by omega
    calc ∫⁻ x, f (IT.hist (k + 1) x, (IT.obs (k + 1) x).1, shiftRounds (k + 1) x)
          ∂stepLaw M π (s, h)
        = ∫⁻ x, (fun q : (ℝ × S) × (ℕ → Round (S × ℕ) A ℝ) ↦
            f (Fin.cons (r0 q.1.1) (IT.hist k q.2), (IT.obs k q.2).1, shiftRounds k q.2))
            ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x) ∂stepLaw M π (s, h) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with x hx
          simp only [hx]
          rfl
      _ = ∫⁻ q, ∫⁻ y, f (Fin.cons (r0 q.1) (IT.hist k y), (IT.obs k y).1, shiftRounds k y)
            ∂stepLaw M π (q.2, h + 1) ∂((M.reward h (s, π h s)).prod (M.trans h (s, π h s))) :=
          lintegral_stepLaw_succ M hπ s h (hf.comp (hcons.prodMk
            ((measurable_fst.comp ((IT.measurable_obs k).comp measurable_snd)).prodMk
              ((measurable_shiftRounds k).comp measurable_snd))))
      _ = ∫⁻ q, ∫⁻ y, G (Fin.cons (r0 q.1) (IT.hist k y), (IT.obs k y).1)
            ∂stepLaw M π (q.2, h + 1) ∂((M.reward h (s, π h s)).prod (M.trans h (s, π h s))) := by
          refine lintegral_congr fun q ↦ ?_
          rw [ih q.2 (h + 1) (fun p ↦ f (Fin.cons (r0 q.1) p.1, p.2.1, p.2.2))
            (hf.comp (((hcons' q.1).comp measurable_fst).prodMk measurable_snd)), hk1]
          simp only [hGeq]
      _ = ∫⁻ x, (fun q : (ℝ × S) × (ℕ → Round (S × ℕ) A ℝ) ↦
            G (Fin.cons (r0 q.1.1) (IT.hist k q.2), (IT.obs k q.2).1))
            ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x) ∂stepLaw M π (s, h) :=
          (lintegral_stepLaw_succ M hπ s h (hGm.comp (hcons.prodMk
            (measurable_fst.comp ((IT.measurable_obs k).comp measurable_snd))))).symm
      _ = _ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with x hx
          simp only [hx, hGeq]
          rfl

/-- **Iterated Markov property**: under `stepLaw M π (s, h)`, the trajectory shifted by `k`
rounds has conditional law `stepLaw M π (s', h + k)` given the first `k` rounds and the state
`s'` of the round `k`. -/
lemma hasCondDistrib_shiftRounds_stepLaw (s : S) (h k : ℕ) :
    HasCondDistrib (shiftRounds k) (fun x ↦ (IT.hist k x, (IT.obs k x).1))
      (Kernel.prodMkLeft (Hist (S × ℕ) A ℝ k) (stepLawKernel M π (h + k)))
      (stepLaw M π (s, h)) := by
  refine hasCondDistrib_of_lintegral_eq (by fun_prop) (by fun_prop) fun f hf ↦ ?_
  simp only [Kernel.prodMkLeft_apply, stepLawKernel_apply]
  exact lintegral_stepLaw_hist_shiftRounds M hπ k s h (fun q ↦ f ((q.1, q.2.1), q.2.2))
    (by fun_prop)

/-- Almost sure properties of the rounds from `k` on, given the first `k` rounds. -/
lemma ae_stepLaw_of_ae_shiftRounds (s : S) (h k : ℕ)
    {P : Hist (S × ℕ) A ℝ k → S → (ℕ → Round (S × ℕ) A ℝ) → Prop}
    (hP : MeasurableSet {z : (Hist (S × ℕ) A ℝ k × S) × (ℕ → Round (S × ℕ) A ℝ) |
      P z.1.1 z.1.2 z.2})
    (hae : ∀ p s', ∀ᵐ y ∂stepLaw M π (s', h + k), P p s' y) :
    ∀ᵐ x ∂stepLaw M π (s, h), P (IT.hist k x) (IT.obs k x).1 (shiftRounds k x) := by
  have hlaw := hasCondDistrib_shiftRounds_stepLaw M hπ s h k
  refine ae_of_ae_map (p := fun z : (Hist (S × ℕ) A ℝ k × S) × (ℕ → Round (S × ℕ) A ℝ) ↦
    P z.1.1 z.1.2 z.2) hlaw.aemeasurable ?_
  rw [hlaw.map_eq]
  refine Measure.ae_compProd_of_ae_ae hP (Filter.Eventually.of_forall fun q ↦ ?_)
  rw [Kernel.prodMkLeft_apply, stepLawKernel_apply]
  exact hae q.1 q.2

/-- The step of the round `k` of a trajectory from the step `h` is `h + k`. -/
lemma ae_obs_eq_stepLaw (s : S) (h k : ℕ) :
    ∀ᵐ x ∂stepLaw M π (s, h), IT.obs k x = ((IT.obs k x).1, h + k) := by
  have := ae_stepLaw_of_ae_shiftRounds M hπ s h k
    (P := fun _ _ y ↦ (IT.obs 0 y).2 = h + k)
    (measurableSet_eq_fun (by fun_prop) measurable_const)
    (fun _ s' ↦ by
      filter_upwards [ae_obs_zero_stepLaw M hπ (s', h + k)] with y hy
      rw [hy])
  filter_upwards [this] with x hx
  refine Prod.ext rfl ?_
  simpa [shiftRounds, IT.obs] using hx

/-- The action of the round `k` of a trajectory from the step `h` is `π (h + k)` of its state
(for an action space with a measurable diagonal, e.g. countable discrete or standard Borel). -/
lemma ae_action_eq_stepLaw [MeasurableEq A] (s : S) (h k : ℕ) :
    ∀ᵐ x ∂stepLaw M π (s, h), IT.action k x = π (h + k) (IT.obs k x).1 := by
  have := ae_stepLaw_of_ae_shiftRounds M hπ s h k
    (P := fun _ s' y ↦ IT.action 0 y = π (h + k) s')
    (measurableSet_eq_fun (by fun_prop) ((hπ _).comp (by fun_prop)))
    (fun _ s' ↦ ae_action_zero_stepLaw M hπ s' (h + k))
  filter_upwards [this] with x hx
  simpa [shiftRounds, IT.action] using hx

/-- The kernel from the state `s` to the reward and the next state of the step `h`:
`R_h(· | s, π_h(s)) ⊗ p_h(· | s, π_h(s))`. -/
noncomputable def rewardTransKernel (h : ℕ) : Kernel S (ℝ × S) :=
  (M.reward h ×ₖ M.trans h).comap (fun s ↦ (s, π h s)) (measurable_id.prodMk (hπ h))

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
lemma rewardTransKernel_apply (h : ℕ) (s : S) :
    rewardTransKernel M hπ h s = (M.reward h (s, π h s)).prod (M.trans h (s, π h s)) := by
  rw [rewardTransKernel, Kernel.comap_apply, Kernel.prod_apply]

instance (h : ℕ) : IsMarkovKernel (rewardTransKernel M hπ h) := by
  unfold rewardTransKernel; infer_instance

/-- The reward of the round `k` and the state of the round `k + 1` have conditional law
`R_{h+k}(· | S_k, π(S_k)) ⊗ p_{h+k}(· | S_k, π(S_k))` given the first `k` rounds and `S_k`. -/
lemma hasCondDistrib_feedback_obs_succ_stepLaw (s : S) (h k : ℕ) :
    HasCondDistrib (fun x ↦ (IT.feedback k x, (IT.obs (k + 1) x).1))
      (fun x ↦ (IT.hist k x, (IT.obs k x).1))
      (Kernel.prodMkLeft (Hist (S × ℕ) A ℝ k) (rewardTransKernel M hπ (h + k)))
      (stepLaw M π (s, h)) := by
  have hφ : Measurable fun y : ℕ → Round (S × ℕ) A ℝ ↦ (IT.feedback 0 y, (IT.obs 1 y).1) := by
    fun_prop
  have hc := (hasCondDistrib_shiftRounds_stepLaw M hπ s h k).comp_left hφ
  have hK : (Kernel.prodMkLeft (Hist (S × ℕ) A ℝ k) (stepLawKernel M π (h + k))).map
      (fun y : ℕ → Round (S × ℕ) A ℝ ↦ (IT.feedback 0 y, (IT.obs 1 y).1))
      = Kernel.prodMkLeft (Hist (S × ℕ) A ℝ k) (rewardTransKernel M hπ (h + k)) := by
    ext q : 1
    rw [Kernel.map_apply _ hφ, Kernel.prodMkLeft_apply, Kernel.prodMkLeft_apply,
      stepLawKernel_apply, rewardTransKernel_apply]
    exact (hasLaw_feedback_zero_fst_obs_one_stepLaw M hπ q.2 (h + k)).map_eq
  rw [hK] at hc
  refine hc.congr (Filter.Eventually.of_forall fun _ ↦ rfl)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  simp [shiftRounds, IT.feedback, IT.obs, add_comm]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
lemma measurable_lastState_policy (h k : ℕ) :
    Measurable fun p : Hist (S × ℕ) A ℝ (k + 1) ↦
      ((p (Fin.last k)).obs.1, π h (p (Fin.last k)).obs.1) := by
  have hm : Measurable fun p : Hist (S × ℕ) A ℝ (k + 1) ↦ (p (Fin.last k)).obs.1 :=
    measurable_fst.comp (Round.measurable_obs.comp (measurable_pi_apply (Fin.last k)))
  exact hm.prodMk ((hπ h).comp hm)

/-- The kernel from the first `k + 1` rounds to the next state at the step `h`:
`p_h(· | S_k, π_h(S_k))`. -/
noncomputable def histTransKernel (h k : ℕ) : Kernel (Hist (S × ℕ) A ℝ (k + 1)) S :=
  (M.trans h).comap _ (measurable_lastState_policy hπ h k)

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
lemma histTransKernel_apply (h k : ℕ) (p : Hist (S × ℕ) A ℝ (k + 1)) :
    histTransKernel M hπ h k p = M.trans h ((p (Fin.last k)).obs.1, π h (p (Fin.last k)).obs.1) :=
  rfl

instance (h k : ℕ) : IsMarkovKernel (histTransKernel M hπ h k) := by
  unfold histTransKernel; infer_instance

/-- **Law of the next state** given the first `k + 1` rounds: the transition kernel of `M` at
the step `h + k`, the state of the round `k` and the action of `π`. -/
lemma hasCondDistrib_obs_succ_hist_stepLaw (s : S) (h k : ℕ) :
    HasCondDistrib (fun x ↦ (IT.obs (k + 1) x).1) (IT.hist (k + 1)) (histTransKernel M hπ (h + k) k)
      (stepLaw M π (s, h)) := by
  refine hasCondDistrib_of_lintegral_eq (by fun_prop) (by fun_prop) fun f hf ↦ ?_
  have hsnoc : Measurable fun q : Hist (S × ℕ) A ℝ k × Round (S × ℕ) A ℝ ↦
      (Fin.snoc q.1 q.2 : Hist (S × ℕ) A ℝ (k + 1)) := measurable_finSnoc
  set j := h + k with hj
  -- the one-step computation under `stepLaw M π (s', j)`
  have hone (p : Hist (S × ℕ) A ℝ k) (s' : S) (g : Hist (S × ℕ) A ℝ (k + 1) × S → ℝ≥0∞)
      (hg : Measurable g) :
      ∫⁻ y, g (Fin.snoc p (y 0), (IT.obs 1 y).1) ∂stepLaw M π (s', j)
        = ∫⁻ r, ∫⁻ s'', g (Fin.snoc p ((s', j), π j s', r), s'') ∂M.trans j (s', π j s')
            ∂M.reward j (s', π j s') := by
    have hm : Measurable fun q : ℝ × S ↦
        g (Fin.snoc p (((s', j), π j s', q.1) : Round (S × ℕ) A ℝ), q.2) :=
      hg.comp ((hsnoc.comp (measurable_const.prodMk (by fun_prop))).prodMk measurable_snd)
    calc ∫⁻ y, g (Fin.snoc p (y 0), (IT.obs 1 y).1) ∂stepLaw M π (s', j)
        = ∫⁻ y, (fun q : (ℝ × S) × (ℕ → Round (S × ℕ) A ℝ) ↦
            g (Fin.snoc p ((s', j), π j s', q.1.1), q.1.2))
            ((IT.feedback 0 y, (IT.obs 1 y).1), shiftRound y) ∂stepLaw M π (s', j) := by
          refine lintegral_congr_ae ?_
          filter_upwards [ae_round_zero_stepLaw M hπ s' j] with y hy
          simp only [hy]
      _ = ∫⁻ q, ∫⁻ _y, g (Fin.snoc p ((s', j), π j s', q.1), q.2)
            ∂stepLaw M π (q.2, j + 1) ∂((M.reward j (s', π j s')).prod (M.trans j (s', π j s'))) :=
          lintegral_stepLaw_succ M hπ s' j (hm.comp measurable_fst)
      _ = ∫⁻ q, g (Fin.snoc p ((s', j), π j s', q.1), q.2)
            ∂((M.reward j (s', π j s')).prod (M.trans j (s', π j s'))) := by
          simp [stepLaw_univ M hπ]
      _ = _ := lintegral_prod _ hm.aemeasurable
  have hF : Measurable fun q : Hist (S × ℕ) A ℝ k × S × (ℕ → Round (S × ℕ) A ℝ) ↦
      f (Fin.snoc q.1 (q.2.2 0), (IT.obs 1 q.2.2).1) :=
    hf.comp ((hsnoc.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp
      measurable_snd.snd))).prodMk (measurable_fst.comp ((IT.measurable_obs 1).comp
        measurable_snd.snd)))
  have hK : Measurable fun p' : Hist (S × ℕ) A ℝ (k + 1) ↦
      ∫⁻ s'', f (p', s'') ∂histTransKernel M hπ j k p' :=
    Measurable.lintegral_kernel_prod_right' (κ := histTransKernel M hπ j k) hf
  have hF' : Measurable fun q : Hist (S × ℕ) A ℝ k × S × (ℕ → Round (S × ℕ) A ℝ) ↦
      ∫⁻ s'', f (Fin.snoc q.1 (q.2.2 0), s'') ∂histTransKernel M hπ j k (Fin.snoc q.1 (q.2.2 0)) :=
    hK.comp (hsnoc.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp
      measurable_snd.snd)))
  calc ∫⁻ x, f (IT.hist (k + 1) x, (IT.obs (k + 1) x).1) ∂stepLaw M π (s, h)
      = ∫⁻ x, f (Fin.snoc (IT.hist k x) (shiftRounds k x 0), (IT.obs 1 (shiftRounds k x)).1)
          ∂stepLaw M π (s, h) := by
        refine lintegral_congr fun x ↦ ?_
        rw [hist_succ_eq_snoc]
        simp [IT.obs, shiftRounds, add_comm]
    _ = ∫⁻ x, ∫⁻ y, f (Fin.snoc (IT.hist k x) (y 0), (IT.obs 1 y).1)
          ∂stepLaw M π ((IT.obs k x).1, j) ∂stepLaw M π (s, h) :=
        lintegral_stepLaw_hist_shiftRounds M hπ k s h _ hF
    _ = ∫⁻ x, ∫⁻ y, ∫⁻ s'', f (Fin.snoc (IT.hist k x) (y 0), s'')
          ∂histTransKernel M hπ j k (Fin.snoc (IT.hist k x) (y 0))
          ∂stepLaw M π ((IT.obs k x).1, j) ∂stepLaw M π (s, h) := by
        refine lintegral_congr fun x ↦ ?_
        rw [hone _ _ _ hf, hone _ _ (fun q ↦ ∫⁻ s'', f (q.1, s'') ∂histTransKernel M hπ j k q.1)
          (hK.comp measurable_fst)]
        refine lintegral_congr fun r ↦ ?_
        simp [histTransKernel_apply]
    _ = ∫⁻ x, ∫⁻ s'', f (Fin.snoc (IT.hist k x) (shiftRounds k x 0), s'')
          ∂histTransKernel M hπ j k (Fin.snoc (IT.hist k x) (shiftRounds k x 0))
          ∂stepLaw M π (s, h) :=
        (lintegral_stepLaw_hist_shiftRounds M hπ k s h _ hF').symm
    _ = _ := by
        refine lintegral_congr fun x ↦ ?_
        rw [hist_succ_eq_snoc]

/-- `E[Ψ(H_{k+1}) g(S_{k+1})] = E[Ψ(H_{k+1}) (p_{h+k} g)(S_k, π(S_k))]` for a bounded measurable
function `Ψ` of the first `k + 1` rounds and a bounded measurable `g`. -/
lemma integral_mul_obs_succ_stepLaw (s : S) (h k : ℕ)
    {Ψ : Hist (S × ℕ) A ℝ (k + 1) → ℝ} (hΨ : Measurable Ψ) {C : ℝ} (hC : ∀ p, |Ψ p| ≤ C)
    {g : S → ℝ} (hg : Measurable g) {D : ℝ} (hD : ∀ s', |g s'| ≤ D) :
    ∫ x, Ψ (IT.hist (k + 1) x) * g (IT.obs (k + 1) x).1 ∂stepLaw M π (s, h)
      = ∫ x, Ψ (IT.hist (k + 1) x)
          * ∫ s', g s' ∂M.trans (h + k) ((IT.obs k x).1, π (h + k) (IT.obs k x).1)
          ∂stepLaw M π (s, h) := by
  have hc := hasCondDistrib_obs_succ_hist_stepLaw M hπ s h k
  have hm : Measurable fun q : Hist (S × ℕ) A ℝ (k + 1) × S ↦ Ψ q.1 * g q.2 :=
    (hΨ.comp measurable_fst).mul (hg.comp measurable_snd)
  rw [hc.integral_prodMk (f := fun q ↦ Ψ q.1 * g q.2) hm.stronglyMeasurable]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [integral_const_mul, histTransKernel_apply]
    rfl
  · refine Integrable.of_bound hm.aestronglyMeasurable (C * D)
      (Filter.Eventually.of_forall fun q ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hC q.1) (hD q.2) (abs_nonneg _) ((abs_nonneg _).trans (hC q.1))

/-- For an MDP with the measurable reward function `r`, the reward of the round `k` is `r (h + k)`
of its state and of the action of the policy in that state. -/
lemma ae_feedback_eq_policy_stepLaw {r : ℕ → S → A → ℝ} (hM : M.HasRewardFn r)
    (hr : ∀ h, Measurable fun p : S × A ↦ r h p.1 p.2) (s : S) (h k : ℕ) :
    ∀ᵐ x ∂stepLaw M π (s, h),
      IT.feedback k x = r (h + k) (IT.obs k x).1 (π (h + k) (IT.obs k x).1) := by
  have hr' : Measurable fun s' : S ↦ r (h + k) s' (π (h + k) s') :=
    (hr (h + k)).comp (measurable_id.prodMk (hπ (h + k)))
  have := ae_stepLaw_of_ae_shiftRounds M hπ s h k
    (P := fun _ s' y ↦ IT.feedback 0 y = r (h + k) s' (π (h + k) s'))
    (measurableSet_eq_fun (by fun_prop) (hr'.comp (measurable_snd.comp measurable_fst)))
    (fun _ s' ↦ by
      have hl := hasLaw_feedback_zero_stepLaw M hπ s' (h + k)
      rw [hM (h + k) s' (π (h + k) s')] at hl
      exact hl.ae_eq_of_dirac)
  filter_upwards [this] with x hx
  simpa [shiftRounds, IT.feedback] using hx

/-- For an MDP with the measurable reward function `r`, the reward of the round `k` is `r (h + k)`
of its state and action. -/
lemma ae_feedback_eq_stepLaw [MeasurableEq A] {r : ℕ → S → A → ℝ} (hM : M.HasRewardFn r)
    (hr : ∀ h, Measurable fun p : S × A ↦ r h p.1 p.2) (s : S) (h k : ℕ) :
    ∀ᵐ x ∂stepLaw M π (s, h), IT.feedback k x = r (h + k) (IT.obs k x).1 (IT.action k x) := by
  filter_upwards [ae_feedback_eq_policy_stepLaw M hπ hM hr s h k, ae_action_eq_stepLaw M hπ s h k]
    with x hx hx'
  rw [hx', hx]

/-! ### The states of an episode -/

variable (H : ℕ)

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
lemma measurable_lastState_policy_states (h : Fin H) :
    Measurable fun τ : Fin (h + 1) → S ↦ (τ (Fin.last h), π h (τ (Fin.last h))) :=
  (measurable_pi_apply _).prodMk ((hπ h).comp (measurable_pi_apply _))

/-- The kernel from the states `s_0, …, s_h` of an episode to the next state:
`p_h(· | s_h, π_h(s_h))`. -/
noncomputable def statesTransKernel (h : Fin H) : Kernel (Fin (h + 1) → S) S :=
  (M.trans h).comap _ (measurable_lastState_policy_states hπ H h)

omit [MeasurableSingletonClass S] [MeasurableSingletonClass A] in
lemma statesTransKernel_apply (h : Fin H) (τ : Fin (h + 1) → S) :
    statesTransKernel M hπ H h τ = M.trans h (τ (Fin.last h), π h (τ (Fin.last h))) := rfl

instance (h : Fin H) : IsMarkovKernel (statesTransKernel M hπ H h) := by
  unfold statesTransKernel; infer_instance

omit hπ [MeasurableSpace S] [MeasurableSpace A] [MeasurableSingletonClass S]
  [MeasurableSingletonClass A] in
lemma castLE_succ_le (h : Fin H) : (h : ℕ) + 1 ≤ H + 1 := Nat.succ_le_succ h.is_lt.le

/-- Under the law of the state sequence of an episode of `π`, the state of the step `h + 1` has
conditional law `p_h(· | s_h, π_h(s_h))` given the states `s_0, …, s_h`. -/
lemma hasCondDistrib_statesLaw (s₁ : S) (h : Fin H) :
    HasCondDistrib (fun τ : Traj S H ↦ τ h.succ)
      (fun τ (i : Fin (h + 1)) ↦ τ (Fin.castLE (castLE_succ_le H h) i))
      (statesTransKernel M hπ H h) (statesLaw M H s₁ π) := by
  have hc := hasCondDistrib_obs_succ_hist_stepLaw M hπ s₁ 0 h
  rw [Nat.zero_add] at hc
  have hg : Measurable fun (p : Hist (S × ℕ) A ℝ (h + 1)) (i : Fin (h + 1)) ↦ (p i).obs.1 := by
    fun_prop
  have hc' : HasCondDistrib (fun x ↦ (IT.obs (h + 1) x).1)
      ((fun (p : Hist (S × ℕ) A ℝ (h + 1)) (i : Fin (h + 1)) ↦ (p i).obs.1) ∘ IT.hist (h + 1))
      (statesTransKernel M hπ H h) (stepLaw M π (s₁, 0)) :=
    HasCondDistrib.comp_right (hf := hg) hc
  exact HasCondDistrib.of_comp_hasLaw (Measurable.of_eval fun i ↦ measurable_pi_apply _)
    (measurable_pi_apply _) ⟨(measurable_episodeStates (S := S) (A := A) H).aemeasurable, rfl⟩ hc'

/-! ### The episode environment -/

section EpisodeEnv

variable [Finite S] [Countable A] [Nonempty A]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {alg : Algorithm Unit (Policy S A H) (Traj S H)} {O : ℕ → Ω → Unit} {X : ℕ → Ω → Policy S A H}
  {Y : ℕ → Ω → Traj S H}

omit hπ

/-- **Law of an episode given the past**: in an interaction with the episode environment of `M`
from `s₁`, the state sequence of the episode `t` has conditional law `statesKernel M H s₁` given
the history of the first `t` episodes and the policy of the episode `t`. -/
lemma hasCondDistrib_feedback_history_action_statesEnv (s₁ : S)
    (h : IsAlgEnvSeq O X Y alg (statesEnv M H s₁) P) (t : ℕ) :
    HasCondDistrib (Y t) (fun ω ↦ ((history O X Y t ω, O t ω), X t ω))
      ((statesKernel M H s₁).prodMkLeft _) P := by
  have h' : IsAlgEnvSeq O X Y alg (stationaryEnv (statesKernel M H s₁)) P := h
  have := IsObliviousEnv.hasCondDistrib_feedback_history_action h' t
  rwa [feedbackCondAction_stationaryEnv] at this

/-- In an interaction with the episode environment of `M` from `s₁`, the state sequence of the
episode `t` has conditional law `statesKernel M H s₁` given the policy of the episode `t`. -/
lemma hasCondDistrib_feedback_statesEnv (s₁ : S)
    (h : IsAlgEnvSeq O X Y alg (statesEnv M H s₁) P) (t : ℕ) :
    HasCondDistrib (Y t) (X t) (statesKernel M H s₁) P :=
  (hasCondDistrib_feedback_history_action_statesEnv M H s₁ h t).comp_right

omit [Nonempty A] in
lemma measurable_episodeStepKernel_aux {γ : Type*} {mγ : MeasurableSpace γ} (h : Fin H) :
    Measurable fun q : (γ × Policy S A H) × (Fin (h + 1) → S) ↦
      (q.2 (Fin.last h), q.1.2 h (q.2 (Fin.last h))) :=
  (measurable_of_countable fun z : Policy S A H × (Fin (h + 1) → S) ↦
    (z.2 (Fin.last h), z.1 h (z.2 (Fin.last h)))).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

/-- The kernel from (the past `γ`, the policy `π`, the states `s_0, …, s_h`) to the next state
of the episode: `p_h(· | s_h, π_h(s_h))`. -/
noncomputable def episodeStepKernel (γ : Type*) [MeasurableSpace γ] (h : Fin H) :
    Kernel ((γ × Policy S A H) × (Fin (h + 1) → S)) S :=
  (M.trans h).comap _ (measurable_episodeStepKernel_aux H h)

omit [Nonempty A] in
lemma episodeStepKernel_apply (γ : Type*) [MeasurableSpace γ] (h : Fin H)
    (q : (γ × Policy S A H) × (Fin (h + 1) → S)) :
    episodeStepKernel M H γ h q = M.trans h (q.2 (Fin.last h), q.1.2 h (q.2 (Fin.last h))) := rfl

instance (γ : Type*) [MeasurableSpace γ] (h : Fin H) :
    IsMarkovKernel (episodeStepKernel M H γ h) := by
  unfold episodeStepKernel; infer_instance

/-- **Law of the next state within an episode**: in an interaction with the episode environment
of `M` from `s₁`, the state of the step `h + 1` of the episode `t` has conditional law
`p_h(· | s_h, π_h(s_h))` given the history of the first `t` episodes, the policy `π` of the
episode `t` and its states `s_0, …, s_h`. -/
lemma hasCondDistrib_feedback_succ_statesEnv (s₁ : S)
    (hseq : IsAlgEnvSeq O X Y alg (statesEnv M H s₁) P) (t : ℕ) (h : Fin H) :
    HasCondDistrib (fun ω ↦ Y t ω h.succ)
      (fun ω ↦ (((history O X Y t ω, O t ω), X t ω),
        fun i : Fin (h + 1) ↦ Y t ω (Fin.castLE (castLE_succ_le H h) i)))
      (episodeStepKernel M H (Hist Unit (Policy S A H) (Traj S H) t × Unit) h) P := by
  have h1 := hasCondDistrib_feedback_history_action_statesEnv M H s₁ hseq t
  have h2 := HasCondDistrib.compProd_left_of_sectR
    (μ := P.map fun ω ↦ ((history O X Y t ω, O t ω), X t ω))
    (κ := (statesKernel M H s₁).prodMkLeft _)
    (X := fun τ : Traj S H ↦ fun i : Fin (h + 1) ↦ τ (Fin.castLE (castLE_succ_le H h) i))
    (Y := fun τ : Traj S H ↦ τ h.succ)
    (η := episodeStepKernel M H (Hist Unit (Policy S A H) (Traj S H) t × Unit) h)
    (Measurable.of_eval fun i ↦ measurable_pi_apply _) (measurable_pi_apply _) fun a ↦ by
      have := hasCondDistrib_statesLaw M a.2.measurable_extend H s₁ h
      rw [Kernel.prodMkLeft_apply, statesKernel_apply]
      convert this using 1
      ext q : 1
      rw [Kernel.sectR_apply, episodeStepKernel_apply, statesTransKernel_apply,
        Policy.extend_fin]
  exact HasCondDistrib.comp_of_hasLaw h2 h1

end EpisodeEnv

end Learning.MDP.Episodic
