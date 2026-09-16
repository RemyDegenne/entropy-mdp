/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.StepLaw

/-!
# The law of the sequence of states of a trajectory

For a finite-horizon MDP `M` and a policy `π`, `stateSeqLaw M π h s` is the law of the sequence
of states `(S_{h + k})_{k ∈ ℕ}` of the trajectory of `π` from the state `s` at the step `h` (the
states after the terminal layer repeat the terminal state). It satisfies the backward recursion
`stateSeqLaw M π h.castSucc s = (K.map (seqCons s)) ∘ₘ M.trans h (s, π h s)` with
`K = stateSeqLaw M π h.succ` (`stateSeqLaw_castSucc`) and `stateSeqLaw M π (Fin.last H) s` is the
Dirac mass at the constant sequence (`stateSeqLaw_last`). The law of the state sequence of an
episode (`statesLaw`) is its image by the restriction to the first `H + 1` states
(`statesLaw_eq_map_stateSeqLaw`).

The file also contains a bound on the return for rewards with step-dependent ranges
(`ae_episodeReturn_mem_Icc_sum`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP

namespace Learning.MDP.Episodic

variable {S A : Type*} [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] {H : ℕ} (M : EpisodicMDP S A H)
  (π : Policy S A H)

/-! ### Sequences of states -/

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Nonempty A] in
/-- The sequence with first term `s` followed by the sequence `f`. -/
def seqCons (s : S) (f : ℕ → S) (k : ℕ) : S := if k = 0 then s else f (k - 1)

omit [Fintype S] [MeasurableSingletonClass S] [Fintype A] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Nonempty A] in
lemma measurable_seqCons (s : S) : Measurable (seqCons s) := by
  refine Measurable.of_eval fun k ↦ ?_
  by_cases hk : k = 0
  · simp only [seqCons, hk, ↓reduceIte]
    exact measurable_const
  · simp only [seqCons, hk, ↓reduceIte]
    exact measurable_pi_apply _

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Nonempty A] in
/-- The sequence of the states of a trajectory of the layered MDP. -/
def stateSeq (x : ℕ → Round (LayerState S H) A ℝ) (k : ℕ) : S := (IT.obs k x).1

omit [Fintype S] [MeasurableSingletonClass S] [Fintype A] [MeasurableSingletonClass A]
  [Nonempty A] in
lemma measurable_stateSeq : Measurable (stateSeq (S := S) (A := A) (H := H)) :=
  Measurable.of_eval fun k ↦ measurable_fst.comp (IT.measurable_obs k)

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Nonempty A] in
lemma stateSeq_eq_seqCons (x : ℕ → Round (LayerState S H) A ℝ) :
    stateSeq x = seqCons (IT.obs 0 x).1 (stateSeq (shiftRound x)) := by
  funext k
  rcases k with _ | k
  · rfl
  · simp only [seqCons, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rfl

/-- The law of the sequence of states of the trajectory of `π` from `s` at the step `h`. -/
noncomputable def stateSeqLaw (h : Fin (H + 1)) (s : S) : Measure (ℕ → S) :=
  (stepLaw M π (s, h)).map stateSeq

instance (h : Fin (H + 1)) (s : S) : IsProbabilityMeasure (stateSeqLaw M π h s) := by
  unfold stateSeqLaw
  exact ⟨by rw [Measure.map_apply measurable_stateSeq MeasurableSet.univ, Set.preimage_univ,
    measure_univ]⟩

lemma measurable_stateSeqLaw (h : Fin (H + 1)) : Measurable (stateSeqLaw M π h) :=
  measurable_of_countable _

/-- The laws of the state sequences from the states at the step `h`, as a kernel. -/
noncomputable def stateSeqKernel (h : Fin (H + 1)) : Kernel S (ℕ → S) :=
  ⟨stateSeqLaw M π h, measurable_stateSeqLaw M π h⟩

@[simp] lemma stateSeqKernel_apply (h : Fin (H + 1)) (s : S) :
    stateSeqKernel M π h s = stateSeqLaw M π h s := rfl

instance (h : Fin (H + 1)) : IsMarkovKernel (stateSeqKernel M π h) :=
  ⟨fun s ↦ by rw [stateSeqKernel_apply]; infer_instance⟩

/-- **Backward recursion of the law of the state sequence**: from `s` at a non-terminal step
`h`, the sequence is `s` followed by the sequence from the next state `s' ∼ M.trans h (s, π h s)`
at the step `h + 1`. -/
lemma stateSeqLaw_castSucc (h : Fin H) (s : S) :
    stateSeqLaw M π h.castSucc s
      = ((stateSeqKernel M π h.succ).map (seqCons s)) ∘ₘ M.trans h (s, π h s) := by
  have hlaw := hasLaw_stepLaw_castSucc M π h s
  have hae : stateSeq =ᵐ[stepLaw M π (s, h.castSucc)]
      (fun z : (ℝ × S) × (ℕ → Round (LayerState S H) A ℝ) ↦ seqCons s (stateSeq z.2))
        ∘ fun x ↦ ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x) := by
    filter_upwards [ae_obs_zero_stepLaw M π (s, h.castSucc)] with x hx
    rw [stateSeq_eq_seqCons, hx]
    rfl
  have hG : Measurable fun y : ℕ → Round (LayerState S H) A ℝ ↦ seqCons s (stateSeq y) :=
    (measurable_seqCons s).comp measurable_stateSeq
  have hT : Measurable fun x : ℕ → Round (LayerState S H) A ℝ ↦
      ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x) :=
    ((IT.measurable_feedback 0).prodMk (measurable_fst.comp (IT.measurable_obs 1))).prodMk
      measurable_shiftRound
  have hK : (stateSeqKernel M π h.succ).map (seqCons s)
      = (stepLawKernel M π h.succ).map fun y ↦ seqCons s (stateSeq y) := by
    ext s' : 1
    rw [Kernel.map_apply _ (measurable_seqCons s), Kernel.map_apply _ hG, stateSeqKernel_apply,
      stateSeqLaw, Measure.map_map (measurable_seqCons s) measurable_stateSeq]
    rfl
  calc stateSeqLaw M π h.castSucc s
      = (stepLaw M π (s, h.castSucc)).map
          ((fun y ↦ seqCons s (stateSeq y)) ∘ Prod.snd
            ∘ fun x ↦ ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x)) := by
        rw [stateSeqLaw, Measure.map_congr hae]
        rfl
    _ = ((((M.reward h (s, π h s)).prod (M.trans h (s, π h s))
          ⊗ₘ Kernel.prodMkLeft ℝ (stepLawKernel M π h.succ)).map Prod.snd).map
            fun y ↦ seqCons s (stateSeq y)) := by
        rw [← hlaw.map_eq, Measure.map_map measurable_snd hT, Measure.map_map hG
          (measurable_snd.comp hT)]
    _ = ((stepLawKernel M π h.succ) ∘ₘ M.trans h (s, π h s)).map
          fun y ↦ seqCons s (stateSeq y) := by
        congr 1
        change (_ ⊗ₘ _).snd = _
        rw [Measure.snd_compProd, ← Measure.compProd_const, Measure.prodMkLeft_comp_compProd,
          Measure.const_comp, measure_univ, one_smul]
    _ = _ := by rw [Measure.map_comp _ _ hG, hK]

/-- At the terminal layer the sequence of states is constant. -/
lemma stateSeqLaw_last (s : S) : stateSeqLaw M π (Fin.last H) s = Measure.dirac fun _ ↦ s := by
  have hae : ∀ᵐ x ∂stepLaw M π (s, Fin.last H), ∀ k, (IT.obs k x).1 = s := by
    rw [ae_all_iff]
    intro k
    induction k with
    | zero => filter_upwards [ae_obs_zero_stepLaw M π (s, Fin.last H)] with x hx using by rw [hx]
    | succ k ih =>
      have hl := hasLaw_shiftRound_stepLaw_last M π s
      exact ae_of_ae_map (p := fun y ↦ (IT.obs k y).1 = s) hl.aemeasurable (by rwa [hl.map_eq])
  have hae' : stateSeq =ᵐ[stepLaw M π (s, Fin.last H)] fun _ _ ↦ s :=
    hae.mono fun x hx ↦ funext fun k ↦ hx k
  rw [stateSeqLaw, Measure.map_congr hae', Measure.map_const, measure_univ, one_smul]

/-- The law of the states of an episode is the image of the law of the state sequence by the
restriction to the first `H + 1` states. -/
lemma statesLaw_eq_map_stateSeqLaw (s₁ : S) :
    statesLaw M s₁ π = (stateSeqLaw M π (startStep H) s₁).map fun f (h : Fin (H + 1)) ↦ f h := by
  rw [statesLaw, stateSeqLaw, Measure.map_map (Measurable.of_eval fun _ ↦ measurable_pi_apply _)
    measurable_stateSeq]
  rfl

/-! ### The return for rewards with step-dependent ranges -/

/-- If the rewards at the step `k` lie in `[0, c k]`, the return from the step `h` lies in
`[0, ∑_{h ≤ k < H} c k]`. -/
lemma ae_episodeReturn_mem_Icc_sum {c : ℕ → ℝ}
    (hM : ∀ (k : Fin H) s a, ∀ᵐ x ∂M.reward k (s, a), x ∈ Set.Icc 0 (c k)) (h : Fin (H + 1))
    (s : S) :
    ∀ᵐ x ∂stepLaw M π (s, h), episodeReturn H x ∈ Set.Icc 0 (∑ k ∈ Finset.Ico (h : ℕ) H, c k) := by
  induction h using Fin.reverseInduction generalizing s with
  | last =>
    filter_upwards [ae_episodeReturn_eq_zero_stepLaw_last M π s] with x hx
    simp [hx]
  | cast i ih =>
    have h0 : ∀ᵐ x ∂stepLaw M π (s, i.castSucc), IT.feedback 0 x ∈ Set.Icc 0 (c i) := by
      have hl := hasLaw_feedback_zero_stepLaw_castSucc M π i s
      exact ae_of_ae_map (p := fun r ↦ r ∈ Set.Icc 0 (c i)) hl.aemeasurable
        (by rw [hl.map_eq]; exact hM i s (π i s))
    have h1 : ∀ᵐ x ∂stepLaw M π (s, i.castSucc),
        episodeReturn H (shiftRound x) ∈ Set.Icc 0 (∑ k ∈ Finset.Ico (i.succ : ℕ) H, c k) :=
      ae_stepLaw_castSucc_of_ae M π
        (P := fun _ _ y ↦ episodeReturn H y ∈ Set.Icc 0 (∑ k ∈ Finset.Ico (i.succ : ℕ) H, c k))
        (measurableSet_Icc.preimage (measurable_episodeReturn.comp measurable_snd))
        (Filter.Eventually.of_forall fun _ s' ↦ ih s')
    have hsum : ∑ k ∈ Finset.Ico (i.castSucc : ℕ) H, c k
        = c i + ∑ k ∈ Finset.Ico (i.succ : ℕ) H, c k := by
      rw [Fin.val_castSucc, Fin.val_succ, Finset.sum_eq_sum_Ico_succ_bot i.is_lt]
    filter_upwards [ae_episodeReturn_eq_add_shiftRound M π i.castSucc s, h0, h1] with x hx h0 h1
    rw [hx, hsum]
    exact ⟨add_nonneg h0.1 h1.1, add_le_add h0.2 h1.2⟩

end Learning.MDP.Episodic
