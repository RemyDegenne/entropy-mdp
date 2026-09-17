/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.StepLaw

/-!
# The law of the sequence of states of a trajectory

For a finite-horizon MDP `M` and a policy `π : ℕ → S → A`, `stateSeqLaw M π h s` is the law of the
sequence of states `(S_{h + k})_{k ∈ ℕ}` of the trajectory of `π` from the state `s` at the step
`h`, and `stateSeqKernel M π h` the corresponding kernel from the state. It satisfies the backward
recursion `stateSeqLaw M π h s = (K.map (seqCons s)) ∘ₘ M.trans h (s, π h s)` with
`K = stateSeqKernel M π (h + 1)` (`stateSeqLaw_succ`). The law of the state sequence of an
episode of horizon `H` (`statesLaw`) is its image by the restriction to the first `H + 1` states
(`statesLaw_eq_map_stateSeqLaw`).

If a state is absorbing under the policy from some step on, the sequence of states from it is
almost surely constant (`ae_stateSeqLaw_eq_const_of_absorbing`,
`stateSeqLaw_eq_dirac_of_absorbing`).

The file also contains a bound on the return for rewards with step-dependent ranges
(`ae_episodeReturn_mem_Icc_sum`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP

namespace Learning.MDP.Episodic

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : EpisodicMDP S A)
  (π : ℕ → S → A)

/-! ### Sequences of states -/

omit [MeasurableSpace S] [MeasurableSpace A] in
/-- The sequence with first term `s` followed by the sequence `f`. -/
def seqCons (s : S) (f : ℕ → S) (k : ℕ) : S := if k = 0 then s else f (k - 1)

omit [MeasurableSpace A] in
lemma measurable_seqCons (s : S) : Measurable (seqCons s) := by
  refine Measurable.of_eval fun k ↦ ?_
  by_cases hk : k = 0
  · simp only [seqCons, hk, ↓reduceIte]
    exact measurable_const
  · simp only [seqCons, hk, ↓reduceIte]
    exact measurable_pi_apply _

omit [MeasurableSpace S] [MeasurableSpace A] in
/-- The sequence of the states of a trajectory of the time-augmented MDP. -/
def stateSeq (x : ℕ → Round (S × ℕ) A ℝ) (k : ℕ) : S := (IT.obs k x).1

lemma measurable_stateSeq : Measurable (stateSeq (S := S) (A := A)) :=
  Measurable.of_eval fun k ↦ measurable_fst.comp (IT.measurable_obs k)

omit [MeasurableSpace S] [MeasurableSpace A] in
lemma stateSeq_eq_seqCons (x : ℕ → Round (S × ℕ) A ℝ) :
    stateSeq x = seqCons (IT.obs 0 x).1 (stateSeq (shiftRound x)) := by
  funext k
  rcases k with _ | k
  · rfl
  · simp only [seqCons, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rfl

/-- The law of the sequence of states of the trajectory of `π` from `s` at the step `h`. -/
noncomputable def stateSeqLaw (h : ℕ) (s : S) : Measure (ℕ → S) :=
  (stepLaw M π (s, h)).map stateSeq


/-- The laws of the state sequences from the states at the step `h`, as a kernel. -/
noncomputable def stateSeqKernel (h : ℕ) : Kernel S (ℕ → S) :=
  (stepLawKernel M π h).map stateSeq

@[simp] lemma stateSeqKernel_apply (h : ℕ) (s : S) :
    stateSeqKernel M π h s = stateSeqLaw M π h s := by
  rw [stateSeqKernel, Kernel.map_apply _ measurable_stateSeq, stepLawKernel_apply, stateSeqLaw]


lemma measurable_stateSeqLaw (h : ℕ) : Measurable (stateSeqLaw M π h) := by
  have : stateSeqLaw M π h = stateSeqKernel M π h :=
    funext fun s ↦ (stateSeqKernel_apply M π h s).symm
  rw [this]; exact (stateSeqKernel M π h).measurable

/-- The law of the states of an episode of horizon `H` is the image of the law of the state
sequence by the restriction to the first `H + 1` states. -/
lemma statesLaw_eq_map_stateSeqLaw (H : ℕ) (s₁ : S) :
    statesLaw M H s₁ π = (stateSeqLaw M π 0 s₁).map fun f (h : Fin (H + 1)) ↦ f h := by
  rw [statesLaw, stateSeqLaw, Measure.map_map (Measurable.of_eval fun _ ↦ measurable_pi_apply _)
    measurable_stateSeq]
  rfl

variable {π} (hπ : ∀ h, Measurable (π h))

include hπ

lemma isProbabilityMeasure_stateSeqLaw (h : ℕ) (s : S) :
    IsProbabilityMeasure (stateSeqLaw M π h s) := by
  have := isProbabilityMeasure_stepLaw M hπ (s, h)
  unfold stateSeqLaw; infer_instance

lemma isMarkovKernel_stateSeqKernel (h : ℕ) : IsMarkovKernel (stateSeqKernel M π h) :=
  ⟨fun s ↦ by rw [stateSeqKernel_apply]; exact isProbabilityMeasure_stateSeqLaw M hπ h s⟩

variable [MeasurableSingletonClass S] [MeasurableSingletonClass A]

/-- **Backward recursion of the law of the state sequence**: from `s` at the step `h`, the
sequence is `s` followed by the sequence from the next state `s' ∼ M.trans h (s, π h s)` at the
step `h + 1`. -/
lemma stateSeqLaw_succ (h : ℕ) (s : S) :
    stateSeqLaw M π h s
      = ((stateSeqKernel M π (h + 1)).map (seqCons s)) ∘ₘ M.trans h (s, π h s) := by
  have hlaw := hasLaw_stepLaw_succ M hπ s h
  have hae : stateSeq =ᵐ[stepLaw M π (s, h)]
      (fun z : (ℝ × S) × (ℕ → Round (S × ℕ) A ℝ) ↦ seqCons s (stateSeq z.2))
        ∘ fun x ↦ ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x) := by
    filter_upwards [ae_obs_zero_stepLaw M hπ (s, h)] with x hx
    rw [stateSeq_eq_seqCons, hx]
    rfl
  have hG : Measurable fun y : ℕ → Round (S × ℕ) A ℝ ↦ seqCons s (stateSeq y) :=
    (measurable_seqCons s).comp measurable_stateSeq
  have hT : Measurable fun x : ℕ → Round (S × ℕ) A ℝ ↦
      ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x) :=
    ((IT.measurable_feedback 0).prodMk (measurable_fst.comp (IT.measurable_obs 1))).prodMk
      measurable_shiftRound
  have hK : (stateSeqKernel M π (h + 1)).map (seqCons s)
      = (stepLawKernel M π (h + 1)).map fun y ↦ seqCons s (stateSeq y) := by
    ext s' : 1
    rw [Kernel.map_apply _ (measurable_seqCons s), Kernel.map_apply _ hG, stateSeqKernel_apply,
      stateSeqLaw, Measure.map_map (measurable_seqCons s) measurable_stateSeq, stepLawKernel_apply]
    rfl
  calc stateSeqLaw M π h s
      = (stepLaw M π (s, h)).map
          ((fun y ↦ seqCons s (stateSeq y)) ∘ Prod.snd
            ∘ fun x ↦ ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x)) := by
        rw [stateSeqLaw, Measure.map_congr hae]
        rfl
    _ = ((((M.reward h (s, π h s)).prod (M.trans h (s, π h s))
          ⊗ₘ Kernel.prodMkLeft ℝ (stepLawKernel M π (h + 1))).map Prod.snd).map
            fun y ↦ seqCons s (stateSeq y)) := by
        rw [← hlaw.map_eq, Measure.map_map measurable_snd hT, Measure.map_map hG
          (measurable_snd.comp hT)]
    _ = ((stepLawKernel M π (h + 1)) ∘ₘ M.trans h (s, π h s)).map
          fun y ↦ seqCons s (stateSeq y) := by
        congr 1
        change (_ ⊗ₘ _).snd = _
        rw [Measure.snd_compProd, ← Measure.compProd_const, Measure.prodMkLeft_comp_compProd,
          Measure.const_comp, measure_univ, one_smul]
    _ = _ := by rw [Measure.map_comp _ _ hG, hK]

/-! ### Absorbing states -/

omit hπ [MeasurableSingletonClass A] in
lemma measurableSet_forall_lt_eq (n : ℕ) (s : S) :
    MeasurableSet {f : ℕ → S | ∀ j < n, f j = s} := by
  simp_rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦
    (measurableSet_singleton s).preimage (measurable_pi_apply j)

/-- If the state `s` is absorbing under `π` from the step `h` on, the sequence of states from
`(s, h)` is almost surely constant. -/
lemma ae_stateSeqLaw_eq_const_of_absorbing (h : ℕ) (s : S)
    (habs : ∀ k, h ≤ k → M.trans k (s, π k s) = Measure.dirac s) :
    ∀ᵐ f ∂stateSeqLaw M π h s, f = fun _ ↦ s := by
  have key : ∀ n k, h ≤ k → ∀ᵐ f ∂stateSeqLaw M π k s, ∀ j < n, f j = s := by
    intro n
    induction n with
    | zero => exact fun k _ ↦ Filter.Eventually.of_forall fun _ j hj ↦ absurd hj (Nat.not_lt_zero j)
    | succ n ih =>
      intro k hk
      rw [stateSeqLaw_succ M hπ, habs k hk, Measure.dirac_bind (Kernel.measurable _),
        Kernel.map_apply _ (measurable_seqCons s), stateSeqKernel_apply,
        ae_map_iff (measurable_seqCons s).aemeasurable (measurableSet_forall_lt_eq (n + 1) s)]
      filter_upwards [ih (k + 1) (by omega)] with g hg j hj
      rcases j with _ | j
      · rfl
      · simp only [seqCons, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        exact hg j (by omega)
  filter_upwards [ae_all_iff.2 fun n ↦ key n h le_rfl] with f hf
  funext j
  exact hf (j + 1) j (Nat.lt_succ_self j)

/-- If the state `s` is absorbing under `π` from the step `h` on, the law of the sequence of
states from `(s, h)` is the Dirac mass at the constant sequence. -/
lemma stateSeqLaw_eq_dirac_of_absorbing (h : ℕ) (s : S)
    (habs : ∀ k, h ≤ k → M.trans k (s, π k s) = Measure.dirac s) :
    stateSeqLaw M π h s = Measure.dirac fun _ ↦ s := by
  have := isProbabilityMeasure_stateSeqLaw M hπ h s
  have hae := ae_stateSeqLaw_eq_const_of_absorbing M hπ h s habs
  calc stateSeqLaw M π h s = (stateSeqLaw M π h s).map id := Measure.map_id.symm
    _ = (stateSeqLaw M π h s).map fun _ ↦ fun _ ↦ s := Measure.map_congr hae
    _ = _ := by rw [Measure.map_const, measure_univ, one_smul]

/-! ### The return for rewards with step-dependent ranges -/

/-- If the rewards at the step `k` lie in `[0, c k]`, the return of `n` steps from the step `h`
lies in `[0, ∑_{k < n} c (h + k)]`. -/
lemma ae_episodeReturn_mem_Icc_sum {c : ℕ → ℝ}
    (hM : ∀ k s a, ∀ᵐ x ∂M.reward k (s, a), x ∈ Set.Icc 0 (c k)) (n : ℕ) :
    ∀ h s, ∀ᵐ x ∂stepLaw M π (s, h),
      episodeReturn n x ∈ Set.Icc 0 (∑ k ∈ range n, c (h + k)) := by
  induction n with
  | zero => intro h s; simp
  | succ n ih =>
    intro h s
    have h0 : ∀ᵐ x ∂stepLaw M π (s, h), IT.feedback 0 x ∈ Set.Icc 0 (c h) := by
      have hl := hasLaw_feedback_zero_stepLaw M hπ s h
      exact ae_of_ae_map (p := fun r ↦ r ∈ Set.Icc 0 (c h)) hl.aemeasurable
        (by rw [hl.map_eq]; exact hM h s (π h s))
    have h1 : ∀ᵐ x ∂stepLaw M π (s, h),
        episodeReturn n (shiftRound x) ∈ Set.Icc 0 (∑ k ∈ range n, c (h + 1 + k)) :=
      ae_stepLaw_succ_of_ae M hπ
        (P := fun _ _ y ↦ episodeReturn n y ∈ Set.Icc 0 (∑ k ∈ range n, c (h + 1 + k)))
        (measurableSet_Icc.preimage ((measurable_episodeReturn n).comp measurable_snd))
        (Filter.Eventually.of_forall fun _ s' ↦ ih (h + 1) s')
    have hsum : ∑ k ∈ range (n + 1), c (h + k) = c h + ∑ k ∈ range n, c (h + 1 + k) := by
      rw [sum_range_succ']
      simp only [add_zero, add_comm (c h)]
      congr 1
      refine sum_congr rfl fun k _ ↦ ?_
      rw [show h + (k + 1) = h + 1 + k by omega]
    filter_upwards [h0, h1] with x h0 h1
    rw [episodeReturn_succ_eq_add_shiftRound, hsum]
    exact ⟨add_nonneg h0.1 h1.1, add_le_add h0.2 h1.2⟩

end Learning.MDP.Episodic
