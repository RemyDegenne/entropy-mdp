/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.StepLaw
public import LeanMachineLearning.SequentialLearning.FiniteActions

/-!
# Sampling at the visits of a state-action pair

Let `(X, Y)` be an algorithm-environment sequence for an arbitrary algorithm in the episode
environment `statesEnv M H s₁` of a finite-horizon MDP `M` with the horizon `H` (`X t` is the
policy of the episode `t`, `Y t` its state sequence). Fix a step `h` and a pair `(s, a)`. The
pair visited at the step `h` of the episode `t` is `stepPair X Y h t`, so that the number of
visits of `(s, a)` in the first `t` episodes is LML's `pullCount (stepPair X Y h) (s, a) t` and
the episode of the `k`-th visit (`k ≥ 1`) is `stepsUntil (stepPair X Y h) (s, a) k` (`⊤` if
there are fewer than `k` visits): the "arm" is the pair `(s, a)` at the step `h`. The next state
observed at the `k`-th visit is `visitNextState X Y h s a k`.

* `measure_inter_feedback_succ_eq_mul`, `integral_mul_feedback_succ_statesEnv`: given the history
  of the first `t` episodes, the policy of the episode `t` and its states up to the step `h`, the
  next state has law `p_h(· | s_h, a_h)` (martingale differences along the episodes);
* `measure_inter_visitNextState_eq_mul`: for an event `E` such that `E ∩ {T_k = t}` is determined
  by the information available before the transition of the episode `t`,
  `P(E ∩ {T_k < ∞} ∩ {W_k ∈ C}) = P(E ∩ {T_k < ∞}) p(C)` (martingale differences along the visits);
* `measure_visitNextState_le_pi`: on the event that the pair is visited at least `n` times, the
  first `n` observed next states are dominated by an i.i.d. sample of `p = p_h(· | s, a)`:
  `P(n visits, (W_1, …, W_n) ∈ C) ≤ p^{⊗ n}(C)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP
open scoped ENNReal

namespace Learning.MDP.Episodic

variable {S A : Type*} [Finite S] [Countable A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] {H : ℕ} (M : EpisodicMDP S A)
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {alg : Algorithm Unit (Policy S A H) (Traj S H)} {O : ℕ → Ω → Unit} {X : ℕ → Ω → Policy S A H}
  {Y : ℕ → Ω → Traj S H}

omit [Finite S] [Countable A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] [IsFiniteMeasure P] in
variable (X Y) in
/-- The state-action pair `(s_h, a_h)` visited at the step `h` of the episode `t`. -/
def stepPair (h : Fin H) (t : ℕ) (ω : Ω) : S × A :=
  (Y t ω h.castSucc, X t ω h (Y t ω h.castSucc))

omit [Finite S] [Countable A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] [IsFiniteMeasure P] in
variable (X Y) in
/-- The next state `W_k = s_{h+1}` observed at the `k`-th visit of `(s, a)` at the step `h`
(`k ≥ 1`; its value is arbitrary if there are fewer than `k` visits). -/
noncomputable def visitNextState [DecidableEq S] [DecidableEq A] (h : Fin H) (s : S) (a : A)
    (k : ℕ) (ω : Ω) : S :=
  Y (stepsUntil (stepPair X Y h) (s, a) k ω).toNat ω h.succ

omit [Finite S] [Countable A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] [IsFiniteMeasure P] in
variable (O X Y) in
/-- The information available just before the transition of the step `h` of the episode `t`: the
history of the first `t` episodes, the policy of the episode `t` and its states up to the step
`h`. -/
def infoBeforeStep (t : ℕ) (h : Fin H) (ω : Ω) :
    ((Hist Unit (Policy S A H) (Traj S H) t × Unit) × Policy S A H) × (Fin (h + 1) → S) :=
  (((history O X Y t ω, O t ω), X t ω), fun i ↦ Y t ω (Fin.castLE (castLE_succ_le H h) i))

omit [Finite S] [Countable A] [MeasurableSingletonClass S] [MeasurableSingletonClass A]
  [Nonempty A] [IsFiniteMeasure P] in
/-- The information before the step `h` of the episode `t` is measurable. -/
lemma measurable_infoBeforeStep (hX : ∀ n, Measurable (X n))
    (hY : ∀ n, Measurable (Y n)) (hO : ∀ n, Measurable (O n)) (t : ℕ) (h : Fin H) :
    Measurable (infoBeforeStep O X Y t h) :=
  (((measurable_history hO hX hY t).prodMk (hO t)).prodMk (hX t)).prodMk
    (Measurable.of_eval fun _ ↦ (measurable_pi_apply _).comp (hY t))

/-! ### Martingale differences along the episodes -/

/-- Given the history of the first `t` episodes, the policy of the episode `t` and its states up
to the step `h`, on an event on which `(s_h, a_h) = (s, a)`, the next state has law
`p_h(· | s, a)`: `P({info ∈ B} ∩ {s_{h+1} ∈ C}) = P(info ∈ B) p_h(C | s, a)`. -/
lemma measure_inter_feedback_succ_eq_mul (s₁ : S)
    (hseq : IsAlgEnvSeq O X Y alg (statesEnv M H s₁) P) (t : ℕ) (h : Fin H) (s : S) (a : A)
    {B : Set (((Hist Unit (Policy S A H) (Traj S H) t × Unit) × Policy S A H) × (Fin (h + 1) → S))}
    (hB : ∀ q ∈ B, q.2 (Fin.last h) = s ∧ q.1.2 h (q.2 (Fin.last h)) = a) (C : Set S) :
    P (infoBeforeStep O X Y t h ⁻¹' B ∩ {ω | Y t ω h.succ ∈ C})
      = P (infoBeforeStep O X Y t h ⁻¹' B) * M.trans h (s, a) C := by
  have hc : HasCondDistrib (fun ω ↦ Y t ω h.succ) (infoBeforeStep O X Y t h)
      (episodeStepKernel M H (Hist Unit (Policy S A H) (Traj S H) t × Unit) h) P :=
    hasCondDistrib_feedback_succ_statesEnv M H s₁ hseq t h
  refine hc.measure_inter_preimage_eq_mul_of_eqOn_const B.to_countable.measurableSet
    (fun q hq ↦ ?_) (Set.to_countable C).measurableSet
  have h1 := (hB q hq).1
  have h2 := (hB q hq).2
  rw [h1] at h2
  simp only [episodeStepKernel_apply, h1, h2]

/-- **Martingale differences along the episodes**: for every function `Ψ` of the history of the
first `t` episodes, the policy of the episode `t` and its states up to the step `h`, and every
`f : S → ℝ`, `E[Ψ f(s_{h+1})] = E[Ψ (p_h f)(s_h, a_h)]`. -/
lemma integral_mul_feedback_succ_statesEnv [Finite A] (s₁ : S)
    (hseq : IsAlgEnvSeq O X Y alg (statesEnv M H s₁) P) (t : ℕ) (h : Fin H)
    (Ψ : ((Hist Unit (Policy S A H) (Traj S H) t × Unit) × Policy S A H) × (Fin (h + 1) → S) → ℝ)
    (f : S → ℝ) :
    ∫ ω, Ψ (infoBeforeStep O X Y t h ω) * f (Y t ω h.succ) ∂P
      = ∫ ω, Ψ (infoBeforeStep O X Y t h ω)
          * ∫ s', f s' ∂M.trans h (Y t ω h.castSucc, X t ω h (Y t ω h.castSucc)) ∂P := by
  have hc : HasCondDistrib (fun ω ↦ Y t ω h.succ) (infoBeforeStep O X Y t h)
      (episodeStepKernel M H (Hist Unit (Policy S A H) (Traj S H) t × Unit) h) P :=
    hasCondDistrib_feedback_succ_statesEnv M H s₁ hseq t h
  refine (hc.integral_prodMk (f := fun q ↦ Ψ q.1 * f q.2)
    (measurable_of_countable _).stronglyMeasurable Integrable.of_finite).trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  simp only
  rw [integral_const_mul, episodeStepKernel_apply]
  rfl

/-! ### Martingale differences along the visits -/

omit [Finite S] [Countable A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] [IsFiniteMeasure P] in
/-- The information before the step `h` of the episode `t` determines the pairs visited at the
step `h` of the episodes `0, …, t`. -/
lemma stepPair_eq_of_infoBeforeStep_eq {t : ℕ} {h : Fin H} {ω ω' : Ω}
    (he : infoBeforeStep O X Y t h ω = infoBeforeStep O X Y t h ω') :
    ∀ i ≤ t, stepPair X Y h i ω = stepPair X Y h i ω' := by
  intro i hi
  simp only [infoBeforeStep, Prod.mk.injEq] at he
  obtain ⟨⟨⟨hhist, -⟩, hX⟩, hY⟩ := he
  rcases hi.lt_or_eq with hi | rfl
  · have := congrFun hhist ⟨i, hi⟩
    simp only [history, Prod.mk.injEq] at this
    simp only [stepPair, this.2.1, this.2.2]
  · have := congrFun hY (Fin.last h)
    rw [show Fin.castLE (castLE_succ_le H h) (Fin.last h) = h.castSucc from Fin.ext rfl] at this
    simp only [stepPair, this, hX]

omit [Finite S] [Countable A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] [IsFiniteMeasure P] in
/-- The information before the step `h` of the episode `t` determines the state sequences of the
episodes `0, …, t - 1`. -/
lemma feedback_eq_of_infoBeforeStep_eq {t : ℕ} {h : Fin H} {ω ω' : Ω}
    (he : infoBeforeStep O X Y t h ω = infoBeforeStep O X Y t h ω') :
    ∀ i < t, Y i ω = Y i ω' := by
  intro i hi
  simp only [infoBeforeStep, Prod.mk.injEq] at he
  have := congrFun he.1.1.1 ⟨i, hi⟩
  simp only [history, Prod.mk.injEq] at this
  exact this.2.2

omit [Finite S] [Countable A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] [IsFiniteMeasure P] in
/-- A set whose membership is determined by `φ` is the preimage of its image. -/
lemma eq_preimage_image_of_determined {α β : Type*} {φ : α → β} {F : Set α}
    (hF : ∀ ω ω', φ ω = φ ω' → ω ∈ F → ω' ∈ F) : F = φ ⁻¹' (φ '' F) := by
  ext ω
  exact ⟨fun hω ↦ ⟨ω, hω, rfl⟩, fun ⟨ω', hω', he⟩ ↦ hF ω' ω he hω'⟩

variable [DecidableEq S] [DecidableEq A]

/-- **Martingale differences along the visits**: let `k ≥ 1` and let `E` be an event such that
`E ∩ {T_k = t}` is determined by the information available before the transition of the step `h`
of the episode `t`, for every `t`. Then
`P(E ∩ {T_k < ∞} ∩ {W_k ∈ C}) = P(E ∩ {T_k < ∞}) p_h(C | s, a)`. -/
lemma measure_inter_visitNextState_eq_mul (s₁ : S)
    (hseq : IsAlgEnvSeq O X Y alg (statesEnv M H s₁) P) (h : Fin H) (s : S) (a : A) {k : ℕ}
    (hk : k ≠ 0) {E : Set Ω}
    (hE : ∀ (t : ℕ) (ω ω' : Ω), infoBeforeStep O X Y t h ω = infoBeforeStep O X Y t h ω' →
      ω ∈ E → stepsUntil (stepPair X Y h) (s, a) k ω = t → ω' ∈ E)
    (C : Set S) :
    P (E ∩ {ω | stepsUntil (stepPair X Y h) (s, a) k ω ≠ ⊤}
        ∩ {ω | visitNextState X Y h s a k ω ∈ C})
      = P (E ∩ {ω | stepsUntil (stepPair X Y h) (s, a) k ω ≠ ⊤}) * M.trans h (s, a) C := by
  set F : ℕ → Set Ω := fun t ↦ E ∩ {ω | stepsUntil (stepPair X Y h) (s, a) k ω = t} with hF
  have hFdet (t : ℕ) : F t = infoBeforeStep O X Y t h ⁻¹' (infoBeforeStep O X Y t h '' F t) := by
    refine eq_preimage_image_of_determined fun ω ω' he hω ↦ ⟨hE t ω ω' he hω.1 hω.2, ?_⟩
    exact (stepsUntil_eq_congr (stepPair_eq_of_infoBeforeStep_eq he)).1 hω.2
  have hmeas (t : ℕ) : MeasurableSet (F t) := by
    rw [hFdet t]
    exact (measurable_infoBeforeStep hseq.measurable_action hseq.measurable_feedback
      hseq.measurable_obs t h) (Set.to_countable _).measurableSet
  have hmeasY (t : ℕ) : MeasurableSet {ω | Y t ω h.succ ∈ C} :=
    ((measurable_pi_apply _).comp (hseq.measurable_feedback t)) (Set.to_countable C).measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint F) := by
    intro t t' htt'
    refine Set.disjoint_left.2 fun ω hω hω' ↦ htt' ?_
    exact_mod_cast hω.2.symm.trans hω'.2
  have hunion : E ∩ {ω | stepsUntil (stepPair X Y h) (s, a) k ω ≠ ⊤} = ⋃ t, F t := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, hF, ENat.ne_top_iff_exists]
    constructor
    · rintro ⟨hE, t, ht⟩
      exact ⟨t, hE, ht.symm⟩
    · rintro ⟨t, hE, ht⟩
      exact ⟨hE, t, ht.symm⟩
  have hunion' : E ∩ {ω | stepsUntil (stepPair X Y h) (s, a) k ω ≠ ⊤}
      ∩ {ω | visitNextState X Y h s a k ω ∈ C} = ⋃ t, (F t ∩ {ω | Y t ω h.succ ∈ C}) := by
    rw [hunion, Set.iUnion_inter]
    refine Set.iUnion_congr fun t ↦ ?_
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hF, and_congr_right_iff]
    intro hω
    simp [visitNextState, hω.2]
  have hB (t : ℕ) : ∀ q ∈ infoBeforeStep O X Y t h '' F t,
      q.2 (Fin.last h) = s ∧ q.1.2 h (q.2 (Fin.last h)) = a := by
    rintro q ⟨ω, hω, rfl⟩
    have hpair := action_eq_of_stepsUntil_eq_coe hk hω.2
    simp only [stepPair, Prod.mk.injEq] at hpair
    have e : Fin.castLE (castLE_succ_le H h) (Fin.last h) = h.castSucc := Fin.ext rfl
    simp only [infoBeforeStep, e]
    exact ⟨hpair.1, hpair.2⟩
  rw [hunion', hunion, measure_iUnion (fun t t' htt' ↦ (hdisj htt').mono Set.inter_subset_left
      Set.inter_subset_left) (fun t ↦ (hmeas t).inter (hmeasY t)),
    measure_iUnion hdisj hmeas, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun t ↦ ?_
  conv_lhs => rw [hFdet t]
  conv_rhs => rw [hFdet t]
  exact measure_inter_feedback_succ_eq_mul M s₁ hseq t h s a (hB t) C

/-! ### Domination of the observed next states by an i.i.d. sample -/

omit [Finite S] [Countable A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] [IsFiniteMeasure P] [DecidableEq S]
  [DecidableEq A] in
/-- There are at least `n ≥ 1` pulls iff the `n`-th pull happens. -/
lemma exists_le_pullCount_iff_stepsUntil_ne_top {α : Type*} [DecidableEq α] {B : ℕ → Ω → α}
    {x : α} {n : ℕ} (hn : n ≠ 0) (ω : Ω) :
    (∃ t, n ≤ pullCount B x t ω) ↔ stepsUntil B x n ω ≠ ⊤ := by
  constructor
  · rintro ⟨t, ht⟩
    rcases t with _ | t
    · simp only [pullCount_zero_apply, nonpos_iff_eq_zero] at ht
      exact absurd ht hn
    · exact stepsUntil_ne_top (exists_pullCount_eq_of_le ht hn)
  · intro h
    obtain ⟨t, ht⟩ := exists_pullCount_eq h
    exact ⟨t + 1, ht.ge⟩

omit [Finite S] [Countable A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] [IsFiniteMeasure P] [DecidableEq S]
  [DecidableEq A] in
/-- The number of pulls takes the value `n` iff it reaches `n`. -/
lemma exists_pullCount_eq_iff_exists_le_pullCount {α : Type*} [DecidableEq α] {B : ℕ → Ω → α}
    {x : α} {n : ℕ} (ω : Ω) :
    (∃ t, pullCount B x t ω = n) ↔ ∃ t, n ≤ pullCount B x t ω := by
  refine ⟨fun ⟨t, ht⟩ ↦ ⟨t, ht.ge⟩, fun h ↦ ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨0, pullCount_zero_apply _ _⟩
  · obtain ⟨t, ht⟩ := exists_pullCount_eq ((exists_le_pullCount_iff_stepsUntil_ne_top hn ω).1 h)
    exact ⟨t + 1, ht⟩

/-- The next state observed at the visit `n + 1` has law `p_h(· | s, a)` given the next states
observed at the first `n` visits, on the event that the visit `n + 1` happens:
`P(T_{n+1} < ∞, W_{≤ n+1} = w) = P(T_{n+1} < ∞, W_{≤ n} = w_{≤ n}) p_h(w_{n+1} | s, a)`. -/
lemma measure_visitNextState_succ_eq_mul (s₁ : S)
    (hseq : IsAlgEnvSeq O X Y alg (statesEnv M H s₁) P) (h : Fin H) (s : S) (a : A) (n : ℕ)
    (w : Fin (n + 1) → S) :
    P {ω | stepsUntil (stepPair X Y h) (s, a) (n + 1) ω ≠ ⊤
        ∧ ∀ k : Fin (n + 1), visitNextState X Y h s a (k + 1) ω = w k}
      = P {ω | stepsUntil (stepPair X Y h) (s, a) (n + 1) ω ≠ ⊤
          ∧ ∀ k : Fin n, visitNextState X Y h s a (k + 1) ω = w k.castSucc}
        * M.trans h (s, a) {w (Fin.last n)} := by
  set E : Set Ω := {ω | ∀ k : Fin n, visitNextState X Y h s a (k + 1) ω = w k.castSucc} with hE
  have hdet : ∀ (t : ℕ) (ω ω' : Ω), infoBeforeStep O X Y t h ω = infoBeforeStep O X Y t h ω' →
      ω ∈ E → stepsUntil (stepPair X Y h) (s, a) (n + 1) ω = t → ω' ∈ E := by
    intro t ω ω' he hω hT k
    have hle : stepsUntil (stepPair X Y h) (s, a) (k + 1) ω ≤ t :=
      hT ▸ stepsUntil_mono (s, a) ω (by omega) (by omega)
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (by simp) hle)
    have hmt : m < t := by
      refine lt_of_le_of_ne (by rw [← hm] at hle; exact_mod_cast hle) fun hmt ↦ ?_
      have h1 := pullCount_add_one_eq_of_stepsUntil_eq_coe hm.symm
      have h2 := pullCount_add_one_eq_of_stepsUntil_eq_coe hT
      rw [hmt] at h1
      have := k.is_lt
      omega
    have hm' : stepsUntil (stepPair X Y h) (s, a) (k + 1) ω' = m :=
      (stepsUntil_eq_congr fun i hi ↦ stepPair_eq_of_infoBeforeStep_eq he i (by omega)).1 hm.symm
    have hω := hω k
    simp only [visitNextState, ← hm, ENat.toNat_natCast] at hω
    simp only [visitNextState, hm', ENat.toNat_natCast]
    rw [← feedback_eq_of_infoBeforeStep_eq he m hmt]
    exact hω
  have := measure_inter_visitNextState_eq_mul M s₁ hseq h s a (k := n + 1) (by omega) hdet
    {w (Fin.last n)}
  have h1 : {ω | stepsUntil (stepPair X Y h) (s, a) (n + 1) ω ≠ ⊤
      ∧ ∀ k : Fin (n + 1), visitNextState X Y h s a (k + 1) ω = w k}
      = E ∩ {ω | stepsUntil (stepPair X Y h) (s, a) (n + 1) ω ≠ ⊤}
        ∩ {ω | visitNextState X Y h s a (n + 1) ω ∈ ({w (Fin.last n)} : Set S)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, hE, Set.mem_singleton_iff,
      Fin.forall_fin_succ', Fin.val_castSucc, Fin.val_last]
    tauto
  have h2 : {ω | stepsUntil (stepPair X Y h) (s, a) (n + 1) ω ≠ ⊤
      ∧ ∀ k : Fin n, visitNextState X Y h s a (k + 1) ω = w k.castSucc}
      = E ∩ {ω | stepsUntil (stepPair X Y h) (s, a) (n + 1) ω ≠ ⊤} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, hE]
    tauto
  rw [h1, h2]
  exact this

/-- **Domination of the observed next states by an i.i.d. sample**: on the event that `(s, a)`
is visited at least `n` times at the step `h`,
`P(W_1 = w_1, …, W_n = w_n) ≤ ∏_k p_h(w_k | s, a)`. -/
lemma measure_visitNextState_le_prod [IsProbabilityMeasure P] (s₁ : S)
    (hseq : IsAlgEnvSeq O X Y alg (statesEnv M H s₁) P) (h : Fin H) (s : S) (a : A) (n : ℕ)
    (w : Fin n → S) :
    P {ω | (∃ t, n ≤ pullCount (stepPair X Y h) (s, a) t ω)
        ∧ ∀ k : Fin n, visitNextState X Y h s a (k + 1) ω = w k}
      ≤ ∏ k, M.trans h (s, a) {w k} := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hset : {ω | (∃ t, n + 1 ≤ pullCount (stepPair X Y h) (s, a) t ω)
        ∧ ∀ k : Fin (n + 1), visitNextState X Y h s a (k + 1) ω = w k}
        = {ω | stepsUntil (stepPair X Y h) (s, a) (n + 1) ω ≠ ⊤
          ∧ ∀ k : Fin (n + 1), visitNextState X Y h s a (k + 1) ω = w k} := by
      ext ω
      simp only [Set.mem_ofPred_eq, exists_le_pullCount_iff_stepsUntil_ne_top (n.succ_ne_zero) ω]
    rw [hset, measure_visitNextState_succ_eq_mul M s₁ hseq h s a n w, Fin.prod_univ_castSucc]
    refine mul_le_mul_left ((measure_mono ?_).trans (ih (fun k ↦ w k.castSucc))) _
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    obtain ⟨t, ht⟩ := (exists_le_pullCount_iff_stepsUntil_ne_top n.succ_ne_zero ω).2 hω.1
    exact ⟨⟨t, by omega⟩, hω.2⟩

/-- **Domination of the observed next states by an i.i.d. sample**: on the event that `(s, a)`
is visited at least `n` times at the step `h`, the law of the first `n` observed next states is
dominated by the law `p^{⊗ n}` of `n` i.i.d. draws from `p = p_h(· | s, a)`:
`P(n visits, (W_1, …, W_n) ∈ C) ≤ p^{⊗ n}(C)`. -/
lemma measure_visitNextState_mem_le_pi [IsProbabilityMeasure P] (s₁ : S)
    (hseq : IsAlgEnvSeq O X Y alg (statesEnv M H s₁) P) (h : Fin H) (s : S) (a : A) (n : ℕ)
    (C : Set (Fin n → S)) :
    P {ω | (∃ t, n ≤ pullCount (stepPair X Y h) (s, a) t ω)
        ∧ (fun k : Fin n ↦ visitNextState X Y h s a (k + 1) ω) ∈ C}
      ≤ Measure.pi (fun _ : Fin n ↦ M.trans h (s, a)) C := by
  classical
  have := Fintype.ofFinite S
  have hset : {ω | (∃ t, n ≤ pullCount (stepPair X Y h) (s, a) t ω)
      ∧ (fun k : Fin n ↦ visitNextState X Y h s a (k + 1) ω) ∈ C}
      = ⋃ w ∈ C.toFinset, {ω | (∃ t, n ≤ pullCount (stepPair X Y h) (s, a) t ω)
        ∧ ∀ k : Fin n, visitNextState X Y h s a (k + 1) ω = w k} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_toFinset, exists_prop]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨_, h2, h1, fun k ↦ rfl⟩
    · rintro ⟨w, hw, h1, h2⟩
      refine ⟨h1, ?_⟩
      convert hw
      exact h2 _
  rw [hset]
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc ∑ w ∈ C.toFinset, P {ω | (∃ t, n ≤ pullCount (stepPair X Y h) (s, a) t ω)
        ∧ ∀ k : Fin n, visitNextState X Y h s a (k + 1) ω = w k}
      ≤ ∑ w ∈ C.toFinset, ∏ k, M.trans h (s, a) {w k} :=
        sum_le_sum fun w _ ↦ measure_visitNextState_le_prod M s₁ hseq h s a n w
    _ = ∑ w ∈ C.toFinset, Measure.pi (fun _ : Fin n ↦ M.trans h (s, a)) {w} := by
        refine sum_congr rfl fun w _ ↦ ?_
        rw [← Set.univ_pi_singleton, Measure.pi_pi]
    _ = Measure.pi (fun _ : Fin n ↦ M.trans h (s, a)) C := by
        rw [sum_measure_singleton, Set.coe_toFinset]

end Learning.MDP.Episodic
