/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.MarkovIter

/-!
# Unrolling a backward recursive inequality along the trajectory

For a policy `π` of a finite-horizon MDP `M`, an initial state `s₁`, `β ∈ ℝ`, `κ ≥ 0` and functions
`r, u : Fin H → S → A → ℝ`, `g : Fin (H + 1) → S → ℝ` with `g_H = 0` satisfying
`g_h(s) ≤ e^{β r_h(s, a)} (u_h(s, a) + κ (p_h g_{h+1})(s, a))` at `a = π_h(s)`, the inequality
unrolls along the trajectory of `π` from `s₁` (`integral_exp_sum_mul_le_of_backward`,
`le_sum_integral_of_backward`):
`g_0(s₁) ≤ ∑_h κ^h E^π[e^{β ∑_{i ≤ h} r_i(S_i, A_i)} u_h(S_h, A_h)]`.

The main tool is `integral_exp_sum_mul_obs_succ`: for a weight `e^{c ∑_{j ≤ i} w_j(S_j, A_j)}`,
a function of the first `i + 1` rounds, `E[W g(S_{i+1})] = E[W (p_i g)(S_i, π_i(S_i))]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP
open scoped ENNReal

namespace Learning.MDP.Episodic

variable {S A : Type*} [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] {H : ℕ} (M : EpisodicMDP S A H)
  (π : Policy S A H) (s₁ : S)

/-! ### Weights along the trajectory -/

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Nonempty A] in
/-- A function on the finite set `Fin H × S × A` is bounded by the sum of its absolute values. -/
lemma abs_le_sum_abs (w : Fin H → S → A → ℝ) (j : Fin H) (s : S) (a : A) :
    |w j s a| ≤ ∑ j, ∑ s, ∑ a, |w j s a| :=
  calc |w j s a| ≤ ∑ a, |w j s a| :=
        single_le_sum (f := fun a ↦ |w j s a|) (fun _ _ ↦ abs_nonneg _) (mem_univ a)
    _ ≤ ∑ s, ∑ a, |w j s a| :=
        single_le_sum (f := fun s ↦ ∑ a, |w j s a|)
          (fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _) (mem_univ s)
    _ ≤ _ := single_le_sum (f := fun j ↦ ∑ s, ∑ a, |w j s a|)
          (fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _) (mem_univ j)

omit [Fintype S] [Fintype A] [MeasurableSingletonClass S] [MeasurableSingletonClass A]
  [Nonempty A] in
/-- `exp (c X) ≤ exp (|c| B)` when `|X| ≤ B`. -/
lemma exp_mul_le_exp_abs_mul {c X B : ℝ} (hX : |X| ≤ B) :
    Real.exp (c * X) ≤ Real.exp (|c| * B) := by
  refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left hX (abs_nonneg _)

omit [Fintype S] [Fintype A] [Nonempty A] in
/-- A function of the state-action pair of a round is measurable. -/
lemma measurable_comp_obs_action [Countable S] [Countable A] (f : S → A → ℝ) (i : ℕ) :
    Measurable fun x : ℕ → Round (LayerState S H) A ℝ ↦ f (IT.obs i x).1 (IT.action i x) :=
  (measurable_of_countable fun q : S × A ↦ f q.1 q.2).comp
    ((measurable_fst.comp (IT.measurable_obs i)).prodMk (IT.measurable_action i))

omit [Fintype S] [Fintype A] [Nonempty A] in
/-- `exp (c ∑_{i ∈ t} w_i(S_i, A_i)) f(S_j, A_j)` is integrable. -/
lemma integrable_exp_sum_mul [Finite S] [Finite A]
    (P : Measure (ℕ → Round (LayerState S H) A ℝ)) [IsFiniteMeasure P] (c : ℝ)
    (w : Fin H → S → A → ℝ) (t : Finset (Fin H)) (f : S → A → ℝ) (j : ℕ) :
    Integrable (fun x ↦ Real.exp (c * ∑ i ∈ t, w i (IT.obs i x).1 (IT.action i x))
      * f (IT.obs j x).1 (IT.action j x)) P := by
  have := Fintype.ofFinite S
  have := Fintype.ofFinite A
  refine Integrable.of_bound ((Real.measurable_exp.comp (measurable_const.mul
    (Finset.measurable_sum t fun i _ ↦ measurable_comp_obs_action (w i) i))).mul
    (measurable_comp_obs_action f j)).aestronglyMeasurable
    (Real.exp (|c| * ∑ _i ∈ t, ∑ j, ∑ s, ∑ a, |w j s a|)
      * ∑ s, ∑ a, |f s a|) (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul (exp_mul_le_exp_abs_mul ((abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun i _ ↦ abs_le_sum_abs w i _ _))) ?_ (abs_nonneg _) (Real.exp_pos _).le
  have := abs_le_sum_abs (fun (_ : Fin 1) s a ↦ f s a) 0 (IT.obs j x).1 (IT.action j x)
  simpa using this

/-- **The Markov property along the trajectory with a weight**: for the weight
`W = e^{c ∑_{j ≤ i} w_j(S_j, A_j)}`, a function of the first `i + 1` rounds,
`E^π[W g(S_{i+1})] = E^π[W (p_i g)(S_i, π_i(S_i))]`. -/
lemma integral_exp_sum_mul_obs_succ (c : ℝ) (w : Fin H → S → A → ℝ) (i : Fin H) (g : S → ℝ) :
    ∫ x, Real.exp (c * ∑ j ∈ Iic i, w j (IT.obs j x).1 (IT.action j x)) * g (IT.obs (i + 1) x).1
        ∂stepLaw M π (s₁, startStep H)
      = ∫ x, Real.exp (c * ∑ j ∈ Iic i, w j (IT.obs j x).1 (IT.action j x))
          * vecExp (M.transVec i (IT.obs i x).1 (π i (IT.obs i x).1)) g
          ∂stepLaw M π (s₁, startStep H) := by
  set Ψ : Hist (LayerState S H) A ℝ (i + 1) → ℝ := fun p ↦ Real.exp (c * ∑ j ∈ Iic i,
    if hj : (j : ℕ) < i + 1 then w j (p ⟨j, hj⟩).obs.1 (p ⟨j, hj⟩).action else 0) with hΨ
  have hΨeq (x : ℕ → Round (LayerState S H) A ℝ) : Ψ (IT.hist (i + 1) x)
      = Real.exp (c * ∑ j ∈ Iic i, w j (IT.obs j x).1 (IT.action j x)) := by
    simp only [hΨ]
    congr 2
    refine sum_congr rfl fun j hj ↦ ?_
    have hj' : (j : ℕ) < i + 1 := Nat.lt_succ_of_le (Fin.le_def.1 (mem_Iic.1 hj : j ≤ i))
    rw [dite_eq_left hj']
    rfl
  have hΨm : Measurable Ψ := by
    refine Real.measurable_exp.comp (measurable_const.mul (Finset.measurable_sum _ fun j _ ↦ ?_))
    by_cases hj : (j : ℕ) < i + 1
    · simp only [hj, dite_true]
      exact (measurable_of_countable fun q : S × A ↦ w j q.1 q.2).comp
        (((measurable_fst.comp Round.measurable_obs).prodMk Round.measurable_action).comp
          (measurable_pi_apply _))
    · simp only [hj, dite_false]
      exact measurable_const
  have hΨC : ∀ p, |Ψ p| ≤ Real.exp (|c| * ∑ _j ∈ Iic i, ∑ j, ∑ s, ∑ a, |w j s a|) := by
    intro p
    rw [abs_of_pos (Real.exp_pos _)]
    refine exp_mul_le_exp_abs_mul ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ ?_))
    split_ifs
    · exact abs_le_sum_abs w j _ _
    · rw [abs_zero]
      exact sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _
  have := integral_mul_obs_succ_stepLaw M π s₁ (h₀ := startStep H) (h := i) (k := i) (by simp)
    hΨm hΨC g
  simpa only [hΨeq] using this

/-! ### Unrolling -/

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Nonempty A] in
/-- The steps before the step `i` (as a state step). -/
lemma filter_castSucc_lt_castSucc (i : Fin H) :
    univ.filter (fun j : Fin H ↦ j.castSucc < i.castSucc) = Iio i := by
  ext j
  simp [Fin.castSucc_lt_castSucc_iff]

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Nonempty A] in
/-- The steps up to the step `i` (the steps before the state step `i + 1`). -/
lemma filter_castSucc_lt_succ (i : Fin H) :
    univ.filter (fun j : Fin H ↦ j.castSucc < i.succ) = Iic i := by
  ext j
  simp [Fin.castSucc_lt_succ_iff]

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Nonempty A] in
/-- The steps from the step `i` on are `i` and the steps from `i + 1` on. -/
lemma filter_castSucc_le_castSucc (i : Fin H) :
    univ.filter (fun j : Fin H ↦ i.castSucc ≤ j.castSucc)
      = insert i (univ.filter (fun j : Fin H ↦ i.succ ≤ j.castSucc)) := by
  ext j
  simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.castSucc_le_castSucc_iff,
    Fin.succ_le_castSucc_iff]
  exact le_iff_eq_or_lt.trans (or_congr eq_comm Iff.rfl)

variable {M π s₁}

/-- **Unrolling a backward recursive inequality along the trajectory**: if `g_H = 0` and
`g_h(s) ≤ e^{β r_h(s, π_h s)} (u_h(s, π_h s) + κ (p_h g_{h+1})(s, π_h s))` for all `h < H` and
`s`, then for every step `h ≤ H`, `E^π[e^{β ∑_{i < h} r_i(S_i, A_i)} g_h(S_h)]` is at most
`∑_{h ≤ h' < H} κ^{h' - h} E^π[e^{β ∑_{i ≤ h'} r_i(S_i, A_i)} u_{h'}(S_{h'}, A_{h'})]`. -/
lemma integral_exp_sum_mul_le_of_backward {β κ : ℝ} (hκ : 0 ≤ κ) {r u : Fin H → S → A → ℝ}
    {g : Fin (H + 1) → S → ℝ} (hlast : ∀ s, g (Fin.last H) s = 0)
    (hg : ∀ (h : Fin H) (s : S), g h.castSucc s ≤ Real.exp (β * r h s (π h s))
      * (u h s (π h s) + κ * vecExp (M.transVec h s (π h s)) (g h.succ)))
    (h : Fin (H + 1)) :
    ∫ x, Real.exp (β * ∑ i ∈ univ.filter (fun i : Fin H ↦ i.castSucc < h),
        r i (IT.obs i x).1 (IT.action i x)) * g h (IT.obs h x).1 ∂stepLaw M π (s₁, startStep H)
      ≤ ∑ h' ∈ univ.filter (fun h' : Fin H ↦ h ≤ h'.castSucc), κ ^ ((h' : ℕ) - h)
          * ∫ x, Real.exp (β * ∑ i ∈ Iic h', r i (IT.obs i x).1 (IT.action i x))
            * u h' (IT.obs h' x).1 (IT.action h' x) ∂stepLaw M π (s₁, startStep H) := by
  set P := stepLaw M π (s₁, startStep H)
  induction h using Fin.reverseInduction with
  | last =>
    simp [hlast]
  | cast i ih =>
    rw [filter_castSucc_lt_castSucc]
    rw [filter_castSucc_lt_succ] at ih
    set E : Fin H → ℝ := fun h' ↦ ∫ x, Real.exp (β * ∑ i ∈ Iic h',
      r i (IT.obs i x).1 (IT.action i x)) * u h' (IT.obs h' x).1 (IT.action h' x) ∂P with hE
    have hae := ae_action_eq_stepLaw M π s₁ (h₀ := startStep H) (h := i) (k := i) (by simp)
    have hIic (x : ℕ → Round (LayerState S H) A ℝ) :
        Real.exp (β * ∑ j ∈ Iio i, r j (IT.obs j x).1 (IT.action j x))
          * Real.exp (β * r i (IT.obs i x).1 (IT.action i x))
        = Real.exp (β * ∑ j ∈ Iic i, r j (IT.obs j x).1 (IT.action j x)) := by
      rw [← Real.exp_add, Iic_eq_cons_Iio, sum_cons]
      ring_nf
    calc ∫ x, Real.exp (β * ∑ j ∈ Iio i, r j (IT.obs j x).1 (IT.action j x))
          * g i.castSucc (IT.obs i x).1 ∂P
        ≤ ∫ x, Real.exp (β * ∑ j ∈ Iic i, r j (IT.obs j x).1 (IT.action j x))
          * u i (IT.obs i x).1 (IT.action i x)
          + κ * (Real.exp (β * ∑ j ∈ Iic i, r j (IT.obs j x).1 (IT.action j x))
            * vecExp (M.transVec i (IT.obs i x).1 (π i (IT.obs i x).1)) (g i.succ)) ∂P := by
          refine integral_mono_ae ?_ ?_ ?_
          · exact integrable_exp_sum_mul P β r _ (fun s _ ↦ g i.castSucc s) i
          · exact (integrable_exp_sum_mul P β r _ (u i) i).add ((integrable_exp_sum_mul P β r _
              (fun s _ ↦ vecExp (M.transVec i s (π i s)) (g i.succ)) i).const_mul κ)
          · filter_upwards [hae] with x hx
            rw [← hIic, hx]
            have := mul_le_mul_of_nonneg_left (hg i (IT.obs i x).1) (Real.exp_pos
              (β * ∑ j ∈ Iio i, r j (IT.obs j x).1 (IT.action j x))).le
            refine this.trans_eq ?_
            ring
      _ = E i + κ * ∫ x, Real.exp (β * ∑ j ∈ Iic i, r j (IT.obs j x).1 (IT.action j x))
            * g i.succ (IT.obs (i + 1) x).1 ∂P := by
          rw [integral_add (integrable_exp_sum_mul P β r _ (u i) i)
            ((integrable_exp_sum_mul P β r _
              (fun s _ ↦ vecExp (M.transVec i s (π i s)) (g i.succ)) i).const_mul κ),
            integral_const_mul, integral_exp_sum_mul_obs_succ]
      _ ≤ E i + κ * ∑ h' ∈ univ.filter (fun h' : Fin H ↦ i.succ ≤ h'.castSucc),
            κ ^ ((h' : ℕ) - i.succ) * E h' := by
          gcongr
          exact ih
      _ = _ := by
          rw [filter_castSucc_le_castSucc, sum_insert (by simp), mul_sum]
          simp only [Fin.val_castSucc, Nat.sub_self, pow_zero, one_mul]
          congr 1
          refine sum_congr rfl fun h' hh' ↦ ?_
          simp only [mem_filter, mem_univ, true_and, Fin.succ_le_castSucc_iff] at hh'
          have : (h' : ℕ) - i = ((h' : ℕ) - (i + 1)) + 1 := by
            have := Fin.lt_def.1 hh'
            omega
          rw [this, pow_succ, Fin.val_succ]
          ring
/-- **Unrolling a backward recursive inequality along the trajectory**, at the first step: if
`g_H = 0` and `g_h(s) ≤ e^{β r_h(s, π_h s)} (u_h(s, π_h s) + κ (p_h g_{h+1})(s, π_h s))` for all
`h < H` and `s`, then
`g_0(s₁) ≤ ∑_h κ^h E^π[e^{β ∑_{i ≤ h} r_i(S_i, A_i)} u_h(S_h, A_h)]`. -/
lemma le_sum_integral_of_backward {β κ : ℝ} (hκ : 0 ≤ κ) {r u : Fin H → S → A → ℝ}
    {g : Fin (H + 1) → S → ℝ} (hlast : ∀ s, g (Fin.last H) s = 0)
    (hg : ∀ (h : Fin H) (s : S), g h.castSucc s ≤ Real.exp (β * r h s (π h s))
      * (u h s (π h s) + κ * vecExp (M.transVec h s (π h s)) (g h.succ))) :
    g (startStep H) s₁ ≤ ∑ h : Fin H, κ ^ (h : ℕ)
      * ∫ x, Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x))
        * u h (IT.obs h x).1 (IT.action h x) ∂stepLaw M π (s₁, startStep H) := by
  have := integral_exp_sum_mul_le_of_backward (s₁ := s₁) hκ hlast hg (startStep H)
  have h1 : univ.filter (fun i : Fin H ↦ i.castSucc < startStep H) = ∅ := by
    ext i
    simp
  have h2 : univ.filter (fun h' : Fin H ↦ startStep H ≤ h'.castSucc) = univ := by
    ext i
    simp
  simp only [h1, h2, sum_empty, mul_zero, Real.exp_zero, one_mul] at this
  have hae := ae_obs_zero_stepLaw M π (s₁, startStep H)
  rw [integral_congr_ae (g := fun _ ↦ g (startStep H) s₁)] at this
  · simpa using this
  · filter_upwards [hae] with x hx
    rw [show (startStep H : ℕ) = 0 from rfl, hx]

end Learning.MDP.Episodic
