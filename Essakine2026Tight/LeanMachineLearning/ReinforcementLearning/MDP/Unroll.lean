/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Values
public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Occupancy

/-!
# Unrolling a backward recursive inequality along the trajectory

For a policy `π : ℕ → S → A` of a finite-horizon MDP `M` on finite state and action spaces,
measurable at every step, an initial state `s₁`, a horizon `H`, nonnegative *weights*
`w : ℕ → S → A → ℝ` with the cumulated weights `W_h = ∏_{i < h} w_i(S_i, A_i)` along the
trajectory, `κ ≥ 0` and functions `u : ℕ → S → A → ℝ`, `g : ℕ → S → ℝ` with `g_H = 0` satisfying,
for `h < H`,
`g_h(s) ≤ w_h(s, π_h s) (u_h(s, π_h s) + κ ∫ g_{h+1} dp_h(· | s, π_h s))`, the inequality unrolls
along the trajectory (`integral_prod_mul_le_of_backward`, `le_sum_integral_of_backward`):
`g_0(s₁) ≤ ∑_{h < H} κ^h E^π[W_{h+1} u_h(S_h, A_h)]`.

The exponential weights `w_i = e^{β r_i}` of the entropic analysis give
`W_h = e^{β ∑_{i < h} r_i(S_i, A_i)}` (`prod_exp_eq_exp_sum`), for which the unrolling is
`le_sum_integral_of_backward_exp`.

The main tool is `integral_prod_mul_obs_succ`: for the weight `W_{i+1}`, a function of the first
`i + 1` rounds, `E[W_{i+1} g(S_{i+1})] = E[W_{i+1} (p_i g)(S_i, π_i(S_i))]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP
open scoped ENNReal

namespace Learning.MDP.Episodic

variable {S A : Type*} [Finite S] [Finite A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] (M : EpisodicMDP S A) {π : ℕ → S → A}
  (hπ : ∀ h, Measurable (π h)) (s₁ : S)

/-! ### Weights along the trajectory -/

omit [Finite S] [Finite A] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- A function on the finite set `{j < n} × S × A` is bounded by the sum of its absolute
values. -/
lemma abs_le_sum_abs [Fintype S] [Fintype A] (w : ℕ → S → A → ℝ) {n j : ℕ} (hj : j < n) (s : S)
    (a : A) : |w j s a| ≤ ∑ j ∈ range n, ∑ s, ∑ a, |w j s a| :=
  calc |w j s a| ≤ ∑ a, |w j s a| :=
        single_le_sum (f := fun a ↦ |w j s a|) (fun _ _ ↦ abs_nonneg _) (mem_univ a)
    _ ≤ ∑ s, ∑ a, |w j s a| :=
        single_le_sum (f := fun s ↦ ∑ a, |w j s a|)
          (fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _) (mem_univ s)
    _ ≤ _ := single_le_sum (f := fun j ↦ ∑ s, ∑ a, |w j s a|)
          (fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _) (mem_range.2 hj)

omit [Finite S] [Finite A] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- A function on the finite set `S × A` is bounded by the sum of its absolute values. -/
lemma abs_le_sum_abs' [Fintype S] [Fintype A] (f : S → A → ℝ) (s : S) (a : A) :
    |f s a| ≤ ∑ s, ∑ a, |f s a| := by
  simpa using abs_le_sum_abs (fun _ ↦ f) (Nat.lt_succ_self 0) s a

/-- A function of the state-action pair of a round is measurable. -/
lemma measurable_comp_obs_action (f : S → A → ℝ) (i : ℕ) :
    Measurable fun x : ℕ → Round (S × ℕ) A ℝ ↦ f (IT.obs i x).1 (IT.action i x) :=
  (measurable_of_countable fun q : S × A ↦ f q.1 q.2).comp (measurable_stateAction i)

/-- The cumulated weight `∏_{i ∈ t} w_i(S_i, A_i)` is measurable. -/
lemma measurable_prod_comp_obs_action (w : ℕ → S → A → ℝ) (t : Finset ℕ) :
    Measurable fun x : ℕ → Round (S × ℕ) A ℝ ↦ ∏ i ∈ t, w i (IT.obs i x).1 (IT.action i x) :=
  Finset.measurable_prod _ fun i _ ↦ measurable_comp_obs_action (w i) i

omit [Finite S] [Finite A] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- The cumulated weight `∏_{i ∈ t} w_i(S_i, A_i)` is bounded. -/
lemma abs_prod_comp_obs_action_le [Fintype S] [Fintype A] (w : ℕ → S → A → ℝ) (t : Finset ℕ)
    (x : ℕ → Round (S × ℕ) A ℝ) :
    |∏ i ∈ t, w i (IT.obs i x).1 (IT.action i x)| ≤ ∏ i ∈ t, ∑ s, ∑ a, |w i s a| := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) fun i _ ↦ abs_le_sum_abs' (w i) _ _

/-- `(∏_{i ∈ t} w_i(S_i, A_i)) f(S_j, A_j)` is integrable under a finite measure. -/
lemma integrable_prod_mul (P : Measure (ℕ → Round (S × ℕ) A ℝ)) [IsFiniteMeasure P]
    (w : ℕ → S → A → ℝ) (t : Finset ℕ) (f : S → A → ℝ) (j : ℕ) :
    Integrable (fun x ↦ (∏ i ∈ t, w i (IT.obs i x).1 (IT.action i x))
      * f (IT.obs j x).1 (IT.action j x)) P := by
  have := Fintype.ofFinite S
  have := Fintype.ofFinite A
  refine Integrable.of_bound ((measurable_prod_comp_obs_action w t).mul
    (measurable_comp_obs_action f j)).aestronglyMeasurable
    ((∏ i ∈ t, ∑ s, ∑ a, |w i s a|) * ∑ s, ∑ a, |f s a|) (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (abs_prod_comp_obs_action_le w t x) (abs_le_sum_abs' f _ _) (abs_nonneg _)
    (prod_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _)

/-- A function of the state-action pair of a round is integrable under a finite measure. -/
lemma integrable_comp_obs_action (P : Measure (ℕ → Round (S × ℕ) A ℝ)) [IsFiniteMeasure P]
    (f : S → A → ℝ) (j : ℕ) :
    Integrable (fun x ↦ f (IT.obs j x).1 (IT.action j x)) P := by
  simpa using integrable_prod_mul P (fun _ _ _ ↦ (1 : ℝ)) ∅ f j

omit [Finite S] [Finite A] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- The exponential weights `e^{β r_i}` cumulate into `e^{β ∑_i r_i}`. -/
lemma prod_exp_eq_exp_sum (β : ℝ) (r : ℕ → S → A → ℝ) (t : Finset ℕ)
    (x : ℕ → Round (S × ℕ) A ℝ) :
    ∏ i ∈ t, Real.exp (β * r i (IT.obs i x).1 (IT.action i x))
      = Real.exp (β * ∑ i ∈ t, r i (IT.obs i x).1 (IT.action i x)) := by
  rw [mul_sum, Real.exp_sum]

/-- `e^{β ∑_{i ∈ t} r_i(S_i, A_i)} f(S_j, A_j)` is integrable under a finite measure. -/
lemma integrable_exp_sum_mul (P : Measure (ℕ → Round (S × ℕ) A ℝ)) [IsFiniteMeasure P] (β : ℝ)
    (r : ℕ → S → A → ℝ) (t : Finset ℕ) (f : S → A → ℝ) (j : ℕ) :
    Integrable (fun x ↦ Real.exp (β * ∑ i ∈ t, r i (IT.obs i x).1 (IT.action i x))
      * f (IT.obs j x).1 (IT.action j x)) P := by
  simpa only [prod_exp_eq_exp_sum] using
    integrable_prod_mul P (fun i s a ↦ Real.exp (β * r i s a)) t f j

include hπ in
/-- **The Markov property along the trajectory with a weight**: for the cumulated weight
`W_{i+1} = ∏_{j ≤ i} w_j(S_j, A_j)`, a function of the first `i + 1` rounds,
`E^π[W_{i+1} g(S_{i+1})] = E^π[W_{i+1} (p_i g)(S_i, π_i(S_i))]`. -/
lemma integral_prod_mul_obs_succ (w : ℕ → S → A → ℝ) (i : ℕ) (g : S → ℝ) :
    ∫ x, (∏ j ∈ range (i + 1), w j (IT.obs j x).1 (IT.action j x)) * g (IT.obs (i + 1) x).1
        ∂stepLaw M π (s₁, 0)
      = ∫ x, (∏ j ∈ range (i + 1), w j (IT.obs j x).1 (IT.action j x))
          * ∫ s', g s' ∂M.trans i ((IT.obs i x).1, π i (IT.obs i x).1) ∂stepLaw M π (s₁, 0) := by
  have := Fintype.ofFinite S
  have := Fintype.ofFinite A
  set Ψ : Hist (S × ℕ) A ℝ (i + 1) → ℝ :=
    fun p ↦ ∏ j : Fin (i + 1), w j (p j).obs.1 (p j).action with hΨ
  have hΨeq (x : ℕ → Round (S × ℕ) A ℝ) :
      Ψ (IT.hist (i + 1) x) = ∏ j ∈ range (i + 1), w j (IT.obs j x).1 (IT.action j x) := by
    simp only [hΨ]
    rw [← Fin.prod_univ_eq_prod_range (fun j ↦ w j (IT.obs j x).1 (IT.action j x)) (i + 1)]
    rfl
  have hΨm : Measurable Ψ :=
    Finset.measurable_prod _ fun j _ ↦
      (measurable_of_countable fun q : S × A ↦ w j q.1 q.2).comp
        (((measurable_fst.comp Round.measurable_obs).prodMk Round.measurable_action).comp
          (measurable_pi_apply _))
  have hΨC : ∀ p, |Ψ p| ≤ ∏ j ∈ range (i + 1), ∑ s, ∑ a, |w j s a| := by
    intro p
    simp only [hΨ]
    rw [Finset.abs_prod, ← Fin.prod_univ_eq_prod_range (fun j ↦ ∑ s, ∑ a, |w j s a|) (i + 1)]
    exact Finset.prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) fun j _ ↦ abs_le_sum_abs' (w j) _ _
  have := integral_mul_obs_succ_stepLaw M hπ s₁ 0 i hΨm hΨC (measurable_of_countable g)
    (D := ∑ s, |g s|) fun s' ↦ single_le_sum (f := fun s ↦ |g s|) (fun _ _ ↦ abs_nonneg _)
      (mem_univ s')
  simp only [Nat.zero_add, hΨeq] at this
  exact this

include hπ in
/-- The Markov property along the trajectory with the exponential weight
`e^{β ∑_{j ≤ i} r_j(S_j, A_j)}`. -/
lemma integral_exp_sum_mul_obs_succ (β : ℝ) (r : ℕ → S → A → ℝ) (i : ℕ) (g : S → ℝ) :
    ∫ x, Real.exp (β * ∑ j ∈ range (i + 1), r j (IT.obs j x).1 (IT.action j x))
        * g (IT.obs (i + 1) x).1 ∂stepLaw M π (s₁, 0)
      = ∫ x, Real.exp (β * ∑ j ∈ range (i + 1), r j (IT.obs j x).1 (IT.action j x))
          * ∫ s', g s' ∂M.trans i ((IT.obs i x).1, π i (IT.obs i x).1) ∂stepLaw M π (s₁, 0) := by
  have := integral_prod_mul_obs_succ M hπ s₁ (fun j s a ↦ Real.exp (β * r j s a)) i g
  simpa only [prod_exp_eq_exp_sum] using this

/-! ### Unrolling -/

variable {M s₁}

include hπ

/-- **Unrolling a backward recursive inequality along the trajectory**: if `g_H = 0` and
`g_h(s) ≤ w_h(s, π_h s) (u_h(s, π_h s) + κ (p_h g_{h+1})(s, π_h s))` for all `h < H` and `s`, then
for every step `h ≤ H`, `E^π[W_h g_h(S_h)]` is at most
`∑_{h ≤ h' < H} κ^{h' - h} E^π[W_{h'+1} u_{h'}(S_{h'}, A_{h'})]`, where
`W_h = ∏_{i < h} w_i(S_i, A_i)` are the cumulated weights. -/
lemma integral_prod_mul_le_of_backward {κ : ℝ} (hκ : 0 ≤ κ) {w u : ℕ → S → A → ℝ}
    (hw : ∀ i s a, 0 ≤ w i s a) {g : ℕ → S → ℝ} {H : ℕ} (hlast : ∀ s, g H s = 0)
    (hg : ∀ h < H, ∀ s, g h s ≤ w h s (π h s)
      * (u h s (π h s) + κ * ∫ s', g (h + 1) s' ∂M.trans h (s, π h s))) :
    ∀ h ≤ H, ∫ x, (∏ i ∈ range h, w i (IT.obs i x).1 (IT.action i x)) * g h (IT.obs h x).1
        ∂stepLaw M π (s₁, 0)
      ≤ ∑ h' ∈ Ico h H, κ ^ (h' - h)
          * ∫ x, (∏ i ∈ range (h' + 1), w i (IT.obs i x).1 (IT.action i x))
            * u h' (IT.obs h' x).1 (IT.action h' x) ∂stepLaw M π (s₁, 0) := by
  set P := stepLaw M π (s₁, 0)
  set E : ℕ → ℝ := fun h' ↦ ∫ x, (∏ i ∈ range (h' + 1), w i (IT.obs i x).1 (IT.action i x))
    * u h' (IT.obs h' x).1 (IT.action h' x) ∂P with hE
  refine horizon_induction H (P := fun h ↦ h ≤ H → _) ?_ ?_
  · intro h hHh hhH
    obtain rfl : h = H := le_antisymm hhH hHh
    simp [hlast]
  · intro h hh ih _
    have ih := ih (by omega)
    have hae := ae_action_eq_stepLaw M hπ s₁ 0 h
    simp only [Nat.zero_add] at hae
    have hW (x : ℕ → Round (S × ℕ) A ℝ) : 0 ≤ ∏ i ∈ range h, w i (IT.obs i x).1 (IT.action i x) :=
      prod_nonneg fun _ _ ↦ hw _ _ _
    calc ∫ x, (∏ i ∈ range h, w i (IT.obs i x).1 (IT.action i x)) * g h (IT.obs h x).1 ∂P
        ≤ ∫ x, (∏ i ∈ range (h + 1), w i (IT.obs i x).1 (IT.action i x))
            * u h (IT.obs h x).1 (IT.action h x)
          + κ * ((∏ i ∈ range (h + 1), w i (IT.obs i x).1 (IT.action i x))
            * ∫ s', g (h + 1) s' ∂M.trans h ((IT.obs h x).1, π h (IT.obs h x).1)) ∂P := by
          refine integral_mono_ae ?_ ?_ ?_
          · exact integrable_prod_mul P w _ (fun s _ ↦ g h s) h
          · exact (integrable_prod_mul P w _ (u h) h).add ((integrable_prod_mul P w _
              (fun s _ ↦ ∫ s', g (h + 1) s' ∂M.trans h (s, π h s)) h).const_mul κ)
          · filter_upwards [hae] with x hx
            rw [prod_range_succ, hx]
            have := mul_le_mul_of_nonneg_left (hg h hh (IT.obs h x).1) (hW x)
            refine this.trans_eq ?_
            ring
      _ = E h + κ * ∫ x, (∏ i ∈ range (h + 1), w i (IT.obs i x).1 (IT.action i x))
            * g (h + 1) (IT.obs (h + 1) x).1 ∂P := by
          rw [integral_add (integrable_prod_mul P w _ (u h) h)
            ((integrable_prod_mul P w _
              (fun s _ ↦ ∫ s', g (h + 1) s' ∂M.trans h (s, π h s)) h).const_mul κ),
            integral_const_mul, integral_prod_mul_obs_succ M hπ]
      _ ≤ E h + κ * ∑ h' ∈ Ico (h + 1) H, κ ^ (h' - (h + 1)) * E h' := by
          gcongr
      _ = _ := by
          rw [sum_eq_sum_Ico_succ_bot hh, Nat.sub_self, pow_zero, one_mul, mul_sum]
          congr 1
          refine sum_congr rfl fun h' hh' ↦ ?_
          have : h' - h = (h' - (h + 1)) + 1 := by
            have := (mem_Ico.1 hh').1
            omega
          rw [this, pow_succ]
          ring

/-- **Unrolling a backward recursive inequality along the trajectory**, at the first step: if
`g_H = 0` and `g_h(s) ≤ w_h(s, π_h s) (u_h(s, π_h s) + κ (p_h g_{h+1})(s, π_h s))` for all `h < H`
and `s`, then `g_0(s₁) ≤ ∑_{h < H} κ^h E^π[W_{h+1} u_h(S_h, A_h)]`. -/
lemma le_sum_integral_of_backward {κ : ℝ} (hκ : 0 ≤ κ) {w u : ℕ → S → A → ℝ}
    (hw : ∀ i s a, 0 ≤ w i s a) {g : ℕ → S → ℝ} {H : ℕ} (hlast : ∀ s, g H s = 0)
    (hg : ∀ h < H, ∀ s, g h s ≤ w h s (π h s)
      * (u h s (π h s) + κ * ∫ s', g (h + 1) s' ∂M.trans h (s, π h s))) :
    g 0 s₁ ≤ ∑ h ∈ range H, κ ^ h
      * ∫ x, (∏ i ∈ range (h + 1), w i (IT.obs i x).1 (IT.action i x))
        * u h (IT.obs h x).1 (IT.action h x) ∂stepLaw M π (s₁, 0) := by
  have := isProbabilityMeasure_stepLaw M hπ (s₁, 0)
  have := integral_prod_mul_le_of_backward hπ (s₁ := s₁) hκ hw hlast hg 0 (Nat.zero_le H)
  simp only [range_zero, prod_empty, one_mul, Nat.sub_zero, ← range_eq_Ico] at this
  rw [integral_congr_ae (g := fun _ ↦ g 0 s₁)] at this
  · simpa using this
  · filter_upwards [ae_obs_zero_stepLaw M hπ (s₁, 0)] with x hx
    rw [hx]

/-- **Unrolling with exponential weights**: if `g_H = 0` and
`g_h(s) ≤ e^{β r_h(s, π_h s)} (u_h(s, π_h s) + κ (p_h g_{h+1})(s, π_h s))` for all `h < H` and `s`,
then `g_0(s₁) ≤ ∑_{h < H} κ^h E^π[e^{β ∑_{i ≤ h} r_i(S_i, A_i)} u_h(S_h, A_h)]`. -/
lemma le_sum_integral_of_backward_exp {β κ : ℝ} (hκ : 0 ≤ κ) {r u : ℕ → S → A → ℝ}
    {g : ℕ → S → ℝ} {H : ℕ} (hlast : ∀ s, g H s = 0)
    (hg : ∀ h < H, ∀ s, g h s ≤ Real.exp (β * r h s (π h s))
      * (u h s (π h s) + κ * ∫ s', g (h + 1) s' ∂M.trans h (s, π h s))) :
    g 0 s₁ ≤ ∑ h ∈ range H, κ ^ h
      * ∫ x, Real.exp (β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
        * u h (IT.obs h x).1 (IT.action h x) ∂stepLaw M π (s₁, 0) := by
  have := le_sum_integral_of_backward hπ (s₁ := s₁) (w := fun j s a ↦ Real.exp (β * r j s a)) hκ
    (fun _ _ _ ↦ (Real.exp_pos _).le) hlast hg
  simpa only [prod_exp_eq_exp_sum] using this

end Learning.MDP.Episodic
