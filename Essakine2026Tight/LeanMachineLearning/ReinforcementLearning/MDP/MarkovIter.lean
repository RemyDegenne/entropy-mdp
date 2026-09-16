/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.StepLaw
public import Essakine2026Tight.LeanMachineLearning.ReinforcementLearning.MDP.Values
public import Essakine2026Tight.Mathlib.Probability.CondDistrib
public import Essakine2026Tight.Mathlib.Probability.HasCondDistribIntegral

/-!
# The iterated Markov property of the trajectory laws of a finite-horizon MDP

For a finite-horizon MDP `M`, a policy `π` and a trajectory law `stepLaw M π (s, h₀)` started at
the state `s` at the step `h₀`, and for `k` rounds with `h₀ + k = j ≤ H`:

* **iterated Markov property** (`hasCondDistrib_shiftRounds_stepLaw`, Lebesgue integral form
  `lintegral_stepLaw_hist_shiftRounds`): the trajectory shifted by `k` rounds has conditional
  law `stepLaw M π (s', j)` given the first `k` rounds and the state `s'` of the round `k`;
* consequences for the round `k`: its layer is `j` (`ae_obs_eq_stepLaw`), its action is
  `π j (S_k)` (`ae_action_eq_stepLaw`) and, for an MDP with a reward function `r`, its reward
  is `r j (S_k) (A_k)` (`ae_feedback_eq_stepLaw`), almost surely;
* the reward of the round `k` and the state of the round `k + 1` have conditional law
  `R_j(· | S_k, π_j(S_k)) ⊗ p_j(· | S_k, π_j(S_k))` given the first `k` rounds and `S_k`
  (`hasCondDistrib_feedback_obs_succ_stepLaw`), and the state of the round `k + 1` has
  conditional law `p_j(· | S_k, π_j(S_k))` given the first `k + 1` rounds
  (`hasCondDistrib_obs_succ_hist_stepLaw`), in integral form
  `E[Ψ g(S_{k+1})] = E[Ψ (p_j g)(S_k, π_j(S_k))]` (`integral_mul_obs_succ_stepLaw`);
* in the episode environment (`statesEnv`), the state of the step `h + 1` of the episode `t` has
  conditional law `p_h(· | s_h, π_h(s_h))` given the history of the first `t` episodes, the policy
  `π` of the episode `t` and its states `s_0, …, s_h` (`hasCondDistrib_feedback_succ_statesEnv`).

The paper's step `i ≥ h₀` of a trajectory started at the step `h₀` is the round `i - h₀`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP
open scoped ENNReal

namespace Learning.MDP

variable {𝓢 𝓐 𝓡 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓡 : MeasurableSpace 𝓡}

/-! ### Shifts and prefixes of trajectories -/

/-- The shift of a trajectory by `k` rounds. -/
def shiftRounds (k : ℕ) (x : ℕ → Round 𝓢 𝓐 𝓡) (n : ℕ) : Round 𝓢 𝓐 𝓡 := x (n + k)

/-- The shift by `k` rounds is measurable. -/
@[fun_prop]
lemma measurable_shiftRounds (k : ℕ) : Measurable (shiftRounds (𝓢 := 𝓢) (𝓐 := 𝓐) (𝓡 := 𝓡) k) :=
  Measurable.of_eval fun _ ↦ measurable_pi_apply _

/-- Shifting by `0` rounds does nothing. -/
@[simp] lemma shiftRounds_zero (x : ℕ → Round 𝓢 𝓐 𝓡) : shiftRounds 0 x = x := rfl

/-- Shifting by `k + 1` rounds is shifting by one round, then by `k` rounds. -/
lemma shiftRounds_succ (k : ℕ) (x : ℕ → Round 𝓢 𝓐 𝓡) :
    shiftRounds (k + 1) x = shiftRounds k (shiftRound x) := rfl

/-- The first `k + 1` rounds are the first round followed by the first `k` rounds of the shifted
trajectory. -/
lemma hist_succ_eq_cons (k : ℕ) (x : ℕ → Round 𝓢 𝓐 𝓡) :
    IT.hist (k + 1) x = Fin.cons (x 0) (IT.hist k (shiftRound x)) := by
  funext i
  refine Fin.cases rfl (fun j ↦ ?_) i
  simp [IT.hist, shiftRound]

omit m𝓢 m𝓐 m𝓡 in
/-- `Fin.cons` is measurable. -/
lemma measurable_finCons {X : Type*} {mX : MeasurableSpace X} {n : ℕ} :
    Measurable fun p : X × (Fin n → X) ↦ (Fin.cons p.1 p.2 : Fin (n + 1) → X) := by
  refine measurable_pi_iff.2 fun i ↦ ?_
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa using measurable_fst
  · simp only [Fin.cons_succ]
    exact (measurable_pi_apply j).comp measurable_snd

omit m𝓢 m𝓐 m𝓡 in
/-- `Fin.snoc` is measurable. -/
lemma measurable_finSnoc {X : Type*} {mX : MeasurableSpace X} {n : ℕ} :
    Measurable fun p : (Fin n → X) × X ↦ (Fin.snoc p.1 p.2 : Fin (n + 1) → X) := by
  refine measurable_pi_iff.2 fun i ↦ ?_
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [Fin.snoc_last]
    exact measurable_snd
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp measurable_fst

/-- The first `k + 1` rounds are the first `k` rounds followed by the round `k`. -/
lemma hist_succ_eq_snoc (k : ℕ) (x : ℕ → Round 𝓢 𝓐 𝓡) :
    IT.hist (k + 1) x = Fin.snoc (IT.hist k x) (shiftRounds k x 0) := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [IT.hist, shiftRounds]
  · simp [IT.hist]

end Learning.MDP

namespace Learning.MDP.Episodic

variable {S A : Type*} [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A] {H : ℕ} (M : EpisodicMDP S A H)
  (π : Policy S A H)

local notation "Traj'" => ℕ → Round (LayerState S H) A ℝ

/-! ### The iterated Markov property -/

/-- The first round of a trajectory started at a non-terminal step. -/
lemma ae_round_zero_stepLaw_castSucc (h : Fin H) (s : S) :
    ∀ᵐ x ∂stepLaw M π (s, h.castSucc), x 0 = ((s, h.castSucc), π h s, IT.feedback 0 x) := by
  filter_upwards [ae_obs_zero_stepLaw M π (s, h.castSucc),
    ae_action_zero_stepLaw M π (s, h.castSucc)] with x h0 h1
  rw [Policy.layer_castSucc] at h1
  exact Prod.ext h0 (Prod.ext h1 rfl)

/-- **Iterated Markov property**, Lebesgue integral form: for a trajectory started at `(s, h₀)` and
`h₀ + k = j`, integrating a function of (the first `k` rounds, the state `S_k` of the round `k`,
the trajectory shifted by `k` rounds) amounts to integrating the shifted trajectory against
`stepLaw M π (S_k, j)`. -/
lemma lintegral_stepLaw_hist_shiftRounds (k : ℕ) :
    ∀ (s : S) (h₀ j : Fin (H + 1)) (_ : (h₀ : ℕ) + k = j)
      (f : Hist (LayerState S H) A ℝ k × S × Traj' → ℝ≥0∞), Measurable f →
    ∫⁻ x, f (IT.hist k x, (IT.obs k x).1, shiftRounds k x) ∂stepLaw M π (s, h₀)
      = ∫⁻ x, ∫⁻ y, f (IT.hist k x, (IT.obs k x).1, y) ∂stepLaw M π ((IT.obs k x).1, j)
          ∂stepLaw M π (s, h₀) := by
  induction k with
  | zero =>
    intro s h₀ j hk f hf
    have hj : h₀ = j := Fin.ext (by simpa using hk)
    subst hj
    have hae : ∀ᵐ x ∂stepLaw M π (s, h₀), (IT.obs 0 x).1 = s := by
      filter_upwards [ae_obs_zero_stepLaw M π (s, h₀)] with x hx
      rw [hx]
    calc ∫⁻ x, f (IT.hist 0 x, (IT.obs 0 x).1, shiftRounds 0 x) ∂stepLaw M π (s, h₀)
        = ∫⁻ x, f (default, s, x) ∂stepLaw M π (s, h₀) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with x hx
          rw [hx, Unique.eq_default (IT.hist 0 x), shiftRounds_zero]
      _ = ∫⁻ x, ∫⁻ y, f (default, s, y) ∂stepLaw M π (s, h₀) ∂stepLaw M π (s, h₀) := by
          rw [lintegral_const, measure_univ, mul_one]
      _ = _ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with x hx
          rw [hx, Unique.eq_default (IT.hist 0 x)]
  | succ k ih =>
    intro s h₀ j hk f hf
    obtain ⟨h, rfl⟩ : ∃ h : Fin H, h.castSucc = h₀ :=
      ⟨⟨h₀, by have := j.is_lt; omega⟩, Fin.ext rfl⟩
    have hk' : (h.succ : ℕ) + k = j := by simp only [Fin.val_succ]; simp at hk; omega
    set r0 : ℝ → Round (LayerState S H) A ℝ := fun r ↦ ((s, h.castSucc), π h s, r) with hr0
    have hr0m : Measurable r0 := by fun_prop
    have hae : ∀ᵐ x ∂stepLaw M π (s, h.castSucc), IT.hist (k + 1) x
        = Fin.cons (r0 (IT.feedback 0 x)) (IT.hist k (shiftRound x)) := by
      filter_upwards [ae_round_zero_stepLaw_castSucc M π h s] with x hx
      rw [hist_succ_eq_cons, hx]
    -- the integrand of the right-hand side
    set G : Hist (LayerState S H) A ℝ (k + 1) × S → ℝ≥0∞ :=
      fun p ↦ ∫⁻ z, f (p.1, p.2, z) ∂stepLaw M π (p.2, j) with hG
    have hGm : Measurable G :=
      Measurable.lintegral_kernel_prod_right'
        (κ := Kernel.prodMkLeft (Hist (LayerState S H) A ℝ (k + 1)) (stepLawKernel M π j))
        (f := fun q ↦ f (q.1.1, q.1.2, q.2)) (by fun_prop)
    have hcons : Measurable fun q : (ℝ × S) × Traj' ↦
        (Fin.cons (r0 q.1.1) (IT.hist k q.2) : Hist (LayerState S H) A ℝ (k + 1)) :=
      measurable_finCons.comp ((hr0m.comp measurable_fst.fst).prodMk
        ((IT.measurable_hist k).comp measurable_snd))
    have hcons' (r : ℝ) : Measurable fun p : Hist (LayerState S H) A ℝ k ↦
        (Fin.cons (r0 r) p : Hist (LayerState S H) A ℝ (k + 1)) :=
      measurable_finCons.comp (measurable_const.prodMk measurable_id)
    calc ∫⁻ x, f (IT.hist (k + 1) x, (IT.obs (k + 1) x).1, shiftRounds (k + 1) x)
          ∂stepLaw M π (s, h.castSucc)
        = ∫⁻ x, (fun q : (ℝ × S) × Traj' ↦ f (Fin.cons (r0 q.1.1) (IT.hist k q.2),
            (IT.obs k q.2).1, shiftRounds k q.2)) ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x)
            ∂stepLaw M π (s, h.castSucc) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with x hx
          simp only [hx]
          rfl
      _ = ∫⁻ q, ∫⁻ y, f (Fin.cons (r0 q.1) (IT.hist k y), (IT.obs k y).1, shiftRounds k y)
            ∂stepLaw M π (q.2, h.succ) ∂((M.reward h (s, π h s)).prod (M.trans h (s, π h s))) :=
          lintegral_stepLaw_castSucc M π h s (hf.comp (hcons.prodMk
            ((measurable_fst.comp ((IT.measurable_obs k).comp measurable_snd)).prodMk
              ((measurable_shiftRounds k).comp measurable_snd))))
      _ = ∫⁻ q, ∫⁻ y, G (Fin.cons (r0 q.1) (IT.hist k y), (IT.obs k y).1)
            ∂stepLaw M π (q.2, h.succ) ∂((M.reward h (s, π h s)).prod (M.trans h (s, π h s))) := by
          refine lintegral_congr fun q ↦ ?_
          exact ih q.2 h.succ j hk' (fun p ↦ f (Fin.cons (r0 q.1) p.1, p.2.1, p.2.2))
            (hf.comp (((hcons' q.1).comp measurable_fst).prodMk measurable_snd))
      _ = ∫⁻ x, (fun q : (ℝ × S) × Traj' ↦ G (Fin.cons (r0 q.1.1) (IT.hist k q.2),
            (IT.obs k q.2).1)) ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x)
            ∂stepLaw M π (s, h.castSucc) :=
          (lintegral_stepLaw_castSucc M π h s (hGm.comp (hcons.prodMk
            (measurable_fst.comp ((IT.measurable_obs k).comp measurable_snd))))).symm
      _ = _ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with x hx
          simp only [hx]
          rfl

/-- **Iterated Markov property**: under `stepLaw M π (s, h₀)`, the trajectory shifted by `k`
rounds has conditional law `stepLaw M π (s', j)` given the first `k` rounds and the state `s'` of
the round `k`, where `j = h₀ + k`. -/
lemma hasCondDistrib_shiftRounds_stepLaw (s : S) {h₀ j : Fin (H + 1)} {k : ℕ}
    (hk : (h₀ : ℕ) + k = j) :
    HasCondDistrib (shiftRounds k) (fun x ↦ (IT.hist k x, (IT.obs k x).1))
      (Kernel.prodMkLeft (Hist (LayerState S H) A ℝ k) (stepLawKernel M π j))
      (stepLaw M π (s, h₀)) := by
  refine hasCondDistrib_of_lintegral_eq (by fun_prop) (by fun_prop) fun f hf ↦ ?_
  exact lintegral_stepLaw_hist_shiftRounds M π k s h₀ j hk (fun q ↦ f ((q.1, q.2.1), q.2.2))
    (by fun_prop)

/-- Almost sure properties of the rounds from `k` on, given the first `k` rounds. -/
lemma ae_stepLaw_of_ae_shiftRounds (s : S) {h₀ j : Fin (H + 1)} {k : ℕ}
    (hk : (h₀ : ℕ) + k = j)
    {P : Hist (LayerState S H) A ℝ k → S → Traj' → Prop}
    (hP : MeasurableSet {z : (Hist (LayerState S H) A ℝ k × S) × Traj' | P z.1.1 z.1.2 z.2})
    (hae : ∀ p s', ∀ᵐ y ∂stepLaw M π (s', j), P p s' y) :
    ∀ᵐ x ∂stepLaw M π (s, h₀), P (IT.hist k x) (IT.obs k x).1 (shiftRounds k x) := by
  have hlaw := hasCondDistrib_shiftRounds_stepLaw M π s hk
  refine ae_of_ae_map (p := fun z : (Hist (LayerState S H) A ℝ k × S) × Traj' ↦
    P z.1.1 z.1.2 z.2) hlaw.aemeasurable ?_
  rw [hlaw.map_eq]
  exact Measure.ae_compProd_of_ae_ae hP (Filter.Eventually.of_forall fun q ↦ hae q.1 q.2)

/-- The layer of the round `k` of a trajectory started at the step `h₀` is `h₀ + k`. -/
lemma ae_obs_eq_stepLaw (s : S) {h₀ j : Fin (H + 1)} {k : ℕ} (hk : (h₀ : ℕ) + k = j) :
    ∀ᵐ x ∂stepLaw M π (s, h₀), IT.obs k x = ((IT.obs k x).1, j) := by
  have := ae_stepLaw_of_ae_shiftRounds M π s hk
    (P := fun _ s' y ↦ IT.obs 0 y = (s', j)) (measurableSet_eq_fun (by fun_prop) (by fun_prop))
    (fun _ s' ↦ ae_obs_zero_stepLaw M π (s', j))
  filter_upwards [this] with x hx
  simpa [shiftRounds, IT.obs] using hx

/-- The action of the round `k` of a trajectory started at the step `h₀` is the action of the
policy at the step `h₀ + k`. -/
lemma ae_action_eq_stepLaw (s : S) {h₀ : Fin (H + 1)} {h : Fin H} {k : ℕ}
    (hk : (h₀ : ℕ) + k = h) :
    ∀ᵐ x ∂stepLaw M π (s, h₀), IT.action k x = π h (IT.obs k x).1 := by
  have := ae_stepLaw_of_ae_shiftRounds M π s (j := h.castSucc) hk
    (P := fun _ s' y ↦ IT.action 0 y = π h s') (measurableSet_eq_fun (by fun_prop) (by fun_prop))
    (fun _ s' ↦ by simpa [Policy.layer_castSucc] using ae_action_zero_stepLaw M π (s', h.castSucc))
  filter_upwards [this, ae_obs_eq_stepLaw M π s (j := h.castSucc) hk] with x hx hx'
  simpa [shiftRounds, IT.action] using hx

/-! ### The next state -/

omit [Fintype S] [Fintype A] [MeasurableSingletonClass A] [Nonempty A] in
/-- The last state of a history and the action of `π` at the step `h` in that state. -/
lemma measurable_lastState_policy [Countable S] (h : Fin H) (k : ℕ) :
    Measurable fun p : Hist (LayerState S H) A ℝ (k + 1) ↦
      ((p (Fin.last k)).obs.1, π h (p (Fin.last k)).obs.1) :=
  (measurable_of_countable (fun s : S ↦ (s, π h s))).comp
    (measurable_fst.comp (Round.measurable_obs.comp (measurable_pi_apply _)))

/-- The law of the next state given a history of `k + 1` rounds whose last state is at the step
`h`: the transition kernel of the step `h` at the last state and the action of `π`. -/
noncomputable def histTransKernel (h : Fin H) (k : ℕ) :
    Kernel (Hist (LayerState S H) A ℝ (k + 1)) S :=
  (M.trans h).comap _ (measurable_lastState_policy π h k)

omit [Fintype A] [MeasurableSingletonClass A] [Nonempty A] in
/-- The value of `histTransKernel`. -/
lemma histTransKernel_apply (h : Fin H) (k : ℕ) (p : Hist (LayerState S H) A ℝ (k + 1)) :
    histTransKernel M π h k p = M.trans h ((p (Fin.last k)).obs.1, π h (p (Fin.last k)).obs.1) :=
  rfl

/-- `histTransKernel` is a Markov kernel. -/
instance (h : Fin H) (k : ℕ) : IsMarkovKernel (histTransKernel M π h k) := by
  unfold histTransKernel; infer_instance

/-- **Law of the next state** given the first `k + 1` rounds, for a trajectory started at the
step `h₀` whose round `k` is at the step `h = h₀ + k`: the transition kernel of `M` at the step
`h`, the state of the round `k` and the action of `π`. -/
lemma hasCondDistrib_obs_succ_hist_stepLaw (s : S) {h₀ : Fin (H + 1)} {h : Fin H} {k : ℕ}
    (hk : (h₀ : ℕ) + k = h) :
    HasCondDistrib (fun x ↦ (IT.obs (k + 1) x).1) (IT.hist (k + 1)) (histTransKernel M π h k)
      (stepLaw M π (s, h₀)) := by
  refine hasCondDistrib_of_lintegral_eq (by fun_prop) (by fun_prop) fun f hf ↦ ?_
  have hsnoc : Measurable fun q : Hist (LayerState S H) A ℝ k × Round (LayerState S H) A ℝ ↦
      (Fin.snoc q.1 q.2 : Hist (LayerState S H) A ℝ (k + 1)) := measurable_finSnoc
  have hj : (h₀ : ℕ) + k = (h.castSucc : Fin (H + 1)) := hk
  -- the one-step computation under `stepLaw M π (s', h)`
  have hone (p : Hist (LayerState S H) A ℝ k) (s' : S)
      (g : Hist (LayerState S H) A ℝ (k + 1) × S → ℝ≥0∞) (hg : Measurable g) :
      ∫⁻ y, g (Fin.snoc p (y 0), (IT.obs 1 y).1) ∂stepLaw M π (s', h.castSucc)
        = ∫⁻ r, ∫⁻ s'', g (Fin.snoc p ((s', h.castSucc), π h s', r), s'') ∂M.trans h (s', π h s')
            ∂M.reward h (s', π h s') := by
    have hm : Measurable fun q : ℝ × S ↦
        g (Fin.snoc p (((s', h.castSucc), π h s', q.1) : Round (LayerState S H) A ℝ), q.2) :=
      hg.comp ((hsnoc.comp (measurable_const.prodMk (by fun_prop))).prodMk measurable_snd)
    calc ∫⁻ y, g (Fin.snoc p (y 0), (IT.obs 1 y).1) ∂stepLaw M π (s', h.castSucc)
        = ∫⁻ y, (fun q : (ℝ × S) × Traj' ↦ g (Fin.snoc p ((s', h.castSucc), π h s', q.1.1),
            q.1.2)) ((IT.feedback 0 y, (IT.obs 1 y).1), shiftRound y)
            ∂stepLaw M π (s', h.castSucc) := by
          refine lintegral_congr_ae ?_
          filter_upwards [ae_round_zero_stepLaw_castSucc M π h s'] with y hy
          simp only [hy]
      _ = ∫⁻ q, ∫⁻ _y, g (Fin.snoc p ((s', h.castSucc), π h s', q.1), q.2)
            ∂stepLaw M π (q.2, h.succ) ∂((M.reward h (s', π h s')).prod (M.trans h (s', π h s'))) :=
          lintegral_stepLaw_castSucc M π h s' (hm.comp measurable_fst)
      _ = ∫⁻ q, g (Fin.snoc p ((s', h.castSucc), π h s', q.1), q.2)
            ∂((M.reward h (s', π h s')).prod (M.trans h (s', π h s'))) := by
          simp
      _ = _ := lintegral_prod _ hm.aemeasurable
  have hF : Measurable fun q : Hist (LayerState S H) A ℝ k × S × Traj' ↦
      f (Fin.snoc q.1 (q.2.2 0), (IT.obs 1 q.2.2).1) :=
    hf.comp ((hsnoc.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp
      measurable_snd.snd))).prodMk (measurable_fst.comp ((IT.measurable_obs 1).comp
        measurable_snd.snd)))
  have hK : Measurable fun p' : Hist (LayerState S H) A ℝ (k + 1) ↦
      ∫⁻ s'', f (p', s'') ∂histTransKernel M π h k p' :=
    Measurable.lintegral_kernel_prod_right' (κ := histTransKernel M π h k) hf
  have hF' : Measurable fun q : Hist (LayerState S H) A ℝ k × S × Traj' ↦
      ∫⁻ s'', f (Fin.snoc q.1 (q.2.2 0), s'') ∂histTransKernel M π h k (Fin.snoc q.1 (q.2.2 0)) :=
    hK.comp (hsnoc.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp
      measurable_snd.snd)))
  calc ∫⁻ x, f (IT.hist (k + 1) x, (IT.obs (k + 1) x).1) ∂stepLaw M π (s, h₀)
      = ∫⁻ x, f (Fin.snoc (IT.hist k x) (shiftRounds k x 0), (IT.obs 1 (shiftRounds k x)).1)
          ∂stepLaw M π (s, h₀) := by
        refine lintegral_congr fun x ↦ ?_
        rw [hist_succ_eq_snoc]
        simp [IT.obs, shiftRounds, add_comm]
    _ = ∫⁻ x, ∫⁻ y, f (Fin.snoc (IT.hist k x) (y 0), (IT.obs 1 y).1)
          ∂stepLaw M π ((IT.obs k x).1, h.castSucc) ∂stepLaw M π (s, h₀) :=
        lintegral_stepLaw_hist_shiftRounds M π k s h₀ h.castSucc hj _ hF
    _ = ∫⁻ x, ∫⁻ y, ∫⁻ s'', f (Fin.snoc (IT.hist k x) (y 0), s'')
          ∂histTransKernel M π h k (Fin.snoc (IT.hist k x) (y 0))
          ∂stepLaw M π ((IT.obs k x).1, h.castSucc) ∂stepLaw M π (s, h₀) := by
        refine lintegral_congr fun x ↦ ?_
        rw [hone _ _ _ hf, hone _ _ (fun q ↦ ∫⁻ s'', f (q.1, s'') ∂histTransKernel M π h k q.1)
          (hK.comp measurable_fst)]
        refine lintegral_congr fun r ↦ ?_
        simp [histTransKernel_apply]
    _ = ∫⁻ x, ∫⁻ s'', f (Fin.snoc (IT.hist k x) (shiftRounds k x 0), s'')
          ∂histTransKernel M π h k (Fin.snoc (IT.hist k x) (shiftRounds k x 0))
          ∂stepLaw M π (s, h₀) :=
        (lintegral_stepLaw_hist_shiftRounds M π k s h₀ h.castSucc hj _ hF').symm
    _ = _ := by
        refine lintegral_congr fun x ↦ ?_
        rw [hist_succ_eq_snoc]


/-- Integral form of the law of the next state: for a bounded measurable function `Ψ` of the
first `k + 1` rounds and `g : S → ℝ`, `E[Ψ g(S_{k+1})] = E[Ψ (p_h g)(S_k, π_h(S_k))]`. -/
lemma integral_mul_obs_succ_stepLaw (s : S) {h₀ : Fin (H + 1)} {h : Fin H} {k : ℕ}
    (hk : (h₀ : ℕ) + k = h) {Ψ : Hist (LayerState S H) A ℝ (k + 1) → ℝ} (hΨ : Measurable Ψ)
    {C : ℝ} (hC : ∀ p, |Ψ p| ≤ C) (g : S → ℝ) :
    ∫ x, Ψ (IT.hist (k + 1) x) * g (IT.obs (k + 1) x).1 ∂stepLaw M π (s, h₀)
      = ∫ x, Ψ (IT.hist (k + 1) x)
          * vecExp (M.transVec h (IT.obs k x).1 (π h (IT.obs k x).1)) g ∂stepLaw M π (s, h₀) := by
  have hc := hasCondDistrib_obs_succ_hist_stepLaw M π s hk
  have hg : Measurable g := measurable_of_countable g
  have hD : ∀ s', |g s'| ≤ ∑ s'', |g s''| := fun s' ↦
    Finset.single_le_sum (f := fun s'' ↦ |g s''|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ s')
  have hm : Measurable fun q : Hist (LayerState S H) A ℝ (k + 1) × S ↦ Ψ q.1 * g q.2 :=
    (hΨ.comp measurable_fst).mul (hg.comp measurable_snd)
  rw [hc.integral_prodMk (f := fun q ↦ Ψ q.1 * g q.2) hm.stronglyMeasurable]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [integral_const_mul, histTransKernel_apply, integral_eq_vecExp_transVec]
    rfl
  · refine Integrable.of_bound hm.aestronglyMeasurable (C * ∑ s'', |g s''|)
      (Filter.Eventually.of_forall fun q ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hC q.1) (hD q.2) (abs_nonneg _) ((abs_nonneg _).trans (hC q.1))

omit [Fintype A] [MeasurableSingletonClass A] in
/-- The kernel `s ↦ R_h(· | s, π_h(s)) ⊗ p_h(· | s, π_h(s))` of the reward and the next state at the
step `h` under the policy `π`. -/
noncomputable def rewardTransKernel (h : Fin H) : Kernel S (ℝ × S) :=
  (M.reward h ×ₖ M.trans h).comap (fun s ↦ (s, π h s)) (measurable_of_countable _)

omit [Fintype A] [MeasurableSingletonClass A] [Nonempty A] in
/-- The value of `rewardTransKernel`. -/
lemma rewardTransKernel_apply (h : Fin H) (s : S) :
    rewardTransKernel M π h s = (M.reward h (s, π h s)).prod (M.trans h (s, π h s)) := by
  rw [rewardTransKernel, Kernel.comap_apply, Kernel.prod_apply]

/-- The reward of the round `k` and the state of the round `k + 1`, for a trajectory started at
the step `h₀` whose round `k` is at the step `h = h₀ + k`, have conditional law
`R_h(· | S_k, π_h(S_k)) ⊗ p_h(· | S_k, π_h(S_k))` given the first `k` rounds and the state `S_k`. -/
lemma hasCondDistrib_feedback_obs_succ_stepLaw (s : S) {h₀ : Fin (H + 1)} {h : Fin H} {k : ℕ}
    (hk : (h₀ : ℕ) + k = h) :
    HasCondDistrib (fun x ↦ (IT.feedback k x, (IT.obs (k + 1) x).1))
      (fun x ↦ (IT.hist k x, (IT.obs k x).1))
      (Kernel.prodMkLeft (Hist (LayerState S H) A ℝ k) (rewardTransKernel M π h))
      (stepLaw M π (s, h₀)) := by
  have hφ : Measurable fun y : Traj' ↦ (IT.feedback 0 y, (IT.obs 1 y).1) := by fun_prop
  have hc := (hasCondDistrib_shiftRounds_stepLaw M π s (j := h.castSucc) hk).comp_left hφ
  have hK : (Kernel.prodMkLeft (Hist (LayerState S H) A ℝ k) (stepLawKernel M π h.castSucc)).map
      (fun y : Traj' ↦ (IT.feedback 0 y, (IT.obs 1 y).1))
      = Kernel.prodMkLeft (Hist (LayerState S H) A ℝ k) (rewardTransKernel M π h) := by
    ext q : 1
    rw [Kernel.map_apply _ hφ, Kernel.prodMkLeft_apply, Kernel.prodMkLeft_apply,
      stepLawKernel_apply, rewardTransKernel_apply]
    have hl := hasLaw_stepLaw_castSucc M π h q.2
    calc (stepLaw M π (q.2, h.castSucc)).map (fun y : Traj' ↦ (IT.feedback 0 y, (IT.obs 1 y).1))
        = ((stepLaw M π (q.2, h.castSucc)).map
            (fun x ↦ ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x))).map Prod.fst :=
          (Measure.map_map measurable_fst
            (f := fun x : Traj' ↦ ((IT.feedback 0 x, (IT.obs 1 x).1), shiftRound x))
            (((IT.measurable_feedback 0).prodMk (measurable_fst.comp (IT.measurable_obs 1))).prodMk
              measurable_shiftRound)).symm
      _ = _ := by rw [hl.map_eq]; exact Measure.fst_compProd _ _
  rw [hK] at hc
  refine hc.congr (Filter.Eventually.of_forall fun _ ↦ rfl)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  simp [shiftRounds, IT.feedback, IT.obs, add_comm]

/-- For an MDP with the reward function `r`, the reward of the round `k` of a trajectory started
at the step `h₀` is `r h (S_k) (A_k)` almost surely, where `h = h₀ + k`. -/
lemma ae_feedback_eq_stepLaw {r : Fin H → S → A → ℝ} (hM : M.HasRewardFn r) (s : S)
    {h₀ : Fin (H + 1)} {h : Fin H} {k : ℕ} (hk : (h₀ : ℕ) + k = h) :
    ∀ᵐ x ∂stepLaw M π (s, h₀), IT.feedback k x = r h (IT.obs k x).1 (IT.action k x) := by
  have hr : Measurable fun s' : S ↦ r h s' (π h s') := measurable_of_countable _
  have := ae_stepLaw_of_ae_shiftRounds M π s (j := h.castSucc) hk
    (P := fun _ s' y ↦ IT.feedback 0 y = r h s' (π h s'))
    (measurableSet_eq_fun (by fun_prop) (hr.comp (measurable_snd.comp measurable_fst)))
    (fun _ s' ↦ by
      have hl := hasLaw_feedback_zero_stepLaw_castSucc M π h s'
      rw [hM h s' (π h s')] at hl
      exact hl.ae_eq_of_dirac)
  filter_upwards [this, ae_action_eq_stepLaw M π s hk] with x hx hx'
  rw [hx']
  simpa [shiftRounds, IT.feedback] using hx

/-! ### The episode environment -/

omit [Fintype S] [Fintype A] [MeasurableSingletonClass A] [Nonempty A] in
/-- The last state of the prefix `s_0, …, s_h` of a state sequence and the action of `π`. -/
lemma measurable_lastState_policy_states [Finite S] (h : Fin H) :
    Measurable fun τ : Fin (h + 1) → S ↦ (τ (Fin.last h), π h (τ (Fin.last h))) :=
  measurable_of_countable _

/-- The law of the state of the step `h + 1` of an episode of `π` given its states
`s_0, …, s_h`: the transition kernel of the step `h` at `s_h` and the action `π_h(s_h)`. -/
noncomputable def statesTransKernel (h : Fin H) : Kernel (Fin (h + 1) → S) S :=
  (M.trans h).comap _ (measurable_lastState_policy_states π h)

/-- `statesTransKernel` is a Markov kernel. -/
instance (h : Fin H) : IsMarkovKernel (statesTransKernel M π h) := by
  unfold statesTransKernel; infer_instance

omit [Fintype S] [Fintype A] [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] [Nonempty A] in
/-- The inequality behind the inclusion of the states `s_0, …, s_h` in the state sequence. -/
lemma castLE_succ_le (h : Fin H) : (h : ℕ) + 1 ≤ H + 1 := Nat.succ_le_succ h.is_lt.le

/-- Under the law of the state sequence of an episode of `π`, the state of the step `h + 1` has
conditional law `p_h(· | s_h, π_h(s_h))` given the states `s_0, …, s_h`. -/
lemma hasCondDistrib_statesLaw (s₁ : S) (h : Fin H) :
    HasCondDistrib (fun τ : Traj S H ↦ τ h.succ)
      (fun τ (i : Fin (h + 1)) ↦ τ (Fin.castLE (castLE_succ_le h) i))
      (statesTransKernel M π h) (statesLaw M s₁ π) := by
  have hc := hasCondDistrib_obs_succ_hist_stepLaw M π s₁ (h₀ := startStep H) (h := h) (k := h)
    (by simp)
  have hg : Measurable fun (p : Hist (LayerState S H) A ℝ (h + 1)) (i : Fin (h + 1)) ↦
      (p i).obs.1 := by fun_prop
  have hc' : HasCondDistrib (fun x ↦ (IT.obs (h + 1) x).1)
      ((fun (p : Hist (LayerState S H) A ℝ (h + 1)) (i : Fin (h + 1)) ↦ (p i).obs.1)
        ∘ IT.hist (h + 1)) (statesTransKernel M π h) (stepLaw M π (s₁, startStep H)) :=
    HasCondDistrib.comp_right (hf := hg) hc
  exact HasCondDistrib.of_comp_hasLaw (measurable_of_countable _) (measurable_of_countable _)
    ⟨(measurable_episodeStates (S := S) (A := A)).aemeasurable, rfl⟩ hc'

section EpisodeEnv

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {alg : Algorithm Unit (Policy S A H) (Traj S H)} {O : ℕ → Ω → Unit} {X : ℕ → Ω → Policy S A H}
  {Y : ℕ → Ω → Traj S H}

omit π

omit [Fintype S] [Fintype A] [Nonempty A] in
/-- The last state of the prefix `s_0, …, s_h` of a state sequence and the action of the policy
component of the conditioning variable. -/
lemma measurable_episodeStepKernel_aux [Finite S] [Finite A] {γ : Type*} {mγ : MeasurableSpace γ}
    (h : Fin H) :
    Measurable fun q : (γ × Policy S A H) × (Fin (h + 1) → S) ↦
      (q.2 (Fin.last h), q.1.2 h (q.2 (Fin.last h))) :=
  (measurable_of_countable fun z : Policy S A H × (Fin (h + 1) → S) ↦
    (z.2 (Fin.last h), z.1 h (z.2 (Fin.last h)))).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

/-- The law of the state of the step `h + 1` of an episode given the past (`γ`), the policy `π`
of the episode and its states `s_0, …, s_h`: `p_h(· | s_h, π_h(s_h))`. -/
noncomputable def episodeStepKernel (γ : Type*) [MeasurableSpace γ] (h : Fin H) :
    Kernel ((γ × Policy S A H) × (Fin (h + 1) → S)) S :=
  (M.trans h).comap _ (measurable_episodeStepKernel_aux h)

/-- `episodeStepKernel` is a Markov kernel. -/
instance (γ : Type*) [MeasurableSpace γ] (h : Fin H) :
    IsMarkovKernel (episodeStepKernel M γ h) := by
  unfold episodeStepKernel; infer_instance

/-- **Law of the next state within an episode**: in an interaction with the episode environment
of `M` from `s₁`, the state of the step `h + 1` of the episode `t` has conditional law
`p_h(· | s_h, π_h(s_h))` given the history of the first `t` episodes, the policy `π` of the
episode `t` and its states `s_0, …, s_h`. -/
lemma hasCondDistrib_feedback_succ_statesEnv (s₁ : S)
    (hseq : IsAlgEnvSeq O X Y alg (statesEnv M s₁) P) (t : ℕ) (h : Fin H) :
    HasCondDistrib (fun ω ↦ Y t ω h.succ)
      (fun ω ↦ (((history O X Y t ω, O t ω), X t ω),
        fun i : Fin (h + 1) ↦ Y t ω (Fin.castLE (castLE_succ_le h) i)))
      (episodeStepKernel M (Hist Unit (Policy S A H) (Traj S H) t × Unit) h) P := by
  have h1 := hasCondDistrib_feedback_history_action_statesEnv M s₁ hseq t
  have h2 := HasCondDistrib.compProd_left_of_sectR
    (μ := P.map fun ω ↦ ((history O X Y t ω, O t ω), X t ω))
    (κ := (statesKernel M s₁).prodMkLeft _)
    (X := fun τ : Traj S H ↦ fun i : Fin (h + 1) ↦ τ (Fin.castLE (castLE_succ_le h) i))
    (Y := fun τ : Traj S H ↦ τ h.succ)
    (η := episodeStepKernel M (Hist Unit (Policy S A H) (Traj S H) t × Unit) h)
    (measurable_of_countable _) (measurable_of_countable _) fun a ↦ by
      have := hasCondDistrib_statesLaw M a.2 s₁ h
      exact this
  exact HasCondDistrib.comp_of_hasLaw h2 h1

end EpisodeEnv

end Learning.MDP.Episodic
