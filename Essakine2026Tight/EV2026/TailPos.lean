/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.EV2026.AnalysisPos
public import Essakine2026Tight.EV2026.Events
public import Essakine2026Tight.EV2026.TailCommon

/-!
# Analysis of Entropic-BPI for `β > 0`: the stopping time and the PAC guarantee

Essakine, Vernade (2026), Appendix B.1, the proof of the sample complexity for `β > 0`
(blueprint chapter "Analysis of Entropic-BPI for β > 0", Sections "The certificate under the true
kernel" and "Bounding the stopping time"). As in `EV2026/AnalysisPos.lean`, the lemmas are first
proved at a history satisfying the concentration inequalities (`HistConcentration`), then for a
run on the good event:

* the unrolled certificate (`lem:cert_unrolled_pos`): `cert_le_exp_mul_sum_integral_of_pos`,
  `certAt_le_exp_mul_sum_integral_of_pos`;
* the normalized certificate bound (`lem:ratio_bound_pos`): `cert_div_optZ_fst_le_of_pos`,
  `certAt_div_ZtildeAt_le_of_pos`;
* the progress at a non-stopping episode (`lem:progress_pos`, no event needed):
  `progress_le_cert_div_optZ_fst_of_pos`, `progress_le_certAt_div_ZtildeAt_of_pos`;
* the bound on the stopping time (`lem:stopping_time_bound_pos`), at an `ω` of the good event at
  which the policies played are the greedy ones: `stoppingTime_le_upperBound_of_pos`;
* the PAC guarantee and the sample complexity in probability (`lem:pac_pos`), for every run:
  `measureReal_bad_le_of_pos`, `one_sub_le_measureReal_stoppingTime_le_of_pos`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP.Episodic Learning.MDP
open scoped ENNReal

namespace Essakine2026Tight

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]
  {H : ℕ} {M : EpisodicMDP S A} {r : ℕ → S → A → ℝ} {β δ : ℝ} {t : ℕ}
  {hist : Hist Unit (Policy S A H) (Traj S H) t}

/-! ### At a history -/

section History

/-- **Unrolled certificate** (`β > 0`), at a history satisfying the concentration inequalities:
with `π` the greedy policy, `π_1 G_1(s₁)` is at most
`e^13 ∑_h E^π[e^{β ∑_{i ≤ h} r_i} (36 √(Var_{p_h}(Z^π_{h+1})(S_h, A_h) ρ*_h(S_h, A_h))
+ 84 H e^{β (H - h)} ρ_h(S_h, A_h))]`. -/
lemma cert_le_exp_mul_sum_integral_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (s₁ : S) :
    cert r β δ hist H s₁ ≤ Real.exp 13 * ∑ h ∈ range H,
      ∫ x, Real.exp (β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
        * (36 * √(vecVar (M.transVec h (IT.obs h x).1 (IT.action h x))
              (expValue M H β (greedy r β δ hist).extend (h + 1))
            * starRateMin δ hist h (IT.obs h x).1 (IT.action h x))
          + 84 * H * Real.exp (β * (H - h : ℕ)) * klRateMin δ hist h (IT.obs h x).1 (IT.action h x))
        ∂stepLaw M (greedy r β δ hist).extend (s₁, 0) := by
  have hu : ∀ (h : ℕ) (s : S) (a : A), 0 ≤ 36 * √(vecVar (M.transVec h s a)
        (expValue M H β (greedy r β δ hist).extend (h + 1)) * starRateMin δ hist h s a)
      + 84 * H * Real.exp (β * (H - h : ℕ)) * klRateMin δ hist h s a :=
    fun h s a ↦ add_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (mul_nonneg (by positivity) (klRateMin_nonneg hist hδ hδ1 h s a))
  have hlast : ∀ s, cert r β δ hist (H - H) s = 0 := fun s ↦ by simp [cert_zero]
  have hg : ∀ h < H, ∀ s : S, cert r β δ hist (H - h) s
      ≤ Real.exp (β * r h s ((greedy r β δ hist).extend h s))
        * ((36 * √(vecVar (M.transVec h s ((greedy r β δ hist).extend h s))
              (expValue M H β (greedy r β δ hist).extend (h + 1))
            * starRateMin δ hist h s ((greedy r β δ hist).extend h s))
          + 84 * H * Real.exp (β * (H - h : ℕ))
            * klRateMin δ hist h s ((greedy r β δ hist).extend h s))
          + (1 + 13 / H) * ∫ s', cert r β δ hist (H - (h + 1)) s'
            ∂M.trans h (s, (greedy r β δ hist).extend h s)) := by
    intro h hh s
    have := cert_le_of_pos hM hr hβ hδ hδ1 hc ⟨h, hh⟩ s
    simp only at this
    rw [Policy.extend_of_lt _ hh, starRateMin_of_lt δ hist hh, klRateMin_of_lt δ hist hh,
      integral_eq_vecExp_transVec, show H - (h + 1) = H - 1 - h by omega]
    exact this.trans_eq (by ring)
  exact le_exp_mul_sum_integral_of_backward (M := M) (greedy r β δ hist).measurable_extend
    (s₁ := s₁) (by norm_num : (0 : ℝ) ≤ 13) (g := fun h s ↦ cert r β δ hist (H - h) s) hu hlast hg

/-- **Normalized certificate bound** (`β > 0`), at a history satisfying the concentration
inequalities: with `π` the greedy policy, `x = ∑_{h, s, a} p^π_h(s, a) ρ*_h(s, a)` and
`y = ∑_{h, s, a} p^π_h(s, a) ρ_h(s, a)`,
`π_1 G_1(s₁) / Z̃_1(s₁) ≤ e^13 (36 √(V_G x) + 84 H e^{|β| (H + 1)} y)` with `G = G_max(M)`. -/
lemma cert_div_optZ_fst_le_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (s₁ : S) :
    cert r β δ hist H s₁ / (optZ r β δ hist H).1 s₁ ≤ Real.exp 13 *
      (36 * √(varianceFactor β (maxReturn M H s₁) * ∑ h : Fin H, ∑ s, ∑ a,
          occupancy M (greedy r β δ hist).extend s₁ h s a
            * rateMin (alphaStar (Fintype.card S) (Fintype.card A) H δ) (visitCount hist h s a))
        + 84 * H * Real.exp (|β| * (H + 1 : ℕ)) * ∑ h : Fin H, ∑ s, ∑ a,
          occupancy M (greedy r β δ hist).extend s₁ h s a
            * rateMin (alphaKL (Fintype.card S) (Fintype.card A) H δ) (visitCount hist h s a)) := by
  rw [← sum_range_occupancy_mul_starRateMin, ← sum_range_occupancy_mul_klRateMin]
  set π := (greedy r β δ hist).extend with hπ_def
  have hπ : ∀ h, Measurable (π h) := (greedy r β δ hist).measurable_extend
  set P := stepLaw M π (s₁, 0) with hP
  set ρs := starRateMin δ hist with hρs
  set ρ := klRateMin δ hist with hρ
  have hρs0 : ∀ h s a, 0 ≤ ρs h s a := starRateMin_nonneg hist hδ hδ1
  have hρ0 : ∀ h s a, 0 ≤ ρ h s a := klRateMin_nonneg hist hδ hδ1
  have hRw := rewardsIn_Icc_of_hasRewardFn hM hr
  -- the denominators
  have hZ1 : 1 ≤ expValue M H β π 0 s₁ := by
    simpa only [Fin.val_zero] using (expValue_mem_Icc_of_pos hM hr hβ (greedy r β δ hist) 0 s₁).1
  have hZle : expValue M H β π 0 s₁ ≤ (optZ r β δ hist H).1 s₁ :=
    (expValue_le_optExpValue M H β hRw hβ hπ 0 s₁).trans (by
      simpa only [Fin.val_zero, Nat.sub_zero] using
        (optExpValue_mem_Icc_optZ_of_pos hM hr hβ hδ hδ1 hc 0 s₁).2)
  have hg0 : 0 ≤ cert r β δ hist H s₁ := (cert_mem hist r β δ hδ hδ1 H le_rfl s₁).1
  refine (div_le_div_of_nonneg_left hg0 (by linarith) hZle).trans ?_
  -- the unrolled certificate, split into the variance and the rate terms
  have hun := cert_le_exp_mul_sum_integral_of_pos hM hr hβ hδ hδ1 hc s₁
  have hsplit : ∑ h ∈ range H,
      ∫ x, Real.exp (β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
        * (36 * √(vecVar (M.transVec h (IT.obs h x).1 (IT.action h x))
              (expValue M H β π (h + 1)) * ρs h (IT.obs h x).1 (IT.action h x))
          + 84 * H * Real.exp (β * (H - h : ℕ)) * ρ h (IT.obs h x).1 (IT.action h x)) ∂P
      = 36 * ∑ h ∈ range H,
          ∫ x, Real.exp (β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
          * √(vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M H β π (h + 1))
            * ρs h (IT.obs h x).1 (IT.action h x)) ∂P
        + ∑ h ∈ range H,
          ∫ x, Real.exp (β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
          * ((fun (h : ℕ) (_ : S) (_ : A) ↦ 84 * H * Real.exp (β * (H - h : ℕ)))
              h (IT.obs h x).1 (IT.action h x) * ρ h (IT.obs h x).1 (IT.action h x)) ∂P := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun h _ ↦ ?_
    rw [← integral_const_mul, ← integral_add]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      simp only
      ring
    · exact (integrable_exp_sum_mul P β r (range (h + 1))
        (fun s a ↦ √(vecVar (M.transVec h s a) (expValue M H β π (h + 1)) * ρs h s a))
        h).const_mul 36
    · exact integrable_exp_sum_mul P β r (range (h + 1))
        (fun s a ↦ 84 * H * Real.exp (β * (H - h : ℕ)) * ρ h s a) h
  have hvar := sum_integral_exp_mul_sqrt_vecVar_mul_le hπ (s₁ := s₁) (H := H) hM hr β hρs0
  have hrate := sum_integral_exp_mul_mul_le (M := M) (π := π) (s₁ := s₁) (r := r) (H := H) β hρ0
    (c := fun (h : ℕ) (_ : S) (_ : A) ↦ 84 * H * Real.exp (β * (H - h : ℕ)))
    (C := 84 * H * Real.exp (|β| * (H + 1 : ℕ))) fun h hh x ↦ by
      have hsum : ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x) ≤ (h : ℝ) + 1 :=
        calc ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x)
            ≤ ∑ _i ∈ range (h + 1), (1 : ℝ) := sum_le_sum fun i _ ↦ (hr _ _ _).2
          _ = (h : ℝ) + 1 := by simp
      have hcast : ((H - h : ℕ) : ℝ) = H - h := Nat.cast_sub hh.le
      rw [mul_comm, mul_assoc, ← Real.exp_add, abs_of_pos hβ]
      gcongr
      rw [hcast]
      push_cast
      nlinarith
  have hVG := variance_exp_episodeReturn_div_sq_le_maxReturn M H β hRw hπ s₁
  have hZpos : 0 < expValue M H β π 0 s₁ := by linarith
  have hVar : √(variance (fun x ↦ Real.exp (β * episodeReturn H x)) P)
      ≤ √(varianceFactor β (maxReturn M H s₁)) * expValue M H β π 0 s₁ := by
    have h1 : variance (fun x ↦ Real.exp (β * episodeReturn H x)) P
        ≤ varianceFactor β (maxReturn M H s₁) * expValue M H β π 0 s₁ ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at hVG
      exact hVG
    calc √(variance (fun x ↦ Real.exp (β * episodeReturn H x)) P)
        ≤ √(varianceFactor β (maxReturn M H s₁) * expValue M H β π 0 s₁ ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = _ := by rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hZpos.le]
  have hy0 : 0 ≤ ∑ h ∈ range H, ∑ s, ∑ a, occupancy M π s₁ h s a * ρ h s a :=
    sum_nonneg fun h _ ↦ sum_nonneg fun s _ ↦ sum_nonneg fun a _ ↦
      mul_nonneg (occupancy_nonneg _ _ _ _ _ _) (hρ0 _ _ _)
  have hE0 : 0 ≤ 84 * (H : ℝ) * Real.exp (|β| * (H + 1 : ℕ)) := by positivity
  rw [div_le_iff₀ hZpos, Real.sqrt_mul (varianceFactor_nonneg _ _)]
  calc cert r β δ hist H s₁
      ≤ Real.exp 13 * (36 * ∑ h ∈ range H, ∫ x,
          Real.exp (β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
          * √(vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M H β π (h + 1))
            * ρs h (IT.obs h x).1 (IT.action h x)) ∂P
        + ∑ h ∈ range H,
          ∫ x, Real.exp (β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
          * ((fun (h : ℕ) (_ : S) (_ : A) ↦ 84 * H * Real.exp (β * (H - h : ℕ)))
              h (IT.obs h x).1 (IT.action h x) * ρ h (IT.obs h x).1 (IT.action h x)) ∂P) := by
        rw [← hsplit]
        exact hun
    _ ≤ Real.exp 13 * (36 * ((√(varianceFactor β (maxReturn M H s₁)) * expValue M H β π 0 s₁)
          * √(∑ h ∈ range H, ∑ s, ∑ a, occupancy M π s₁ h s a * ρs h s a))
        + 84 * H * Real.exp (|β| * (H + 1 : ℕ))
          * (∑ h ∈ range H, ∑ s, ∑ a, occupancy M π s₁ h s a * ρ h s a)
          * expValue M H β π 0 s₁) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left
          (hvar.trans (mul_le_mul_of_nonneg_right hVar (Real.sqrt_nonneg _))) (by norm_num))
          (hrate.trans (le_mul_of_one_le_right (mul_nonneg hE0 hy0) hZ1)))
          (Real.exp_pos _).le
    _ = _ := by ring

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- **Progress at a non-stopping episode** (`β > 0`; no event is needed): if the stopping
condition fails, `κ(β, ε) ≤ π_1 G_1(s₁) / Z̃_1(s₁)`. -/
lemma progress_le_cert_div_optZ_fst_of_pos (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε) {s₁ : S}
    (hstop : ¬ stopCond r β δ ε s₁ hist) :
    progress β ε ≤ cert r β δ hist H s₁ / (optZ r β δ hist H).1 s₁ := by
  simp only [stopCond, hβ, ↓reduceIte, not_le] at hstop
  obtain ⟨h1, h2, -⟩ := optZ_mem_of_pos (hist := hist) hr hβ hδ hδ1 H le_rfl s₁
  have hZ : 0 < (optZ r β δ hist H).1 s₁ := by linarith
  rw [le_div_iff₀ hZ]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hZ.le) hstop.le
  have hu : 1 ≤ Real.exp (β * ε) := Real.one_le_exp (mul_nonneg hβ.le hε)
  have hvu : Real.exp (-(2 : ℕ) * |β| * ε) * Real.exp (β * ε) ≤ 1 := by
    rw [← Real.exp_add, abs_of_pos hβ]
    exact Real.exp_le_one_iff.2 (by push_cast; nlinarith)
  have hv0 := Real.exp_pos (-(2 : ℕ) * |β| * ε)
  unfold progress
  rw [le_div_iff₀ (Real.exp_pos _), abs_of_pos hβ]
  rw [abs_of_pos hβ] at hvu hv0
  push_cast at hvu hv0 ⊢
  nlinarith

end History

/-! ### On the good event of a run -/

section Run

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℕ → Ω → Policy S A H} {Y : ℕ → Ω → Traj S H}
  {s₁ : S} {ω : Ω}

/-- **Unrolled certificate** (`β > 0`): on the good event, for every episode `t`, with
`π = π^{t+1}`, `π_1 G_1^t(s₁)` is at most
`e^13 ∑_h E^π[e^{β ∑_{i ≤ h} r_i} (36 √(Var_{p_h}(Z^π_{h+1}) ρ*^t_h) + 84 H e^{β (H - h)} ρ^t_h)]`
(the rate terms at `(S_h, A_h)`). -/
lemma certAt_le_exp_mul_sum_integral_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hω : ω ∈ goodEvent X Y M s₁ β δ) (t : ℕ) :
    certAt X Y r β δ t ω 0 s₁ ≤ Real.exp 13 * ∑ h ∈ range H,
      ∫ x, Real.exp (β * ∑ i ∈ range (h + 1), r i (IT.obs i x).1 (IT.action i x))
        * (36 * √(vecVar (M.transVec h (IT.obs h x).1 (IT.action h x))
              (expValue M H β (greedyAt X Y r β δ t ω).extend (h + 1))
            * starRateMin δ (histAt X Y t ω) h (IT.obs h x).1 (IT.action h x))
          + 84 * H * Real.exp (β * (H - h : ℕ))
            * klRateMin δ (histAt X Y t ω) h (IT.obs h x).1 (IT.action h x))
        ∂stepLaw M (greedyAt X Y r β δ t ω).extend (s₁, 0) := by
  simpa only [certAt, greedyAt, Fin.val_zero, Nat.sub_zero] using
    cert_le_exp_mul_sum_integral_of_pos hM hr hβ hδ hδ1 (histConcentration_histAt hω t) s₁

/-- **Normalized certificate bound** (`β > 0`): on the good event, for every episode `t`, with
`π = π^{t+1}`, `x_t = ∑_{h, s, a} p^π_h(s, a) ρ*^t_h(s, a)` and
`y_t = ∑_{h, s, a} p^π_h(s, a) ρ^t_h(s, a)`,
`π_1 G_1^t(s₁) / Z̃_1^t(s₁) ≤ e^13 (36 √(V_G x_t) + 84 H e^{|β| (H + 1)} y_t)`. -/
lemma certAt_div_ZtildeAt_le_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hω : ω ∈ goodEvent X Y M s₁ β δ) (t : ℕ) :
    certAt X Y r β δ t ω 0 s₁ / ZtildeAt X Y r β δ t ω 0 s₁
      ≤ Real.exp 13 * (36 * √(varianceFactor β (maxReturn M H s₁) * ∑ h : Fin H, ∑ s, ∑ a,
          occupancy M (greedyAt X Y r β δ t ω).extend s₁ h s a * starRateMinAt X Y δ h s a t ω)
        + 84 * H * Real.exp (|β| * (H + 1 : ℕ)) * ∑ h : Fin H, ∑ s, ∑ a,
          occupancy M (greedyAt X Y r β δ t ω).extend s₁ h s a * klRateMinAt X Y δ h s a t ω) :=
        by
  simpa only [certAt, ZtildeAt, greedyAt, starRateMinAt, klRateMinAt, visitCountAt, Fin.val_zero,
    Nat.sub_zero] using
    cert_div_optZ_fst_le_of_pos hM hr hβ hδ hδ1 (histConcentration_histAt hω t) s₁

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- **Progress at a non-stopping episode** (`β > 0`; no event is needed): if the stopping
condition fails after `t` episodes, `κ(β, ε) ≤ π_1 G_1^t(s₁) / Z̃_1^t(s₁)`. -/
lemma progress_le_certAt_div_ZtildeAt_of_pos (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε) {t : ℕ}
    (hstop : ¬ stopCond r β δ ε s₁ (histAt X Y t ω)) :
    progress β ε ≤ certAt X Y r β δ t ω 0 s₁ / ZtildeAt X Y r β δ t ω 0 s₁ := by
  simpa only [certAt, ZtildeAt, Fin.val_zero, Nat.sub_zero] using
    progress_le_cert_div_optZ_fst_of_pos hr hβ hδ hδ1 hε hstop

/-- **Bound on the stopping time** (`β > 0`): at every `ω` of the good event at which the policies
played are the greedy ones (almost surely the case in a run of Entropic-BPI), the stopping time
is at most `upperBound S A H β ε δ G_max(M)`; in particular it is finite. -/
lemma stoppingTime_le_upperBound_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℝ}
    (hε : 0 < ε) (hω : ω ∈ goodEvent X Y M s₁ β δ) (hX : ∀ t, X t ω = greedyAt X Y r β δ t ω) :
    ((entropicBPI H r β δ ε s₁).stoppingTime (fun _ _ ↦ ()) X Y ω : ℝ≥0∞)
      ≤ ENNReal.ofReal
        (upperBound (Fintype.card S) (Fintype.card A) H β ε δ (maxReturn M H s₁)) := by
  refine ENat.toENNReal_le_ofReal_of_forall_natCast_le fun T hT ↦ ?_
  have hx := sum_occupancy_mul_starRateMinAt_le hδ hδ1 hω.2 T
  have hy := sum_occupancy_mul_klRateMinAt_le hδ hδ1 hω.2 T
  simp only [hX] at hx hy
  refine natCast_le_upperBound (one_le_card_of_elem s₁) Fintype.card_pos hβ.ne' hε hδ hδ1
    (x := fun t ↦ ∑ h : Fin H, ∑ s, ∑ a,
      occupancy M (greedyAt X Y r β δ t ω).extend s₁ h s a * starRateMinAt X Y δ h s a t ω)
    (y := fun t ↦ ∑ h : Fin H, ∑ s, ∑ a,
      occupancy M (greedyAt X Y r β δ t ω).extend s₁ h s a * klRateMinAt X Y δ h s a t ω)
    (fun t ↦ sum_nonneg fun h _ ↦ sum_nonneg fun s _ ↦ sum_nonneg fun a _ ↦
      mul_nonneg (occupancy_nonneg _ _ _ _ _ _) (rateMin_nonneg (alphaStar_nonneg _ _ _ hδ hδ1) _))
    (fun t ht ↦ ?_) hx hy
  have hlt : (t : ℕ∞) < (entropicBPI H r β δ ε s₁).stoppingTime (fun _ _ ↦ ()) X Y ω :=
    lt_of_lt_of_le (by exact_mod_cast ht) hT
  exact (progress_le_certAt_div_ZtildeAt_of_pos hr hβ hδ hδ1 hε.le
    (not_stopCond_histAt_of_lt_stoppingTime hlt)).trans
    (certAt_div_ZtildeAt_le_of_pos hM hr hβ hδ hδ1 hω t)

variable {P : Measure Ω} [IsProbabilityMeasure P] {out : Ω → Policy S A H}

/-- **PAC guarantee of Entropic-BPI** (`β > 0`): in every run in the episode environment of `M`
from `s₁`, the output is `ε`-optimal with probability at least `1 - δ`. -/
lemma measureReal_bad_le_of_pos (hM : M.HasRewardFn r) (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (h : (entropicBPI H r β δ ε s₁).IsRun (statesEnv M H s₁) (fun _ _ ↦ ()) X Y out P) :
    P.real {ω | ε < optEntropicValue M H β 0 s₁ - entropicValue M H β (out ω).extend 0 s₁}
      ≤ δ :=
  measureReal_bad_le h hδ.le (measure_compl_goodEvent_le h.isAlgEnvSeq hM hr β hδ hδ1)
    (fun _ hω hX ↦ stoppingTime_ne_top_of_le
      (stoppingTime_le_upperBound_of_pos hM hr hβ hδ hδ1 hε hω hX))
    (fun _ hω _ hstop ↦
      optEntropicValue_sub_entropicValue_greedyAt_le_of_pos hM hr hβ hδ hδ1 hω hε.le hstop)

/-- **Sample complexity of Entropic-BPI** (`β > 0`): in every run in the episode environment of
`M` from `s₁`, the stopping time is at most `upperBound S A H β ε δ G_max(M)` with probability at
least `1 - δ`. -/
lemma one_sub_le_measureReal_stoppingTime_le_of_pos (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : 0 < β) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℝ}
    (hε : 0 < ε)
    (h : (entropicBPI H r β δ ε s₁).IsRun (statesEnv M H s₁) (fun _ _ ↦ ()) X Y out P) :
    1 - δ ≤ P.real {ω | ((entropicBPI H r β δ ε s₁).stoppingTime (fun _ _ ↦ ()) X Y ω : ℝ≥0∞)
      ≤ ENNReal.ofReal (upperBound (Fintype.card S) (Fintype.card A) H β ε δ (maxReturn M H s₁))} :=
  one_sub_le_measureReal_stoppingTime_le h hδ.le
    (measure_compl_goodEvent_le h.isAlgEnvSeq hM hr β hδ hδ1)
    (fun _ hω hX ↦ stoppingTime_le_upperBound_of_pos hM hr hβ hδ hδ1 hε hω hX)

end Run

end Essakine2026Tight
