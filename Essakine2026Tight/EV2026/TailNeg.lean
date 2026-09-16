/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Essakine2026Tight.EV2026.AnalysisNeg
public import Essakine2026Tight.EV2026.Events
public import Essakine2026Tight.EV2026.TailCommon

/-!
# Analysis of Entropic-BPI for `β < 0`: the stopping time and the PAC guarantee

Essakine, Vernade (2026), Appendix B.2, the proof of the sample complexity for `β < 0`
(blueprint chapter "Analysis of Entropic-BPI for β < 0", Sections "The certificate under the true
kernel" and "Bounding the stopping time"). As in `EV2026/AnalysisNeg.lean`, the lemmas are first
proved at a history satisfying the concentration inequalities (`HistConcentration`), then for a
run on the good event:

* the unrolled certificate (`lem:cert_unrolled_neg`): `cert_le_exp_mul_sum_integral_of_neg`,
  `certAt_le_exp_mul_sum_integral_of_neg`;
* the normalized certificate bound (`lem:ratio_bound_neg`): `cert_div_expValue_le_of_neg`,
  `cert_div_optZ_snd_add_cert_le_of_neg`, `certAt_div_ZlowerAt_add_certAt_le_of_neg`;
* the progress at a non-stopping episode (`lem:progress_neg`, no event needed):
  `progress_le_cert_div_optZ_snd_add_cert_of_neg`,
  `progress_le_certAt_div_ZlowerAt_add_certAt_of_neg`;
* the bound on the stopping time (`lem:stopping_time_bound_neg`), at an `ω` of the good event at
  which the policies played are the greedy ones: `stoppingTime_le_upperBound_of_neg`;
* the PAC guarantee and the sample complexity in probability (`lem:pac_neg`), for every run:
  `measureReal_bad_le_of_neg`, `one_sub_le_measureReal_stoppingTime_le_of_neg`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP.Episodic Learning.MDP
open scoped ENNReal

namespace Essakine2026Tight

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] [Nonempty A]
  [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A] [MeasurableSingletonClass A]
  {H : ℕ} {M : EpisodicMDP S A H} {r : Fin H → S → A → ℝ} {β δ : ℝ} {t : ℕ}
  {hist : Hist Unit (Policy S A H) (Traj S H) t}

/-! ### At a history -/

section History

/-- **Unrolled certificate** (`β < 0`), at a history satisfying the concentration inequalities:
with `π` the greedy policy, `π_1 G_1(s₁)` is at most
`e^13 ∑_h E^π[e^{β ∑_{i ≤ h} r_i} 36 √(Var_{p_h}(Z^π_{h+1})(S_h, A_h) ρ*_h(S_h, A_h))
+ 84 H ρ_h(S_h, A_h)]`. -/
lemma cert_le_exp_mul_sum_integral_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (s₁ : S) :
    cert r β δ hist H s₁ ≤ Real.exp 13 * ∑ h : Fin H,
      ∫ x, (Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x))
          * (36 * √(vecVar (M.transVec h (IT.obs h x).1 (IT.action h x))
              (expValue M β (greedy r β δ hist) h.succ)
            * rateMin (alphaStar (Fintype.card S) (Fintype.card A) H δ)
              (visitCount hist h (IT.obs h x).1 (IT.action h x))))
        + 84 * H * rateMin (alphaKL (Fintype.card S) (Fintype.card A) H δ)
          (visitCount hist h (IT.obs h x).1 (IT.action h x)))
        ∂stepLaw M (greedy r β δ hist) (s₁, startStep H) := by
  set π := greedy r β δ hist with hπ
  set P := stepLaw M π (s₁, startStep H) with hP
  set v : Fin H → S → A → ℝ := fun h s a ↦ √(vecVar (M.transVec h s a) (expValue M β π h.succ)
    * rateMin (alphaStar (Fintype.card S) (Fintype.card A) H δ) (visitCount hist h s a)) with hv
  set ρ : Fin H → S → A → ℝ := fun h s a ↦
    rateMin (alphaKL (Fintype.card S) (Fintype.card A) H δ) (visitCount hist h s a) with hρ
  have hρ0 : ∀ h s a, 0 ≤ ρ h s a := fun h s a ↦ rateMin_nonneg (alphaKL_nonneg _ _ _ hδ hδ1) _
  have hu : ∀ (h : Fin H) (s : S) (a : A),
      0 ≤ 36 * v h s a + 84 * H * Real.exp (-(β * r h s a)) * ρ h s a :=
    fun h s a ↦ add_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (mul_nonneg (by positivity) (hρ0 h s a))
  have hlast : ∀ s, cert r β δ hist (H - (Fin.last H : ℕ)) s = 0 := fun s ↦ by
    simp [cert_zero]
  have hg : ∀ (h : Fin H) (s : S), cert r β δ hist (H - (h.castSucc : ℕ)) s
      ≤ Real.exp (β * r h s (π h s))
        * ((36 * v h s (π h s) + 84 * H * Real.exp (-(β * r h s (π h s))) * ρ h s (π h s))
          + (1 + 13 / H) * vecExp (M.transVec h s (π h s))
            (fun s' ↦ cert r β δ hist (H - (h.succ : ℕ)) s')) := by
    intro h s
    have := cert_le_of_neg hM hr hβ hδ hδ1 hc h s
    rw [Fin.val_castSucc, sub_succ_eq]
    have e : Real.exp (β * r h s (π h s)) * Real.exp (-(β * r h s (π h s))) = 1 := by
      rw [← Real.exp_add]; simp
    refine this.trans_eq ?_
    simp only [hv, hρ]
    linear_combination (-(84 * H * rateMin (alphaKL (Fintype.card S) (Fintype.card A) H δ)
      (visitCount hist h s (π h s)))) * e
  have hun := le_exp_mul_sum_integral_of_backward (M := M) (π := π) (s₁ := s₁)
    (by norm_num : (0 : ℝ) ≤ 13) (g := fun h s ↦ cert r β δ hist (H - h) s) hu hlast hg
  refine hun.trans (mul_le_mul_of_nonneg_left (sum_le_sum fun h _ ↦ ?_) (Real.exp_pos _).le)
  refine integral_mono (integrable_exp_sum_mul P β r (Iic h)
      (fun s a ↦ 36 * v h s a + 84 * H * Real.exp (-(β * r h s a)) * ρ h s a) h)
    ((integrable_exp_sum_mul P β r (Iic h) (fun s a ↦ 36 * v h s a) h).add
      ((integrable_comp_obs_action P (ρ h) h).const_mul (84 * H))) fun x ↦ ?_
  have hW : Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x))
      * Real.exp (-(β * r h (IT.obs h x).1 (IT.action h x))) ≤ 1 := by
    rw [← Real.exp_add, Real.exp_le_one_iff]
    have : r h (IT.obs h x).1 (IT.action h x) ≤ ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x) :=
      single_le_sum (f := fun i ↦ r i (IT.obs i x).1 (IT.action i x))
        (fun i _ ↦ (hr _ _ _).1) (mem_Iic.2 le_rfl)
    nlinarith
  have hc0 : 0 ≤ 84 * (H : ℝ) * ρ h (IT.obs h x).1 (IT.action h x) :=
    mul_nonneg (by positivity) (hρ0 _ _ _)
  simp only
  nlinarith

/-- **Normalized certificate bound** (`β < 0`), at a history satisfying the concentration
inequalities: with `π` the greedy policy, `x = ∑_{h, s, a} p^π_h(s, a) ρ*_h(s, a)` and
`y = ∑_{h, s, a} p^π_h(s, a) ρ_h(s, a)`,
`π_1 G_1(s₁) / Z^π_1(s₁) ≤ e^13 (36 √(V_G x) + 84 H e^{|β| H} y)` with `G = G_max(M)`. -/
lemma cert_div_expValue_le_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (s₁ : S) :
    cert r β δ hist H s₁ / expValue M β (greedy r β δ hist) (startStep H) s₁ ≤ Real.exp 13 *
      (36 * √(varianceFactor β (maxReturn M s₁) * ∑ h, ∑ s, ∑ a,
          occupancy M (greedy r β δ hist) s₁ h s a
            * rateMin (alphaStar (Fintype.card S) (Fintype.card A) H δ) (visitCount hist h s a))
        + 84 * H * Real.exp (|β| * H) * ∑ h, ∑ s, ∑ a,
          occupancy M (greedy r β δ hist) s₁ h s a
            * rateMin (alphaKL (Fintype.card S) (Fintype.card A) H δ) (visitCount hist h s a)) := by
  set π := greedy r β δ hist with hπ
  set P := stepLaw M π (s₁, startStep H) with hP
  set ρs : Fin H → S → A → ℝ := fun h s a ↦
    rateMin (alphaStar (Fintype.card S) (Fintype.card A) H δ) (visitCount hist h s a) with hρs
  set ρ : Fin H → S → A → ℝ := fun h s a ↦
    rateMin (alphaKL (Fintype.card S) (Fintype.card A) H δ) (visitCount hist h s a) with hρ
  have hρs0 : ∀ h s a, 0 ≤ ρs h s a := fun h s a ↦ rateMin_nonneg (alphaStar_nonneg _ _ _ hδ hδ1) _
  have hρ0 : ∀ h s a, 0 ≤ ρ h s a := fun h s a ↦ rateMin_nonneg (alphaKL_nonneg _ _ _ hδ hδ1) _
  have hRw := rewardsIn_Icc_of_hasRewardFn hM hr
  -- the denominator
  have hZ : Real.exp (β * H) ≤ expValue M β π (startStep H) s₁ := by
    have := (expValue_mem_Icc_of_neg hM hr hβ π (startStep H) s₁).1
    simpa [startStep] using this
  have hZpos : 0 < expValue M β π (startStep H) s₁ := (Real.exp_pos _).trans_le hZ
  have hZE : 1 ≤ Real.exp (|β| * H) * expValue M β π (startStep H) s₁ := by
    have e : Real.exp (|β| * H) * Real.exp (β * H) = 1 := by
      rw [← Real.exp_add, abs_of_neg hβ]; simp
    calc (1 : ℝ) = Real.exp (|β| * H) * Real.exp (β * H) := e.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hZ (Real.exp_pos _).le
  -- the unrolled certificate, split into the variance and the rate terms
  have hun := cert_le_exp_mul_sum_integral_of_neg hM hr hβ hδ hδ1 hc s₁
  have hsplit : ∑ h : Fin H,
      ∫ x, (Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x))
          * (36 * √(vecVar (M.transVec h (IT.obs h x).1 (IT.action h x))
              (expValue M β π h.succ) * ρs h (IT.obs h x).1 (IT.action h x)))
        + 84 * H * ρ h (IT.obs h x).1 (IT.action h x)) ∂P
      = 36 * ∑ h : Fin H, ∫ x, Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x))
          * √(vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M β π h.succ)
            * ρs h (IT.obs h x).1 (IT.action h x)) ∂P
        + 84 * H * ∑ h, ∑ s, ∑ a, occupancy M π s₁ h s a * ρ h s a := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun h _ ↦ ?_
    have e1 : ∫ x, 84 * (H : ℝ) * ρ h (IT.obs h x).1 (IT.action h x) ∂P
        = 84 * H * ∑ s, ∑ a, occupancy M π s₁ h s a * ρ h s a := by
      rw [integral_const_mul, hP, integral_comp_obs_action_stepLaw]
    have e2 : ∫ x, Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x))
          * (36 * √(vecVar (M.transVec h (IT.obs h x).1 (IT.action h x))
              (expValue M β π h.succ) * ρs h (IT.obs h x).1 (IT.action h x))) ∂P
        = 36 * ∫ x, Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x))
          * √(vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M β π h.succ)
            * ρs h (IT.obs h x).1 (IT.action h x)) ∂P := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      simp only
      ring
    rw [integral_add, e1, e2]
    · exact integrable_exp_sum_mul P β r (Iic h)
        (fun s a ↦ 36 * √(vecVar (M.transVec h s a) (expValue M β π h.succ) * ρs h s a)) h
    · exact (integrable_comp_obs_action P (ρ h) h).const_mul _
  have hvar := sum_integral_exp_mul_sqrt_vecVar_mul_le (π := π) (s₁ := s₁) hM β hρs0
  have hVG := variance_exp_episodeReturn_div_sq_le_maxReturn (β := β) hRw π s₁
  have hVar : √(variance (fun x ↦ Real.exp (β * episodeReturn H x)) P)
      ≤ √(varianceFactor β (maxReturn M s₁)) * expValue M β π (startStep H) s₁ := by
    have h1 : variance (fun x ↦ Real.exp (β * episodeReturn H x)) P
        ≤ varianceFactor β (maxReturn M s₁) * expValue M β π (startStep H) s₁ ^ 2 := by
      rw [div_le_iff₀ (by positivity)] at hVG
      exact hVG
    calc √(variance (fun x ↦ Real.exp (β * episodeReturn H x)) P)
        ≤ √(varianceFactor β (maxReturn M s₁) * expValue M β π (startStep H) s₁ ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = _ := by rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hZpos.le]
  have hy0 : 0 ≤ ∑ h, ∑ s, ∑ a, occupancy M π s₁ h s a * ρ h s a :=
    sum_nonneg fun h _ ↦ sum_nonneg fun s _ ↦ sum_nonneg fun a _ ↦
      mul_nonneg (occupancy_nonneg _ _ _ _ _ _) (hρ0 _ _ _)
  have hH0 : 0 ≤ 84 * (H : ℝ) * ∑ h, ∑ s, ∑ a, occupancy M π s₁ h s a * ρ h s a := by positivity
  rw [div_le_iff₀ hZpos, Real.sqrt_mul (varianceFactor_nonneg _ _)]
  calc cert r β δ hist H s₁
      ≤ Real.exp 13 * (36 * ∑ h : Fin H, ∫ x,
          Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x))
          * √(vecVar (M.transVec h (IT.obs h x).1 (IT.action h x)) (expValue M β π h.succ)
            * ρs h (IT.obs h x).1 (IT.action h x)) ∂P
        + 84 * H * ∑ h, ∑ s, ∑ a, occupancy M π s₁ h s a * ρ h s a) := by
        rw [← hsplit]
        exact hun
    _ ≤ Real.exp 13 * (36 * ((√(varianceFactor β (maxReturn M s₁))
          * expValue M β π (startStep H) s₁)
          * √(∑ h, ∑ s, ∑ a, occupancy M π s₁ h s a * ρs h s a))
        + 84 * H * (∑ h, ∑ s, ∑ a, occupancy M π s₁ h s a * ρ h s a)
          * (Real.exp (|β| * H) * expValue M β π (startStep H) s₁)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left
          (hvar.trans (mul_le_mul_of_nonneg_right hVar (Real.sqrt_nonneg _))) (by norm_num))
          (le_mul_of_one_le_right hH0 hZE)) (Real.exp_pos _).le
    _ = _ := by ring

/-- **Normalized certificate bound** (`β < 0`), with the computable ratio: at a history satisfying
the concentration inequalities, `π_1 G_1(s₁) / (Z̲_1(s₁) + π_1 G_1(s₁))` is at most
`e^13 (36 √(V_G x) + 84 H e^{|β| (H + 1)} y)`. -/
lemma cert_div_optZ_snd_add_cert_le_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : HistConcentration M β δ hist) (s₁ : S) :
    cert r β δ hist H s₁ / ((optZ r β δ hist H).2 s₁ + cert r β δ hist H s₁) ≤ Real.exp 13 *
      (36 * √(varianceFactor β (maxReturn M s₁) * ∑ h, ∑ s, ∑ a,
          occupancy M (greedy r β δ hist) s₁ h s a
            * rateMin (alphaStar (Fintype.card S) (Fintype.card A) H δ) (visitCount hist h s a))
        + 84 * H * Real.exp (|β| * (H + 1 : ℕ)) * ∑ h, ∑ s, ∑ a,
          occupancy M (greedy r β δ hist) s₁ h s a
            * rateMin (alphaKL (Fintype.card S) (Fintype.card A) H δ) (visitCount hist h s a)) := by
  have hZ : Real.exp (β * H) ≤ expValue M β (greedy r β δ hist) (startStep H) s₁ := by
    have := (expValue_mem_Icc_of_neg hM hr hβ (greedy r β δ hist) (startStep H) s₁).1
    simpa [startStep] using this
  have hZpos : 0 < expValue M β (greedy r β δ hist) (startStep H) s₁ :=
    (Real.exp_pos _).trans_le hZ
  have h1 : expValue M β (greedy r β δ hist) (startStep H) s₁ ≤ ringZ M r β δ hist H s₁ :=
    (optZ_fst_le_ringZ_and_expValue_le_of_neg (δ := δ) (hist := hist) hM hr hβ (startStep H) s₁).2
  have h2 : ringZ M r β δ hist H s₁ - (optZ r β δ hist H).2 s₁ ≤ cert r β δ hist H s₁ :=
    ringZ_sub_optZ_snd_le_cert_of_neg hM hr hβ hδ hδ1 hc (startStep H) s₁
  have hg0 : 0 ≤ cert r β δ hist H s₁ := (cert_mem hist r β δ hδ hδ1 H le_rfl s₁).1
  have hy0 : 0 ≤ ∑ h, ∑ s, ∑ a, occupancy M (greedy r β δ hist) s₁ h s a
      * rateMin (alphaKL (Fintype.card S) (Fintype.card A) H δ) (visitCount hist h s a) :=
    sum_nonneg fun h _ ↦ sum_nonneg fun s _ ↦ sum_nonneg fun a _ ↦
      mul_nonneg (occupancy_nonneg _ _ _ _ _ _) (rateMin_nonneg (alphaKL_nonneg _ _ _ hδ hδ1) _)
  refine (div_le_div_of_nonneg_left hg0 hZpos (by linarith)).trans
    ((cert_div_expValue_le_of_neg hM hr hβ hδ hδ1 hc s₁).trans ?_)
  gcongr
  linarith

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- **Progress at a non-stopping episode** (`β < 0`; no event is needed): if the stopping
condition fails, `κ(β, ε) ≤ π_1 G_1(s₁) / (Z̲_1(s₁) + π_1 G_1(s₁))`. -/
lemma progress_le_cert_div_optZ_snd_add_cert_of_neg (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε) {s₁ : S}
    (hstop : ¬ stopCond r β δ ε s₁ hist) :
    progress β ε ≤ cert r β δ hist H s₁ / ((optZ r β δ hist H).2 s₁ + cert r β δ hist H s₁) := by
  simp only [stopCond, hβ.not_gt, ↓reduceIte, not_le] at hstop
  obtain ⟨-, hZl, -⟩ := optZ_mem_of_neg (hist := hist) hr hβ hδ hδ1 H le_rfl s₁
  have hc0 : 0 < (optZ r β δ hist H).2 s₁ := (Real.exp_pos _).trans_le hZl
  have hg0 : 0 ≤ cert r β δ hist H s₁ := (cert_mem hist r β δ hδ hδ1 H le_rfl s₁).1
  rw [le_div_iff₀ (by linarith)]
  -- `κ = (1 - v) v / 2` with `v = e^{β ε} ∈ (0, 1]`
  have hv0 := Real.exp_pos (β * ε)
  have hv1 : Real.exp (β * ε) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hκ : progress β ε = (1 - Real.exp (β * ε)) * Real.exp (β * ε) / 2 := by
    have e1 : Real.exp (-β * ε) * Real.exp (β * ε) = 1 := by
      rw [← Real.exp_add]; simp
    have e2 : Real.exp (-(2 : ℕ) * -β * ε) = Real.exp (β * ε) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    unfold progress
    rw [abs_of_neg hβ, e2]
    push_cast
    linear_combination (Real.exp (β * ε) / 2) * e1
  rw [hκ]
  have hκ1 : (1 - Real.exp (β * ε)) * Real.exp (β * ε) / 2 ≤ (1 - Real.exp (β * ε)) / 2 := by
    nlinarith
  have hκ2 : (1 - Real.exp (β * ε)) * Real.exp (β * ε) / 2 ≤ 1 / 2 := by nlinarith
  have h1 : (1 - Real.exp (β * ε)) * Real.exp (β * ε) / 2 * (optZ r β δ hist H).2 s₁
      ≤ cert r β δ hist H s₁ / 2 := by
    calc (1 - Real.exp (β * ε)) * Real.exp (β * ε) / 2 * (optZ r β δ hist H).2 s₁
        ≤ (1 - Real.exp (β * ε)) / 2 * (optZ r β δ hist H).2 s₁ :=
          mul_le_mul_of_nonneg_right hκ1 hc0.le
      _ ≤ cert r β δ hist H s₁ / 2 := by linarith
  have h2 : (1 - Real.exp (β * ε)) * Real.exp (β * ε) / 2 * cert r β δ hist H s₁
      ≤ cert r β δ hist H s₁ / 2 := by
    calc (1 - Real.exp (β * ε)) * Real.exp (β * ε) / 2 * cert r β δ hist H s₁
        ≤ 1 / 2 * cert r β δ hist H s₁ := mul_le_mul_of_nonneg_right hκ2 hg0
      _ = cert r β δ hist H s₁ / 2 := by ring
  linarith

end History

/-! ### On the good event of a run -/

section Run

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℕ → Ω → Policy S A H} {Y : ℕ → Ω → Traj S H}
  {s₁ : S} {ω : Ω}

/-- **Unrolled certificate** (`β < 0`): on the good event, for every episode `t`, with
`π = π^{t+1}`, `π_1 G_1^t(s₁)` is at most
`e^13 ∑_h E^π[e^{β ∑_{i ≤ h} r_i} 36 √(Var_{p_h}(Z^π_{h+1}) ρ*^t_h) + 84 H ρ^t_h]` (the rate
terms at `(S_h, A_h)`). -/
lemma certAt_le_exp_mul_sum_integral_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hω : ω ∈ goodEvent X Y M s₁ β δ) (t : ℕ) :
    certAt X Y r β δ t ω (startStep H) s₁ ≤ Real.exp 13 * ∑ h : Fin H,
      ∫ x, (Real.exp (β * ∑ i ∈ Iic h, r i (IT.obs i x).1 (IT.action i x))
          * (36 * √(vecVar (M.transVec h (IT.obs h x).1 (IT.action h x))
              (expValue M β (greedyAt X Y r β δ t ω) h.succ)
            * starRateMinAt X Y δ h (IT.obs h x).1 (IT.action h x) t ω))
        + 84 * H * klRateMinAt X Y δ h (IT.obs h x).1 (IT.action h x) t ω)
        ∂stepLaw M (greedyAt X Y r β δ t ω) (s₁, startStep H) :=
  cert_le_exp_mul_sum_integral_of_neg hM hr hβ hδ hδ1 (histConcentration_histAt hω t) s₁

/-- **Normalized certificate bound** (`β < 0`): on the good event, for every episode `t`, with
`π = π^{t+1}`, `x_t = ∑_{h, s, a} p^π_h(s, a) ρ*^t_h(s, a)` and
`y_t = ∑_{h, s, a} p^π_h(s, a) ρ^t_h(s, a)`,
`π_1 G_1^t(s₁) / (Z̲_1^t(s₁) + π_1 G_1^t(s₁)) ≤ e^13 (36 √(V_G x_t) + 84 H e^{|β| (H + 1)} y_t)`. -/
lemma certAt_div_ZlowerAt_add_certAt_le_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hω : ω ∈ goodEvent X Y M s₁ β δ) (t : ℕ) :
    certAt X Y r β δ t ω (startStep H) s₁
        / (ZlowerAt X Y r β δ t ω (startStep H) s₁ + certAt X Y r β δ t ω (startStep H) s₁)
      ≤ Real.exp 13 * (36 * √(varianceFactor β (maxReturn M s₁) * ∑ h, ∑ s, ∑ a,
          occupancy M (greedyAt X Y r β δ t ω) s₁ h s a * starRateMinAt X Y δ h s a t ω)
        + 84 * H * Real.exp (|β| * (H + 1 : ℕ)) * ∑ h, ∑ s, ∑ a,
          occupancy M (greedyAt X Y r β δ t ω) s₁ h s a * klRateMinAt X Y δ h s a t ω) :=
  cert_div_optZ_snd_add_cert_le_of_neg hM hr hβ hδ hδ1 (histConcentration_histAt hω t) s₁

omit [MeasurableSpace S] [MeasurableSingletonClass S] [MeasurableSpace A]
  [MeasurableSingletonClass A] in
/-- **Progress at a non-stopping episode** (`β < 0`; no event is needed): if the stopping
condition fails after `t` episodes,
`κ(β, ε) ≤ π_1 G_1^t(s₁) / (Z̲_1^t(s₁) + π_1 G_1^t(s₁))`. -/
lemma progress_le_certAt_div_ZlowerAt_add_certAt_of_neg (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε) {t : ℕ}
    (hstop : ¬ stopCond r β δ ε s₁ (histAt X Y t ω)) :
    progress β ε ≤ certAt X Y r β δ t ω (startStep H) s₁
      / (ZlowerAt X Y r β δ t ω (startStep H) s₁ + certAt X Y r β δ t ω (startStep H) s₁) :=
  progress_le_cert_div_optZ_snd_add_cert_of_neg hr hβ hδ hδ1 hε hstop

/-- **Bound on the stopping time** (`β < 0`): at every `ω` of the good event at which the policies
played are the greedy ones (almost surely the case in a run of Entropic-BPI), the stopping time
is at most `upperBound S A H β ε δ G_max(M)`; in particular it is finite. -/
lemma stoppingTime_le_upperBound_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℝ}
    (hε : 0 < ε) (hω : ω ∈ goodEvent X Y M s₁ β δ) (hX : ∀ t, X t ω = greedyAt X Y r β δ t ω) :
    ((entropicBPI r β δ ε s₁).stoppingTime (fun _ _ ↦ ()) X Y ω : ℝ≥0∞)
      ≤ ENNReal.ofReal (upperBound (Fintype.card S) (Fintype.card A) H β ε δ (maxReturn M s₁)) := by
  refine ENat.toENNReal_le_ofReal_of_forall_natCast_le fun T hT ↦ ?_
  have hx := sum_occupancy_mul_starRateMinAt_le hδ hδ1 hω.2 T
  have hy := sum_occupancy_mul_klRateMinAt_le hδ hδ1 hω.2 T
  simp only [hX] at hx hy
  refine natCast_le_upperBound (one_le_card_of_elem s₁) Fintype.card_pos hβ.ne hε hδ hδ1
    (x := fun t ↦ ∑ h, ∑ s, ∑ a,
      occupancy M (greedyAt X Y r β δ t ω) s₁ h s a * starRateMinAt X Y δ h s a t ω)
    (y := fun t ↦ ∑ h, ∑ s, ∑ a,
      occupancy M (greedyAt X Y r β δ t ω) s₁ h s a * klRateMinAt X Y δ h s a t ω)
    (fun t ↦ sum_nonneg fun h _ ↦ sum_nonneg fun s _ ↦ sum_nonneg fun a _ ↦
      mul_nonneg (occupancy_nonneg _ _ _ _ _ _) (rateMin_nonneg (alphaStar_nonneg _ _ _ hδ hδ1) _))
    (fun t ht ↦ ?_) hx hy
  have hlt : (t : ℕ∞) < (entropicBPI r β δ ε s₁).stoppingTime (fun _ _ ↦ ()) X Y ω :=
    lt_of_lt_of_le (by exact_mod_cast ht) hT
  exact (progress_le_certAt_div_ZlowerAt_add_certAt_of_neg hr hβ hδ hδ1 hε.le
    (not_stopCond_histAt_of_lt_stoppingTime hlt)).trans
    (certAt_div_ZlowerAt_add_certAt_le_of_neg hM hr hβ hδ hδ1 hω t)

variable {P : Measure Ω} [IsProbabilityMeasure P] {out : Ω → Policy S A H}

/-- **PAC guarantee of Entropic-BPI** (`β < 0`): in every run in the episode environment of `M`
from `s₁`, the output is `ε`-optimal with probability at least `1 - δ`. -/
lemma measureReal_bad_le_of_neg (hM : M.HasRewardFn r) (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (h : (entropicBPI r β δ ε s₁).IsRun (statesEnv M s₁) (fun _ _ ↦ ()) X Y out P) :
    P.real {ω | ε < optEntropicValue M β (startStep H) s₁
      - entropicValue M β (out ω) (startStep H) s₁} ≤ δ :=
  measureReal_bad_le h hδ.le (measure_compl_goodEvent_le h.isAlgEnvSeq hM hr β hδ hδ1)
    (fun _ hω hX ↦ stoppingTime_ne_top_of_le
      (stoppingTime_le_upperBound_of_neg hM hr hβ hδ hδ1 hε hω hX))
    (fun _ hω _ hstop ↦
      optEntropicValue_sub_entropicValue_greedyAt_le_of_neg hM hr hβ hδ hδ1 hω hε.le hstop)

/-- **Sample complexity of Entropic-BPI** (`β < 0`): in every run in the episode environment of
`M` from `s₁`, the stopping time is at most `upperBound S A H β ε δ G_max(M)` with probability at
least `1 - δ`. -/
lemma one_sub_le_measureReal_stoppingTime_le_of_neg (hM : M.HasRewardFn r)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1) (hβ : β < 0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℝ}
    (hε : 0 < ε)
    (h : (entropicBPI r β δ ε s₁).IsRun (statesEnv M s₁) (fun _ _ ↦ ()) X Y out P) :
    1 - δ ≤ P.real {ω | ((entropicBPI r β δ ε s₁).stoppingTime (fun _ _ ↦ ()) X Y ω : ℝ≥0∞)
      ≤ ENNReal.ofReal (upperBound (Fintype.card S) (Fintype.card A) H β ε δ (maxReturn M s₁))} :=
  one_sub_le_measureReal_stoppingTime_le h hδ.le
    (measure_compl_goodEvent_le h.isAlgEnvSeq hM hr β hδ hδ1)
    (fun _ hω hX ↦ stoppingTime_le_upperBound_of_neg hM hr hβ hδ hδ1 hε hω hX)

end Run

end Essakine2026Tight
