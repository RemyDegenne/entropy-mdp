/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# The logarithmic sum bound

For a sequence `u` with values in `[0, 1]` and partial sums `U t = ∑ i < t, u i`,
`∑ t < T, u t / max (U t) 1 ≤ 3 log (U T + 1)` (`Real.sum_div_max_one_le_three_mul_log`; this is
Lemma 8 of Ménard et al., *Fast active learning for pure exploration in reinforcement learning*,
2021, with the constant `3` in place of `4`; the form with `4` is
`Real.sum_div_max_one_le_four_mul_log`). It follows from the one-step bound
`u / max U 1 ≤ 3 log ((U + u + 1) / (U + 1))` (`Real.div_max_one_le_three_mul_log`) by
telescoping.
-/

@[expose] public section

namespace Real

/-- One step of the logarithmic sum bound: `u / max U 1 ≤ 3 log ((U + u + 1) / (U + 1))` for
`U ≥ 0` and `u ∈ [0, 1]`. -/
lemma div_max_one_le_three_mul_log {U u : ℝ} (hU : 0 ≤ U) (hu : u ∈ Set.Icc 0 1) :
    u / max U 1 ≤ 3 * log ((U + u + 1) / (U + 1)) := by
  obtain ⟨hu0, hu1⟩ := hu
  have hpos : 0 < U + 1 := by linarith
  have hpos' : 0 < U + u + 1 := by linarith
  have hlog : u / (U + u + 1) ≤ log ((U + u + 1) / (U + 1)) := by
    have h := one_sub_inv_le_log_of_pos (x := (U + u + 1) / (U + 1)) (by positivity)
    rw [inv_div] at h
    calc u / (U + u + 1) = 1 - (U + 1) / (U + u + 1) := by field_simp; ring
      _ ≤ _ := h
  have hmax : u / max U 1 ≤ 3 * u / (U + u + 1) := by
    rw [div_le_div_iff₀ (lt_max_of_lt_right one_pos) hpos']
    have h3 : U + u + 1 ≤ 3 * max U 1 := by
      rcases le_or_gt 1 U with h | h
      · rw [max_eq_left h]; linarith
      · rw [max_eq_right h.le]; linarith
    nlinarith
  calc u / max U 1 ≤ 3 * u / (U + u + 1) := hmax
    _ = 3 * (u / (U + u + 1)) := by ring
    _ ≤ 3 * log ((U + u + 1) / (U + 1)) := by linarith

/-- The logarithmic sum bound: for `u` with values in `[0, 1]` and `U t = ∑ i < t, u i`,
`∑ t < T, u t / max (U t) 1 ≤ 3 log (U T + 1)`. -/
lemma sum_div_max_one_le_three_mul_log {u : ℕ → ℝ} (hu : ∀ t, u t ∈ Set.Icc 0 1) (T : ℕ) :
    ∑ t ∈ Finset.range T, u t / max (∑ i ∈ Finset.range t, u i) 1
      ≤ 3 * log (∑ i ∈ Finset.range T, u i + 1) := by
  have hU : ∀ t, 0 ≤ ∑ i ∈ Finset.range t, u i :=
    fun t ↦ Finset.sum_nonneg fun i _ ↦ (hu i).1
  have hstep : ∀ t, u t / max (∑ i ∈ Finset.range t, u i) 1
      ≤ 3 * (log (∑ i ∈ Finset.range (t + 1), u i + 1)
        - log (∑ i ∈ Finset.range t, u i + 1)) := by
    intro t
    have h := div_max_one_le_three_mul_log (hU t) (hu t)
    rw [Finset.sum_range_succ]
    rwa [log_div (by linarith [(hu t).1, hU t]) (by linarith [hU t])] at h
  calc ∑ t ∈ Finset.range T, u t / max (∑ i ∈ Finset.range t, u i) 1
      ≤ ∑ t ∈ Finset.range T, 3 * (log (∑ i ∈ Finset.range (t + 1), u i + 1)
          - log (∑ i ∈ Finset.range t, u i + 1)) := Finset.sum_le_sum fun t _ ↦ hstep t
    _ = 3 * (log (∑ i ∈ Finset.range T, u i + 1) - log (∑ i ∈ Finset.range 0, u i + 1)) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (fun t ↦ log (∑ i ∈ Finset.range t, u i + 1))]
    _ = 3 * log (∑ i ∈ Finset.range T, u i + 1) := by simp

/-- The logarithmic sum bound with the constant `4` of Lemma 8 of Ménard et al. (2021):
for `u` with values in `[0, 1]` and `U t = ∑ i < t, u i`,
`∑ t < T, u t / max (U t) 1 ≤ 4 log (U T + 1)`. -/
lemma sum_div_max_one_le_four_mul_log {u : ℕ → ℝ} (hu : ∀ t, u t ∈ Set.Icc 0 1) (T : ℕ) :
    ∑ t ∈ Finset.range T, u t / max (∑ i ∈ Finset.range t, u i) 1
      ≤ 4 * log (∑ i ∈ Finset.range T, u i + 1) := by
  refine (sum_div_max_one_le_three_mul_log hu T).trans ?_
  have : 0 ≤ log (∑ i ∈ Finset.range T, u i + 1) :=
    log_nonneg (by linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.range T) ↦ (hu i).1])
  linarith

end Real
