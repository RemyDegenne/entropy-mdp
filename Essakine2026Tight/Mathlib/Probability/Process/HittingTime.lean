/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Process.HittingTime

/-!
# The value and the process at a hitting time

For a process `u : ι → Ω → β` and a set `s`, Mathlib's `hittingAfter u s a` is the first time
`≥ a` at which `u` is in `s` (`⊤` if there is none). We name the value of the process at that
time, `hittingValue u s a := stoppedValue u (hittingAfter u s a)`, and the process stopped at
that time, `hittingProcess u s a := stoppedProcess u (hittingAfter u s a)`.
-/

@[expose] public section

namespace MeasureTheory

variable {Ω β ι : Type*} [ConditionallyCompleteLinearOrder ι] [Nonempty ι] {u : ι → Ω → β}
  {s : Set β} {a i : ι} {ω : Ω}

/-- The value of the process `u` where it first hits `s` after time `a` (its value at an
arbitrary time if it never does). -/
noncomputable def hittingValue (u : ι → Ω → β) (s : Set β) (a : ι) : Ω → β :=
  stoppedValue u (hittingAfter u s a)

/-- The process `u` stopped when it first hits `s` after time `a`. -/
noncomputable def hittingProcess (u : ι → Ω → β) (s : Set β) (a : ι) : ι → Ω → β :=
  stoppedProcess u (hittingAfter u s a)

/-- Unfolding lemma for `hittingValue`. -/
lemma hittingValue_def : hittingValue u s a = stoppedValue u (hittingAfter u s a) := rfl

/-- Unfolding lemma for `hittingProcess`. -/
lemma hittingProcess_def : hittingProcess u s a = stoppedProcess u (hittingAfter u s a) := rfl

/-- The value at the hitting time, pointwise. -/
lemma hittingValue_apply (ω : Ω) :
    hittingValue u s a ω = u (hittingAfter u s a ω).untopA ω := rfl

/-- The process stopped at the hitting time, pointwise. -/
lemma hittingProcess_apply (i : ι) (ω : Ω) :
    hittingProcess u s a i ω = u (min (i : WithTop ι) (hittingAfter u s a ω)).untopA ω := rfl

/-- The process stopped at the hitting time, at time `i`, is the value at `min i τ`. -/
lemma hittingProcess_eq_stoppedValue (i : ι) :
    hittingProcess u s a i = stoppedValue u fun ω ↦ min (i : WithTop ι) (hittingAfter u s a ω) :=
  rfl

/-- When the hitting time is finite, the value at the hitting time belongs to `s`. -/
lemma hittingValue_mem [WellFoundedLT ι] (h : hittingAfter u s a ω ≠ ⊤) :
    hittingValue u s a ω ∈ s :=
  hittingAfter_mem_set_of_ne_top h

/-- Before the hitting time, the process stopped at the hitting time is the process. -/
lemma hittingProcess_eq_of_le (h : (i : WithTop ι) ≤ hittingAfter u s a ω) :
    hittingProcess u s a i ω = u i ω :=
  stoppedProcess_eq_of_le h

/-- After the hitting time, the process stopped at the hitting time is the value at the hitting
time. -/
lemma hittingProcess_eq_of_ge (h : hittingAfter u s a ω ≤ i) :
    hittingProcess u s a i ω = hittingValue u s a ω :=
  stoppedProcess_eq_of_ge h

/-- The process stopped at the hitting time of the empty set is the process itself. -/
lemma hittingProcess_empty (a : ι) : hittingProcess u ∅ a = u := by
  rw [hittingProcess_def, hittingAfter_empty, stoppedProcess_const_top]

end MeasureTheory
