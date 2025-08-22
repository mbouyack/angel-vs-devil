import AngelDevil.Basic
import AngelDevil.Subjourney
import AngelDevil.Util

set_option linter.style.longLine false
set_option linter.style.multiGoal false

/- This file contains only a single result: the lower bound on the journey length
   Ideally this result would be placed in 'Main' or 'Basic', but we have the
   following dependency chain (left depending on right):

    Main → Runner → Nice → Bound → Subjourney → Basic

  The alternative would be to place this result in either Nice.lean or Subjourney.lean
  but it isn't really a good fit for either of those. So it gets its own file.
-/

-- We can set a lower bound on the length of a journey based on
-- how far from the origin the angel has moved
lemma journey_lb {p : Nat} (A : Journey p) (N : Nat) : p * N < dist (0, 0) (last A) → N < steps A := by
  intro h
  -- Prove that steps ≠ 0
  have snz : steps A ≠ 0 := by
    intro sz
    rw [last, cell_congr_idx A sz (Nat.lt_add_one _), journey_start, dist_self] at h
    exact Nat.not_lt_zero _ h
  -- Prove a trivial but useful upper bound on steps A - 1
  have splt : steps A - 1 < steps A + 1 :=
    Nat.sub_one_lt_of_le (Nat.pos_of_ne_zero snz) (Nat.le_of_lt (Nat.lt_add_one _))
  by_cases Nz : N = 0
  · subst Nz
    exact Nat.pos_of_ne_zero snz
  rename' Nz => Nnz; push_neg at Nnz
  -- Show that the antecedant holds for N-1
  -- This is essentially the induction step
  have hlb : p * (N - 1) < dist (0, 0) (last (subjourney A (steps A - 1) splt)) := by
    contrapose! h
    replace h := (Nat.mul_add_one _ _) ▸ (add_le_add_right h p)
    rw [subjourney_last_cell, Nat.sub_one_add_one Nnz] at h
    apply le_trans _ h
    calc
      dist (0, 0) (last A) ≤ dist (0, 0) (cell A (steps A - 1) splt) + dist (cell A (steps A - 1) splt) (last A) := by
        apply dist_tri
      _ ≤ dist (0, 0) (cell A (steps A - 1) splt) + p := by
        apply Nat.add_le_add_left
        convert journey_steps_close A (steps A - 1) (Nat.sub_one_lt snz)
        rw [last]; congr
        exact (Nat.sub_one_add_one snz).symm
  -- Apply 'journey_lb' recursively
  have := (journey_lb (subjourney A (steps A - 1) splt) (N-1)) hlb
  rw [subjourney_steps] at this
  -- Add one to both sides and cancel to close the goal
  apply Nat.add_one_lt_add_one_iff.mpr at this
  rwa [Nat.sub_one_add_one snz, Nat.sub_one_add_one Nnz] at this
