import AngelDevil.Defs
import AngelDevil.Basic

set_option linter.style.longLine false
set_option linter.style.multiGoal false

/-
  This file contains results related to the 'subjourney' structure
  Note that subjourney itself is defined in Defs.lean, since it is
  required to state our final result.
-/

lemma subjourney_steps {p : Nat} (A : Journey p) (n : Nat) (nlt : n < steps A + 1) :
  steps (subjourney A n nlt) = n := rfl

-- The number of steps in the subjourney is less than or equal to
-- the number of steps in the original journey
lemma subjourney_steps_le {p : Nat} (A : Journey p) (n : Nat) (nlt : n < steps A + 1) :
  steps (subjourney A n nlt) ≤ steps A := by rw [subjourney_steps]; linarith

-- The last cell in a subjourney is the same as the cell at
-- the corresponding step of the original journey
lemma subjourney_last_cell {p : Nat} (A : Journey p) (n : Nat) (nlt : n < steps A + 1) :
  last (subjourney A n nlt) = cell A n nlt := rfl

-- If the index used to create the subjourney is 'Fin.last'
-- the subjourney will be identical to the original journey
lemma subjourney_full {p : Nat} (A : Journey p) :
  subjourney A (steps A) (Nat.lt_add_one _) = A := by
  unfold subjourney; rfl

-- A cell in a subjourney matches the corresponding cell in the original journey
lemma subjourney_cell {p : Nat} (A : Journey p) (i j : Nat) (ilt : i < steps A + 1) (jle : j ≤ i) :
  cell (subjourney A i ilt) j (by rw [subjourney_steps]; linarith) =
  cell A j (Nat.lt_of_le_of_lt jle ilt) := rfl

-- A subjourney of a subjourney is a subjourney
lemma subjourney_subjourney {p : Nat} (A : Journey p) {i j : Nat} (jlt : j < i + 1) (ilt : i < steps A + 1) :
  subjourney (subjourney A i ilt) j (by rw [subjourney_steps]; linarith) =
  subjourney A j (lt_of_le_of_lt (Nat.le_of_lt_add_one jlt) ilt) := rfl

lemma subjourney_congr_idx {p : Nat} (A : Journey p) {i j : Nat} (hij : i = j) (ilt : i < steps A + 1) :
  subjourney A i ilt = subjourney A j (hij ▸ ilt) := by
  apply (journey_ext_iff _ _).mpr
  push_neg
  use Eq.trans (Eq.trans (subjourney_steps A i ilt) hij) (subjourney_steps A j (hij ▸ ilt)).symm
  intros
  subst hij
  rfl

lemma subjourney_congr_journey {p : Nat} {A B : Journey p} (hAB : A = B) (i : Nat) (ilt : i < steps A + 1) :
  subjourney A i ilt = subjourney B i (by rwa [← hAB]) := by
  apply (journey_ext_iff _ _).mpr
  push_neg
  use (by rw [subjourney_steps, subjourney_steps])
  intro j jlt
  subst hAB; rfl

-- The subjourney which includes all but the last step is often useful in
-- recursive definitions and proofs by induction
def subjourney_drop_last {p : Nat} (A : Journey p) (snz : steps A ≠ 0) : Journey p :=
  subjourney A (steps A - 1) (by
    apply Nat.le_of_lt_add_one (lt_of_eq_of_lt (Nat.sub_one_add_one snz) _)
    exact lt_trans (Nat.lt_add_one _) (Nat.lt_add_one _)
  )

-- The number of steps in 'subjourney_drop_last' is one less than
-- the number of steps in the original journey
lemma subjourney_drop_last_steps {p : Nat} (A : Journey p) (snz : steps A ≠ 0) :
  steps (subjourney_drop_last A snz) = (steps A) - 1 := by
  unfold subjourney_drop_last
  rw [subjourney_steps]

-- Identity for the 'subjourney_drop_last' of a subjourney
lemma subjourney_subjourney_drop_last {p : Nat} (A : Journey p)
  (n : Nat) (nnz : n ≠ 0) (nlt : n < steps A + 1) :
  subjourney_drop_last (subjourney A n nlt) (by rwa [subjourney_steps]) =
  (subjourney A (n-1) (lt_of_le_of_lt (Nat.sub_le _ _) nlt)) := by
  unfold subjourney_drop_last
  rw [subjourney_subjourney]
  apply subjourney_congr_idx
  · rw [subjourney_steps]
  · rw [subjourney_steps]
    exact lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_add_one _)

-- Identity for the subjourney of a 'subjourney_drop_last'
lemma subjourney_drop_last_subjourney {p : Nat} (A : Journey p)
  (n : Nat) (nlt : n < steps A) :
  subjourney (subjourney_drop_last A (Nat.ne_zero_of_lt nlt)) n (by
    rwa [subjourney_drop_last_steps, Nat.sub_one_add_one (Nat.ne_zero_of_lt nlt)]
  ) = subjourney A n (lt_trans nlt (Nat.lt_add_one _)) := by
  unfold subjourney_drop_last
  rw [subjourney_subjourney]
  rwa [Nat.sub_one_add_one (Nat.ne_zero_of_lt nlt)]
