import Mathlib.Tactic.Ring
import AngelDevil.Basic
import AngelDevil.Bound
import AngelDevil.Util

set_option linter.style.longLine false
set_option linter.style.multiGoal false

/- Máthé defines a "nice" devil as one who "never eats a square on which the Angel has
   previously stayed nor a square on which the Angel could have jumped at a previous stage but
   did not."

  We will define such a cell as a "mean" cell and a Nice Devil as one that never eats a mean cell.
  Note that the Nice Devil is *not* prohibited from eating cells close to the Angel, only those
  close to one of the Angel's prior locations.

  Note that the first condition - that a nice devil never eats a cell on which an angel has
  previously stayed - is only included to prevent the nice devil from ever eating (0, 0).
  That is, every other location on which an angel has stayed is also a cell the angel could have
  jumped to on a previous step.
-/

-- True if the ith cell in a Journey proves 'u' is "mean"
-- Used in various definitions and proofs below
abbrev mean_fun {p : Nat} (A : Journey p) (u : Int × Int) :=
  fun (i : Fin (steps A + 1)) ↦ i.val ≠ steps A ∧ close p u (cell A i.1 i.2)

def mean_cell {p : Nat} (A : Journey p) (u : Int × Int) : Prop :=
  u = (0, 0) ∨ ∃ i, mean_fun A u i

-- A "nice" devil never eats a "mean" cell. Note that referring to such cells as "mean" was not
-- in the original paper, but is useful for our purposes.
def nice (D : Devil) (p : Nat) : Prop :=
  ∀ (A : Journey p), ¬mean_cell A (response D A)

-- Determine whether a cell is nice
-- Note that this should be decidable, so we can use it in if statements
def is_nice_cell {p : Nat} (A : Journey p) (u : Int × Int) : Prop :=
  u ≠ (0, 0) ∧ ¬_can_sat (mean_fun A u)

instance {p : Nat} (A : Journey p) (u : Int × Int) : Decidable (is_nice_cell A u) :=
  if horigin : u = (0, 0) then by
    unfold is_nice_cell
    apply isFalse
    push_neg; intro _
    contradiction
  else
    if hsat : _can_sat (mean_fun A u) then by
      unfold is_nice_cell
      apply isFalse
      push_neg
      intro _; assumption
    else by
      unfold is_nice_cell
      apply isTrue
      constructor <;> assumption

-- Prove that the function which checks whether a cell is nice is equivalent
-- to the definition (or rather, the negation of the definition of a mean cell).
lemma is_nice_cell_iff {p : Nat} (A : Journey p) (u : Int × Int) :
  is_nice_cell A u ↔ ¬mean_cell A u := by
  unfold is_nice_cell mean_cell
  constructor
  · intro ⟨horigin, hclose⟩
    push_neg
    use horigin
    rw [_can_sat_iff] at hclose
    push_neg at hclose
    assumption
  · intro h
    push_neg at h
    constructor
    · exact h.left
    rw [_can_sat_iff]
    push_neg
    exact h.right

-- In the original paper, the Devil may choose to do "nothing".
-- To keep our formalization simple, we just have the devil pick a
-- provably "nice" cell when it would normally do nothing.
def nothing {p : Nat} (A : Journey p) : Int × Int := ((((steps A + 1) * p + 1) : Nat), 0)

lemma nothing_is_nice {p : Nat} (A : Journey p) : is_nice_cell A (nothing A) := by
  unfold is_nice_cell
  constructor
  · unfold nothing
    have := Int.mul_nonneg (Int.natCast_nonneg (steps A)) (Int.natCast_nonneg p)
    simp; linarith -- This works with the wrong ineqality but fails with the right one ???
  intro h
  rw [_can_sat_iff] at h
  rcases h with ⟨i, iprop⟩
  unfold mean_fun at iprop
  have : dist (0, 0) (nothing A) ≤ dist (0, 0) (cell A i.1 i.2) + p :=
    le_trans (dist_tri _ _ _) (Nat.add_le_add_left (le_of_eq_of_le (dist_comm _ _) iprop.2) _)
  apply not_lt_of_ge this; clear this
  have : dist (0, 0) (nothing A) = (steps A) * p + 1 + p := by
    rw [dist_comm]
    unfold nothing dist
    rw [Int.sub_zero, Int.sub_zero, Int.natAbs_cast, Int.natAbs_zero]
    simp; ring
  rw [this]; clear this
  apply add_lt_add_right
  apply Nat.lt_succ_iff.mpr
  apply le_of_not_gt
  intro h
  have := journey_lb (subjourney A i.1 i.2) (steps A)
  rw [subjourney_last_cell, subjourney_steps, mul_comm] at this
  apply this at h; clear this
  linarith [i.2]

-- Make a "nice" devil by doing "nothing" for all non-nice responses
def make_nice (D : Devil) : Devil :=
  fun Ap ↦ if is_nice_cell Ap.A (response D Ap.A) then (response D Ap.A) else (nothing Ap.A)

-- Prove that a devil created with 'make_nice' is indeed nice.
lemma make_nice_is_nice (D : Devil) (p : Nat) : nice (make_nice D) p := by
  unfold nice make_nice response
  intro A; dsimp
  rw [← is_nice_cell_iff]
  split_ifs with hnc
  · exact hnc
  · exact nothing_is_nice A

-- Any devil that eats the origin at some point of some journey is not nice
lemma not_nice_of_eats_origin (D : Devil) (p : Nat) :
  (∃ (A : Journey p) (i : Fin ((steps A) + 1)), (response D (subjourney A i.1 i.2)) = (0, 0)) → ¬nice D p := by
  rintro ⟨A, i, h⟩
  unfold nice mean_cell; push_neg
  use (subjourney A i.1 i.2)
  left
  assumption
