import Mathlib.Data.Fin.Basic
import AngelDevil.Defs

set_option linter.style.longLine false
set_option linter.style.multiGoal false

/-
  This file contains basic results for the ojects defined in Defs.lean
-/

-- Arguments to the 'dist' function commute
lemma dist_comm (u v : Int × Int) : dist u v = dist v u := by
  unfold dist
  rw [← Int.neg_sub, ← Int.neg_sub v.2, Int.natAbs_neg, Int.natAbs_neg]

-- The triangle inequality holds for "dist"
lemma dist_tri (u v w : Int × Int) : dist u w ≤ dist u v + dist v w := by
  unfold dist
  rw [add_comm, sub_eq_sub_add_sub u.1 w.1 v.1, sub_eq_sub_add_sub u.2 w.2 v.2]
  apply le_trans (max_le_max (Int.natAbs_add_le (v.1 - w.1) (u.1 - v.1)) (Int.natAbs_add_le (v.2 - w.2) (u.2 - v.2)))
  exact max_add_add_le_max_add_max

lemma dist_self (u : Int × Int) : dist u u = 0 := by simp

-- Every cell is close to itself
lemma close_self (r : Nat) (u : Int × Int) : close r u u := by
  unfold close dist
  rw [sub_self, sub_self, Int.natAbs_zero]
  exact zero_le _

-- "close" is commutative
lemma close_comm (r : Nat) (u v : Int × Int) : close r u v ↔ close r v u := by
  unfold close
  rw [dist_comm]

-- Lower bound on x for cells close to the origin
lemma close_origin_negxle (r : Nat) (u : Int × Int) : close r (0, 0) u → -u.1 ≤ r := by
  unfold close dist; dsimp
  rw [Int.zero_sub, Int.zero_sub]
  intro h
  exact le_trans (Int.le_natAbs) (Int.ofNat_le_ofNat_of_le (le_of_max_le_left h))

-- Upper bound on x for cells close to the origin
lemma close_origin_xle (r : Nat) (u : Int × Int) : close r (0, 0) u → u.1 ≤ r := by
  unfold close dist; dsimp
  rw [Int.zero_sub, Int.zero_sub, Int.natAbs_neg, Int.natAbs_neg]
  intro h
  exact le_trans (Int.le_natAbs) (Int.ofNat_le_ofNat_of_le (le_of_max_le_left h))

-- Lower bound on y for cells close to the origin
lemma close_origin_negyle (r : Nat) (u : Int × Int) : close r (0, 0) u → -u.2 ≤ r := by
  unfold close dist; dsimp
  rw [Int.zero_sub, Int.zero_sub]
  intro h
  exact le_trans (Int.le_natAbs) (Int.ofNat_le_ofNat_of_le (le_of_max_le_right h))

-- Upper bound on y for cells close to the origin
lemma close_origin_yle (r : Nat) (u : Int × Int) : close r (0, 0) u → u.2 ≤ r := by
  unfold close dist; dsimp
  rw [Int.zero_sub, Int.zero_sub, Int.natAbs_neg, Int.natAbs_neg]
  intro h
  exact le_trans (Int.le_natAbs) (Int.ofNat_le_ofNat_of_le (le_of_max_le_right h))

-- If a cell is within certain bounds, it is close to the origin
lemma close_origin_of_bounds (r : Nat) (u : Int × Int) :
  -u.1 ≤ r ∧ u.1 ≤ r ∧ -u.2 ≤ r ∧ u.2 ≤ r → close r (0, 0) u := by
  intro h
  unfold close dist; simp
  constructor
  · apply Int.ofNat_le.mp
    rcases Int.natAbs_eq u.1 with lhs | rhs
    · rw [← lhs]; exact h.2.1
    · rw [← Int.neg_eq_comm.mp rhs.symm]
      exact h.1
  · apply Int.ofNat_le.mp
    rcases Int.natAbs_eq u.2 with lhs | rhs
    · rw [← lhs]; exact h.2.2.2
    · rw [← Int.neg_eq_comm.mp rhs.symm]
      exact h.2.2.1

-- If two cells are within distance r₀ of each-other and r₀ ≤ r₁,
-- then they are also within distance r₁ of each-other
lemma close_of_le_of_close (r₀ r₁ : Nat) (u v : Int × Int) :
  r₀ ≤ r₁ → close r₀ u v → close r₁ u v := fun hle hcr₀ ↦ le_trans hcr₀ hle

-- Two 'cell' invocations are equal if the indices are equal
lemma cell_congr_idx {p : Nat} (A : Journey p) {i j : Nat} (hij : i = j) (ilt : i < steps A + 1) :
  cell A i ilt = cell A j (hij ▸ ilt) := by congr

-- Get the final cell of the journey
def last {p : Nat} (A : Journey p) : Int × Int := cell A (steps A) (Nat.lt_add_one _)

-- Every journey starts at the origin
lemma journey_start {p : Nat} (A : Journey p) : cell A 0 (Nat.add_one_pos _) = (0, 0) := A.start

-- Consecutive cells along the journey are "close"
lemma journey_steps_close {p : Nat} (A : Journey p) :
  ∀ i, (ilt : i < steps A) → close p (cell A i (by linarith)) (cell A (i+1) (by linarith)) := A.plimit

-- Two journeys are equivalent if-and-only-if they are
-- the same length and follow the same cells
-- Note that the theorem is stated in a somewhat awkward way to allow the
-- statement of step equality ("hs") to be used in the statement of cell equality
lemma journey_ext_iff {p : Nat} (A B : Journey p) :
  A = B ↔ ¬ ((hs : steps A = steps B) → ¬(∀ i (ilt : i < steps A + 1), cell A i ilt = cell B i (hs ▸ ilt))) := by
  constructor
  · intro hAB h
    apply h (congrArg (fun X ↦ steps X) hAB)
    intro _ _
    congr
  · intro h
    contrapose! h
    intro hs
    contrapose! h
    ext
    · exact hs
    · unfold cell at h
      apply (Fin.heq_fun_iff (Nat.add_one_inj.mpr hs)).mpr
      intro i
      exact h i.1 i.2
