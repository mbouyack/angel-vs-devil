import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NormNum

-- This file includes definitions and theorems for the unit vectors of integers

/- We make use of unit vectors in the definition of edges (Perimeter.lean),
   in the definition of adjacency (Region.lean), and in the definition of
   RunState (Trace.lean). Prior to the creation of this file there was no
   unified definition, which led to unnecessarily complicated and / or
   redundant proofs. This file is intended to solve that problem.

   Note that 'UVec' was made its own type (rather than just having a
   collection of theorems on Int × Int) so that cardinality results can
   be proven by demonstrating an injective function from UVec. -/

set_option linter.style.longLine false

@[ext] structure UVec where
  x : Int
  y : Int
  unit : x^2 + y^2 = 1

-- Prove that we can determine whether two 'UVec' are equal
instance : DecidableEq UVec := fun a b ↦
  if h : a.x = b.x ∧ a.y = b.y then
    isTrue (UVec.ext_iff.mpr h)
  else
    isFalse (fun h' ↦ h (UVec.ext_iff.mp h'))

-- Define a coercion from UVec to Int × Int
def uvec_coe (u : UVec) : Int × Int := ⟨u.x, u.y⟩

-- Get the negation of a unit vector.
-- Note that the result of this operation is still a 'UVec'
-- which wouldn't be the case if we just used '-'
def uvec_neg (u : UVec) : UVec :=
  UVec.mk (-u.x) (-u.y) (by simp; exact u.unit)

-- It may be useful to automatically convert a 'UVec'
-- to a cartesian product of integers
instance : Coe UVec (Int × Int) := ⟨uvec_coe⟩

lemma uvec_coe_neg (u : UVec) :
  uvec_coe (uvec_neg u) = -(uvec_coe u) := by
  unfold uvec_coe uvec_neg; simp

lemma uvec_coe_eq_coe_iff (u v : UVec) :
  uvec_coe u = uvec_coe v ↔ u = v := ⟨
    fun h ↦ UVec.ext (Prod.ext_iff.mp h).1 (Prod.ext_iff.mp h).2,
    fun h ↦ Prod.ext (UVec.ext_iff.mp h).1 (UVec.ext_iff.mp h).2⟩

-- Upper bound on the x-coordinate of a UVec
lemma uvec_abs_x_le_one (u : UVec) : Int.natAbs u.x ≤ 1 := by
  by_contra! h
  have h₀ : 2 ≤ u.x * u.x := by
    rw [← one_add_one_eq_two, ← pow_two, ← Int.natAbs_pow_two, pow_two]
    apply Int.add_one_le_of_lt
    apply Nat.cast_lt.mpr
    exact Nat.mul_lt_mul'' h h
  have h₁ : 0 ≤ u.y * u.y := by
    rw [← pow_two]
    exact pow_two_nonneg u.y
  have := Int.add_le_add h₀ h₁
  rw [add_zero, ← pow_two, ← pow_two, u.unit] at this
  absurd this
  norm_num

-- Upper bound on the y-coordinate of a UVec
lemma uvec_abs_y_le_one (u : UVec) : Int.natAbs u.y ≤ 1 := by
  -- Use symmetry to prove the result from the x-case
  convert uvec_abs_x_le_one ⟨u.y, u.x, (by rw [add_comm]; exact u.unit)⟩

-- Either the x or y-coordinate of the UVec must be zero
lemma uvec_x_zero_or_y_zero (u : UVec) :
  u.x = 0 ∨ u.y = 0 := by
  rw [← Int.natAbs_eq_zero, ← Int.natAbs_eq_zero]
  by_contra! h
  have hx1 : Int.natAbs u.x = 1 :=
    le_antisymm (uvec_abs_x_le_one u) ((Nat.one_le_of_lt (Nat.pos_of_ne_zero h.1)))
  have hy1 : Int.natAbs u.y = 1 :=
    le_antisymm (uvec_abs_y_le_one u) ((Nat.one_le_of_lt (Nat.pos_of_ne_zero h.2)))
  have hxpow2 : u.x ^ 2 = 1 := by
    rw [← Int.natAbs_pow_two, hx1]; simp
  have hypow2 : u.y ^ 2 = 1 := by
    rw [← Int.natAbs_pow_two, hy1]; simp
  have : u.x ^ 2 + u.y ^ 2 = 2 := by
    rw [hxpow2, hypow2]; simp
  rw [u.unit] at this
  absurd this
  norm_num

-- The sum of the absolute values of the x and y-coordinates must be one
lemma uvec_xabs_add_yabs_eq_one (u : UVec) :
  u.x.natAbs + u.y.natAbs = 1 := by
  have := u.unit
  rcases uvec_x_zero_or_y_zero u with lhs | rhs
  · rw [Int.natAbs_eq_zero.mpr lhs, zero_add]
    by_contra! h
    have yz : u.y = 0 :=
      Int.natAbs_eq_zero.mp (Nat.le_zero.mp (Nat.le_of_lt_add_one (lt_of_le_of_ne (uvec_abs_y_le_one u) h)))
    rw [lhs, yz, pow_two, mul_zero, add_zero] at this
    absurd this
    norm_num
  · rw [Int.natAbs_eq_zero.mpr rhs, add_zero]
    by_contra! h
    have xz : u.x = 0 :=
      Int.natAbs_eq_zero.mp (Nat.le_zero.mp (Nat.le_of_lt_add_one (lt_of_le_of_ne (uvec_abs_x_le_one u) h)))
    rw [rhs, xz, pow_two, mul_zero, add_zero] at this
    absurd this
    norm_num

lemma uvec_xnez_or_ynez (u : UVec) :
  u.x ≠ 0 ∨ u.y ≠ 0 := by
  by_contra! h
  have := u.unit
  rw [h.1, h.2] at this
  simp at this

-- Give names to each of the unit vectors
def uvec_up : UVec := UVec.mk 0 1 (by simp)
def uvec_down : UVec := UVec.mk 0 (-1) (by simp)
def uvec_left : UVec := UVec.mk (-1) 0 (by simp)
def uvec_right : UVec := UVec.mk 1 0 (by simp)

-- Give a name to the Finset of unit vectors
-- We will prove below that this set is complete.
def uvec_finset : Finset UVec :=
  {uvec_up, uvec_down, uvec_left, uvec_right}

-- Prove that 'uvec_finset' has exactly four elements
lemma uvec_finset_card : uvec_finset.card = 4 := by
  unfold uvec_finset uvec_up uvec_down uvec_left uvec_right
  rw [Finset.card_insert_of_notMem]; swap
  · intro h
    repeat rcases Finset.mem_insert.mp h with h | h; absurd (UVec.ext_iff.mp h).2; simp
    absurd (UVec.ext_iff.mp (Finset.mem_singleton.mp h)).2; simp
  rw [Finset.card_insert_of_notMem]; swap
  · intro h
    repeat rcases Finset.mem_insert.mp h with h | h; absurd (UVec.ext_iff.mp h).2; simp
    absurd (UVec.ext_iff.mp (Finset.mem_singleton.mp h)).2; simp
  rw [Finset.card_insert_of_notMem]; swap
  · intro h
    absurd (UVec.ext_iff.mp (Finset.mem_singleton.mp h)).1; simp
  rw [Finset.card_singleton]

lemma uvec_finset_mem : ∀ u, u ∈ uvec_finset := by
  intro u
  have := uvec_xabs_add_yabs_eq_one u
  unfold uvec_finset uvec_up uvec_down uvec_left uvec_right
  rcases uvec_x_zero_or_y_zero u with lhs | rhs
  · rw [lhs, Int.natAbs_zero, zero_add] at this
    rcases Int.natAbs_eq_iff.mp this with lhs' | rhs'
    · rw [Int.natCast_one] at lhs'
      exact Finset.mem_insert.mpr (Or.inl (UVec.ext (by rw [lhs]) (by rw [lhs'])))
    · rw [Int.natCast_one] at rhs'
      apply Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl _)))
      exact UVec.ext (by rw [lhs]) (by rw [rhs'])
  · rw [rhs, Int.natAbs_zero, add_zero] at this
    rcases Int.natAbs_eq_iff.mp this with lhs' | rhs'
    · rw [Int.natCast_one] at lhs'
      apply Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr _)))
      apply Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr _))
      exact UVec.ext (by rw [lhs']) (by rw [rhs])
    · rw [Int.natCast_one] at rhs'
      apply Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr _)))
      apply Finset.mem_insert.mpr (Or.inl (UVec.ext (by rw [rhs']) (by rw [rhs])))

-- If a unit vector is coerced to an Int × Int, there are four possible results
lemma uvec_coe_eq : ∀ u : UVec,
  (u : Int × Int) = (0, 1) ∨ (u : Int × Int) = (0, -1) ∨
  (u : Int × Int) = (-1, 0) ∨ (u : Int × Int) = (1, 0) := by
  intro u
  rcases Finset.mem_insert.mp (uvec_finset_mem u) with lhs₀ | rhs₀
  · left; rw [lhs₀]; rfl
  right
  rcases Finset.mem_insert.mp rhs₀ with lhs₁ | rhs₁
  · left; rw [lhs₁]; rfl
  right
  rcases Finset.mem_insert.mp rhs₁ with lhs₂ | rhs₂
  · left; rw [lhs₂]; rfl
  right
  rw [Finset.mem_singleton.mp rhs₂]; rfl
