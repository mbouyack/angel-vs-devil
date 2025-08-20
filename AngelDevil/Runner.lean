import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import AngelDevil.Defs
import AngelDevil.Basic
import AngelDevil.Append
import AngelDevil.Subjourney

set_option linter.style.longLine false

/- This file defines the behavior of the "runner", who attempts to follow the
   y-axis northward and will use a strategy of following the "left wall" any
   time they are blocked by a cell the Devil has eaten.
-/

@[ext] structure RunState where
  x : Int -- Current location, x-coord
  y : Int -- Current location, y-coord
  u : Int -- Direction of travel, x-coord
  v : Int -- Direction of travel, y-coord
  unit : u * u + v * v = 1 -- ⟨u, v⟩ should be a unit vector

-- Convenience macros for repackaging the location and direction
-- parameters as Int × Int
def loc (rs : RunState) : Int × Int := ⟨rs.x, rs.y⟩
def dir (rs : RunState) : Int × Int := ⟨rs.u, rs.v⟩

-- The runner begins at the origin, running northward (up the positive y-axis)
def run_start : RunState where
  x := 0
  y := 0
  u := 0
  v := 1
  unit := by simp

/- Move forward one cell, turn left, and move forward one cell again.
   Note that for the purposes of counting traversed walls, this counts
   as a single step, not two. -/
def turn_left (rs : RunState) : RunState where
  x := rs.x + rs.u - rs.v
  y := rs.y + rs.u + rs.v
  u := -rs.v
  v := rs.u
  unit := by
    rw [Int.neg_mul_neg, Int.add_comm]
    exact rs.unit

-- Move forward one cell
def move_forward (rs : RunState) : RunState where
  x := rs.x + rs.u
  y := rs.y + rs.v
  u := rs.u
  v := rs.v
  unit := rs.unit

-- Without changing cells, turn 90-degrees to the right
def turn_right (rs : RunState) : RunState where
  x := rs.x
  y := rs.y
  u := rs.v
  v := -rs.u
  unit := by
    rw [Int.neg_mul_neg, Int.add_comm]
    exact rs.unit

abbrev blocked (eaten : List (Int × Int)) (x : Int × Int) :=
  x.1 < 0 ∨ x ∈ eaten

/- Determine where the next step of the run would take us.
   That is, try each of the actions listed above (turn left, move forward,
   and turn right) and pick the first which lands on an unblocked cell
-/
def next_step (eaten : List (Int × Int)) (rs : RunState) : RunState :=
  if ¬blocked eaten (loc (turn_left rs)) then turn_left rs else
  if ¬blocked eaten (loc (move_forward rs)) then move_forward rs else
  turn_right rs

/- Attempts to add 'rs' to the current partial sprint.
   If it succeeds, repeat with the cell indicated by 'next_step'.
-/
def sprint_partial (p ns : Nat) (start : Int × Int) (eaten : List (Int × Int)) (rs : RunState) : List RunState :=
  if hterm : 2 * p < ns ∨ ¬close p start (loc rs) then [] else
  rs :: (sprint_partial p (ns + 1) start eaten (next_step eaten rs))
termination_by 2 * p + 1 - ns
decreasing_by
  push_neg at hterm
  rw [add_comm ns, Nat.sub_add_eq, Nat.add_one_sub_one, Nat.sub_add_comm hterm.1]
  exact Nat.lt_add_one_of_le (le_refl _)

-- If the list constructed by 'sprint_partial' is not empty, the first element of the list will be 'rs'
lemma sprint_partial_getElem_zero_of_nonnil (p ns : Nat) (start : Int × Int) (eaten : List (Int × Int)) (rs : RunState) :
  (hnnil : sprint_partial p ns start eaten rs ≠ []) → (sprint_partial p ns start eaten rs)[0]'(List.length_pos_iff.mpr hnnil) = rs := by
  intro hnnil
  -- Use the trick of starting with 'sprint_partial = sprint_partial' followed by 'nth_rw'
  -- to expand only the right-hand side. This allows us to easily do
  -- the necessary rewrites without having to worry about 'getElem_congr_coll'
  have : sprint_partial p ns start eaten rs = _ := rfl
  nth_rw 2 [sprint_partial] at this
  by_cases hterm : ns > 2 * p ∨ ¬close p start (loc rs)
  · -- If we hit the termination case this leads to a contradiction
    rw [dif_pos hterm] at this
    exact False.elim (hnnil this)
  rw [dif_neg hterm] at this
  rw [getElem_congr_coll this, List.getElem_cons_zero]

-- If the list constructed by 'sprint_partial' is not empty, ns < 2 * p + 1
lemma sprint_partial_nslt_of_nonnil (p ns : Nat) (start : Int × Int) (eaten : List (Int × Int)) (rs : RunState) :
  (hnnil : sprint_partial p ns start eaten rs ≠ []) → ns < 2 * p + 1 := by
  intro hnnil
  apply Nat.lt_add_one_of_le
  contrapose! hnnil
  rename' hnnil => ltns
  unfold sprint_partial
  rw [dif_pos (Or.inl ltns)]

-- If the list constructed by 'sprint_partial' is not empty, then the first element is close to 'start'
lemma sprint_partial_close_getElem_zero_of_nonnil (p ns : Nat) (start : Int × Int) (eaten : List (Int × Int)) (rs : RunState) :
  (hnnil : sprint_partial p ns start eaten rs ≠ []) →
  close p start (loc ((sprint_partial p ns start eaten rs)[0]'(List.length_pos_iff.mpr hnnil))) := by
  intro hnnil
  rw [sprint_partial_getElem_zero_of_nonnil]
  · contrapose! hnnil
    rename' hnnil => hnclose
    unfold sprint_partial
    rw [dif_pos (Or.inr hnclose)]
  · assumption

-- If the list constructed by 'sprint_partial' is not empty, rewrite it in 'cons' form.
lemma sprint_partial_cons_of_nonnil (p ns : Nat) (start : Int × Int) (eaten : List (Int × Int)) (rs : RunState) :
  (hnnil : sprint_partial p ns start eaten rs ≠ []) →
  sprint_partial p ns start eaten rs = (rs :: (sprint_partial p (ns + 1) start eaten (next_step eaten rs))) := by
  intro hnnil
  nth_rw 1 [sprint_partial]
  split_ifs with hterm
  · apply hnnil
    unfold sprint_partial
    rw [dif_pos hterm]
  · rfl

lemma sprint_partial_mem_close (p ns : Nat) (start : Int × Int) (eaten : List (Int × Int)) (rs : RunState) :
  ∀ x ∈ sprint_partial p ns start eaten rs, close p start (loc x) := by
  intro x hxmem
  rcases List.getElem_of_mem hxmem with ⟨i, ilt, helem⟩
  by_cases iz : i = 0
  · -- We've already proven that if 'sprint_partial ≠ []', sprint_partial[0] is "close"
    subst iz
    subst helem
    apply sprint_partial_close_getElem_zero_of_nonnil
    exact List.ne_nil_of_mem hxmem
  · rename' iz => inz; push_neg at inz
    -- Otherwise, rewrite the list in 'cons' form and use recursion to close the goal
    rw [getElem_congr_coll (sprint_partial_cons_of_nonnil p ns start eaten rs (List.ne_nil_of_mem hxmem))] at helem
    rw [getElem_congr_idx ((Nat.sub_one_add_one inz).symm), List.getElem_cons_succ] at helem
    exact sprint_partial_mem_close _ _ _ _ _ x (List.mem_of_getElem helem)
termination_by (2 * p + 1 - ns)
decreasing_by
  have hnnil : sprint_partial p ns start eaten rs ≠ [] :=
    List.ne_nil_of_length_pos (lt_of_le_of_lt (Nat.zero_le _) ilt)
  have nsle : ns ≤ 2 * p := by
    apply Nat.le_of_lt_add_one
    apply sprint_partial_nslt_of_nonnil
    exact hnnil
  rw [add_comm ns, Nat.sub_add_eq, Nat.add_one_sub_one, Nat.sub_add_comm nsle]
  exact Nat.lt_add_one_of_le (le_refl _)

-- A sprint is a sequence of steps taken by the runner between moves by the devil.
-- Later we will show that the cells corresponding to the beginning and end of
-- the sprints can be used to construct an angel which escapes the Nice Devil.
def sprint (p : Nat) (rs₀ : RunState) (eaten : List (Int × Int)) : List RunState :=
  sprint_partial p 1 (loc rs₀) eaten rs₀

-- If 'p' is positive, the sprint will not be empty
-- Up to this point we have not needed this assumption, but it appears
-- to be necessary if we wish to match the logic of the original paper.
lemma sprint_nonnil_of_ppos (p : Nat) (rs₀ : RunState) (eaten : List (Int × Int)) :
  0 < p → sprint p rs₀ eaten ≠ [] := by
  intro hpos
  unfold sprint sprint_partial
  split_ifs with hterm
  · contrapose! hterm
    constructor
    · apply Nat.le_of_lt_add_one
      apply Nat.add_one_lt_add_one_iff.mpr
      linarith
    · exact close_self p (loc rs₀)
  exact List.cons_ne_nil _ _

-- Prove that the first and last cells in a sprint are "close"
lemma sprint_close_first_last (p : Nat) (hpos : 0 < p) (rs₀ : RunState) (eaten : List (Int × Int)) :
  close p
  (loc ((sprint p rs₀ eaten).head (sprint_nonnil_of_ppos p rs₀ eaten hpos)))
  (loc ((sprint p rs₀ eaten).getLast (sprint_nonnil_of_ppos p rs₀ eaten hpos))) := by
  have hnnil := sprint_nonnil_of_ppos p rs₀ eaten hpos
  unfold sprint at *
  rw [List.head_eq_getElem_zero hnnil, sprint_partial_getElem_zero_of_nonnil]
  · exact sprint_partial_mem_close p 1 (loc rs₀) eaten _ _ (List.getLast_mem hnnil)
  · assumption

-- TODO: This might be useful more generally
-- Maybe put this in 'Basic'?
/- A journey of zero steps.
   This will be used as the base case for constructing the Runner.
-/
def NoSteps (p : Nat) : Journey p where
  n := 0
  seq := fun _ ↦ (0, 0)
  start := rfl
  plimit := fun i ilt ↦ False.elim (Nat.not_lt_zero i ilt)

lemma nosteps_steps (p : Nat) : steps (NoSteps p) = 0 := rfl
