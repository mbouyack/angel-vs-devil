import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import AngelDevil.Basic
import AngelDevil.Misc
import AngelDevil.Unit
import AngelDevil.Dupes

set_option linter.style.longLine false

/- This file defines the behavior of the "runner", who traces the perimeter of a set of blocked cells.
-/

@[ext] structure RunState where
  x : Int -- Current location, x-coord
  y : Int -- Current location, y-coord
  u : UVec -- Direction of travel, given by a unit vector

-- Prove that we can determine whether two 'RunState' are equal
instance : DecidableEq RunState := fun a b ↦
  if h : a.x = b.x ∧ a.y = b.y ∧ a.u = b.u then
    isTrue (RunState.ext_iff.mpr h)
  else
    isFalse (fun h' ↦ h (RunState.ext_iff.mp h'))

-- Convenience macros for repackaging the location and direction
-- parameters as Int × Int
def loc (rs : RunState) : Int × Int := ⟨rs.x, rs.y⟩
def dir (rs : RunState) : Int × Int := rs.u

-- Get the wall adjacent to a given run state
def left_of_runner (rs : RunState) : (Int × Int) := ⟨rs.x - rs.u.y, rs.y + rs.u.x⟩

/- Move forward one cell, turn left, and move forward one cell again.
   Note that for the purposes of counting traversed walls, this counts
   as a single step, not two. -/
def turn_left (rs : RunState) : RunState where
  x := rs.x + rs.u.x - rs.u.y
  y := rs.y + rs.u.x + rs.u.y
  u := UVec.mk (-rs.u.y) (rs.u.x) (by
    simp; rw [add_comm]; exact rs.u.unit
  )

-- Move forward one cell
def move_forward (rs : RunState) : RunState where
  x := rs.x + rs.u.x
  y := rs.y + rs.u.y
  u := rs.u

-- Without changing cells, turn 90-degrees to the right
def turn_right (rs : RunState) : RunState where
  x := rs.x
  y := rs.y
  u := UVec.mk rs.u.y (-rs.u.x) (by
    simp; rw [add_comm]; exact rs.u.unit
  )

-- Turning right doesn't change the location, only the direction
lemma turn_right_loc (rs : RunState) : loc (turn_right rs) = loc rs := rfl

/- Determine where the next step of the run would take us.
   That is, try each of the actions listed above (turn left, move forward,
   and turn right) and pick the first which lands on an unblocked cell
-/
def next_step (blocked : List (Int × Int)) (rs : RunState) : RunState :=
  if loc (turn_left rs) ∉ blocked then turn_left rs else
  if loc (move_forward rs) ∉ blocked then move_forward rs else
  turn_right rs

-- The inverse of 'turn_left'
def undo_turn_left (rs : RunState) : RunState where
  x := rs.x - rs.u.x - rs.u.y
  y := rs.y + rs.u.x - rs.u.y
  u := UVec.mk (rs.u.y) (-rs.u.x) (by
    simp; rw [add_comm]; exact rs.u.unit
  )

-- The inverse of 'move_forward'
def undo_move_forward (rs : RunState) : RunState where
  x := rs.x - rs.u.x
  y := rs.y - rs.u.y
  u := rs.u

-- The inverse of 'turn_right'
def undo_turn_right (rs : RunState) : RunState where
  x := rs.x
  y := rs.y
  u := UVec.mk (-rs.u.y) rs.u.x (by
    simp; rw [add_comm]; exact rs.u.unit
  )

def undo_next_step (blocked : List (Int × Int)) (rs : RunState) : RunState :=
  if loc (undo_turn_left rs) ∉ blocked then undo_turn_left rs else
  if loc (undo_move_forward rs) ∉ blocked then undo_move_forward rs else
  undo_turn_right rs

-- 'turn_left' and 'undo_turn_left' are in-fact inverses
lemma turn_left_undo_cancel (rs : RunState) :
  undo_turn_left (turn_left rs) = rs := by
  unfold undo_turn_left turn_left; simp

-- 'move_forward' and 'undo_move_forward' are in-fact inverses
lemma move_forward_undo_cancel (rs : RunState) :
  undo_move_forward (move_forward rs) = rs := by
  unfold undo_move_forward move_forward; simp

-- 'turn_right' and 'undo_turn_right' are in-fact inverses
lemma turn_right_undo_cancel (rs : RunState) :
  undo_turn_right (turn_right rs) = rs := by
  unfold undo_turn_right turn_right; simp

-- 'next_step' and 'undo_next_step' are inverses, conditional on
-- the cell to the runner's left being blocked and the initial
-- cell *not* being blocked.
lemma next_step_undo_cancel
  (blocked : List (Int × Int)) (rs : RunState)
  (hsafe : (loc rs) ∉ blocked) (hblocked : left_of_runner rs ∈ blocked) :
  undo_next_step blocked (next_step blocked rs) = rs := by
  unfold next_step
  split_ifs with _ _
  · unfold undo_next_step
    have h₂ : ¬loc (undo_turn_left (turn_right rs)) ∉ blocked := by
      unfold turn_right undo_turn_left; push_neg; simp
      rwa [← add_sub_right_comm, add_right_comm _ rs.u.y]
    have h₃ : ¬loc (undo_move_forward (turn_right rs)) ∉ blocked := by
      unfold turn_right undo_move_forward; push_neg; simp
      exact hblocked
    rw [if_neg h₂, if_neg h₃, turn_right_undo_cancel]
  · unfold undo_next_step
    have h₂ : ¬loc (undo_turn_left (move_forward rs)) ∉ blocked := by
      unfold undo_turn_left move_forward; push_neg; simp
      rw [add_sub_right_comm, add_sub_cancel_right]
      exact hblocked
    have h₃ : loc (undo_move_forward (move_forward rs)) ∉ blocked := by
      rwa [move_forward_undo_cancel]
    rw [if_neg h₂, if_pos h₃, move_forward_undo_cancel]
  · unfold undo_next_step
    have h₂ : loc (undo_turn_left (turn_left rs)) ∉ blocked := by
      rwa [turn_left_undo_cancel]
    rw [if_pos h₂, turn_left_undo_cancel]

-- A right turn moves the runner a distance
-- no more than '1' from the previous cell
lemma turn_right_dist_le_one (rs : RunState) :
  dist (loc rs) (loc (turn_right rs)) ≤ 1 := by
  unfold turn_right dist loc; simp

-- A forward step moves the runner a distance
-- no more than '1' from the previous cell
lemma move_forward_dist_le_one (rs : RunState) :
  dist (loc rs) (loc (move_forward rs)) ≤ 1 := by
  unfold move_forward dist loc; simp
  exact ⟨uvec_abs_x_le_one rs.u, uvec_abs_y_le_one rs.u⟩

-- A left turn moves the runner a distance
-- no more than '1' from the previous cell
lemma turn_left_dist_le_one (rs : RunState) :
  dist (loc rs) (loc (turn_left rs)) ≤ 1 := by
  unfold turn_left dist loc; simp
  have (a b c : Int) (h : b.natAbs + c.natAbs = 1) : (a - (a + b + c)).natAbs ≤ 1 := by
    rw [Int.sub_eq_add_neg, Int.neg_add, Int.neg_add]
    rw [← Int.add_assoc, Int.add_neg_cancel_left]
    rw [← Int.neg_add, Int.natAbs_neg, ← h]
    exact Int.natAbs_add_le b c
  constructor
  · apply this
    rw [Int.natAbs_neg]
    exact uvec_xabs_add_yabs_eq_one rs.u
  · apply this
    exact uvec_xabs_add_yabs_eq_one rs.u

-- The "distance" between consecutive states in a trace is no greater than 1
lemma next_step_dist_le_one (blocked : List (Int × Int)) (rs : RunState) :
  dist (loc rs) (loc (next_step blocked rs)) ≤ 1 := by
  unfold next_step
  split_ifs with h₀ h₁
  · exact turn_right_dist_le_one rs
  · exact move_forward_dist_le_one rs
  · exact turn_left_dist_le_one rs

-- Adding more cells to the block list won't change the
-- next step if that cell is not in the updated block list
lemma next_step_unchanged_of_block_unvisited_cells
  (blocked blocked' : List (Int × Int)) (rs : RunState) :
  loc (next_step blocked rs) ∉ blocked' ∧ blocked ⊆ blocked' →
  next_step blocked rs = next_step blocked' rs := by
  intro ⟨hnmem, hss⟩
  unfold next_step at *
  by_cases h₀ : loc (turn_left rs) ∉ blocked
  · rw [if_pos h₀] at *
    rw [if_pos hnmem]
  rw [if_neg h₀] at *
  have h₀' : ¬loc (turn_left rs) ∉ blocked' := by
    push_neg at *
    exact hss h₀
  rw [if_neg h₀']
  by_cases h₁ : loc (move_forward rs) ∉ blocked
  · rw [if_pos h₁] at *
    rw [if_pos hnmem]
  rw [if_neg h₁]
  have h₁' : ¬loc (move_forward rs) ∉ blocked' := by
    push_neg at *
    exact hss h₁
  rw [if_neg h₁']

-- A value bounded by the x-coordinates of consecutive steps must equal one of those x-coordinates
-- TODO: We didn't use this in the proof of trace_intermediate_value_x. Can we delete it?
lemma next_step_intermediate_value_x (blocked : List (Int × Int)) (rs : RunState) :
  ∀ x (_ : x ≤ max rs.x (next_step blocked rs).x) (_ : min rs.x (next_step blocked rs).x ≤ x),
  x = rs.x ∨ x = (next_step blocked rs).x := by
  intro x xle lex
  -- Helper theorem to handle the symmetry
  have hhelper {a b c : Int} (hle : a ≤ b) (hdiff : b - a ≤ 1) (lec : a ≤ c) (cle : c ≤ b) :
    c = a ∨ c = b := by
    by_cases h : c = a
    · left; assumption
    push_neg at h; right
    have ltc : a < c := lt_of_le_of_ne lec h.symm
    have dnn : 0 ≤ b - a := Int.sub_nonneg.mpr hle
    by_cases hbna : b = a
    · rw [hbna] at cle
      exact False.elim (Int.not_le.mpr ltc cle)
    push_neg at hbna
    have hsle : a + 1 ≤ b := Int.add_one_le_of_lt (lt_of_le_of_ne hle hbna.symm)
    have heq : a + 1 = b :=
      le_antisymm hsle ((add_comm 1 a) ▸ (Int.le_add_of_sub_right_le hdiff))
    exact le_antisymm cle (heq ▸ (Int.add_one_le_of_lt ltc))
  -- Use 'next_step_dist_le_one' to bound the difference between the x-coordinates
  have ub : (rs.x - (next_step blocked rs).x).natAbs ≤ 1 := by
    apply le_trans (le_max_left _ (rs.y - (next_step blocked rs).y).natAbs)
    exact next_step_dist_le_one blocked rs
  -- Now handle the two cases (depending on which x-coord is greater)
  by_cases hle : rs.x ≤ (next_step blocked rs).x
  · rw [min_eq_left hle] at lex
    rw [max_eq_right hle] at xle
    rw [← Int.neg_sub, Int.natAbs_neg] at ub
    have hleone : (next_step blocked rs).x - rs.x ≤ 1 :=
      (Int.natAbs_of_nonneg (Int.sub_nonneg.mpr hle)) ▸ (Nat.cast_le.mpr ub)
    exact hhelper hle hleone lex xle
  push_neg at hle
  apply le_of_lt at hle
  rw [min_eq_right hle] at lex
  rw [max_eq_left hle] at xle
  have hleone : rs.x - (next_step blocked rs).x ≤ 1 :=
    (Int.natAbs_of_nonneg (Int.sub_nonneg.mpr hle)) ▸ (Nat.cast_le.mpr ub)
  exact (hhelper hle hleone lex xle).symm

-- In order to produce a valid trace, the runner must begin on a
-- cell that isn't blocked, with a blocked cell to its left.
def run_start_valid (blocked : List (Int × Int)) : RunState → Prop :=
  fun run_start ↦ (loc run_start ∉ blocked) ∧ left_of_runner run_start ∈ blocked

-- Build a trace of length 'n' around the cells in 'blocked' starting at 'rs'
def trace (n : Nat) (rs : RunState) (blocked : List (Int × Int)) : List RunState :=
  if n = 0 then [] else
  rs :: (trace (n - 1) (next_step blocked rs) blocked)

lemma trace_nil (rs : RunState) (blocked : List (Int × Int)) :
  trace 0 rs blocked = [] := by
  unfold trace
  rfl

-- If the list constructed by 'trace_partial' is not empty, the first element of the list will be 'rs'
lemma trace_getElem_zero_of_nonnil (n : Nat) (rs : RunState) (blocked : List (Int × Int)) :
  (hnnil : trace n rs blocked ≠ []) →
  (trace n rs blocked)[0]'(List.length_pos_iff.mpr hnnil) = rs := by
  intro hnnil
  -- Use the trick of starting with 'trace = trace' followed by 'nth_rw'
  -- to expand only the right-hand side. This allows us to easily do
  -- the necessary rewrites without having to worry about 'getElem_congr_coll'
  have : trace n rs blocked = _ := rfl
  nth_rw 2 [trace] at this
  split_ifs at this
  · exact False.elim (hnnil this)
  rw [getElem_congr_coll this, List.getElem_cons_zero]

-- Identity for the trace of length '1'
lemma trace_singleton (rs : RunState) (blocked : List (Int × Int)) :
  trace 1 rs blocked = [rs] := by
  unfold trace; simp
  exact trace_nil _ _

-- If the list constructed by trace is not empty, rewrite it in 'cons' form.
lemma trace_cons_of_nonnil (n : Nat) (rs : RunState) (blocked : List (Int × Int)) :
  (hnnil : trace n rs blocked ≠ []) →
  trace n rs blocked = (rs :: (trace (n - 1) (next_step blocked rs) blocked)) := by
  intro hnnil
  nth_rw 1 [trace]
  split_ifs with hterm
  · apply hnnil
    unfold trace
    rw [if_pos hterm]
  · rfl

-- The length of a trace is given by 'n'
lemma trace_length (n : Nat) (rs : RunState) (blocked : List (Int × Int)) :
  (trace n rs blocked).length = n := by
  unfold trace
  split_ifs with h
  · rw [List.length_nil]
    exact h.symm
  push_neg at h
  rw [List.length_cons, trace_length, Nat.sub_one_add_one h]

-- The distance to the end of the trace is less than or equal to 'n - 1'
-- Note that there is an off-by-one issue at play here:
-- E.g., a trace of length '1' will have an end at distance '0'
lemma trace_getLast_close (n : Nat) (npos : 0 < n) (rs : RunState) (blocked : List (Int × Int)) :
  close (n - 1) (loc rs) (loc ((trace n rs blocked).getLast (by
    apply List.ne_nil_of_length_pos
    rwa [trace_length]
  ))) := by
  have hnnil : trace n rs blocked ≠ [] := by
    apply List.ne_nil_of_length_pos
    rwa [trace_length]
  rw [List.getLast_congr _ _ (trace_cons_of_nonnil _ _ _ hnnil)]; swap
  · exact List.cons_ne_nil _ _
  -- Handle the case where n = 1 first
  by_cases nle : n ≤ 1
  · have n1 : n = 1 := le_antisymm nle (Nat.add_one_le_of_lt npos)
    subst n1
    -- The tail of the cons is nil, but proving it directly is obnoxious
    -- Instead, prove the remainder of the goal and use convert
    have : close (1 - 1) (loc rs) (loc ((rs :: []).getLast (by
      apply List.ne_nil_of_length_pos
      rw [List.length_singleton]
      norm_num
    ))) := by
      rw [List.getLast_singleton]
      exact close_self _ _
    convert this
    rw [Nat.sub_self 1, trace_nil]
  rename' nle => ltn; push_neg at ltn
  -- Apply the triangle inequality
  let rs' := next_step blocked rs
  apply le_trans (dist_tri (loc rs) (loc rs') _)
  apply le_trans (Nat.add_le_add_right (next_step_dist_le_one blocked rs) _)
  apply Nat.add_le_of_le_sub' (Nat.le_sub_one_of_lt ltn)
  -- And finally recurse
  convert trace_getLast_close (n - 1) (Nat.lt_sub_of_add_lt ltn) rs' blocked using 3
  apply List.getLast_cons

-- Recurrence for getting a particular element of a trace
lemma trace_getElem_recurrence (n : Nat) (rs : RunState) (blocked : List (Int × Int)) :
  ∀ i (islt : i + 1 < n),
  (trace n rs blocked)[i + 1]'(by rwa [trace_length]) =
  next_step blocked ((trace n rs blocked)[i]'(by
    rw [trace_length]
    exact lt_trans (Nat.lt_add_one _) islt
  )) := by
  intro i islt
  have hnnil : trace n rs blocked ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [trace_length]
    exact Nat.zero_lt_of_lt islt
  rw [getElem_congr_coll (trace_cons_of_nonnil n rs blocked hnnil)]
  rw [getElem_congr_coll (trace_cons_of_nonnil n rs blocked hnnil)]
  -- Now handle the case where i = 0
  by_cases iz : i = 0
  · subst iz
    rw [List.getElem_cons_zero, List.getElem_cons_succ]
    rw [trace_getElem_zero_of_nonnil]
    apply List.ne_nil_of_length_pos
    rw [trace_length]
    exact Nat.lt_sub_of_add_lt islt
  rename' iz => inz; push_neg at inz
  rw [getElem_congr_idx (Nat.add_one_inj.mpr (Nat.sub_one_add_one inz).symm)]
  rw [getElem_congr_idx ((Nat.sub_one_add_one inz).symm)]
  rw [List.getElem_cons_succ, List.getElem_cons_succ]
  -- Prove the upper bound on i - 1
  have ipslt : i - 1 + 1 < n - 1 := by
    apply Nat.add_one_lt_add_one_iff.mp
    rwa [Nat.sub_one_add_one, Nat.sub_one_add_one]
    · apply Nat.ne_zero_of_lt islt
    · exact inz
  -- Now we can recurse!
  exact trace_getElem_recurrence (n - 1) (next_step blocked rs) blocked (i - 1) ipslt

-- Another recurrence for getting a particular element of a trace
lemma trace_getElem_recurrence' (n : Nat) (rs : RunState) (blocked : List (Int × Int)) :
  ∀ i (_ : 0 < i) (islt : i < n),
  (trace n rs blocked)[i]'(by rwa [trace_length]) =
  next_step blocked ((trace n rs blocked)[i-1]'(by
    rw [trace_length]
    exact lt_of_le_of_lt (Nat.sub_le _ _) islt
  )) := by
  intro i ipos ilt
  have inz : i ≠ 0 := Nat.ne_zero_of_lt ipos
  rw [← getElem_congr_idx (Nat.sub_one_add_one inz), trace_getElem_recurrence]
  exact lt_of_eq_of_lt (Nat.sub_one_add_one inz) ilt

-- Taking the first 'm' states from a trace of length 'n' results in
-- the same list as the trace of length 'm'
lemma trace_take (n : Nat) (rs : RunState) (blocked : List (Int × Int)) :
  ∀ m, m <= n → trace m rs blocked = (trace n rs blocked).take m := by
  intro m mle
  by_cases mz : m = 0
  · subst mz
    have hnil : trace 0 rs blocked = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [trace_length]
    rw [hnil]; symm
    apply List.eq_nil_of_length_eq_zero
    apply List.length_take_of_le
    exact Nat.zero_le _
  rename' mz => mnz; push_neg at mnz
  rw [trace_cons_of_nonnil]; swap
  · apply List.ne_nil_of_length_pos
    rw [trace_length]
    exact Nat.pos_of_ne_zero mnz
  rw [trace_cons_of_nonnil n]; swap
  · apply List.ne_nil_of_length_pos
    rw [trace_length]
    exact lt_of_lt_of_le (Nat.pos_of_ne_zero mnz) mle
  rw [List.take_cons]; swap
  · exact Nat.pos_of_ne_zero mnz
  congr
  apply trace_take (n - 1) (next_step blocked rs) blocked (m - 1)
  apply (Nat.sub_le_sub_iff_right _).mpr mle
  apply le_trans _ mle
  exact Nat.one_le_iff_ne_zero.mpr mnz

-- Relates an element in one trace to the last element of another
lemma trace_getElem_getLast (n : Nat) (rs : RunState) (blocked : List (Int × Int)) :
  ∀ i (ilt : i < (trace n rs blocked).length),
  (trace n rs blocked)[i] = (trace (i + 1) rs blocked).getLast (by
    apply List.ne_nil_of_length_pos
    rw [trace_length]
    exact Nat.add_one_pos _
  ) := by
  intro i ilt
  have isle : i + 1 ≤ n := by
    rw [trace_length] at ilt
    exact Nat.add_one_le_of_lt ilt
  have htakelen := List.length_take_of_le (Nat.add_one_le_of_lt ilt)
  rw [List.getLast_congr _ _ (trace_take n rs blocked (i + 1) isle)]; swap
  · apply List.ne_nil_of_length_pos
    rw [htakelen]
    exact Nat.add_one_pos _
  rw [List.getLast_eq_getElem, List.getElem_take]
  congr
  rw [htakelen, Nat.add_one_sub_one]

-- A trace can be split into two appended traces
lemma trace_split (m n : Nat) (mlt : m < n) (rs : RunState) (blocked : List (Int × Int)) :
  trace n rs blocked = (trace m rs blocked) ++
  (trace (n - m) ((trace n rs blocked)[m]'(by rwa [trace_length])) blocked) := by
  have hnnil : trace n rs blocked ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [trace_length]
    exact Nat.zero_lt_of_lt mlt
  by_cases mz : m = 0
  · subst mz
    rwa [trace_nil, List.nil_append, Nat.sub_zero, trace_getElem_zero_of_nonnil]
  rename' mz => mnz; push_neg at mnz
  have mpos : 0 < m := Nat.pos_of_ne_zero mnz
  have hnnil' : trace m rs blocked ≠ [] := by
    apply List.ne_nil_of_length_pos
    rwa [trace_length]
  nth_rw 1 [trace_cons_of_nonnil n rs blocked hnnil]
  rw [trace_cons_of_nonnil m rs blocked hnnil']
  rw [List.cons_append]
  congr
  have mplt := Nat.sub_lt_sub_right (Nat.one_le_of_lt mpos) mlt
  convert trace_split (m - 1) (n - 1) mplt (next_step blocked rs) blocked using 3
  · exact (Nat.sub_sub_sub_cancel_right (Nat.one_le_of_lt mpos)).symm
  rw [getElem_congr_coll (trace_cons_of_nonnil n rs blocked hnnil)]
  rw [getElem_congr_idx (Nat.sub_one_add_one mnz).symm]
  rw [List.getElem_cons_succ]

-- Theorem relating a sub-list of a trace to a trace that
-- begins with the first element of that sub-list
-- TODO: Simplify this proof
-- TODO: We didn't actually use this in proving the intermediate value theorems.
-- Consider deleting it.
lemma trace_trim (n : Nat) (rs : RunState) (blocked : List (Int × Int)) :
  ∀ i j k (ilt : i ≤ j) (jlt : j < (trace n rs blocked).length) (klt : k < j + 1 - i),
  (trace (j + 1 - i) ((trace n rs blocked)[i]'(lt_of_le_of_lt ilt jlt)) blocked)[k]'(by rwa [trace_length]) =
  (trace n rs blocked)[k + i]'(by
    rw [trace_length]
    apply lt_of_le_of_lt (Nat.le_of_lt_add_one (Nat.add_lt_of_lt_sub klt))
    rwa [trace_length] at jlt
  ) := by
intro i j k ile jlt klt
have jlt' : j < n := by rwa [trace_length] at jlt
have jssilt : j + 1 - i ≤ n := by
  exact le_trans (Nat.sub_le (j + 1) i) (Nat.add_one_le_of_lt jlt')
-- Handle the case where i = 0
by_cases iz : i = 0
· subst iz
  rw [getElem_congr_coll (trace_take n _ blocked (j + 1 - 0) jssilt), List.getElem_take]
  congr
  apply trace_getElem_zero_of_nonnil n rs blocked (List.ne_nil_of_length_pos _)
  exact lt_of_le_of_lt ile jlt
rename' iz => inz; push_neg at inz
have jnz : j ≠ 0 := Nat.ne_zero_of_lt (lt_of_lt_of_le (Nat.pos_of_ne_zero inz) ile)
let rsi := (trace n rs blocked)[i]'(lt_of_le_of_lt ile jlt)
-- Prepare two results for re-writing the left and
-- right-hand sides of the goal in 'cons' form
have lhs_rw := trace_cons_of_nonnil (j + 1 - i) rsi blocked (by
  apply List.ne_nil_of_length_pos
  rw [trace_length]
  exact Nat.pos_of_ne_zero (Nat.ne_zero_of_lt klt)
)
have rhs_rw := trace_cons_of_nonnil n rs blocked (by
  apply List.ne_nil_of_length_pos
  exact lt_of_le_of_lt (Nat.zero_le _) jlt
)
-- Handle the case where k = 0
by_cases kz : k = 0
· subst kz
  rw [getElem_congr_coll lhs_rw]
  rw [List.getElem_cons_zero]
  rw [getElem_congr_idx (zero_add i)]
-- Now rearrange the goal so we can recurse
rename' kz => knz; push_neg at knz
nth_rw 6 [getElem_congr_coll rhs_rw]
have hkinz := lt_of_lt_of_le (Nat.pos_of_ne_zero knz) (Nat.le_add_right k i)
rw [getElem_congr_idx (Nat.sub_one_add_one (Nat.ne_zero_of_lt hkinz)).symm]
rw [List.getElem_cons_succ]
have onelei : 1 ≤ i := by
  rw [← zero_add 1]
  exact Nat.add_one_le_of_lt (Nat.pos_of_ne_zero inz)
have onelej : 1 ≤ j := le_trans onelei ile
rw [getElem_congr_idx (Nat.add_sub_assoc onelei k)]
rw [← trace_trim (n - 1) _ blocked (i - 1) (j - 1)]; swap
· exact (Nat.sub_le_sub_iff_right onelej).mpr ile
swap
· rw [trace_length]
  exact (Nat.sub_lt_sub_iff_right onelej).mpr jlt'
swap
· rw [Nat.sub_one_add_one jnz]
  apply lt_of_lt_of_eq klt
  exact Nat.Simproc.add_sub_le j onelei
-- Now 'congr' and resolve all the resulting goals
congr 2
· rw [Nat.sub_one_add_one jnz]
  exact Nat.Simproc.add_sub_le j onelei
· rw [getElem_congr_coll rhs_rw]
  rw [getElem_congr_idx (Nat.sub_one_add_one inz).symm, List.getElem_cons_succ]

-- Prove that a trace never steps on blocked cell
-- (but it may *remain* on a blocked cell)
lemma trace_avoids_blocked' (n : Nat) (rs : RunState) (blocked : List (Int × Int)) :
  ∀ x ∈ trace n rs blocked, loc x ≠ loc rs → loc x ∉ blocked := by
  intro x hmem₀ nelrs hmem₁
  have nnz : n ≠ 0 := by
    intro nz
    subst nz
    absurd List.length_pos_of_mem hmem₀
    push_neg
    rw [trace_length]
  have nonnil : trace n rs blocked ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [trace_length]
    exact Nat.pos_of_ne_zero nnz
  rw [trace_cons_of_nonnil n rs blocked nonnil] at hmem₀
  have hmem₂ : x ∈ trace (n - 1) (next_step blocked rs) blocked :=
    Or.elim (List.mem_cons.mp hmem₀) (fun h ↦ False.elim ((h ▸ nelrs) rfl)) id
  -- Use recursion to show that x = next_step
  by_cases h : loc x ≠ loc (next_step blocked rs)
  · exact False.elim ((trace_avoids_blocked' (n - 1) (next_step blocked rs) blocked x hmem₂ h) hmem₁)
  push_neg at h
  -- Now show that 'next_step' either moves onto
  -- an unblocked cell or remains on a blocked cell
  unfold next_step at h
  split_ifs at h with h₀ h₁
  · exact (h ▸ nelrs) rfl
  · exact (h ▸ h₁) hmem₁
  · exact (h ▸ h₀) hmem₁

-- Prove that a trace never steps on blocked cell
-- given that the starting cell isn't blocked
lemma trace_avoids_blocked (n : Nat) (rs : RunState) (blocked : List (Int × Int)) (hsafe : loc rs ∉ blocked) :
  ∀ x ∈ trace n rs blocked, loc x ∉ blocked := by
  intro x hmem₀ hmem₁
  have h : loc x ≠ loc rs := by
    contrapose! hsafe
    rwa [← hsafe]
  exact trace_avoids_blocked' n rs blocked x hmem₀ h hmem₁

-- Intermediate value theorem for x-coordinates in a trace
-- This relies on a more general verion of the threorem proven in Misc.lean
lemma trace_intermediate_value_x (n : Nat) (rs : RunState) (blocked : List (Int × Int)) :
  ∀ rs₀ rs₁ (_ : rs₀ ∈ trace n rs blocked) (_ : rs₁ ∈ trace n rs blocked),
  ∀ x (_ : rs₀.x ≤ x) (_ : x ≤ rs₁.x),
  ∃ rs₂ ∈ trace n rs blocked, rs₂.x = x := by
  intro rs₀ rs₁ h₀ h₁ x lex xle
  rcases List.getElem_of_mem h₀ with ⟨i₀, i₀lt, hgE₀⟩
  rcases List.getElem_of_mem h₁ with ⟨i₁, i₁lt, hgE₁⟩
  let ileft := min i₀ i₁
  let iright := max i₀ i₁
  let n' := iright - ileft
  have irlt : iright < n := by
    unfold iright
    by_cases hle : i₀ ≤ i₁
    · rw [max_eq_right hle]
      rwa [trace_length] at i₁lt
    · push_neg at hle
      rw [max_eq_left (le_of_lt hle)]
      rwa [trace_length] at i₀lt
  -- Prove a bound we'll need in order to define 'f' (below)
  have idxlt (i : Fin (n' + 1)) : i.val + ileft < n := by
    apply lt_of_le_of_lt (Nat.le_of_lt_add_one _) irlt
    apply (Nat.sub_lt_sub_iff_right (Nat.le_add_left ileft i.val)).mp
    rw [Nat.add_sub_cancel, Nat.sub_add_comm]
    · exact i.2
    · exact min_le_max
  -- Define a function from Fin to the x-coordinates in the segment
  -- of the trace between i₀ and i₁ (inclusive)
  -- Proving that the 'getElem' is valid requires a bit of work.
  let f : Fin (n' + 1) → Int := fun i ↦ ((trace n rs blocked)[i.val + ileft]'(by
    rw [trace_length]; exact idxlt i)).x
  -- Prove the "adjacency" requirement for f
  have hadj : ∀ (i : Fin n'), (f i.succ - f i.castSucc).natAbs ≤ 1 := by
    intro i
    unfold f; dsimp
    rw [getElem_congr_idx (add_right_comm i.val 1 ileft)]
    rw [trace_getElem_recurrence]; swap
    · rw [add_right_comm]
      exact idxlt i.succ
    rw [← Int.neg_sub, Int.natAbs_neg]
    apply le_trans (le_max_left _ _)
    -- We have previously proven that the distance to 'next_step'
    -- will never be greater than one. Use that result to close the goal.
    exact next_step_dist_le_one blocked ((trace n rs blocked)[i.val + ileft]'(by
      rw [trace_length]
      exact idxlt i.castSucc
    ))
  -- Prove some identities on f 0 and f (Fin.last n')
  have fz_of_i₀lei₁ (i₀lei₁ : i₀ ≤ i₁) : f 0 = rs₀.x := by
    unfold f; congr
    convert hgE₀
    rw [Fin.val_zero, zero_add]
    exact min_eq_left i₀lei₁
  have fz_of_i₁lei₀ (i₁lei₀ : i₁ ≤ i₀) : f 0 = rs₁.x := by
    unfold f; congr
    convert hgE₁
    rw [Fin.val_zero, zero_add]
    exact min_eq_right i₁lei₀
  have fl_of_i₀lei₁ (i₀lei₁ : i₀ ≤ i₁) : f (Fin.last n') = rs₁.x := by
    unfold f; congr
    convert hgE₁; dsimp
    unfold n'
    rw [Nat.sub_add_cancel min_le_max]
    exact max_eq_right i₀lei₁
  have fl_of_i₁lei₀ (i₁lei₀ : i₁ ≤ i₀) : f (Fin.last n') = rs₀.x := by
    unfold f; congr
    convert hgE₀; dsimp
    unfold n'
    rw [Nat.sub_add_cancel min_le_max]
    exact max_eq_left i₁lei₀
  have lex' : min (f 0) (f (Fin.last n')) ≤ x := by
    by_cases hi₀i₁ : i₀ ≤ i₁
    · rw [fz_of_i₀lei₁ hi₀i₁, fl_of_i₀lei₁ hi₀i₁]
      exact min_le_of_left_le lex
    · push_neg at hi₀i₁
      apply le_of_lt at hi₀i₁
      rw [fz_of_i₁lei₀ hi₀i₁, fl_of_i₁lei₀ hi₀i₁]
      exact min_le_of_right_le lex
  have xle' : x ≤ max (f 0) (f (Fin.last n')) := by
    by_cases hi₀i₁ : i₀ ≤ i₁
    · rw [fz_of_i₀lei₁ hi₀i₁, fl_of_i₀lei₁ hi₀i₁]
      exact le_max_of_le_right xle
    · push_neg at hi₀i₁
      apply le_of_lt at hi₀i₁
      rw [fz_of_i₁lei₀ hi₀i₁, fl_of_i₁lei₀ hi₀i₁]
      exact le_max_of_le_left xle
  -- Use the intermediate value theorem proven in Misc.lean to get 'j'
  rcases fin_intermediate_value_of_consec_adj f hadj x lex' xle' with ⟨j, hj⟩
  unfold f at hj
  use ((trace n rs blocked)[j.val + ileft]'(by
    rw [trace_length]
    exact idxlt j
  ))
  apply And.intro _ hj
  apply List.getElem_mem

-- Intermediate value theorem for y-coordinates in a trace
-- This relies on a more general verion of the threorem proven in Misc.lean
-- Ideally we would prove this from the '_x' variant using symmetry, but that
-- actually require a longer proof than just copy/paste/modifying the exising
-- proof.
lemma trace_intermediate_value_y (n : Nat) (rs : RunState) (blocked : List (Int × Int)) :
  ∀ rs₀ rs₁ (_ : rs₀ ∈ trace n rs blocked) (_ : rs₁ ∈ trace n rs blocked),
  ∀ y (_ : rs₀.y ≤ y) (_ : y ≤ rs₁.y),
  ∃ rs₂ ∈ trace n rs blocked, rs₂.y = y := by
  intro rs₀ rs₁ h₀ h₁ y ley yle
  rcases List.getElem_of_mem h₀ with ⟨i₀, i₀lt, hgE₀⟩
  rcases List.getElem_of_mem h₁ with ⟨i₁, i₁lt, hgE₁⟩
  let ileft := min i₀ i₁
  let iright := max i₀ i₁
  let n' := iright - ileft
  have irlt : iright < n := by
    unfold iright
    by_cases hle : i₀ ≤ i₁
    · rw [max_eq_right hle]
      rwa [trace_length] at i₁lt
    · push_neg at hle
      rw [max_eq_left (le_of_lt hle)]
      rwa [trace_length] at i₀lt
  -- Prove a bound we'll need in order to define 'f' (below)
  have idxlt (i : Fin (n' + 1)) : i.val + ileft < n := by
    apply lt_of_le_of_lt (Nat.le_of_lt_add_one _) irlt
    apply (Nat.sub_lt_sub_iff_right (Nat.le_add_left ileft i.val)).mp
    rw [Nat.add_sub_cancel, Nat.sub_add_comm]
    · exact i.2
    · exact min_le_max
  -- Define a function from Fin to the y-coordinates in the segment
  -- of the trace between i₀ and i₁ (inclusive)
  -- Proving that the 'getElem' is valid requires a bit of work.
  let f : Fin (n' + 1) → Int := fun i ↦ ((trace n rs blocked)[i.val + ileft]'(by
    rw [trace_length]; exact idxlt i)).y
  -- Prove the "adjacency" requirement for f
  have hadj : ∀ (i : Fin n'), (f i.succ - f i.castSucc).natAbs ≤ 1 := by
    intro i
    unfold f; dsimp
    rw [getElem_congr_idx (add_right_comm i.val 1 ileft)]
    rw [trace_getElem_recurrence]; swap
    · rw [add_right_comm]
      exact idxlt i.succ
    rw [← Int.neg_sub, Int.natAbs_neg]
    apply le_trans (le_max_right _ _)
    -- We have previously proven that the distance to 'next_step'
    -- will never be greater than one. Use that result to close the goal.
    exact next_step_dist_le_one blocked ((trace n rs blocked)[i.val + ileft]'(by
      rw [trace_length]
      exact idxlt i.castSucc
    ))
  -- Prove some identities on f 0 and f (Fin.last n')
  have fz_of_i₀lei₁ (i₀lei₁ : i₀ ≤ i₁) : f 0 = rs₀.y := by
    unfold f; congr
    convert hgE₀
    rw [Fin.val_zero, zero_add]
    exact min_eq_left i₀lei₁
  have fz_of_i₁lei₀ (i₁lei₀ : i₁ ≤ i₀) : f 0 = rs₁.y := by
    unfold f; congr
    convert hgE₁
    rw [Fin.val_zero, zero_add]
    exact min_eq_right i₁lei₀
  have fl_of_i₀lei₁ (i₀lei₁ : i₀ ≤ i₁) : f (Fin.last n') = rs₁.y := by
    unfold f; congr
    convert hgE₁; dsimp
    unfold n'
    rw [Nat.sub_add_cancel min_le_max]
    exact max_eq_right i₀lei₁
  have fl_of_i₁lei₀ (i₁lei₀ : i₁ ≤ i₀) : f (Fin.last n') = rs₀.y := by
    unfold f; congr
    convert hgE₀; dsimp
    unfold n'
    rw [Nat.sub_add_cancel min_le_max]
    exact max_eq_left i₁lei₀
  have ley' : min (f 0) (f (Fin.last n')) ≤ y := by
    by_cases hi₀i₁ : i₀ ≤ i₁
    · rw [fz_of_i₀lei₁ hi₀i₁, fl_of_i₀lei₁ hi₀i₁]
      exact min_le_of_left_le ley
    · push_neg at hi₀i₁
      apply le_of_lt at hi₀i₁
      rw [fz_of_i₁lei₀ hi₀i₁, fl_of_i₁lei₀ hi₀i₁]
      exact min_le_of_right_le ley
  have yle' : y ≤ max (f 0) (f (Fin.last n')) := by
    by_cases hi₀i₁ : i₀ ≤ i₁
    · rw [fz_of_i₀lei₁ hi₀i₁, fl_of_i₀lei₁ hi₀i₁]
      exact le_max_of_le_right yle
    · push_neg at hi₀i₁
      apply le_of_lt at hi₀i₁
      rw [fz_of_i₁lei₀ hi₀i₁, fl_of_i₁lei₀ hi₀i₁]
      exact le_max_of_le_left yle
  -- Use the intermediate value theorem proven in Misc.lean to get 'j'
  rcases fin_intermediate_value_of_consec_adj f hadj y ley' yle' with ⟨j, hj⟩
  unfold f at hj
  use ((trace n rs blocked)[j.val + ileft]'(by
    rw [trace_length]
    exact idxlt j
  ))
  apply And.intro _ hj
  apply List.getElem_mem

-- Adding cells to the blocked list has no effect on the path of the
-- trace if none of the cells are on the original trace.
lemma trace_unchanged_of_block_unvisited_cells
  (n : Nat) (start : RunState) (blocked blocked' : List (Int × Int)) :
  (∀ rs ∈ trace n start blocked, loc rs ∉ blocked') ∧ blocked ⊆ blocked' →
  trace n start blocked = trace n start blocked' := by
  intro ⟨hnmem, hss⟩
  -- Handle the case where n = 0
  by_cases nz : n = 0
  · subst nz
    rw [trace_nil, trace_nil]
  rename' nz => nnz; push_neg at nnz
  have npos : 0 < n := Nat.pos_of_ne_zero nnz
  -- Generalize the recursion case since we'll need it twice
  have : ∀ i (ilt : i < n - 1), (trace n start blocked)[i]'(by
    rw [trace_length]
    exact lt_of_lt_of_le ilt (Nat.sub_le _ _)
  ) = (trace n start blocked')[i]'(by
    rw [trace_length]
    exact lt_of_lt_of_le ilt (Nat.sub_le _ _)
  ) := by
    intro i ilt₀
    have ilt₁ : i < (trace n start blocked).length := by
      rw [trace_length]
      exact lt_of_lt_of_le ilt₀ (Nat.sub_le _ _)
    have ilt₂ : i < (trace n start blocked').length := by
      rw [trace_length]
      exact lt_of_lt_of_le ilt₀ (Nat.sub_le _ _)
    rw [List.getElem_take' ilt₁ ilt₀]
    rw [List.getElem_take' ilt₂ ilt₀]
    rw [← getElem_congr_coll (trace_take _ _ _ _ (Nat.sub_le n 1))]; swap
    · rwa [trace_length]
    rw [← getElem_congr_coll (trace_take _ _ _ _ (Nat.sub_le n 1))]; swap
    · rwa [trace_length]
    congr 1
    -- Apply the recursion, then prove that the preconditions hold
    apply trace_unchanged_of_block_unvisited_cells
    apply And.intro _ hss
    intro rs rsmem
    rw [trace_take _ _ _ _ (Nat.sub_le n 1)] at rsmem
    exact hnmem rs (List.mem_of_mem_take rsmem)
  apply List.ext_getElem
  · rw [trace_length, trace_length]
  intro i ilt₀ ilt₁
  have ilt₂ : i < n := by
    rwa [trace_length] at ilt₀
  -- If i ≠ n - 1 we can apply the recursion case (proven above)
  by_cases ilt₃ : i < n - 1
  · exact this i ilt₃
  rename' ilt₃ => nple; push_neg at nple
  have inp : i = n - 1 := le_antisymm (Nat.le_sub_one_of_lt ilt₂) nple
  subst inp
  -- Handle the case where n - 1 = 0
  by_cases npz : n - 1 = 0
  · rw [getElem_congr_idx npz, getElem_congr_idx npz]
    rw [trace_getElem_zero_of_nonnil, trace_getElem_zero_of_nonnil]
    · apply List.ne_nil_of_length_pos
      rwa [trace_length]
    · apply List.ne_nil_of_length_pos
      rwa [trace_length]
  rename' npz => npnz; push_neg at npnz
  have nplt : n - 1 < n := by
    exact Nat.sub_lt_of_pos_le (by norm_num) (Nat.add_one_le_of_lt npos)
  have npplt : n - 1 - 1 < n - 1 := by
    apply Nat.sub_lt_sub_right _ nplt
    exact Nat.add_one_le_of_lt (Nat.pos_of_ne_zero npnz)
  -- Rewrite the indices so we can apply the trace recurrence
  rw [← getElem_congr_idx (Nat.sub_one_add_one npnz)]; swap
  · rwa [trace_length, Nat.sub_one_add_one]
    assumption
  rw [← getElem_congr_idx (Nat.sub_one_add_one npnz)]; swap
  · rwa [trace_length, Nat.sub_one_add_one]
    assumption
  rw [trace_getElem_recurrence]; swap
  · rwa [Nat.sub_one_add_one npnz]
  rw [trace_getElem_recurrence]; swap
  · rwa [Nat.sub_one_add_one npnz]
  rw [← this (n - 1 - 1) npplt]
  -- Apply the corresponding result for 'next_step' to finish the goal
  apply next_step_unchanged_of_block_unvisited_cells
  apply And.intro _ hss
  apply hnmem
  -- Now we just need to prove that the result of 'next_step'
  -- was in the original trace.
  rw [← trace_getElem_recurrence]; swap
  · rwa [Nat.sub_one_add_one npnz]
  apply List.getElem_mem

-- If the trace starts next to a wall, it will always be next to a wall
-- Note that this result could also be proven as a special case of
-- 'edge_of_runner_mem_region_edges' (from Perimeter.lean) but that would
-- have introduced dependency issues because Perimeter.lean depends on Trace.lean
lemma trace_wall_blocked_of_valid (n : Nat) (start : RunState) (blocked : List (Int × Int)) :
  run_start_valid blocked start → ∀ rs ∈ trace n start blocked, left_of_runner rs ∈ blocked := by
  intro hvalid rs rsmem
  by_cases nz : n = 0
  · subst nz
    rw [trace_nil] at rsmem
    exact False.elim (List.not_mem_nil rsmem)
  rename' nz => nnz; push_neg at nnz
  rcases List.getElem_of_mem rsmem with ⟨i, ilt, rfl⟩
  have hnnil : trace n start blocked ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [trace_length]
    exact Nat.pos_of_ne_zero nnz
  by_cases iz : i = 0
  · subst iz
    rw [trace_getElem_zero_of_nonnil n start blocked hnnil]
    exact hvalid.2
  rename' iz => inz; push_neg at inz
  have ilt' : i < n := by rwa [trace_length] at ilt
  rw [trace_getElem_recurrence' n start blocked i (Nat.pos_of_ne_zero inz) ilt']
  -- Let rs' be the run state prior to the cell in question
  let rs' := (trace n start blocked)[i - 1]'(lt_of_le_of_lt (Nat.sub_le _ _) ilt)
  change left_of_runner (next_step blocked rs') ∈ blocked
  -- Use recursion to prove that rs' has a wall to its left
  have hvalid' : left_of_runner rs' ∈ blocked := by
    unfold rs'
    rw [trace_getElem_getLast]
    apply trace_wall_blocked_of_valid i start blocked hvalid
    have hnnil' : trace (i - 1 + 1) start blocked ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [trace_length, Nat.sub_one_add_one inz]
      exact Nat.pos_of_ne_zero inz
    convert List.getLast_mem hnnil'
    rw [Nat.sub_one_add_one inz]
  unfold next_step
  split_ifs with h₀ h₁
  · unfold loc move_forward at h₁; dsimp at h₁
    unfold left_of_runner turn_right; dsimp
    rwa [sub_neg_eq_add]
  · unfold loc turn_left at h₀; dsimp at h₀
    unfold left_of_runner move_forward; dsimp
    rwa [Int.add_right_comm]
  · unfold left_of_runner at hvalid'
    unfold left_of_runner turn_left; dsimp
    rw [sub_right_comm, add_sub_assoc, sub_self, add_zero]
    rwa [← sub_eq_add_neg, add_sub_assoc, sub_self, add_zero]

-- If a trace loops, the first state to repeat is the initial state.
lemma trace_start_is_first_dupe (n : Nat) (start : RunState) (blocked : List (Int × Int))
  (hdupe : list_has_dupes (trace n start blocked)) (hvalid : run_start_valid blocked start) :
  (trace n start blocked)[find_first_dupe (trace n start blocked) (list_ne_nil_of_has_dupes _ hdupe)] = start := by
  have hnnil : trace n start blocked ≠ [] := list_ne_nil_of_has_dupes _ hdupe
  -- Start by getting the locations of the duplicates:
  have := first_dupe_is_dupe _ hdupe; dsimp at this
  rcases this with ⟨i, ilt, hij⟩
  let j := (find_first_dupe (trace n start blocked) hnnil).1
  -- Prove a bunch of useful inequalities, etc.
  let jlt : j < (trace n start blocked).length :=
    (find_first_dupe (trace n start blocked) hnnil).2
  have jlt' : j < n := by rwa [trace_length] at jlt
  have jpos : 0 < j := Nat.zero_lt_of_lt ilt
  have ilt' : i < (trace n start blocked).length := lt_trans ilt jlt
  have ilt'' : i < n := by rwa [trace_length] at ilt'
  -- Make 'ilt' and 'hij' a bit nicer to work with
  change i < j at ilt
  change (trace n start blocked)[i]'(lt_trans ilt jlt) = (trace n start blocked)[j]'(jlt) at hij
  -- First handle the case where i = 0
  by_cases iz : i = 0
  · subst iz
    rw [trace_getElem_zero_of_nonnil n start blocked hnnil] at hij
    exact hij.symm
  rename' iz => inz; push_neg at inz
  -- Prove some move inequalities on 'i' and 'j' now that we can assume i ≠ 0
  have ipos : 0 < i := Nat.pos_of_ne_zero inz
  have iplt : i - 1 < j - 1 :=
    Nat.sub_lt_sub_right (Nat.one_le_of_lt ipos) ilt
  have jplt : j - 1 < (trace n start blocked).length :=
    lt_of_le_of_lt (Nat.sub_le _ _) jlt
  have iplt' : i - 1 < (trace n start blocked).length :=
    lt_trans iplt jplt
  -- Now we will achieve a contradiction by showing that some earlier duplicate must exist
  -- Start by setting up the goal 'j ≤ j - 1'
  apply False.elim (Nat.not_le.mpr (Nat.sub_lt (Nat.zero_lt_of_lt ilt) (one_pos)) _)
  -- In particular will show that the i-1st and j-1st elements must match
  apply first_dupe_is_first (trace n start blocked) hdupe (i - 1) (j - 1) iplt jplt
  rw [trace_getElem_recurrence' n start blocked i ipos ilt''] at hij
  rw [trace_getElem_recurrence' n start blocked j jpos jlt'] at hij
  -- Prove that the cells at steps 'i' and 'j' are unblocked while the cells
  -- to the runner's left on those steps *are* blocked. These conditions
  -- are required to cancel 'next_step' with 'undo_next_step'.
  have tip : loc ((trace n start blocked)[i - 1]'iplt') ∉ blocked :=
    trace_avoids_blocked n start blocked hvalid.1 _ (List.getElem_mem _)
  have tjp : loc ((trace n start blocked)[j - 1]'jplt) ∉ blocked :=
    trace_avoids_blocked n start blocked hvalid.1 _ (List.getElem_mem _)
  have lorip : left_of_runner ((trace n start blocked)[i - 1]'iplt') ∈ blocked :=
    trace_wall_blocked_of_valid n start blocked hvalid _ (List.getElem_mem _)
  have lorjp : left_of_runner ((trace n start blocked)[j - 1]'jplt) ∈ blocked :=
    trace_wall_blocked_of_valid n start blocked hvalid _ (List.getElem_mem _)
  -- Apply 'undo_next_step' to 'hij' and cancel
  convert congrArg (undo_next_step blocked) hij
  · exact (next_step_undo_cancel blocked _ tip lorip).symm
  · exact (next_step_undo_cancel blocked _ tjp lorjp).symm
