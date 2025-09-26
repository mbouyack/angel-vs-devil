import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import AngelDevil.Basic
import AngelDevil.Misc

set_option linter.style.longLine false

/- This file defines the behavior of the "runner", who traces the perimeter of a set of blocked cells.
-/

@[ext] structure RunState where
  x : Int -- Current location, x-coord
  y : Int -- Current location, y-coord
  u : Int -- Direction of travel, x-coord
  v : Int -- Direction of travel, y-coord
  unit : u * u + v * v = 1 -- ⟨u, v⟩ should be a unit vector

-- Prove that we can determine whether two 'RunState' are equal
instance : DecidableEq RunState := fun a b ↦
  if h : a.x = b.x ∧ a.y = b.y ∧ a.u = b.u ∧ a.v = b.v then
    isTrue (RunState.ext_iff.mpr h)
  else
    isFalse (fun h' ↦ h (RunState.ext_iff.mp h'))

-- Convenience macros for repackaging the location and direction
-- parameters as Int × Int
def loc (rs : RunState) : Int × Int := ⟨rs.x, rs.y⟩
def dir (rs : RunState) : Int × Int := ⟨rs.u, rs.v⟩

-- Upper bound on the x-coordinate of the direction
lemma runstate_abs_u_le_one (rs : RunState) : Int.natAbs rs.u ≤ 1 := by
  by_contra! h
  have h₀ : 2 ≤ rs.u * rs.u := by
    rw [← one_add_one_eq_two, ← pow_two, ← Int.natAbs_pow_two, pow_two]
    apply Int.add_one_le_of_lt
    apply Nat.cast_lt.mpr
    exact Nat.mul_lt_mul'' h h
  have h₁ : 0 ≤ rs.v * rs.v := by
    rw [← pow_two]
    exact pow_two_nonneg rs.v
  have := Int.add_le_add h₀ h₁
  rw [add_zero, rs.unit] at this
  absurd this
  norm_num

-- Upper bound on the y-coordinate of the direction
lemma runstate_abs_v_le_one (rs : RunState) : Int.natAbs rs.v ≤ 1 := by
  by_contra! h
  have h₀ : 2 ≤ rs.v * rs.v := by
    rw [← one_add_one_eq_two, ← pow_two, ← Int.natAbs_pow_two, pow_two]
    apply Int.add_one_le_of_lt
    apply Nat.cast_lt.mpr
    exact Nat.mul_lt_mul'' h h
  have h₁ : 0 ≤ rs.u * rs.u := by
    rw [← pow_two]
    exact pow_two_nonneg rs.u
  have := Int.add_le_add h₁ h₀
  rw [zero_add, rs.unit] at this
  absurd this
  norm_num

-- Either the x or y-coordinate of the direction must be zero
lemma runstate_u_zero_or_v_zero (rs : RunState) :
  rs.u = 0 ∨ rs.v = 0 := by
  rw [← Int.natAbs_eq_zero, ← Int.natAbs_eq_zero]
  by_contra! h
  have hu1 : Int.natAbs rs.u = 1 :=
    le_antisymm (runstate_abs_u_le_one rs) ((Nat.one_le_of_lt (Nat.pos_of_ne_zero h.1)))
  have hv1 : Int.natAbs rs.v = 1 :=
    le_antisymm (runstate_abs_v_le_one rs) ((Nat.one_le_of_lt (Nat.pos_of_ne_zero h.2)))
  have hupow2 : rs.u ^ 2 = 1 := by
    rw [← Int.natAbs_pow_two, hu1]; simp
  have hvpow2 : rs.v ^ 2 = 1 := by
    rw [← Int.natAbs_pow_two, hv1]; simp
  have : rs.u * rs.u + rs.v * rs.v = 2 := by
    rw [← pow_two, ← pow_two, hupow2, hvpow2]; simp
  rw [rs.unit] at this
  absurd this
  norm_num

lemma runstate_uabs_add_vabs_eq_one (rs : RunState) :
  rs.u.natAbs + rs.v.natAbs = 1 := by
  rcases runstate_u_zero_or_v_zero rs with lhs | rhs
  · rw [Int.natAbs_eq_zero.mpr lhs, zero_add]
    by_contra! h
    have vz : rs.v = 0 :=
      Int.natAbs_eq_zero.mp (Nat.le_zero.mp (Nat.le_of_lt_add_one (lt_of_le_of_ne (runstate_abs_v_le_one rs) h)))
    have := rs.unit
    rw [lhs, vz, mul_zero, add_zero] at this
    absurd this
    norm_num
  · rw [Int.natAbs_eq_zero.mpr rhs, add_zero]
    by_contra! h
    have uz : rs.u = 0 :=
      Int.natAbs_eq_zero.mp (Nat.le_zero.mp (Nat.le_of_lt_add_one (lt_of_le_of_ne (runstate_abs_u_le_one rs) h)))
    have := rs.unit
    rw [rhs, uz, mul_zero, add_zero] at this
    absurd this
    norm_num

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

-- The "distance" between consecutive states in a trace is no greater than 1
lemma next_step_dist_le_one (blocked : List (Int × Int)) (rs : RunState) :
  dist (loc rs) (loc (next_step blocked rs)) ≤ 1 := by
  unfold next_step
  split_ifs with h₀ h₁
  · unfold turn_right dist loc; simp
  · unfold move_forward dist loc; simp
    exact ⟨runstate_abs_u_le_one rs, runstate_abs_v_le_one rs⟩
  unfold turn_left dist loc; simp
  have (a b c : Int) (h : b.natAbs + c.natAbs = 1) : (a - (a + b + c)).natAbs ≤ 1 := by
    rw [Int.sub_eq_add_neg, Int.neg_add, Int.neg_add]
    rw [← Int.add_assoc, Int.add_neg_cancel_left]
    rw [← Int.neg_add, Int.natAbs_neg, ← h]
    exact Int.natAbs_add_le b c
  constructor
  · apply this
    rw [Int.natAbs_neg]
    exact runstate_uabs_add_vabs_eq_one rs
  · apply this
    exact runstate_uabs_add_vabs_eq_one rs

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

-- In order to produce a valid trace, the runner must begin with a blocked cell to its left.
def run_start_valid (blocked : List (Int × Int)) : RunState → Prop :=
  fun run_start ↦ ⟨run_start.x - run_start.v, run_start.y + run_start.u⟩ ∈ blocked

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
lemma trace_avoids_blocked (n : Nat) (rs : RunState) (blocked : List (Int × Int)) (hsafe : loc rs ∉ blocked) :
  ∀ x ∈ trace n rs blocked, loc x ∉ blocked := by
  intro x hmem₀ hmem₁
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
  rcases List.mem_cons.mp hmem₀ with lhs | rhs
  · subst lhs
    contradiction
  have hsafe' : loc (next_step blocked rs) ∉ blocked := by
    intro hmem₂
    unfold next_step at hmem₂
    split_ifs at hmem₂ with h₁ h₂
    · rw [turn_right_loc] at hmem₂
      contradiction
    · contradiction
    · contradiction
  absurd hmem₁
  apply trace_avoids_blocked (n - 1) (next_step blocked rs) blocked hsafe' _ rhs

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
