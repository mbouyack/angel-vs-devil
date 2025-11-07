import AngelDevil.Runner
import AngelDevil.Blocked
import AngelDevil.Perimeter

set_option linter.style.longLine false

/- This file defines the idea of an "Endgame", in which a nice devil
   has forced the runner to return to the x-axis. The main argument
   of this file will be to show that six key points fall on the
   perimeter of the region formed by the endgame blocked list and
  to prove that the perimeter around that region has a lower bound
  based on the distances between successive pairs of those points.

  Note that the final argument of this project is to show that
  an 'Endgame 2' cannot exist, and therefore the angel of power 2 wins.
-/

-- If the devil wins, then some "nice" devil can force the runner to
-- return to the x-axis. We'll bundle all the objects which describe
-- this arrangement into a structure called an 'Endgame'. The final
-- argument of the proof will be to show that an "Endgame 2" cannot
-- exist.
structure Endgame (p : Nat) where
  D : Devil
  n : Nat
  i : Nat
  T : List RunState
  hlt : i < (RunPath D p n).length
  hlb : (RunPath D p (n - 1)).length ≤ i
  hnice : nice D p
  hpath : T = List.take (i + 1) (RunPath D p n)
  hnodupe : list_nodupes T
  hynonneg : ∀ rs ∈ T, 0 ≤ rs.y
  hwest : ∀ rs ∈ T,
    rs.y = 0 → rs.u ≠ uvec_left
  hsouth : south_facing_yz_xnn (T.getLast (by
    apply List.ne_nil_of_length_pos
    rw [hpath, List.length_take_of_le (Nat.add_one_le_of_lt hlt)]
    exact Nat.add_one_pos _
  ))

-- Produce the final 'blocked' list by taking the last blocked list
-- used in the endgame trace and removing any cells eaten by the devil
-- outside of the first quadrant or higher than the west wall.
abbrev endgame_blocked {p : Nat} (E : Endgame p) : List (Int × Int) :=
  blocked_trim_quad1 (E.i + 1) run_start (make_block_list E.D p (E.n + 1)) (E.n * p + 1)

-- Prove that run_start is "valid" under the endgame blocked list
lemma endgame_run_start_valid {p : Nat} (E : Endgame p) :
  run_start_valid (endgame_blocked E) run_start := by
  unfold run_start_valid
  let ⟨rsnmem, lormem⟩ := run_start_valid_of_nice E.D p E.hnice (E.n + 1)
  let BL := make_block_list E.D p (E.n + 1)
  let T := trace (E.i + 1) run_start BL
  have tlpos : 0 < T.length := by
    rw [trace_length]
    exact Nat.add_one_pos _
  have hnnil : T ≠ [] := List.ne_nil_of_length_pos tlpos
  constructor
  · apply trace_trim_quad1_notmem_of_notmem
    exact rsnmem
  · apply trace_trim_quad1_mem _ _ _ _ _ lormem
    unfold run_start left_of_runner uvec_up; simp
    use (by rw [← Int.natCast_mul]; linarith), run_start
    constructor
    · apply List.mem_of_getElem
      · convert trace_getElem_zero_of_nonnil _ _ _ hnnil
      · exact tlpos
    · unfold run_start loc; simp

lemma endgame_trace_ne_nil {p : Nat} (E : Endgame p) : E.T ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [E.hpath]
  have isle : E.i + 1 ≤ (RunPath E.D p E.n).length :=
    Nat.add_one_le_of_lt E.hlt
  rw [List.length_take_of_le isle]
  exact Nat.add_one_pos _

-- The endgame trace is equal to the trace of length 'E.i + 1',
-- starting at 'run_start' and using the endgame blocked list
lemma endgame_trace_eq {p : Nat} (E : Endgame p) :
  E.T = trace (E.i + 1) run_start (endgame_blocked E) := by
  let BL := make_block_list E.D p (E.n + 1)
  let RP := RunPath E.D p E.n
  rw [E.hpath]
  have Eislt := Nat.add_one_le_of_lt E.hlt
  have htrace := run_path_eq_trace_of_nice E.D p E.n (E.n + 1) (by simp) E.hnice
  have htake := trace_take RP.length run_start BL (E.i + 1) Eislt
  rw [htrace, ← htake]
  apply trace_trim_quad1_unchanged (E.i + 1) run_start BL (E.n * p + 1)
  intro rs rsmem
  have rsmem' : rs ∈ RP := by
    unfold RP
    rw [htrace]
    apply List.mem_of_mem_take
    rwa [← htake]
  rcases List.getElem_of_mem rsmem with ⟨i, ilt, hi⟩
  have rsmem'' : rs ∈ E.T := by
    rw [← hi, E.hpath, htrace, ← htake]
    exact List.getElem_mem _
  constructor
  · exact run_path_x_nonneg E.D p E.n rs rsmem'
  constructor
  · exact E.hynonneg rs rsmem''
  constructor
  · apply Int.lt_add_one_of_le
    rw [← Int.natCast_mul]
    exact run_path_y_le E.D p E.n _ rsmem'
  · exact E.hwest _ rsmem''

def endgame_perimeter_length {p : Nat} (E : Endgame p) : Nat :=
  perimeter_length run_start (endgame_blocked E) (endgame_run_start_valid E)

-- Give a name to the trace which circumnavigates the endgame blocked list
def endgame_perimeter {p : Nat} (E : Endgame p) : List RunState :=
  trace (endgame_perimeter_length E) run_start (endgame_blocked E)

lemma endgame_perimeter_length_def {p : Nat} (E : Endgame p) :
  (endgame_perimeter E).length = endgame_perimeter_length E := by
  unfold endgame_perimeter
  rw [trace_length]

lemma endgame_perimeter_length_pos {p : Nat} (E : Endgame p) :
  0 < endgame_perimeter_length E := by
  apply perimeter_length_pos

lemma endgame_perimeter_length_pos' {p : Nat} (E : Endgame p) :
  0 < (endgame_perimeter E).length := by
  rw [endgame_perimeter_length_def]
  exact endgame_perimeter_length_pos E

lemma endgame_perimeter_ne_nil {p : Nat} (E : Endgame p) : endgame_perimeter E ≠ [] := by
  apply List.ne_nil_of_length_pos
  exact endgame_perimeter_length_pos' E

lemma endgame_perimeter_getElem_zero {p : Nat} (E : Endgame p) :
  (endgame_perimeter E)[0]'(endgame_perimeter_length_pos' E) = run_start := by
  exact trace_getElem_zero_of_nonnil _ _ _ (endgame_perimeter_ne_nil E)

-- Prove that the endpoint of the endgame trace falls within the endgame perimeter
lemma endgame_endpoint_lt {p : Nat} (E : Endgame p) :
  E.i < (endgame_perimeter E).length := by
  rw [endgame_perimeter_length_def, endgame_perimeter_length]
  by_contra! lei
  let BL := endgame_blocked E
  let T := trace (E.i + 1) run_start BL
  have hvalid := endgame_run_start_valid E
  have hnnil : T ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [trace_length]
    exact Nat.add_one_pos _
  let P := perimeter_length run_start BL hvalid
  have Ppos : 0 < P :=
    perimeter_length_pos run_start BL hvalid
  -- Show that if E.i is not less than that perimeter length,
  -- there must be a duplicate (which is a contradiction)
  have Psle : P + 1 ≤ T.length := by
    rw [trace_length]
    exact Nat.add_one_le_add_one_iff.mpr lei
  absurd E.hnodupe
  rw [list_not_nodupes]
  use 0, P, (perimeter_length_pos _ _ hvalid), (by
    rw [E.hpath]
    rw [List.length_take_of_le (Nat.add_one_le_of_lt E.hlt)]
    exact Nat.lt_add_one_of_le lei
  )
  repeat rw [getElem_congr_coll (endgame_trace_eq E)]
  rw [trace_getElem_zero_of_nonnil (E.i + 1) run_start BL hnnil]; symm
  have hrepeat := trace_start_repeats_idx run_start BL hvalid
  rw [List.getElem_take' _ (Nat.lt_add_one P)]
  rw [← getElem_congr_idx (Nat.add_one_sub_one P)]; swap
  · rw [List.length_take_of_le Psle]; simp
  rw [List.getLast_eq_getElem] at hrepeat
  convert hrepeat
  · rw [← trace_take]
    exact Nat.add_one_le_add_one_iff.mpr lei
  · rw [trace_length]

-- Prove a lower bound on length of the endgame trace
lemma endgame_endpoint_lb {p : Nat} (E : Endgame p) : (E.n - 1) * p + 1 ≤ E.i := by
  apply le_trans _ E.hlb
  rw [add_comm, mul_comm]
  exact run_path_length_lb E.D p (E.n - 1)

def endgame_endpoint {p : Nat} (E : Endgame p) : RunState :=
  (endgame_perimeter E)[E.i]'(endgame_endpoint_lt E)

lemma endgame_endpoint_def {p : Nat} (E : Endgame p) :
  (endgame_endpoint E) = (endgame_perimeter E)[E.i]'(endgame_endpoint_lt E) := rfl

lemma endgame_endpoint_eq {p : Nat} (E : Endgame p) :
  endgame_endpoint E = E.T.getLast (endgame_trace_ne_nil E) := by
  let BL := (endgame_blocked E)
  let P := endgame_perimeter_length E
  have isle : E.i + 1 ≤ (trace P run_start BL).length :=
    Nat.add_one_le_of_lt (endgame_endpoint_lt E)
  have isle' : E.i + 1 ≤ P := by
    rwa [trace_length] at isle
  rw [List.getLast_congr _ _ (endgame_trace_eq E)]; swap
  · apply List.ne_nil_of_length_pos
    rw [trace_length]
    exact Nat.add_one_pos _
  have htake := trace_take P run_start BL _ isle'
  rw [List.getLast_congr _ _ htake]; swap
  · apply List.ne_nil_of_length_pos
    rw [List.length_take_of_le isle]
    exact Nat.add_one_pos _
  rw [List.getLast_eq_getElem, List.getElem_take, endgame_endpoint_def]; congr
  rw [List.length_take_of_le isle]; simp

lemma endgame_endpoint_yz {p : Nat} (E : Endgame p) :
  (endgame_endpoint E).y = 0 := by
  convert E.hsouth.2.1
  exact endgame_endpoint_eq E

lemma endgame_endpoint_lex {p : Nat} (E : Endgame p) :
  0 ≤ (endgame_endpoint E).x := by
  convert E.hsouth.1
  exact endgame_endpoint_eq E

lemma endgame_endpoint_u {p : Nat} (E : Endgame p) :
  (endgame_endpoint E).u = uvec_down := by
  convert E.hsouth.2.2
  exact endgame_endpoint_eq E

-- Prove that the last point in the perimeter has coordinates (-1, -1)
lemma endgame_southwest_point_eq {p : Nat} (E : Endgame p) :
  ((endgame_perimeter E)[endgame_perimeter_length E - 1]'(by
    rw [endgame_perimeter_length_def]
    apply Nat.sub_one_lt (Nat.ne_zero_of_lt (endgame_perimeter_length_pos E))
  )) = ⟨-1, -1, uvec_right⟩ := by
  let P := endgame_perimeter_length E
  let BL := endgame_blocked E
  have Ppos : 0 < P := by
    apply perimeter_length_pos
  have hvalid := endgame_run_start_valid E
  have hrepeat := trace_start_repeats_idx run_start BL hvalid
  change (trace (P + 1) run_start BL).getLast _ = _ at hrepeat
  rw [List.getLast_eq_getElem] at hrepeat
  have rw₀ : (trace (P + 1) run_start BL).length - 1 = P := by
    rw [trace_length]; simp
  rw [getElem_congr_idx rw₀] at hrepeat
  rw [trace_getElem_recurrence' (P + 1) run_start BL P Ppos (Nat.lt_add_one _)] at hrepeat
  apply congrArg (undo_next_step BL) at hrepeat
  rw [next_step_undo_cancel] at hrepeat
  -- In order to use 'undo_next_step' we need to prove
  -- that the last cell in the perimeter is "valid"
  pick_goal 2; pick_goal 3
  · exact trace_wall_blocked_of_valid (P + 1) run_start BL hvalid _ (List.getElem_mem _)
  · exact trace_avoids_blocked (P + 1) run_start BL hvalid.1 _ (List.getElem_mem _)
  unfold endgame_perimeter
  rw [getElem_congr_coll (trace_take (P + 1) run_start BL P (by norm_num))]
  rw [List.getElem_take, hrepeat]
  unfold undo_next_step; simp
  have huleft : loc (undo_turn_left run_start) ∉ BL := by
    apply trace_trim_quad1_notmem_of_yneg
    unfold undo_turn_left run_start loc uvec_up; simp
  rw [if_neg huleft]
  unfold undo_turn_left run_start uvec_up uvec_right; simp

-- Prove the bounds check for the southwest point
-- (which comes immediately after the "endpoint")
lemma endgame_southeast_point_lt {p : Nat} (E : Endgame p) :
  E.i + 1 < (endgame_perimeter E).length := by
  apply lt_of_le_of_ne (Nat.add_one_le_of_lt (endgame_endpoint_lt E))
  rw [endgame_perimeter_length_def]
  by_contra! iseq
  -- If E.i + 1 = P, the endpoint is equal to the southwest point
  -- But this is impossible because the former has x = 0 and the
  -- latter has x = -1
  absurd endgame_endpoint_yz E
  rw [endgame_endpoint_def, getElem_congr_idx (Nat.eq_sub_of_add_eq iseq)]
  rw [(RunState.ext_iff.mp (endgame_southwest_point_eq E)).2.1]; simp

-- Prove that the southeast point has y = -1 and x-coordinate
-- one greater than the endgame endpoint.
lemma endgame_southeast_point_eq {p : Nat} (E : Endgame p) :
  ((endgame_perimeter E)[E.i + 1]'(endgame_southeast_point_lt E)) =
  ⟨(endgame_endpoint E).x + 1, -1, uvec_right⟩ := by
  let P := endgame_perimeter_length E
  let BL := endgame_blocked E
  let T := endgame_perimeter E
  have hnnil : E.T ≠ [] := endgame_trace_ne_nil E
  unfold endgame_perimeter
  have ilt : E.i < T.length := by
    exact endgame_endpoint_lt E
  have islt : E.i + 1 < endgame_perimeter_length E := by
    convert endgame_southeast_point_lt E
    exact (endgame_perimeter_length_def E).symm
  rw [trace_getElem_recurrence _ _ _ _ islt]
  unfold next_step
  have : turn_left T[E.i] = ⟨(endgame_endpoint E).x + 1, -1, uvec_right⟩ := by
    have hy : (E.T.getLast hnnil).y = 0 := by
      convert endgame_endpoint_yz E
      exact (endgame_endpoint_eq E).symm
    have hu : (E.T.getLast hnnil).u = uvec_down := by
      convert endgame_endpoint_u E
      exact (endgame_endpoint_eq E).symm
    have rw₀ := endgame_endpoint_eq E
    unfold endgame_endpoint at rw₀
    rw [endgame_endpoint_eq E, rw₀]
    unfold turn_left; simp
    rw [← and_assoc]
    unfold uvec_down at hu
    constructor
    · rw [hu, hy]; simp
    unfold uvec_right
    apply UVec.ext
    · simp; rw [hu]; simp
    · simp; rw [hu]
  have hleft : loc (turn_left T[E.i]) ∉ endgame_blocked E := by
    apply trace_trim_quad1_notmem_of_yneg
    rw [this, loc]; simp
  unfold T endgame_perimeter at hleft
  rw [if_pos hleft]
  exact this

-- Prove that the second-to-last point in the endgame perimeter
-- has coordinates (-2, 0)
lemma endgame_west_point_eq {p : Nat} (E : Endgame p) :
  ((endgame_perimeter E)[endgame_perimeter_length E - 2]'(by
    rw [endgame_perimeter_length_def]
    exact Nat.sub_lt (endgame_perimeter_length_pos E) (by norm_num)
  )) = ⟨-2, 0, uvec_down⟩ := by
  let P := endgame_perimeter_length E
  let BL := endgame_blocked E
  have hnnil : (endgame_perimeter E) ≠ [] := by
    exact endgame_perimeter_ne_nil E
  have Pnz : P ≠ 0 := Nat.ne_zero_of_lt (endgame_perimeter_length_pos E)
  have Ppnz : P - 1 ≠ 0 := by
    by_contra! Ppz
    absurd endgame_southwest_point_eq E
    rw [getElem_congr_idx Ppz]
    rw [endgame_perimeter_getElem_zero]
    unfold run_start; simp
  have Pppos : 0 < P - 1 :=
    Nat.pos_of_ne_zero Ppnz
  have hvalid := endgame_run_start_valid E
  have htrace := trace_getElem_recurrence' P run_start BL (P - 1) Pppos (Nat.sub_one_lt Pnz)
  -- Apply 'undo_next_step' to both side of the recurrence to get the
  -- second-to-last step in terms of the last step
  apply congrArg (undo_next_step BL) at htrace
  rw [next_step_undo_cancel] at htrace
  pick_goal 2; pick_goal 3
  · exact trace_wall_blocked_of_valid P run_start BL hvalid _ (List.getElem_mem _)
  · exact trace_avoids_blocked P run_start BL hvalid.1 _ (List.getElem_mem _)
  have rw₀ : P - 2 = P - 1 - 1 := by
    rw [← one_add_one_eq_two, Nat.sub_add_eq]
  unfold endgame_perimeter
  rw [getElem_congr_idx rw₀, ← htrace]
  have rw₁ := endgame_southwest_point_eq E
  unfold endgame_perimeter at rw₁
  rw [rw₁]
  unfold undo_next_step; simp
  have hleft : loc (undo_turn_left { x := -1, y := -1, u := uvec_right }) ∉ BL := by
    apply trace_trim_quad1_notmem_of_xneg
    unfold undo_turn_left loc uvec_right; simp
  rw [if_neg hleft]
  unfold undo_turn_left uvec_right uvec_down; simp
