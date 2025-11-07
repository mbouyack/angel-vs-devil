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

-- The west wall turned out to be taller than intended but any
-- wall tall enough to keep the runner east of the y-axis will work.
-- As long as we define the endgame blocked list to include the
-- full height of the wall (above the x-axis) the final argument
-- should still work.
def endgame_wall_height {p : Nat} (E : Endgame p) : Nat := ((E.n + 2) * p) + 2

-- The endgame wall has positive height
lemma endgame_wall_height_pos {p : Nat} (E : Endgame p) :
  0 < endgame_wall_height E := by
  unfold endgame_wall_height
  norm_num

-- The endgame wall has non-zero height
lemma endgame_wall_height_ge_one {p : Nat} (E : Endgame p) :
  1 ≤ endgame_wall_height E := by
  unfold endgame_wall_height
  exact Nat.one_le_of_lt (Nat.add_one_pos _)

-- The endgame trace never even touches the top cell of the wall
lemma endgame_wall_height_lb {p : Nat} (E : Endgame p) :
  E.n * p + 1 ≤ endgame_wall_height E - 1 := by
  apply Nat.add_one_le_of_lt
  unfold endgame_wall_height; simp
  apply Nat.lt_add_one_of_le
  rw [add_mul]
  exact Nat.le_add_right _ _

-- Produce the final 'blocked' list by taking the last blocked list
-- used in the endgame trace and removing any cells eaten by the devil
-- outside of the first quadrant or higher than the west wall.
def endgame_blocked {p : Nat} (E : Endgame p) : List (Int × Int) :=
  blocked_trim_quad1 (E.i + 1) run_start (make_block_list E.D p (E.n + 1))
    (endgame_wall_height E - 1)

-- Any cell with x = -1 and positive y-coordinate less than the
-- height of the endgame wall will be in the endgame blocked list
lemma endgame_blocked_mem_of_wall_mem {p : Nat} (E : Endgame p) :
  ∀ i (_ : i < endgame_wall_height E),
  (-1, (i : Int)) ∈ (endgame_blocked E) := by
  intro i ilt
  apply trace_trim_quad1_mem
  · -- First, prove that the cell in question was in the wall to begin with
    unfold make_block_list
    apply List.mem_union_iff.mpr; right
    rw [make_run_eaten_length]
    -- Prove the y-coordinate bounds required to be in the west wall
    apply west_wall_mem
    · apply le_trans (Int.neg_ofNat_le_natCast _ 0)
      exact Int.ofNat_le.mpr (Nat.zero_le _)
    · unfold endgame_wall_height at ilt
      rw [← one_add_one_eq_two, ← add_assoc] at ilt
      convert Int.ofNat_le.mpr (Nat.le_of_lt_add_one ilt)
  constructor
  · simp
  constructor
  · simp
    convert Int.ofNat_le.mpr (Nat.le_sub_one_of_lt ilt)
    rw [Int.natCast_sub (endgame_wall_height_ge_one E)]
    rw [Int.natCast_one]
  constructor
  · simp
  use run_start
  let BL' := make_block_list E.D p (E.n + 1)
  constructor
  · nth_rw 2 [← trace_getElem_zero_of_nonnil (E.i + 1) run_start BL']
    · exact List.getElem_mem _
    · apply List.ne_nil_of_length_pos
      rw [trace_length]
      exact Nat.add_one_pos _
  · unfold run_start uvec_up loc; simp

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
    constructor
    · exact endgame_wall_height_ge_one E
    use run_start
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
  apply trace_trim_quad1_unchanged (E.i + 1) run_start BL (endgame_wall_height E - 1)
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
  · rw [← Int.natCast_one, ← Int.natCast_sub (endgame_wall_height_ge_one E)]
    apply lt_of_lt_of_le _ (Int.ofNat_le.mpr (endgame_wall_height_lb E))
    rw [Int.natCast_add, Int.natCast_one]
    exact Int.lt_add_one_of_le (run_path_y_le E.D p E.n rs rsmem')
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
    apply trace_trim_quad1_notmem_of_xlt
    unfold undo_turn_left loc uvec_right; simp
  rw [if_neg hleft]
  unfold undo_turn_left uvec_right uvec_down; simp

-- Prove the coordinates and direction of all perimeter cells
-- west of the wall.
lemma endgame_west_of_wall {p : Nat} (E : Endgame p)
  (i : Nat) (ilt : i < endgame_wall_height E) :
  (endgame_perimeter E)[endgame_perimeter_length E - 2 - i]'(by
    rw [endgame_perimeter_length_def, ← Nat.sub_add_eq]
    apply Nat.sub_lt (endgame_perimeter_length_pos E)
    exact Nat.lt_add_right i (by norm_num)
  ) = ⟨-2, i, uvec_down⟩ := by
  let P := endgame_perimeter_length E
  let BL := endgame_blocked E
  -- If i = 0, we get the west point, which has already been proven
  by_cases iz : i = 0
  · subst iz
    exact endgame_west_point_eq E
  rename' iz => inz; push_neg at inz
  have ipos : 0 < i := Nat.pos_of_ne_zero inz
  have iplt : i - 1 < endgame_wall_height E - 1 := by
    exact Nat.sub_lt_sub_right (Nat.one_le_of_lt ipos) ilt
  have hvalid := endgame_run_start_valid E
  -- Use recursion to get the previous cell in the west wall
  -- (though we're working backward, so in some sense the "next" cell?)
  have hrecurse := endgame_west_of_wall E (i - 1) (lt_of_le_of_lt (Nat.sub_le _ _) ilt)
  -- Rewriting the list index in 'hrecurse' is more work than you might think!
  have hrw₀ : endgame_perimeter_length E - 2 - (i - 1) =
              endgame_perimeter_length E - 1 - i := by
    rw [Nat.sub_sub_right _ (Nat.one_le_of_lt ipos)]
    rw [← one_add_one_eq_two, Nat.sub_add_eq, Nat.sub_one_add_one]
    apply @Nat.ne_zero_of_lt (E.i + 1 - 1)
    rw [← endgame_perimeter_length_def E]
    -- We can use the bound for the southeast point to prove this
    apply Nat.sub_lt_sub_right _ (endgame_southeast_point_lt E)
    exact Nat.one_le_of_lt (Nat.add_one_pos _)
  rw [getElem_congr_idx hrw₀] at hrecurse
  have hpos : 0 < endgame_perimeter_length E - 1 - i := by
    apply Nat.pos_of_ne_zero
    contrapose! hrecurse
    -- If this were true, then the previous step would be
    -- 'run_start' which is impossible
    rw [getElem_congr_idx hrecurse, endgame_perimeter_getElem_zero]
    unfold run_start uvec_up uvec_down; simp
  have hlt : endgame_perimeter_length E - 1 - i < P := by
    rw [← Nat.sub_add_eq]
    apply Nat.sub_lt (endgame_perimeter_length_pos E)
    rw [add_comm]
    exact Nat.add_one_pos _
  -- Get the trace recurrence and apply 'undo_next_step' to both sides
  have htrace := trace_getElem_recurrence' P run_start BL _ hpos hlt
  apply congrArg (undo_next_step BL) at htrace
  rw [next_step_undo_cancel] at htrace
  pick_goal 2; pick_goal 3
  · exact trace_wall_blocked_of_valid P run_start BL hvalid _ (List.getElem_mem _)
  · exact trace_avoids_blocked P run_start BL hvalid.1 _ (List.getElem_mem _)
  have hrw₁ : P - 2 - i = P - 1 - i - 1 := by
    rw [← one_add_one_eq_two, Nat.sub_add_eq, Nat.sub_right_comm]
  unfold endgame_perimeter at *
  rw [getElem_congr_idx hrw₁, ← htrace, hrecurse]
  -- Prove that the cell at 'undo_left_turn' is always in the wall
  have huleft : loc (undo_turn_left { x := -2, y := ↑(i - 1), u := uvec_down }) ∈ BL := by
    unfold undo_turn_left uvec_down loc; simp
    nth_rw 2 [← Int.natCast_one]
    rw [← Int.natCast_add, Nat.sub_one_add_one inz]
    exact endgame_blocked_mem_of_wall_mem E i ilt
  unfold undo_next_step; simp
  -- Prove that the cell at 'undo_move_forward' is *not* in the wall
  have huforward : loc (undo_move_forward { x := -2, y := ↑(i - 1), u := uvec_down }) ∉ BL := by
    apply trace_trim_quad1_notmem_of_xlt
    unfold undo_move_forward loc uvec_down; simp
  rw [if_pos huleft, if_neg huforward]
  unfold undo_move_forward uvec_down; simp
  rw [Int.natCast_sub (Nat.one_le_of_lt ipos)]
  simp

-- Prove that the index of the north point is less than the
-- length of the endgame perimeter
lemma endgame_north_point_lt {p : Nat} (E : Endgame p) :
  endgame_perimeter_length E - endgame_wall_height E - 2 < (endgame_perimeter E).length := by
  rw [endgame_perimeter_length_def, ← Nat.sub_add_eq]
  exact Nat.sub_lt (endgame_perimeter_length_pos E) (by norm_num)

-- Prove the coordinates and direction of the north point
lemma endgame_north_point_eq {p : Nat} (E : Endgame p) :
  (endgame_perimeter E)[endgame_perimeter_length E - endgame_wall_height E - 2]'(
    endgame_north_point_lt E) = ⟨-1, endgame_wall_height E, uvec_left⟩ := by
  let P := endgame_perimeter_length E
  let BL := endgame_blocked E
  have hvalid := endgame_run_start_valid E
  -- Save the details of the top perimeter cell west of the wall
  have ewhpos : 0 < endgame_wall_height E := endgame_wall_height_pos E
  have htw := endgame_west_of_wall E (endgame_wall_height E - 1) (Nat.sub_lt ewhpos (one_pos))
  have hrw₀ : P - 2 - (endgame_wall_height E - 1) =
              P - endgame_wall_height E - 1 := by
    rw [Nat.sub_right_comm]
    rw [Nat.sub_sub_right _ (endgame_wall_height_ge_one E)]
    rw [← one_add_one_eq_two, Nat.sub_add_eq]
    rw [Nat.sub_right_comm (P + 1), Nat.add_one_sub_one]
  rw [getElem_congr_idx hrw₀] at htw
  have hpos : 0 < (P - endgame_wall_height E - 1) := by
    apply Nat.pos_of_ne_zero
    contrapose! htw
    -- If 'htw' is true, the top-most perimeter cell west of the wall
    -- would be equal to 'run_start', which is obviously false.
    rw [getElem_congr_idx htw, endgame_perimeter_getElem_zero]
    unfold run_start uvec_up uvec_down; simp
  have hlt : (P - endgame_wall_height E - 1) < P := by
    rw [← Nat.sub_add_eq]
    exact Nat.sub_lt (endgame_perimeter_length_pos E) (by norm_num)
  -- Get the trace recurrence and apply 'undo_next_step' to both sides
  have htrace := trace_getElem_recurrence' P run_start BL _ hpos hlt
  apply congrArg (undo_next_step BL) at htrace
  unfold endgame_perimeter at *
  rw [htw] at htrace
  rw [next_step_undo_cancel] at htrace
  pick_goal 2; pick_goal 3
  · exact trace_wall_blocked_of_valid P run_start BL hvalid _ (List.getElem_mem _)
  · exact trace_avoids_blocked P run_start BL hvalid.1 _ (List.getElem_mem _)
  have hrw₁ : P - endgame_wall_height E - 2 = P - endgame_wall_height E - 1 -1 := by
    rw [← one_add_one_eq_two, Nat.sub_add_eq]
  rw [getElem_congr_idx hrw₁, ← htrace]
  unfold undo_next_step; simp
  -- Show that undoing a left turn starting at the top-most
  -- west-of-wall cell gives a cell that isn't in the wall
  have huleft : loc (undo_turn_left { x := -2, y := ↑(endgame_wall_height E - 1), u := uvec_down }) ∉ BL := by
    apply trace_trim_quad1_notmem_of_lty
    unfold loc undo_turn_left uvec_down; simp
    rw [Int.natCast_sub (endgame_wall_height_ge_one E)]
    simp
  rw [if_neg huleft]
  unfold undo_turn_left uvec_down uvec_left; simp
  rw [← Int.natCast_one, ← Int.natCast_add, Nat.sub_one_add_one]
  exact Nat.ne_zero_of_lt (endgame_wall_height_pos E)
