import AngelDevil.Trace

set_option linter.style.longLine false

/- This file defines the notion of a TraceSegment, which is subsegment
   of the list of RunStates constructed by the 'trace' function.
   There are facilities for splitting the segment and accessing the
   underlying states of the segment.

   The objective is to prove lower bounds on the length of segments
   of various types in terms of the "Manhattan" distance between their
   end points. This will be critical in the final argument of
   the proof. -/

-- To put a lower bound on the length of a trace segment
-- we'll need the definition of "Manhattan" distance
def manhattan (a b : Int × Int) : Nat :=
  Int.natAbs (b.1 - a.1) + Int.natAbs (b.2 - a.2)

lemma manhattan_self (a : Int × Int) :
  manhattan a a = 0 := by
  unfold manhattan; simp

-- The triangular inequality for Manhattan distance
lemma manhattan_tri (a b c : Int × Int) :
  manhattan a c ≤ manhattan a b + manhattan b c := by
  unfold manhattan
  have hx : (c.1 - a.1).natAbs ≤ (b.1 - a.1).natAbs + (c.1 - b.1).natAbs := by
    apply le_of_eq_of_le _ (Int.natAbs_add_le _ _); simp
  have hy : (c.2 - a.2).natAbs ≤ (b.2 - a.2).natAbs + (c.2 - b.2).natAbs := by
    apply le_of_eq_of_le _ (Int.natAbs_add_le _ _); simp
  rw [add_right_comm, ← add_assoc, add_assoc (_ + _), add_comm (c.2 - b.2).natAbs]
  exact add_le_add hx hy

-- This structure describes a segment of the trace 'trace n start blocked'
-- We will ultimately prove a lower bound on the length of such a segment
-- based on its endpoints.
structure TraceSegment where
  n : Nat
  start : RunState
  blocked : List (Int × Int)
  i : Nat
  j : Nat
  ile : i ≤ j
  jlt : j < (trace n start blocked).length

-- Get the underlying trace on which the segment is based
def segment_trace (seg : TraceSegment) : List RunState := trace seg.n seg.start seg.blocked

-- Get the first RunState of the segment
def segment_start (seg : TraceSegment) : RunState :=
  (segment_trace seg)[seg.i]'(lt_of_le_of_lt seg.ile seg.jlt)

-- Get the last RunState of the segment
def segment_end (seg : TraceSegment) : RunState :=
  (segment_trace seg)[seg.j]'seg.jlt

-- Get the list of RunStates corresponding to the trace segment
def segment_states (seg : TraceSegment) : List RunState :=
  List.take (seg.j - seg.i + 1) (List.drop seg.i (segment_trace seg))

-- Get the number of RunStates in the segment
def segment_length (seg : TraceSegment) : Nat := seg.j - seg.i + 1

-- Split the segment into two pieces and take the first part
def segment_split_first (seg : TraceSegment) (k : Nat) (klt : k < segment_length seg) : TraceSegment where
  n := seg.n
  start := seg.start
  blocked := seg.blocked
  i := seg.i
  j := seg.i + k
  ile := Nat.le_add_right _ _
  jlt := lt_of_le_of_lt (Nat.add_le_of_le_sub' seg.ile (Nat.le_of_lt_add_one klt)) seg.jlt

-- Split the segment into two pieces and take the second part
def segment_split_second (seg : TraceSegment) (k : Nat) (klt : k < segment_length seg) : TraceSegment where
  n := seg.n
  start := seg.start
  blocked := seg.blocked
  i := seg.i + k
  j := seg.j
  ile := Nat.add_le_of_le_sub' seg.ile (Nat.le_of_lt_add_one klt)
  jlt := seg.jlt

lemma segment_length_pos (seg : TraceSegment) :
  0 < segment_length seg := by
  unfold segment_length
  exact Nat.add_one_pos _

-- The length of the segment states is the same as the segment length
lemma segment_states_length (seg : TraceSegment) :
  (segment_states seg).length = (segment_length seg) := by
  unfold segment_states segment_trace segment_length
  rw [List.length_take_of_le]
  rw [List.length_drop, trace_length]
  apply Nat.add_one_le_of_lt (Nat.sub_lt_sub_right seg.ile _)
  apply (trace_length _ _ _) ▸ seg.jlt

lemma segment_start_eq_getElem_zero (seg : TraceSegment) :
  segment_start seg = (segment_states seg)[0]'(by
    rw [segment_states_length, segment_length]
    exact Nat.add_one_pos _
  ) := by
  unfold segment_start segment_states
  rw [List.getElem_take, List.getElem_drop]
  rw [getElem_congr_idx (Nat.add_zero _)]

lemma segment_end_eq_getElem (seg : TraceSegment) :
  segment_end seg = (segment_states seg)[segment_length seg - 1]'(by
    rw [segment_states_length]
    apply Nat.sub_one_lt (Nat.ne_zero_of_lt (segment_length_pos seg))
  ) := by
  unfold segment_end segment_states
  rw [List.getElem_take, List.getElem_drop]; congr
  rw [segment_length, Nat.add_one_sub_one]
  apply (Nat.add_sub_cancel' _).symm
  exact seg.ile

lemma segment_split_first_start (seg : TraceSegment) (k : Nat) (klt : k < segment_length seg) :
  segment_start (segment_split_first seg k klt) = segment_start seg := rfl

lemma segment_split_second_end (seg : TraceSegment) (k : Nat) (klt : k < segment_length seg) :
  segment_end (segment_split_second seg k klt) = segment_end seg := rfl

lemma segment_split_overlap (seg : TraceSegment) (k : Nat) (klt : k < segment_length seg) :
  segment_end (segment_split_first seg k klt) =
  segment_start (segment_split_second seg k klt) := rfl

-- Get the length of the first half of a split trace
lemma segment_split_first_length (seg : TraceSegment) (k : Nat) (klt : k < segment_length seg) :
  segment_length (segment_split_first seg k klt) = k + 1 := by
  unfold segment_length segment_split_first; simp

-- Get the length of the second half of a split trace
lemma segment_split_second_length (seg : TraceSegment) (k : Nat) (klt : k < segment_length seg) :
  segment_length (segment_split_second seg k klt) = segment_length seg - k := by
  unfold segment_length segment_split_second; simp
  rw [Nat.sub_add_eq, Nat.sub_add_comm]
  exact Nat.le_of_lt_add_one klt

-- The length of a segment is one less than the sum of the
-- lengths of its two parts
lemma segment_split_length (seg : TraceSegment) (k : Nat) (klt : k < segment_length seg) :
  segment_length seg =
  (segment_length (segment_split_first seg k klt)) +
  (segment_length (segment_split_second seg k klt)) - 1 := by
  rw [segment_split_first_length, segment_split_second_length]; simp
  exact (Nat.add_sub_cancel' (le_of_lt klt)).symm

-- Get an element from the first half of a split trace segment
lemma segment_split_first_states_getElem
  (seg : TraceSegment) (k : Nat) (klt : k < segment_length seg) :
  ∀ a (alt : a < (segment_states (segment_split_first seg k klt)).length),
  (segment_states (segment_split_first seg k klt))[a] =
  (segment_states seg)[a]'(by
    rw [segment_states_length, segment_split_first_length] at alt
    rw [segment_states_length]
    exact lt_of_le_of_lt (Nat.le_of_lt_add_one alt) klt
  ) := by
  intro _ _
  unfold segment_states segment_split_first segment_trace; simp

-- Get an element from the second half of a split trace segment
lemma segment_split_second_states_getElem
  (seg : TraceSegment) (k : Nat) (klt : k < segment_length seg) :
  ∀ a (alt : a < (segment_states (segment_split_second seg k klt)).length),
  (segment_states (segment_split_second seg k klt))[a] =
  (segment_states seg)[a + k]'(by
    rw [segment_states_length, segment_split_second_length] at alt
    rw [segment_states_length]
    exact Nat.add_lt_of_lt_sub alt) := by
  intro a alt
  unfold segment_states segment_split_second segment_trace; simp; congr 1
  rw [add_comm a, add_assoc]

-- Prove an identity for the states of the first half of a split segment
lemma segment_split_first_states (seg : TraceSegment) (k : Nat) (klt : k < segment_length seg) :
  segment_states (segment_split_first seg k klt) =
  List.take (k + 1) (segment_states seg) := by
  apply List.ext_getElem
  · rw [segment_states_length, segment_split_first_length]
    rw [List.length_take_of_le]
    rw [segment_states_length]
    exact Nat.add_one_le_of_lt klt
  intro a alt alt'
  rw [segment_split_first_states_getElem, List.getElem_take]

-- Prove an identity for the states of the second half of a split segment
lemma segment_split_second_states (seg : TraceSegment) (k : Nat) (klt : k < segment_length seg) :
  segment_states (segment_split_second seg k klt) =
  List.drop k (segment_states seg) := by
  apply List.ext_getElem
  · rw [segment_states_length, segment_split_second_length, List.length_drop]
    rw [segment_states_length]
  intro a alt _
  rw [segment_split_second_states_getElem, List.getElem_drop]; congr 1
  exact add_comm _ _

-- The list of states for a split segment is equal to those
-- in the first part followed by the tail of those in the second
lemma segment_split_states (seg : TraceSegment) (k : Nat) (klt : k < segment_length seg) :
  segment_states seg =
  segment_states (segment_split_first seg k klt) ++
  (segment_states (segment_split_second seg k klt)).tail := by
  apply List.ext_getElem
  · rw [List.length_append, List.length_tail, ← Nat.add_sub_assoc]; swap
    · rw [segment_states_length, segment_split_second_length]
      exact Nat.le_sub_of_add_le' (Nat.add_one_le_of_lt klt)
    repeat rw [segment_states_length]
    exact segment_split_length seg k klt
  intro a alt _
  by_cases alt' : a < (segment_states (segment_split_first seg k klt)).length
  · rw [List.getElem_append_left alt']
    rw [segment_split_first_states_getElem]
  · rename' alt' => lea; push_neg at lea
    rw [List.getElem_append_right lea, List.getElem_tail]
    rw [segment_split_second_states_getElem]
    congr
    rw [segment_states_length, segment_split_first_length]
    rw [add_assoc, Nat.add_comm 1, Nat.sub_add_cancel]
    rwa [segment_states_length, segment_split_first_length] at lea

-- Check if the 'move' between state 'a' and state 'a+1' is 'f'
def check_for_move (seg : TraceSegment)
  (f : RunState → RunState) (a : Nat) (alt : a + 1 < segment_length seg) : Prop :=
  f ((segment_states seg)[a]'(by
    rw [segment_states_length]
    exact lt_trans (Nat.lt_add_one _) alt
  )) = (segment_states seg)[a + 1]'(by rwa [segment_states_length])

def segment_starts_with_move_forward (seg : TraceSegment) (h : 1 < segment_length seg) : Prop :=
  check_for_move seg move_forward 0 h

def segment_starts_with_turn_left (seg : TraceSegment) (h : 1 < segment_length seg) : Prop :=
  check_for_move seg turn_left 0 h

def segment_starts_with_turn_right (seg : TraceSegment) (h : 1 < segment_length seg) : Prop :=
  check_for_move seg turn_right 0 h

-- A split segment starts with a particular move if the original segment did
def segment_split_first_starts_with_move (seg : TraceSegment) (h : 1 < segment_length seg)
  (f : RunState → RunState) (hmove : check_for_move seg f 0 h) :
  ∀ k (kpos : 0 < k) (klt : k < segment_length seg),
  check_for_move (segment_split_first seg k klt) f 0
  (by
    rw [segment_split_first_length]
    exact Nat.add_one_lt_add_one_iff.mpr kpos
  ) := by
  intro k kpos klt
  ---have lek : seg.i ≤ k := le_of_lt ltk
  unfold check_for_move at *
  repeat rw [getElem_congr_coll (segment_split_first_states seg k klt)]
  rwa [List.getElem_take, List.getElem_take]

-- The segment begins with a left turn and continues straight
def segment_is_L (seg : TraceSegment) (h : 1 < segment_length seg) : Prop :=
  segment_starts_with_turn_left seg h ∧
  ∀ a (aslt : a + 1 < segment_length seg), a ≠ 0 →
  check_for_move seg move_forward a aslt

-- The segment begins and ends with a left turn, with only straight segments in-between
def segment_is_U (seg : TraceSegment) (h : 2 < segment_length seg) : Prop :=
  (fun segL sllb ↦ segment_is_L segL sllb ∧
  segment_end seg = turn_left (segment_end segL))
  (segment_split_first seg (segment_length seg - 2)
    (Nat.sub_lt (Nat.zero_lt_of_lt h) (Nat.two_pos)))
  (by
    rw [segment_split_first_length]
    exact Nat.add_one_lt_add_one_iff.mpr (Nat.lt_sub_of_add_lt ((Nat.zero_add 2) ▸ h)))

-- The segment begins with a left turn and ends with a right turn,
-- with only straight segments in-between
def segment_is_S (seg : TraceSegment) (h : 2 < segment_length seg) : Prop :=
  (fun segL sllb ↦ segment_is_L segL sllb ∧
  segment_end seg = turn_right (segment_end segL))
  (segment_split_first seg (segment_length seg - 2)
    (Nat.sub_lt (Nat.zero_lt_of_lt h) (Nat.two_pos)))
  (by
    rw [segment_split_first_length]
    exact Nat.add_one_lt_add_one_iff.mpr (Nat.lt_sub_of_add_lt ((Nat.zero_add 2) ▸ h)))

-- Write the end of an 'L' segment in terms of the start
lemma segment_end_of_L (seg : TraceSegment) (h : 1 < segment_length seg) :
  segment_is_L seg h → segment_end seg =
  (fun n rs ↦ RunState.mk
    (n * (rotate_left rs.u).x + rs.u.x + rs.x)
    (n * (rotate_left rs.u).y + rs.u.y + rs.y)
    (rotate_left rs.u)
  )
  (segment_length seg - 1) (segment_start seg) := by
  intro ⟨hL, hMF⟩
  have hssllb : 1 < (segment_states seg).length := by
    rwa [segment_states_length]
  unfold segment_starts_with_turn_left check_for_move at hL
  rw [getElem_congr_idx (Nat.zero_add _)] at hL
  by_cases hsl2 : segment_length seg = 2
  · rw [segment_end_eq_getElem]
    rw [getElem_congr_idx (congrArg (fun n ↦ n - 1) hsl2)]; simp
    rw [← hL]
    unfold turn_left rotate_left
    rw [segment_start_eq_getElem_zero]
    apply RunState.ext
    · nth_rw 1 [hsl2]; simp
      rw [add_right_comm, add_comm (-_), add_right_comm]
      rw [Int.add_neg_eq_sub]
    · simp
      nth_rw 1 [hsl2]; simp
      rw [add_comm (segment_states seg)[0].y, add_right_comm]
    · simp
  rename' hsl2 => hslne2; push_neg at hslne2
  have sllb : 2 < segment_length seg := by
    apply lt_of_le_of_ne _ hslne2.symm
    exact Nat.add_one_le_of_lt h
  have s2a1 {n : Nat} (onelt : 1 < n) : n - 2 + 1 = n - 1 := by
    rw [← one_add_one_eq_two, Nat.sub_add_eq]
    rw [Nat.sub_one_add_one (Nat.sub_ne_zero_of_lt onelt)]
  let k := segment_length seg - 2
  have klt : k < segment_length seg :=
    Nat.sub_lt (Nat.zero_lt_of_lt h) Nat.two_pos
  have kpos : 0 < k := Nat.sub_pos_of_lt sllb
  -- Split the segment into an L segment, and a single forward step
  let seg_first := segment_split_first seg k klt
  have hsflb : 1 < segment_length seg_first := by
    rw [segment_split_first_length]
    exact Nat.add_one_lt_add_one_iff.mpr kpos
  have kslt : k + 1 < segment_length seg := by
    unfold k
    rw [s2a1 h]
    exact Nat.sub_lt (Nat.zero_lt_of_lt h) Nat.one_pos
  have hsfL : segment_is_L seg_first hsflb := by
    constructor
    · exact segment_split_first_starts_with_move seg h turn_left hL k kpos klt
    · intro a aslt anz
      unfold check_for_move
      repeat rw [getElem_congr_coll (segment_split_first_states seg k klt)]
      rw [List.getElem_take, List.getElem_take]
      apply hMF a _ anz
      apply lt_trans aslt
      rwa [segment_split_first_length]
  -- Recursively write the end of 'first_seg' in terms of 'segment_start'
  have hend₀ := segment_end_of_L seg_first hsflb hsfL
  -- Write the end of the segment in terms of the end of 'first_seg'
  have hend₁ : segment_end seg = move_forward (segment_end seg_first) := by
    rw [segment_end_eq_getElem, segment_end_eq_getElem]
    rw [segment_split_first_states_getElem]
    have := hMF k kslt (Nat.ne_zero_of_lt kpos)
    convert this.symm using 2
    · exact Nat.eq_add_of_sub_eq (Nat.le_sub_one_of_lt h) rfl
    · congr 1
      rw [segment_split_first_length]; simp
  rw [hend₁, hend₀, segment_split_first_start, segment_split_first_length]
  unfold move_forward rotate_left k
  apply RunState.ext <;> simp
  · rw [add_right_comm _ (segment_start seg).x]
    apply (Int.add_left_inj _).mpr
    rw [add_right_comm]
    apply (Int.add_left_inj _).mpr
    rw [← Int.neg_add]
    nth_rw 2 [← one_mul (segment_start seg).u.y]
    rw [← Int.add_mul]; congr
    rw [← Int.natCast_one, ← Int.natCast_add]
    rw [s2a1 h, Int.natCast_sub]
    exact le_of_lt h
  · rw [add_right_comm _ (segment_start seg).y]
    apply (Int.add_left_inj _).mpr
    rw [add_right_comm]
    apply (Int.add_left_inj _).mpr
    nth_rw 2 [← one_mul (segment_start seg).u.x]
    rw [← Int.add_mul]; congr
    rw [← Int.natCast_one, ← Int.natCast_add]
    rw [s2a1 h, Int.natCast_sub]
    exact le_of_lt h
termination_by (segment_length seg)
decreasing_by
  -- For some reason Lean isn't giving us the right context here
  -- so we can't use 's2a1'. Just copy and paste the logic from there.
  rw [segment_split_first_length]
  rw [← one_add_one_eq_two, Nat.sub_add_eq]
  rw [Nat.sub_one_add_one (Nat.sub_ne_zero_of_lt h)]
  exact Nat.sub_lt (Nat.zero_lt_of_lt h) Nat.one_pos

-- Write the end of a 'U' segment in terms of the start
lemma segment_end_of_U (seg : TraceSegment) (h : 2 < segment_length seg) :
  segment_is_U seg h → segment_end seg =
  (fun rs n ↦ RunState.mk
    (rs.x + n * (rotate_left rs.u).x)
    (rs.y + n * (rotate_left rs.u).y)
    (rotate_left (rotate_left rs.u))
  ) (segment_start seg) (segment_length seg - 1) := by
  unfold segment_is_U
  intro ⟨hL, hlast⟩
  let k := segment_length seg - 2
  have klt : k < segment_length seg :=
    Nat.sub_lt (Nat.zero_lt_of_lt h) Nat.two_pos
  have kpos : 0 < k := Nat.sub_pos_of_lt h
  have ks : k + 1 = segment_length seg - 1 := by
    unfold k
    rw [← one_add_one_eq_two, Nat.sub_add_eq, Nat.sub_one_add_one]
    exact Nat.sub_ne_zero_of_lt (lt_trans (by norm_num) h)
  let seg_first := segment_split_first seg k klt
  have slssf : 1 < segment_length seg_first := by
    rw [segment_split_first_length]
    exact Nat.add_one_lt_add_one_iff.mpr kpos
  have lesl : 1 ≤ segment_length seg := le_of_lt (lt_trans (by norm_num) h)
  rw [hlast, segment_end_of_L _ slssf hL, segment_split_first_start]
  rw [segment_split_first_length]
  unfold turn_left rotate_left
  apply RunState.ext <;> simp
  · rw [add_right_comm, add_right_comm _ _ (-(segment_start seg).u.y)]
    rw [mul_comm, ← Int.neg_mul]
    nth_rw 2 [← Int.mul_one (-(segment_start seg).u.y)]
    rw [← mul_add, neg_mul, mul_comm, add_right_comm]
    rw [Int.add_sub_cancel, add_comm]; congr
    rwa [← Int.natCast_one, ← Int.natCast_add, ks, Int.natCast_sub]
  · repeat rw [add_right_comm _ _ (segment_start seg).u.x]
    nth_rw 2 [← Int.one_mul (segment_start seg).u.x]
    rw [← add_mul, add_right_comm, add_neg_cancel_right, add_comm]; congr
    rwa [← Int.natCast_one, ← Int.natCast_add, ks, Int.natCast_sub]

-- Write the end of an 'S' segment in terms of the start
lemma segment_end_of_S (seg : TraceSegment) (h : 2 < segment_length seg) :
  segment_is_S seg h → segment_end seg =
  (fun rs n ↦ RunState.mk
    (rs.x + n * (rotate_left rs.u).x + rs.u.x)
    (rs.y + n * (rotate_left rs.u).y + rs.u.y)
    rs.u
  ) (segment_start seg) (segment_length seg - 2) := by
  unfold segment_is_S
  intro ⟨hL, hlast⟩
  let k := segment_length seg - 2
  have klt : k < segment_length seg :=
    Nat.sub_lt (Nat.zero_lt_of_lt h) Nat.two_pos
  have kpos : 0 < k := Nat.sub_pos_of_lt h
  let seg_first := segment_split_first seg k klt
  have slssf : 1 < segment_length seg_first := by
    rw [segment_split_first_length]
    exact Nat.add_one_lt_add_one_iff.mpr kpos
  rw [hlast, segment_end_of_L _ slssf hL, segment_split_first_start]
  rw [segment_split_first_length]
  unfold turn_right rotate_left
  apply RunState.ext <;> simp
  · rw [add_assoc (segment_start seg).x, add_comm]
    apply (Int.add_right_inj _).mpr ((Int.add_left_inj _).mpr _)
    unfold k
    rw [Int.natCast_sub (le_of_lt h)]; simp
  · rw [add_assoc (segment_start seg).y, add_comm]
    apply (Int.add_right_inj _).mpr ((Int.add_left_inj _).mpr _)
    unfold k
    rw [Int.natCast_sub (le_of_lt h)]; simp

def segment_length_lb_prop (seg : TraceSegment) : Prop :=
  manhattan (loc (segment_start seg)) (loc (segment_end seg)) ≤ segment_length seg

-- Prove the segment length lower bound when the length is 1
lemma segment_length_lb_case1 (seg : TraceSegment) (h : segment_length seg = 1) :
  segment_length_lb_prop seg := by
  unfold segment_length_lb_prop
  unfold segment_length at h
  -- If length = 1, i = j
  have hij := le_antisymm seg.ile (Nat.le_of_sub_eq_zero (Nat.add_right_cancel h))
  convert Nat.zero_le _
  convert manhattan_self _ using 2
  unfold segment_start segment_end
  rw [getElem_congr_idx hij]

-- Prove the induction case for the length lower bound when
-- the segment begins with a 'move forward'
lemma segment_length_lb_case2 (seg : TraceSegment) (h : 1 < segment_length seg) :
  segment_starts_with_move_forward seg h →
  segment_length_lb_prop (segment_split_second seg 1 h) →
  segment_length_lb_prop seg := by
  unfold segment_length_lb_prop
  let seg_first := segment_split_first seg 1 h
  let seg_second := segment_split_second seg 1 h
  intro hmf hman₁
  have ltsl : 1 < (segment_states seg).length := by rwa [segment_states_length]
  have hman₀ : manhattan (loc (segment_start seg)) (loc ((segment_states seg)[1]'ltsl)) = 1 := by
    unfold segment_starts_with_move_forward check_for_move at hmf
    rw [getElem_congr_idx (Nat.zero_add 1)] at hmf
    rw [← hmf, ← segment_start_eq_getElem_zero, manhattan]
    unfold loc move_forward; simp
    exact uvec_xabs_add_yabs_eq_one _
  rw [← segment_split_overlap, segment_end_eq_getElem] at hman₁
  rw [segment_split_first_states_getElem, segment_split_second_end] at hman₁
  have idxrw := congrArg (fun n ↦ n - 1) (segment_split_first_length seg 1 h)
  dsimp at idxrw
  rw [getElem_congr_idx idxrw, segment_split_second_length] at hman₁
  convert le_trans (manhattan_tri _ _ _) (Nat.add_le_add (le_of_eq hman₀) hman₁)
  rw [add_comm, Nat.sub_one_add_one (Nat.ne_zero_of_lt h)]

-- Prove the induction case for the length lower bound when
-- the segment begins with a 'turn_right'
lemma segment_length_lb_case3 (seg : TraceSegment) (h : 1 < segment_length seg) :
  segment_starts_with_turn_right seg h →
  segment_length_lb_prop (segment_split_second seg 1 h) →
  segment_length_lb_prop seg := by
  unfold segment_length_lb_prop
  let seg_first := segment_split_first seg 1 h
  let seg_second := segment_split_second seg 1 h
  intro hmf hman₁
  have ltsl : 1 < (segment_states seg).length := by rwa [segment_states_length]
  have hman₀ : manhattan (loc (segment_start seg)) (loc ((segment_states seg)[1]'ltsl)) ≤ 1 := by
    unfold segment_starts_with_turn_right check_for_move at hmf
    apply le_of_lt (Nat.lt_add_one_of_le (le_of_eq _))
    rw [getElem_congr_idx (Nat.zero_add 1)] at hmf
    rw [← hmf, ← segment_start_eq_getElem_zero, manhattan]
    unfold loc turn_right; simp
  rw [← segment_split_overlap, segment_end_eq_getElem] at hman₁
  rw [segment_split_first_states_getElem, segment_split_second_end] at hman₁
  have idxrw := congrArg (fun n ↦ n - 1) (segment_split_first_length seg 1 h)
  dsimp at idxrw
  rw [getElem_congr_idx idxrw, segment_split_second_length] at hman₁
  convert le_trans (manhattan_tri _ _ _) (Nat.add_le_add hman₀ hman₁)
  rw [add_comm, Nat.sub_one_add_one (Nat.ne_zero_of_lt h)]

-- Prove the segment length lower bound for 'L segments
lemma segment_length_lb_case4 (seg : TraceSegment) (h : 1 < segment_length seg) :
  segment_is_L seg h → segment_length_lb_prop seg := by
  intro hL
  unfold segment_length_lb_prop
  rw [segment_end_of_L seg h hL]
  unfold manhattan loc rotate_left
  simp
  rcases Finset.mem_insert.mp (uvec_finset_mem (segment_start seg).u) with hup | hrest
  · rw [hup]; unfold uvec_up; simp
    rw [← Int.natAbs_neg]
    apply Int.le_of_ofNat_le_ofNat
    rw [Int.natCast_add, Int.natAbs_of_nonneg]; swap
    · simp; exact le_of_lt h
    rw [Int.neg_sub, Int.natCast_one, Int.sub_add_cancel]
  rcases Finset.mem_insert.mp hrest with hdown | hrest
  · rw [hdown]; unfold uvec_down; simp
    apply Int.le_of_ofNat_le_ofNat
    rw [Int.natCast_add, Int.natAbs_of_nonneg]; swap
    · simp; exact le_of_lt h
    rw [Int.natCast_one, Int.sub_add_cancel]
  rcases Finset.mem_insert.mp hrest with hleft | hright
  · rw [hleft]; unfold uvec_left; simp
    apply Int.le_of_ofNat_le_ofNat
    rw [Int.natCast_add, ← Int.natAbs_neg, Int.natAbs_of_nonneg]; swap
    · simp; exact le_of_lt h
    rw [Int.neg_sub, ← Int.add_sub_assoc, add_comm]
    rw [Int.natCast_one, Int.add_sub_cancel]
  · rw [Finset.mem_singleton.mp hright]; unfold uvec_right; simp
    apply Int.le_of_ofNat_le_ofNat
    rw [Int.natCast_add, Int.natAbs_of_nonneg]; swap
    · simp; exact le_of_lt h
    rw [← Int.add_sub_assoc, add_comm]
    rw [Int.natCast_one, Int.add_sub_cancel]

-- Prove the induction case for the length lower bound when
-- the segment begins with a 'U-segment'
lemma segment_length_lb_case5 (seg : TraceSegment)
  (k : Nat) (ltk : 1 < k) (klt : k < segment_length seg) :
  segment_is_U (segment_split_first seg k klt) (by
    rw [segment_split_first_length]
    exact Nat.add_one_lt_add_one_iff.mpr ltk) →
  segment_length_lb_prop (segment_split_second seg k klt) →
  segment_length_lb_prop seg := by
  intro hU sllb
  let seg_first := segment_split_first seg k klt
  let seg_second := segment_split_second seg k klt
  have ltsl1 : 2 < segment_length seg_first := by
    rw [segment_split_first_length]
    exact Nat.add_one_lt_add_one_iff.mpr ltk
  have lesl1 : 1 ≤ segment_length seg_first := by
    rw [segment_split_first_length]
    exact Nat.add_one_le_add_one_iff.mpr (Nat.zero_le _)
  unfold segment_length_lb_prop at *
  rw [← segment_split_overlap, segment_split_second_end] at sllb
  apply le_trans (manhattan_tri _ (loc (segment_end seg_first)) _)
  rw [segment_split_length seg k klt, Nat.sub_add_comm lesl1]
  apply Nat.add_le_add _ sllb
  rw [segment_split_first_length, Nat.add_one_sub_one]
  rw [segment_end_of_U seg_first ltsl1 hU, segment_split_first_start]
  rw [segment_split_first_length]
  unfold manhattan rotate_left loc; simp
  -- Finish the proof for each of the possible starting directions
  rcases Finset.mem_insert.mp (uvec_finset_mem (segment_start seg).u) with hup | hrest
  · rw [hup]; unfold uvec_up; simp
  rcases Finset.mem_insert.mp hrest with hdown | hrest
  · rw [hdown]; unfold uvec_down; simp
  rcases Finset.mem_insert.mp hrest with hleft | hright
  · rw [hleft]; unfold uvec_left; simp
  · rw [Finset.mem_singleton.mp hright]; unfold uvec_right; simp
