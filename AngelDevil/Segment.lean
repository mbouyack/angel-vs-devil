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
def segment_split_first (seg : TraceSegment) (k : Nat) (lek : seg.i ≤ k) (kle : k ≤ seg.j) : TraceSegment where
  n := seg.n
  start := seg.start
  blocked := seg.blocked
  i := seg.i
  j := k
  ile := lek
  jlt := lt_of_le_of_lt kle seg.jlt

-- Split the segment into two pieces and take the second part
def segment_split_second (seg : TraceSegment) (k : Nat) (_ : seg.i ≤ k) (kle : k ≤ seg.j) : TraceSegment where
  n := seg.n
  start := seg.start
  blocked := seg.blocked
  i := k
  j := seg.j
  ile := kle
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

lemma segment_split_first_start (seg : TraceSegment) (k : Nat) (lek : seg.i ≤ k) (kle : k ≤ seg.j) :
  segment_start (segment_split_first seg k lek kle) = segment_start seg := rfl

lemma segment_split_second_end (seg : TraceSegment) (k : Nat) (lek : seg.i ≤ k) (kle : k ≤ seg.j) :
  segment_end (segment_split_second seg k lek kle) = segment_end seg := rfl

lemma segment_split_overlap (seg : TraceSegment) (k : Nat) (lek : seg.i ≤ k) (kle : k ≤ seg.j) :
  segment_end (segment_split_first seg k lek kle) =
  segment_start (segment_split_second seg k lek kle) := rfl

-- Get the length of the first half of a split trace
lemma segment_split_first_length (seg : TraceSegment) (k : Nat) (lek : seg.i ≤ k) (kle : k ≤ seg.j) :
  segment_length (segment_split_first seg k lek kle) = k - seg.i + 1 := by
  unfold segment_length segment_split_first; simp

-- Get the length of the second half of a split trace
lemma segment_split_second_length (seg : TraceSegment) (k : Nat) (lek : seg.i ≤ k) (kle : k ≤ seg.j) :
  segment_length (segment_split_second seg k lek kle) = seg.j - k + 1 := by
  unfold segment_length segment_split_second; simp

-- The length of a segment is one less than the sum of the
-- lengths of its two parts
lemma segment_split_length (seg : TraceSegment) (k : Nat) (lek : seg.i ≤ k) (kle : k ≤ seg.j) :
  segment_length seg =
  (segment_length (segment_split_first seg k lek kle)) +
  (segment_length (segment_split_second seg k lek kle)) - 1 := by
  rw [segment_split_first_length, segment_split_second_length, segment_length]; simp
  rw [add_comm _ (seg.j - k), ← add_assoc, ← Nat.add_sub_assoc lek]
  rw [Nat.sub_add_cancel kle]

-- Get an element from the first half of a split trace segment
lemma segment_split_first_states_getElem
  (seg : TraceSegment) (k : Nat) (lek : seg.i ≤ k) (kle : k ≤ seg.j) :
  ∀ a (alt : a < (segment_states (segment_split_first seg k lek kle)).length),
  (segment_states (segment_split_first seg k lek kle))[a] =
  (segment_states seg)[a]'(by
    rw [segment_states_length, segment_split_first_length] at alt
    rw [segment_states_length, segment_length]
    exact lt_of_lt_of_le alt ((Nat.add_le_add_right (Nat.sub_le_sub_right kle _)) _)
  ) := by
  intro _ _
  unfold segment_states segment_split_first segment_trace; simp

-- Get an element from the second half of a split trace segment
lemma segment_split_second_states_getElem
  (seg : TraceSegment) (k : Nat) (lek : seg.i ≤ k) (kle : k ≤ seg.j) :
  ∀ a (alt : a < (segment_states (segment_split_second seg k lek kle)).length),
  (segment_states (segment_split_second seg k lek kle))[a] =
  (segment_states seg)[a + k - seg.i]'(by
    rw [segment_states_length, segment_split_second_length] at alt
    rw [segment_states_length, segment_length]
    apply Nat.sub_lt_right_of_lt_add (le_trans lek (Nat.le_add_left _ _))
    rw [add_right_comm, Nat.sub_add_cancel]; swap
    · exact le_trans lek kle
    apply Nat.add_lt_of_lt_sub
    rwa [Nat.sub_add_comm]
    exact kle
  ) := by
  intro a alt
  unfold segment_states segment_split_second segment_trace; simp; congr 1
  rw [add_comm, add_comm seg.i, Nat.sub_add_cancel]
  exact le_trans lek (Nat.le_add_left _ _)

-- Prove an identity for the states of the first half of a split segment
lemma segment_split_first_states (seg : TraceSegment) (k : Nat) (lek : seg.i ≤ k) (kle : k ≤ seg.j) :
  segment_states (segment_split_first seg k lek kle) =
  List.take (k - seg.i + 1) (segment_states seg) := by
  apply List.ext_getElem
  · rw [segment_states_length, segment_split_first_length]
    rw [List.length_take_of_le]
    rw [segment_states_length, segment_length]
    exact Nat.add_le_add_right (Nat.sub_le_sub_right kle _) _
  intro a alt alt'
  rw [segment_split_first_states_getElem, List.getElem_take]

-- Prove an identity for the states of the second half of a split segment
lemma segment_split_second_states (seg : TraceSegment) (k : Nat) (lek : seg.i ≤ k) (kle : k ≤ seg.j) :
  segment_states (segment_split_second seg k lek kle) =
  List.drop (k - seg.i) (segment_states seg) := by
  apply List.ext_getElem
  · rw [segment_states_length, segment_split_second_length, List.length_drop]
    rw [segment_states_length, segment_length]
    rw [Nat.sub_sub_right _ lek, add_right_comm _ 1]
    rw [Nat.sub_add_cancel (le_trans lek kle)]
    rw [Nat.sub_add_comm]
    exact kle
  intro a alt _
  rw [segment_split_second_states_getElem, List.getElem_drop]; congr
  rw [add_comm (k - seg.i), Nat.add_sub_assoc]
  exact lek

-- The list of states for a split segment is equal to those
-- in the first part followed by the tail of those in the second
lemma segment_split_states (seg : TraceSegment) (k : Nat) (lek : seg.i ≤ k) (kle : k ≤ seg.j) :
  segment_states seg =
  segment_states (segment_split_first seg k lek kle) ++
  (segment_states (segment_split_second seg k lek kle)).tail := by
  apply List.ext_getElem
  · rw [List.length_append, List.length_tail, ← Nat.add_sub_assoc]; swap
    · rw [segment_states_length]
      unfold segment_length segment_split_second; simp
    repeat rw [segment_states_length]
    exact segment_split_length seg k lek kle
  intro a alt _
  by_cases alt' : a < (segment_states (segment_split_first seg k lek kle)).length
  · rw [List.getElem_append_left alt']
    rw [segment_split_first_states_getElem]
  · rename' alt' => lea; push_neg at lea
    rw [List.getElem_append_right lea, List.getElem_tail]
    rw [segment_split_second_states_getElem]
    congr
    rw [segment_states_length, segment_split_first_length]
    rw [add_assoc, Nat.add_sub_assoc, add_comm 1]; swap
    · rw [add_comm]
      exact le_of_lt (lt_of_le_of_lt lek (Nat.lt_add_one _))
    rw [Nat.sub_add_comm lek, Nat.sub_add_cancel]
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
  segment_length_lb_prop (segment_split_second seg (seg.i + 1) (Nat.le_add_right _ _)
    (Nat.add_one_le_of_lt (Nat.lt_of_sub_pos (Nat.pos_of_lt_add_left h)))) →
  segment_length_lb_prop seg := by
  unfold segment_length_lb_prop
  intro hmf hllb
  let k := seg.i + 1
  have lek : seg.i ≤ k := Nat.le_add_right _ _
  have kle : k ≤ seg.j :=
    Nat.add_one_le_of_lt (Nat.lt_of_sub_pos (Nat.pos_of_lt_add_left h))
  rw [segment_split_length seg k lek kle]
  rw [segment_split_first_length]
  rw [Nat.sub_add_comm (Nat.le_refl seg.i), Nat.sub_self, zero_add]
  rw [add_right_comm, Nat.add_one_sub_one, add_comm]
  let seg_first := segment_split_first seg k lek kle
  let seg_second := segment_split_second seg k lek kle
  apply le_trans (manhattan_tri _ _ _)
  change manhattan _ (loc (segment_start seg_second)) + _ ≤ _
  rw [← segment_split_first_start seg k lek kle]
  rw [← segment_split_second_end seg k lek kle]
  nth_rw 1 [← segment_split_overlap]
  rw [add_comm]
  convert Nat.add_le_add_right hllb 1
  unfold segment_starts_with_move_forward check_for_move at hmf
  rw [← segment_start_eq_getElem_zero, getElem_congr_idx (Nat.zero_add _)] at hmf
  rw [← segment_split_first_start seg k lek kle] at hmf
  have : segment_end seg_first = (segment_states seg)[1]'(by rwa [segment_states_length]) := by
    rw [segment_end_eq_getElem, getElem_congr_coll (segment_split_first_states _ _ _ _)]
    rw [List.getElem_take]; congr
    rw [segment_split_first_length, Nat.add_one_sub_one]
    unfold k
    rw [add_comm, Nat.add_sub_cancel]
  rw [← this] at hmf
  rw [← hmf]
  let s := segment_start seg_first
  change manhattan (loc s) (loc (move_forward s)) = 1
  unfold manhattan move_forward loc; simp
  exact uvec_xabs_add_yabs_eq_one _
