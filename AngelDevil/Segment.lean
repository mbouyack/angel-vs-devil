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

-- The length of the segment states is the same as the segment length
lemma segment_states_length (seg : TraceSegment) :
  (segment_states seg).length = (segment_length seg) := by
  unfold segment_states segment_trace segment_length
  rw [List.length_take_of_le]
  rw [List.length_drop, trace_length]
  apply Nat.add_one_le_of_lt (Nat.sub_lt_sub_right seg.ile _)
  apply (trace_length _ _ _) ▸ seg.jlt

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
