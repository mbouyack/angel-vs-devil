import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import AngelDevil.Defs
import AngelDevil.Basic
import AngelDevil.Append
import AngelDevil.Nice
import AngelDevil.Sprint
import AngelDevil.Bound

set_option linter.style.longLine false

/- This file defines the behavior of the "runner", who attempts to follow the
   y-axis northward and will use a strategy of following the "left wall" any
   time they are blocked by a cell the Devil has eaten.
-/

-- The runner begins at the origin, running northward (up the positive y-axis)
def run_start : RunState where
  x := 0
  y := 0
  u := uvec_up

/- The three different structures needed to define the runner's journey
   have interdependencies that make them difficult to construct separately.
   This structure will allow us to build all three together. -/
structure RunBuilder (p : Nat) where
  D : Devil
  A : Journey p
  eaten : List (Int × Int)
  sprints : List (List RunState)
  -- These bundled properties are somewhat eclectic
  -- They are only included to facilitate the definition of 'extend_run' (below)
  nonnil : ∀ s ∈ sprints, s ≠ []
  samelen : steps A = sprints.length
  origin : (snn : sprints ≠ []) →
    (sprints[0]'(List.length_pos_of_ne_nil snn))[0]'(
      List.length_pos_of_ne_nil (nonnil _ (List.getElem_mem (List.length_pos_of_ne_nil snn)))
    ) = run_start
  dest : (snn : sprints ≠ []) →
    loc ((sprints.getLast snn).getLast (nonnil _ (List.getLast_mem snn))) = last A

-- Get the final runner state from a run builder
-- If we haven't had any sprints yet, use the default location and direction
def final_state {p : Nat} (S : RunBuilder p) : RunState :=
  if hlz : S.sprints.length = 0 then run_start else
    (S.sprints.getLast (List.ne_nil_of_length_pos (Nat.pos_of_ne_zero hlz))).getLast
    (S.nonnil _ (List.getLast_mem (List.ne_nil_of_length_pos (Nat.pos_of_ne_zero hlz))))

-- If the list of sprints is empty, the final state of the run is the 'run_start'
lemma final_state_of_sprints_nil {p : Nat} (S : RunBuilder p) (hnil : S.sprints = []) :
  final_state S = run_start := by
  unfold final_state
  rw [dif_pos (List.length_eq_zero_iff.mpr hnil)]

-- If 'sprints' is nonnil, the final state is an element in the final sprint
lemma final_state_getLast_mem_of_nonnil {p : Nat} (S : RunBuilder p) (hnil : S.sprints ≠ []) :
  final_state S ∈ S.sprints.getLast hnil := by
  unfold final_state
  rw [dif_neg (Nat.ne_zero_of_lt (List.length_pos_of_ne_nil hnil))]
  apply List.getLast_mem

-- The location given by 'final_state' matches the last cell in the builder journey
lemma final_state_loc_eq_journey_last {p : Nat} (S : RunBuilder p) :
  loc (final_state S) = last S.A := by
  unfold final_state
  split_ifs with hlz
  · exact (journey_last_of_steps_zero S.A (Eq.trans S.samelen hlz)).symm
  · push_neg at hlz
    exact S.dest (List.ne_nil_of_length_pos (Nat.pos_of_ne_zero hlz))

-- List of cells necessary to prevent the runner from ever moving west of the y-axis
-- TODO: Reevaluate whether the size of the wall should be smaller by 'p'
-- I increased it to make sure one of the proofs would work but it may not be necessary.
def west_wall (p n : Nat) :=
  List.map (fun i : Nat ↦ (-1, (i : Int) - Int.ofNat (n * p))) (List.range (2 * n * p + 1))

-- Any cell which is an elment of the west wall has x-coordinate -1
lemma west_wall_xcoord_of_mem (p n : Nat) :
  ∀ l ∈ west_wall p n, l.1 = -1 := by
  unfold west_wall
  intro l lmem
  rcases List.getElem_of_mem lmem with ⟨i, ilt, hi⟩
  rw [List.getElem_map] at hi
  rw [← hi]

-- Prove the conditions for a cell to be an element of the west wall
lemma west_wall_mem (p n : Nat) :
  ∀ y (_ : -(Int.ofNat (n * p)) ≤ y) (_ : y ≤ Int.ofNat (n * p)), (-1, y) ∈ west_wall p n := by
  intro y ley yle
  unfold west_wall
  apply List.mem_iff_getElem.mpr
  use Int.toNat (y + Int.ofNat (n * p))
  have hnonneg : 0 ≤ y + Int.ofNat (n * p) := by
    apply Int.le_add_of_sub_right_le
    rwa [zero_sub]
  use (by
    rw [List.length_map, List.length_range]
    apply (Int.toNat_lt hnonneg).mpr
    rw [Int.natCast_add, Int.natCast_one, mul_assoc, two_mul, Int.natCast_add]
    exact Int.lt_add_one_of_le (Int.add_le_add_right yle _)
  )
  rw [List.getElem_map, List.getElem_range, Int.ofNat_toNat]
  rw [max_eq_left hnonneg, Int.add_sub_cancel]

-- Get the next sprint to be added to the builder
-- Note that for the purposes of finding the next sprint, a wall of cells
-- is added along the y-axis that prevent the runner from ever moving that direction.
def next_sprint {p : Nat} (S : RunBuilder p) : List RunState :=
  sprint p (final_state S) (List.union S.eaten (west_wall p S.eaten.length))

lemma next_sprint_nonnil {p : Nat} (S : RunBuilder p) :
  next_sprint S ≠ [] := by
  exact sprint_nonnil _ _ _

-- The initial state of the next sprint is the
-- same as the final state of the builder
lemma next_sprint_first_eq_builder_last {p : Nat} (S : RunBuilder p) :
  final_state S = (next_sprint S)[0]'(by
    apply List.length_pos_of_ne_nil
    exact next_sprint_nonnil _
  ) := by
  exact (sprint_getElem_zero _ _ _).symm

-- The last cell of the next sprint is "close" to the
-- last cell of the builder journey.
lemma next_sprint_last_close_builder_last {p : Nat} (S : RunBuilder p) :
  close p (loc ((next_sprint S).getLast (next_sprint_nonnil _))) (last S.A) := by
  rw [← final_state_loc_eq_journey_last, next_sprint_first_eq_builder_last S]
  rw [close_comm, List.getElem_zero]
  exact sprint_close_first_last _ _ _

-- Define the base case for our builder construction:
-- The journey has no steps, there are no sprints, and the
-- Devil has only eaten one cell
def empty_builder (D : Devil) (p : Nat) : RunBuilder p where
  D := D
  A := NoSteps p
  eaten := [response D (NoSteps p)]
  sprints := []
  nonnil := fun _ hs ↦ False.elim (List.not_mem_nil hs)
  samelen := by rw [nosteps_steps, List.length_nil]
  origin := fun snn ↦ False.elim (snn rfl)
  dest := fun snn ↦ False.elim (snn rfl)

lemma empty_builder_sprints (D : Devil) (p : Nat) :
  (empty_builder D p).sprints = [] := by
  unfold empty_builder; dsimp

lemma empty_builder_journey (D : Devil) (p : Nat) :
  (empty_builder D p).A = NoSteps p := by
  unfold empty_builder; dsimp

lemma empty_builder_eaten (D : Devil) (p : Nat) :
  (empty_builder D p).eaten = [response D (NoSteps p)] := by
  unfold empty_builder; dsimp

-- Construct the journey that corresponds to appending the
-- last location of the next sprint
def builder_journey_extend {p : Nat} (S : RunBuilder p) : Journey p :=
  append_journey S.A (loc ((next_sprint S).getLast (sprint_nonnil p _ _)))
  ((close_comm p _ _).mp (next_sprint_last_close_builder_last S))

-- Why doesn't this theorem aleady exist?
-- TODO: If this is needed elsewhere, move it into 'Basic.lean' or 'Util.lean'
-- Note, "List.cons_ne_nil x []" is equivalent
lemma list_singleton_ne_nil {α : Type} (x : α) : [x] ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [List.length_singleton]
  norm_num

/- Add another sprint to a 'RunBuilder'
   Originally this was named 'make_run' and used recursion to
   directly construct the RunBuilder (rather than taking 'S' as an argument).
   Unfortunately this caused timeouts, so now 'make_run' handles the recursion
   separately and wraps 'extend_run' -/
def extend_run (D : Devil) (p : Nat) (S : RunBuilder p) : RunBuilder p:=
  RunBuilder.mk D
    (builder_journey_extend S)
    (S.eaten ++ [response D (builder_journey_extend S)])
    (S.sprints ++ [next_sprint S])
    (by
      intro s smem
      rcases List.mem_append.mp smem with lhs | rhs
      · exact RunBuilder.nonnil _ s lhs
      · exact (List.mem_singleton.mp rhs) ▸ (sprint_nonnil _ _ _)
    )
    (by
      unfold builder_journey_extend
      rw [append_steps, List.length_append, List.length_singleton]
      exact Nat.add_one_inj.mpr (RunBuilder.samelen _)
    )
    (by
      intro h
      let sprints := S.sprints
      let s := next_sprint S
      by_cases hsn : sprints = []
      · have h₀ : 0 < (sprints ++ [s]).length := by
          rw [List.length_append, List.length_singleton]
          exact Nat.add_one_pos _
        have h₁ : sprints ++ [s] = [s] := by
          rw [hsn, List.nil_append]
        have h₂ : (sprints ++ [s])[0]'(h₀) = s :=
          getElem_congr_coll h₁
        rw [getElem_congr_coll h₂]
        rw [← next_sprint_first_eq_builder_last _]
        exact final_state_of_sprints_nil _ hsn
      · rename' hsn => hsnn; push_neg at hsnn
        rw [getElem_congr_coll (List.getElem_append_left (List.length_pos_of_ne_nil hsnn))]
        exact RunBuilder.origin _ hsnn
    )
    (by
      intro h
      unfold builder_journey_extend
      rw [append_last]; congr
      rw [List.getLast_append_right (list_singleton_ne_nil _)]
      rw [List.getLast_singleton (list_singleton_ne_nil _)]
    )

-- Recursively construct the RunBuilder
def make_run (D : Devil) (p n : Nat) : RunBuilder p :=
  if n = 0 then empty_builder D p else
  extend_run D p (make_run D p (n - 1))

-- A run of length zero is represented by the 'empty_builder'
lemma make_run_eq_empty_of_length_zero (D : Devil) (p : Nat) :
  make_run D p 0 = empty_builder D p := by
  unfold make_run
  rw [if_pos rfl]

-- The recursive definition of the runner's journey:
-- Append the last cell of the 'next_sprint' to the journey to extend it.
lemma make_run_journey_recurrence (D : Devil) (p n : Nat) (npos : 0 < n) :
  (make_run D p n).A =
  append_journey
    (make_run D p (n - 1)).A
    (loc ((next_sprint (make_run D p (n - 1))).getLast (sprint_nonnil p _ _)))
    ((close_comm p _ _).mp (next_sprint_last_close_builder_last (make_run D p (n - 1)))) := by
  nth_rw 1 [make_run]
  rw [if_neg (Nat.ne_zero_iff_zero_lt.mpr npos)]
  rfl

-- The recursive definition of the runner's sprints
-- Just append the 'next_sprint' to the existing list of sprints.
lemma make_run_sprints_recurrence (D : Devil) (p n : Nat) (npos : 0 < n) :
  (make_run D p n).sprints =
  (make_run D p (n - 1)).sprints ++ [(next_sprint (make_run D p (n - 1)))] := by
  nth_rw 1 [make_run]
  rw [if_neg (Nat.ne_zero_iff_zero_lt.mpr npos)]
  rfl

-- The recursive definition of the cells eaten in response to the runner
-- This is just the devil's response to the new journey append to the old list
lemma make_run_eaten_recurrence (D : Devil) (p n : Nat) (npos : 0 < n) :
  (make_run D p n).eaten =
  (make_run D p (n - 1)).eaten ++ [response D (make_run D p n).A] := by
  nth_rw 1 [make_run]
  rw [if_neg (Nat.ne_zero_iff_zero_lt.mpr npos)]
  rw [make_run_journey_recurrence D p n npos];
  rfl

-- The number of steps in the journey is just 'n'
lemma make_run_journey_steps (D : Devil) (p n : Nat) :
  steps (make_run D p n).A = n := by
  by_cases hnz : n = 0
  · subst hnz
    rw [make_run_eq_empty_of_length_zero, empty_builder_journey, nosteps_steps]
  rename' hnz => hnnz; push_neg at hnnz
  have hpos : 0 < n := Nat.zero_lt_of_ne_zero hnnz
  rwa [make_run_journey_recurrence, append_steps, make_run_journey_steps, Nat.sub_one_add_one hnnz]

-- The number of eaten cells is just n+1
lemma make_run_eaten_length (D : Devil) (p n : Nat) :
  (make_run D p n).eaten.length = n + 1 := by
  by_cases hnz : n = 0
  · subst hnz
    rw [make_run_eq_empty_of_length_zero, empty_builder_eaten, List.length_singleton]
  rename' hnz => hnnz; push_neg at hnnz
  have npos : 0 < n := Nat.ne_zero_iff_zero_lt.mp hnnz
  rw [make_run_eaten_recurrence D p n npos, List.length_append]
  rw [List.length_singleton]
  apply Nat.add_one_inj.mpr
  nth_rw 2 [← Nat.sub_one_add_one hnnz]
  exact make_run_eaten_length D p (n - 1)

-- The number of sprints in the RunBuilder is 'n'
lemma make_run_sprints_length (D : Devil) (p n : Nat) :
  (make_run D p n).sprints.length = n := by
  rw [← (make_run D p n).samelen]
  exact make_run_journey_steps _ _ _

-- The subjourney of a 'make_run' journey is just the
-- 'make_run' journey of that length
lemma make_run_subjourney (D : Devil) (p m n : Nat) (mlt : m < n + 1) :
  subjourney (make_run D p n).A m (by rwa [make_run_journey_steps]) =
  (make_run D p m).A := by
  -- First handle the case where m = n
  by_cases hmn : m = n
  · subst hmn
    convert subjourney_full _
    rw [make_run_journey_steps]
  push_neg at hmn
  -- If m ≠ n, n ≠ 0
  have nnz : n ≠ 0 :=
    fun nz ↦ False.elim (Nat.not_lt_zero _ (nz ▸ (lt_of_le_of_ne (Nat.le_of_lt_add_one mlt) hmn)))
  -- Prove a tighter bound on m
  have mlt' : m < n :=
    lt_of_le_of_ne (Nat.le_of_lt_add_one mlt) hmn
  have hrecurse := make_run_journey_recurrence D p n (Nat.pos_of_ne_zero nnz)
  rw [subjourney_congr_journey hrecurse, append_subjourney]
  · -- Do the recursion
    exact make_run_subjourney D p m (n - 1) (by rwa [Nat.sub_one_add_one nnz])

-- The first 'm+1' cells eaten in response to the runner moving 'n' steps
-- will correspond to all the cells eaten in response to the runner moving
-- 'm' steps.
lemma make_run_eaten_take (D : Devil) (p m n : Nat) (mlt : m < n + 1) :
  (make_run D p n).eaten.take (m+1) = (make_run D p m).eaten := by
  -- First handle the case where m = n
  by_cases hmn : m = n
  · subst hmn
    convert List.take_length
    exact (make_run_eaten_length D p m).symm
  push_neg at hmn
  -- If m ≠ n, n ≠ 0
  have nnz : n ≠ 0 :=
    fun nz ↦ False.elim (Nat.not_lt_zero _ (nz ▸ (lt_of_le_of_ne (Nat.le_of_lt_add_one mlt) hmn)))
  -- Prove a tighter bound on m
  have mlt' : m < n :=
    lt_of_le_of_ne (Nat.le_of_lt_add_one mlt) hmn
  have hrecurse := make_run_eaten_recurrence D p n (Nat.pos_of_ne_zero nnz)
  rw [hrecurse, List.take_append_of_le_length]
  · -- Do the recursion
    exact make_run_eaten_take D p m (n - 1) (by rwa [Nat.sub_one_add_one nnz])
  -- Prove the remaining bounds check
  rw [make_run_eaten_length, Nat.sub_one_add_one nnz]
  exact Nat.add_one_le_of_lt mlt'

-- The first 'm' sprints of a run of 'n' sprints are the same as
-- the full list of sprints in a run of 'm' sprints
lemma make_run_sprints_take (D : Devil) (p m n : Nat) (mlt : m < n + 1) :
  (make_run D p n).sprints.take m = (make_run D p m).sprints := by
  -- First handle the case where m = n
  by_cases hmn : m = n
  · subst hmn
    convert List.take_length
    exact (make_run_sprints_length D p m).symm
  push_neg at hmn
  -- If m ≠ n, n ≠ 0
  have nnz : n ≠ 0 :=
    fun nz ↦ False.elim (Nat.not_lt_zero _ (nz ▸ (lt_of_le_of_ne (Nat.le_of_lt_add_one mlt) hmn)))
  -- Prove a tighter bound on m
  have mlt' : m < n :=
    lt_of_le_of_ne (Nat.le_of_lt_add_one mlt) hmn
  have hrecurse := make_run_sprints_recurrence D p n (Nat.pos_of_ne_zero nnz)
  rw [hrecurse, List.take_append_of_le_length]
  · -- Do the recursion
    exact make_run_sprints_take D p m (n - 1) (by rwa [Nat.sub_one_add_one nnz])
  -- Prove the remaining bounds check
  rw [make_run_sprints_length]
  apply Nat.le_of_lt_add_one
  rwa [Nat.sub_one_add_one nnz]

-- Extract the runner's journey from the RunBuilder
-- TODO: Is there any reason for this actually?
def Runner (D : Devil) (p n : Nat) : Journey p :=
  (make_run D p n).A

-- Each cell in the runner's journey (other than the first)
-- corresponds to the final location of the previous sprint.
lemma make_run_journey_cell (D : Devil) (p n : Nat) :
  ∀ i (ilt : i < n),
  cell (make_run D p n).A (i + 1)
    (by rw [make_run_journey_steps]; exact Nat.add_one_lt_add_one_iff.mpr ilt) =
  (loc (((make_run D p n).sprints[i]'
    (by rwa [make_run_sprints_length])).getLast
      (by
        apply (make_run D p n).nonnil
        apply List.getElem_mem
      ))) := by
  intro i ilt
  -- Prove sprints is nonnil so we can use RunBuilder.dest below
  have hsnn : (make_run D p (i + 1)).sprints ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [make_run_sprints_length]
    exact Nat.add_one_pos _
  have islt : i + 1 < n + 1 :=
    Nat.add_one_lt_add_one_iff.mpr ilt
  rw [← subjourney_last_cell, make_run_subjourney]; swap
  · assumption -- bounds check
  rw [((make_run D p (i + 1)).dest hsnn).symm]
  congr
  -- Rewrite the sprints of the sub-run as 'take' of the sprints of the full run.
  rw [List.getLast_congr _ _ (make_run_sprints_take D p (i + 1) n islt).symm]; swap
  · -- Resolve pending bounds check
    apply List.ne_nil_of_length_pos
    have ispos : 0 < i + 1 := Nat.add_one_pos _
    rwa [List.length_take_of_le]
    rw [make_run_sprints_length]
    exact Nat.add_one_le_of_lt ilt
  -- Apply list identities to resolve goal
  rw [List.getLast_eq_getElem, List.getElem_take]; congr
  rw [List.length_take_of_le]
  · exact Nat.add_one_sub_one _
  · rw [make_run_sprints_length]
    exact Nat.add_one_le_of_lt ilt

-- Each cell in the 'eaten' list is the devil's response to some shorter journey
lemma make_run_eaten (D : Devil) (p n : Nat) :
  ∀ i (ilt : i < n + 1),
  (make_run D p n).eaten[i]'(by rwa [make_run_eaten_length]) =
  (response D (make_run D p i).A) := by
  intro i ilt
  -- If i ≠ n, we can recurse
  by_cases ilt' : i < n
  · have npos : 0 < n := Nat.zero_lt_of_lt ilt'
    have nnz : n ≠ 0 := Nat.ne_zero_of_lt npos
    rw [getElem_congr_coll (make_run_eaten_recurrence D p n npos)]
    rw [← List.getElem_append_left']; swap
    · -- Resolve bounds check
      rwa [make_run_eaten_length, Nat.sub_one_add_one nnz]
    apply make_run_eaten
    exact lt_of_lt_of_eq ilt' (Nat.sub_one_add_one nnz).symm
  rename' ilt' => nle; push_neg at nle
  have hin : i = n := le_antisymm (Nat.le_of_lt_add_one ilt) nle
  subst hin
  -- Handle the case where i = 0
  by_cases iz : i = 0
  · subst iz
    have rwl : (make_run D p 0).eaten = [response D (NoSteps p)] := by
      rw [make_run_eq_empty_of_length_zero, empty_builder_eaten]
    have rwr : (make_run D p 0).A = (NoSteps p) := by
      rw [make_run_eq_empty_of_length_zero, empty_builder_journey]
    rw [getElem_congr_coll rwl, rwr, List.getElem_singleton]
  rename' iz => inz; push_neg at inz
  have ipos : 0 < i := Nat.zero_lt_of_ne_zero inz
  rw [getElem_congr_coll (make_run_eaten_recurrence D p i ipos)]
  rw [List.getElem_append_right]; swap
  · -- Resolve bounds check
    rw [make_run_eaten_length, Nat.sub_one_add_one inz]
  rw [List.getElem_singleton]

-- Each sprint is created by calling 'next_sprint' on some shorter 'make_run'
lemma make_run_sprint (D : Devil) (p n : Nat) :
  ∀ i (ilt : i < n),
  (make_run D p n).sprints[i]'(by rwa [make_run_sprints_length]) =
  (next_sprint (make_run D p i)) := by
  intro i ilt
  rw [getElem_congr_coll (make_run_sprints_recurrence D p n (Nat.zero_lt_of_lt ilt))]
  by_cases ilt' : i < n - 1
  · rw [← List.getElem_append_left']; swap
    · rwa [make_run_sprints_length]
    · convert make_run_sprint D p (n-1) i ilt'
  rename' ilt' => nple; push_neg at nple
  have inp := le_antisymm (Nat.le_sub_one_of_lt ilt) nple
  rw [List.getElem_append_right, List.getElem_singleton, inp]
  rwa [make_run_sprints_length]

-- Every "sprint" in a 'make_run' is in-fact a sprint.
-- That is, every theorem on sprints can be applied to the sprints
-- of a 'make_run.
lemma make_run_sprint_is_sprint (D : Devil) (p n : Nat) :
  ∀ s ∈ (make_run D p n).sprints,
  ∃ start blocked, s = sprint p start blocked := by
  intro s smem
  rcases List.getElem_of_mem smem with ⟨i, ilt, rfl⟩
  rw [make_run_sprints_length] at ilt
  exact ⟨_, _, make_run_sprint D p n i ilt⟩

-- Every element of a sprint is close to the head of that sprint
lemma make_run_close_sprint_mem_head (D : Devil) (p n : Nat) :
  ∀ s, (smem : s ∈ (make_run D p n).sprints) → ∀ x ∈ s,
  close p (loc x) (loc (s.head (RunBuilder.nonnil _ _ smem))) := by
  intro s smem
  rcases make_run_sprint_is_sprint D p n s smem with ⟨start, blocked, h⟩
  subst h
  exact sprint_close_mem_head p start blocked

-- The last element of each sprint equals the first element of the next
-- TODO: This seems longer than it should need to be.
-- Perhaps we're missing some useful 'sprints' theorems?
lemma make_run_sprint_last_eq_sprint_head (D : Devil) (p n : Nat) :
  ∀ i (islt : i + 1 < n),
  ((make_run D p n).sprints[i]'(by
    rw [make_run_sprints_length]; exact lt_trans (Nat.lt_add_one _) islt)).getLast
    (by apply RunBuilder.nonnil _ _ (List.getElem_mem _)) =
  ((make_run D p n).sprints[i+1]'(by rwa [make_run_sprints_length])).head
    (by apply RunBuilder.nonnil _ _ (List.getElem_mem _)) := by
  intro i islt
  have nnz : n ≠ 0 := by
    intro nz; subst nz
    exact (Nat.not_lt_zero _) islt
  -- If i + 1 ≠ n - 1, we can close the goal with recursion
  by_cases islt' : i + 1 < n - 1
  · convert make_run_sprint_last_eq_sprint_head D p (n - 1) i islt' using 2
    repeat
    rw [getElem_congr_coll (make_run_sprints_recurrence D p n (Nat.pos_of_ne_zero nnz))]
    rw [← List.getElem_append_left']
  rename' islt' => nple; push_neg at nple
  have iseq := le_antisymm (Nat.le_sub_one_of_lt islt) nple
  rw [List.head_eq_getElem]
  rw [getElem_congr_coll (make_run_sprint D p n (i+1) islt)]
  rw [← next_sprint_first_eq_builder_last]
  unfold final_state
  have lnz : (make_run D p (i + 1)).sprints.length ≠ 0 := by
    rw [make_run_sprints_length]
    exact Nat.add_one_ne_zero _
  rw [dif_neg lnz]; congr
  have mrst := make_run_sprints_take D p (i + 1) n (lt_trans islt (Nat.lt_add_one _))
  rw [← List.getLast_congr _ _ mrst]; swap
  · -- Resolve nil check
    intro hnil
    rcases List.take_eq_nil_iff.mp hnil with lhs | rhs
    · exact (Nat.add_one_ne_zero _) lhs
    · apply nnz
      rw [← make_run_sprints_length D p n]
      exact List.length_eq_zero_iff.mpr rhs
  rw [List.getLast_eq_getElem, List.getElem_take]; congr
  rw [List.length_take_of_le, Nat.add_one_sub_one]
  rw [make_run_sprints_length]
  exact le_of_lt islt

-- Every element of a sprint is "close" to the corresponding journey cell
lemma make_run_sprint_mem_journey_cell_close (D : Devil) (p n : Nat) :
  ∀ i (ilt : i < n), ∀ rs ∈ (make_run D p n).sprints[i]'(by rwa [make_run_sprints_length]),
  close p (loc rs) (cell (make_run D p n).A i
    (by rw [make_run_journey_steps]; exact lt_trans ilt (Nat.lt_add_one _))) := by
  intro i ilt rs hmem
  -- First handle the case where i = 0
  by_cases iz : i = 0
  · subst iz
    rw [journey_start]
    convert make_run_close_sprint_mem_head D p n _ (List.getElem_mem _) rs hmem using 1
    have hnnil : (make_run D p n).sprints ≠ [] := by
      apply List.ne_nil_of_length_pos
      rwa [make_run_sprints_length]
    rw [List.head_eq_getElem_zero, RunBuilder.origin _ hnnil]; rfl
  rename' iz => inz; push_neg at inz
  -- If i ≠ 0, swap in '(i-1)+1' for 'i' and rewrite with 'make_run_journey_cell'
  have iplt : i - 1 < n := by
    apply lt_of_le_of_lt _ ilt
    exact Nat.sub_le _ _
  have := make_run_journey_cell D p n (i-1) iplt
  rw [cell_congr_idx _ (Nat.sub_one_add_one inz)] at this
  rw [this, make_run_sprint_last_eq_sprint_head]; swap
  · -- Resolve bounds check
    rwa [Nat.sub_one_add_one inz]
  apply make_run_close_sprint_mem_head D p n
  · apply List.getElem_mem
  · convert hmem
    exact Nat.sub_one_add_one inz

-- Every element of the 'next_sprint' is close to the previous journey cell
lemma make_run_next_sprint_mem_journey_cell_close (D : Devil) (p n : Nat) :
  ∀ rs ∈ next_sprint (make_run D p n),
  close p (loc rs) (cell (make_run D p n).A n (by
    rw [make_run_journey_steps]; exact Nat.lt_add_one _)
  ) := by
  intro rs rsmem
  have rsmem' : rs ∈ (make_run D p (n + 1)).sprints[n]'(by
    rw [make_run_sprints_length]; exact Nat.lt_add_one _
  ) := by
    rw [getElem_congr_coll (make_run_sprints_recurrence D p (n + 1) (Nat.add_one_pos _))]
    rw [List.getElem_append_right]; swap
    · rw [make_run_sprints_length, Nat.add_one_sub_one]
    rw [List.getElem_singleton]
    rwa [Nat.add_one_sub_one]
  convert make_run_sprint_mem_journey_cell_close D p (n + 1) n (Nat.lt_add_one _) rs rsmem' using 1
  have mrsj := make_run_subjourney D p n (n + 1) (lt_trans (Nat.lt_add_one _) (Nat.lt_add_one _))
  rw [← cell_congr_journey mrsj, subjourney_cell]
  exact le_refl _

-- List of blocked cells used to generate 'next_sprint (make_run D p n)'
def make_block_list (D : Devil) (p n : Nat) : List (Int × Int) :=
  List.union (make_run D p n).eaten (west_wall p (make_run D p n).eaten.length)

-- Each block list contains a subset of cells from any later block list
lemma make_block_list_subset (D : Devil) (p m n : Nat) (mle : m ≤ n) :
  make_block_list D p m ⊆ make_block_list D p n := by
  intro x xmem
  apply List.mem_union_iff.mpr
  rcases List.mem_union_iff.mp xmem with lhs | rhs
  · left
    rw [← make_run_eaten_take D p m n (Nat.lt_add_one_of_le mle)] at lhs
    exact List.mem_of_mem_take lhs
  · right
    unfold west_wall at rhs
    rcases List.mem_map.mp rhs with ⟨a, amem, rfl⟩
    have alt := List.mem_range.mp amem
    rw [make_run_eaten_length] at *
    rw [make_run_eaten_length] -- Uh... shouldn't '*' include this?
    have hle : Int.ofNat ((m + 1) * p) ≤ Int.ofNat ((n + 1) * p) := by
      apply Int.ofNat_le_ofNat_of_le
      exact Nat.mul_le_mul_right _ (Nat.add_le_add_right mle 1)
    apply west_wall_mem p (n + 1)
    · apply Int.le_sub_left_of_add_le
      rw [← Int.sub_eq_add_neg]
      apply Int.sub_left_le_of_le_add
      rw [← add_zero (Int.ofNat ((m + 1) * p))]
      exact Int.add_le_add hle (Int.ofNat_zero_le _)
    · apply Int.sub_right_le_of_le_add
      rw [mul_assoc, two_mul] at alt
      apply le_trans ((Int.natCast_add _ _) ▸ (Int.ofNat_le_ofNat_of_le (Nat.le_of_lt_add_one alt)))
      exact Int.add_le_add_right hle _

-- Expand the 'next_sprint' of a 'make_run' using 'make_block_list'
lemma next_sprint_make_run_def (D : Devil) (p n : Nat) :
  next_sprint (make_run D p n) =
  sprint p (final_state (make_run D p n)) (make_block_list D p n) := rfl

-- The final state of a 'make_run' is a member of the 'next_sprint' of a smaller make_run
lemma make_run_final_state_mem_next_state (D : Devil) (p n : Nat) (npos : 0 < n) :
(final_state (make_run D p n)) ∈ next_sprint (make_run D p (n - 1)) := by
  have hsnnil : (make_run D p n).sprints ≠ [] := by
    apply List.ne_nil_of_length_pos
    rwa [make_run_sprints_length]
  convert final_state_getLast_mem_of_nonnil (make_run D p n) hsnnil
  rw [List.getLast_congr _ _ (make_run_sprints_recurrence D p n npos)]; swap
  · apply List.append_ne_nil_of_right_ne_nil
    exact list_singleton_ne_nil _
  rw [List.getLast_append_right]; swap
  · exact list_singleton_ne_nil _
  rw [List.getLast_singleton]

-- Show how to rewrite the last sprint of a 'make_run' as a raw sprint
lemma make_run_sprints_get_last_eq_sprint (D : Devil) (p n : Nat) (npos : 0 < n) :
  (make_run D p n).sprints.getLast (by
    apply List.ne_nil_of_length_pos
    rwa [make_run_sprints_length]) =
  sprint p (final_state (make_run D p (n - 1))) (make_block_list D p (n - 1)) := by
  rw [List.getLast_eq_getElem, make_run_sprint, next_sprint_make_run_def]; swap
  · rw [make_run_sprints_length]
    exact Nat.sub_lt npos Nat.zero_lt_one
  rw [make_run_sprints_length]

-- If the angel has no power it never leaves the start
lemma final_state_of_pzero (D : Devil) (n : Nat) :
  final_state (make_run D 0 n) = run_start := by
  by_cases nz : n = 0
  · subst nz
    unfold final_state
    rw [dif_pos (make_run_sprints_length D 0 0)]
  rename' nz => nnz; push_neg at nnz
  unfold final_state
  rw [dif_neg (ne_of_eq_of_ne (make_run_sprints_length D 0 n) nnz)]
  convert List.getLast_singleton (List.cons_ne_nil _ _)
  rw [make_run_sprints_get_last_eq_sprint _ _ _ (Nat.pos_of_ne_zero nnz), sprint_pzero]; congr
  exact final_state_of_pzero D (n - 1)

-- Prove an upper bound on the distance the elements in the
-- next sprint can be from the origin.
lemma make_run_next_sprint_mem_origin_close (D : Devil) (p n : Nat) :
  ∀ rs ∈ next_sprint (make_run D p n), close (p * (n + 1)) (0, 0) (loc rs) := by
  intro rs rsmem
  have hclose₀ : close (p * n) (0, 0) (last (make_run D p n).A) := by
    unfold close
    by_contra! h
    apply (lt_self_iff_false n).mp
    nth_rw 2 [← make_run_journey_steps D p n]
    exact journey_lb _ _ h
  have hclose₁ : close p (last (make_run D p n).A) (loc rs) := by
    rw [close_comm, last]
    rw [cell_congr_idx (make_run D p n).A (make_run_journey_steps D p n)]
    apply make_run_next_sprint_mem_journey_cell_close
    assumption
  rw [mul_add, mul_one]
  exact le_trans (dist_tri _ _ _) (Nat.add_le_add hclose₀ hclose₁)

-- If the angel has no power it never leaves the start
lemma make_run_of_pzero (D : Devil) (n : Nat) :
  ∀ s ∈ (make_run D 0 n).sprints, s = [run_start] := by
  intro s smem
  -- Handle the case where n = 0
  by_cases nz : n = 0
  · subst nz
    rw [make_run_eq_empty_of_length_zero] at smem
    rw [empty_builder_sprints] at smem
    exact False.elim ((List.mem_nil_iff _).mp smem)
  rename' nz => nnz; push_neg at nnz
  rw [make_run_sprints_recurrence D 0 n (Nat.pos_of_ne_zero nnz)] at smem
  rcases List.mem_append.mp smem with lhs | rhs
  · exact make_run_of_pzero D (n - 1) s lhs
  · rw [List.mem_singleton.mp rhs]
    unfold next_sprint
    rw [sprint_pzero]; congr
    exact final_state_of_pzero D (n - 1)

-- Show that the 'make_run' never crosses the y-axis
lemma make_run_x_nonneg (D : Devil) (p n : Nat) :
  ∀ s ∈ (make_run D p n).sprints, ∀ rs ∈ s, 0 ≤ rs.x := by
  intro s smem rs rsmem
  -- If p = 0, the angel never leaves the start
  by_cases pz : p = 0
  · subst pz
    rw [make_run_of_pzero D n s smem] at rsmem
    rw [List.mem_singleton.mp rsmem]
    unfold run_start; simp
  rename' pz => pnz; push_neg at pnz
  have ppos : 0 < p := Nat.pos_of_ne_zero pnz
  by_cases nz : n = 0
  · subst nz
    rw [make_run_eq_empty_of_length_zero, empty_builder_sprints] at smem
    exact False.elim ((List.mem_nil_iff _).mp smem)
  rename' nz => nnz; push_neg at nnz
  have npos : 0 < n := Nat.pos_of_ne_zero nnz
  rw [make_run_sprints_recurrence D p n npos] at smem
  -- If 's' is not the last sprint we can recurse
  rcases List.mem_append.mp smem with lhs | rhs
  · exact make_run_x_nonneg D p (n - 1) s lhs rs rsmem
  have hs := List.mem_singleton.mp rhs
  have snnil : s ≠ [] := by
    rw [hs]
    exact sprint_nonnil _ _ _
  have lehead : 0 ≤ (s.head snnil).x := by
    by_cases npz : n - 1 = 0
    · rw [npz, make_run_eq_empty_of_length_zero] at hs
      unfold next_sprint at hs
      rw [final_state_of_sprints_nil _ (empty_builder_sprints D p)] at hs
      rw [List.head_eq_getElem, getElem_congr_coll hs]
      rw [sprint_getElem_zero]
      unfold run_start; simp
    rename' npz => npnz; push_neg at npnz
    rw [List.head_eq_getElem, getElem_congr_coll hs]
    rw [← next_sprint_first_eq_builder_last]
    unfold final_state
    rw [dif_neg (ne_of_eq_of_ne (make_run_sprints_length D p (n - 1)) npnz)]
    -- The head of one sprint is the end of the previous so we can recurse
    exact make_run_x_nonneg D p (n - 1) _ (List.getLast_mem _) _ (List.getLast_mem _)
  have lehead' : -1 ≤ (s.head snnil).x := by
    exact le_of_lt (lt_of_lt_of_le (by norm_num) lehead)
  -- If the head of the sprint has non-negative x-coordinate
  -- suppose 'rs' has negative x-coordinate and show this leads to a contradiction
  apply Int.le_of_sub_one_lt
  rw [zero_sub]
  by_contra! xle
  -- Prove the elements of 's' are "close"
  have hclose : ∀ rs ∈ s, close (n * p) (0, 0) (loc rs) := by
    intro rs rsmem
    rw [← Nat.sub_one_add_one nnz, mul_comm]
    exact make_run_next_sprint_mem_origin_close D p (n - 1) rs (hs ▸ rsmem)
  unfold next_sprint at hs
  let rs₀ := (final_state (make_run D p (n - 1)))
  let blocked := make_block_list D p (n - 1)
  change s = sprint p rs₀ blocked at hs
  -- Rewrite the sprint as a trace and use the intermediate value theorem
  -- to show that some element in the sprint must have x = -1
  have htrace := sprint_eq_trace p s.length rs₀ blocked (by rw [hs])
  have rsmem' : rs ∈ trace s.length rs₀ blocked := by
    rw [← htrace]
    rwa [hs] at rsmem
  have headmem : s.head snnil ∈ trace s.length rs₀ blocked := by
    rw [← htrace]
    convert List.head_mem snnil
    exact hs.symm
  rcases trace_intermediate_value_x
    s.length rs₀ blocked rs (s.head snnil) rsmem' headmem (-1) xle lehead' with ⟨rs', rs'mem, hrs'⟩
  rw [← htrace] at rs'mem
  have yle := close_origin_yle _ _ (hclose rs' (hs ▸ rs'mem))
  have ley := close_origin_negyle _ _ (hclose rs' (hs ▸ rs'mem))
  rw [← Int.neg_le_neg_iff, Int.neg_neg] at ley
  -- Show that loc rs' must appear in the blocked list
  have hblocked : loc rs' ∈ blocked := by
    unfold blocked make_block_list
    rw [make_run_eaten_length, Nat.sub_one_add_one nnz]
    -- NOTE: There's a great example here of an incomprehensible
    -- Lean failure. Just try using 'List.mem_union_right' instead
    -- of 'List.mem_union_iff.mpr; right' and watch it fail!
    -- (It has something to do with using two different types of BEq)
    apply List.mem_union_iff.mpr; right
    convert west_wall_mem p n (loc rs').2 ley yle
  -- If the sprint moved off the starting square then all states but
  -- the first must not be in the blocked list. This leaves rs' ≠ rs₀
  -- as the remaining goal
  apply sprint_avoids_blocked' p rs₀ blocked rs' rs'mem _ hblocked
  -- To show rs' ≠ rs₀, put a lower bound on rs₀.x
  have lers₀x : 0 ≤ rs₀.x := by
    rwa [List.head_eq_getElem, getElem_congr_coll hs, sprint_getElem_zero] at lehead
  unfold loc
  intro h
  have xeq := (Prod.ext_iff.mp h).1; dsimp at xeq
  absurd (hrs' ▸ xeq); push_neg
  exact ne_of_lt ((Int.zero_sub _) ▸ (Int.sub_one_lt_of_le lers₀x))

-- For every nice devil and any run length, the run's starting cell is "valid"
-- That is, it is unblocked and the cell to its left is a wall.
lemma run_start_valid_of_nice (D : Devil) (p : Nat) (hnice : nice D p) :
  ∀ n, run_start_valid (make_block_list D p n) run_start := by
  intro n
  constructor
  · intro h
    rcases List.mem_union_iff.mp h with lhs | rhs
    · rcases List.getElem_of_mem lhs with ⟨i, ilt, hi⟩
      have ilt' : i < n + 1 := by rwa [make_run_eaten_length] at ilt
      rw [make_run_eaten D p n i ilt', ← make_run_subjourney D p i n ilt'] at hi
      unfold loc run_start at hi; simp at hi
      apply not_nice_of_eats_origin D p _ hnice
      use (make_run D p n).A, i, (by rwa [make_run_journey_steps])
    · rw [make_run_eaten_length] at rhs
      absurd west_wall_xcoord_of_mem p (n + 1) _ rhs
      unfold run_start loc; simp
  · apply List.mem_union_iff.mpr; right
    rw [make_run_eaten_length]
    unfold left_of_runner run_start uvec_up; simp
    apply west_wall_mem
    · apply neg_le.mp
      rw [neg_zero]
      exact Int.zero_le_ofNat _
    · exact Int.zero_le_ofNat _

-- This theorem is a bit odd, but useful in several places.
-- It states that a 'make_run' never steps on a later block list, given
-- that it never steps on its own block list and the devil is nice.
-- In some sense, this is the induction step for the more general
-- 'make_run_next_sprint_avoids_blocked_of_nice' (see below).
lemma make_run_next_sprint_avoids_later_block_list_of_nice
  (D : Devil) (p n : Nat) (hnice : nice D p) :
  ∀ rs ∈ next_sprint (make_run D p n), loc rs ∉ make_block_list D p n →
  ∀ n' (_ : n ≤ n'), loc rs ∉ make_block_list D p n' := by
  intro rs rsmemns rsnmembl n' nle rsmembl'
  have nnen' : n ≠ n' := by
    intro nn'
    subst nn'
    exact rsnmembl rsmembl'
  have nltn' : n < n' := Nat.lt_of_le_of_ne nle nnen'
  by_cases n'z : n' = 0
  · subst n'z
    exact nnen' (Nat.le_zero.mp nle)
  rename' n'z => n'nz; push_neg at n'nz
  have n'pos : 0 < n' := Nat.pos_of_ne_zero n'nz
  rcases List.mem_union_iff.mp rsmembl' with lhs | rhs
  · -- Handle the case where the 'rs' is on the eaten list
    rcases List.getElem_of_mem lhs with ⟨i, ilt, hi⟩
    rw [make_run_eaten_length] at ilt
    rw [make_run_eaten D p n' i ilt] at hi
    -- Handle the case where 'rs'  was eaten after it was visited
    by_cases nlt : n < i
    · -- Since 'rs' is in the previous sprint, the devil has eaten a cell
      -- close to a previous journey cell, which contradicts 'hnice'.
      apply not_nice_of_eats_close D p _ hnice
      use (make_run D p n').A, n, i, nlt
      use (by rwa [make_run_journey_steps])
      rw [make_run_subjourney, hi, close_comm]; swap
      · exact ilt
      apply make_run_sprint_mem_journey_cell_close; swap
      · exact nltn'
      rw [make_run_sprint]
      · exact rsmemns
      · exact nltn'
    · rename' nlt => ile; push_neg at ile
      -- If i ≤ n, we will show that 'rs' was on the old eaten list - a contradiction
      apply rsnmembl
      apply List.mem_union_iff.mpr; left
      rw [← hi]
      have ilt' : i < (make_run D p n).eaten.length := by
        rw [make_run_eaten_length]
        exact Nat.lt_add_one_of_le ile
      convert List.getElem_mem ilt'; symm
      exact make_run_eaten D p n i (Nat.lt_add_one_of_le ile)
  -- Now handle the case where 'rs' is a wall cell
  · unfold west_wall at rhs
    rcases List.getElem_of_mem rhs with ⟨i, ilt, hi⟩
    rw [List.length_map, List.length_range, make_run_eaten_length] at ilt
    rw [List.getElem_map, List.getElem_range, make_run_eaten_length] at hi
    -- Prove that 'rs' is "close" to the origin using the bound proven in Bound.lean
    have hclose := make_run_next_sprint_mem_origin_close D p n rs rsmemns
    -- Using hclose₂, prove bounds on rs.y
    by_cases ltrsy : Int.ofNat ((n + 1) * p) < (loc rs).2
    · rw [mul_comm] at ltrsy
      exact not_lt_of_ge (close_origin_yle _ _ hclose) ltrsy
    rename' ltrsy => rsyle; push_neg at rsyle
    by_cases rsylt : (loc rs).2 < -(Int.ofNat ((n + 1) * p))
    · rw [mul_comm] at rsylt
      apply not_lt_of_ge (close_origin_negyle _ _ hclose)
      convert (Int.neg_neg _) ▸ (Int.neg_lt_neg rsylt)
    rename' rsylt => lersy; push_neg at lersy
    -- If -(p * (n + 1) ≤ rs.y ≤ p * (n + 1), show that 'rs' was in the old west wall
    apply rsnmembl (List.mem_union_iff.mpr _); right
    rw [make_run_eaten_length]
    rw [← hi] at *
    exact west_wall_mem _ _ _ lersy rsyle

/- Note that it *is* possible to force the runner to remain on a blocked cell
   if the devil is not nice. Technically, even with a devil that isn't nice,
   the runner can never be forced onto a 'wall' cell (cells with x = -1, 0 ≤ y)
   but that proof is more difficult and we're only concerned with nice devils
   for this section of the proof so we can make our work easier by assuming such. -/
lemma make_run_next_sprint_avoids_blocked_of_nice (D : Devil) (p n : Nat) (hnice : nice D p) :
  ∀ rs ∈ next_sprint (make_run D p n), (loc rs) ∉ make_block_list D p n := by
  intro rs rsmem lrsmem
  -- First handle the case where n = 0
  -- This mostly involves showing that the origin will never be on the block list
  by_cases nz : n = 0
  · subst nz
    apply sprint_avoids_blocked p _ (make_block_list D p 0) _ rs rsmem lrsmem
    rw [make_run_eq_empty_of_length_zero]
    rw [final_state_of_sprints_nil _ (empty_builder_sprints D p)]
    unfold run_start loc; dsimp
    intro omem
    -- We have two cases depending on whether rs is an eaten cell or wall cell
    rcases List.mem_union_iff.mp omem with lhs | rhs
    · -- The nice devil never eats the origin, so we can show a contradiction
      rw [make_run_eq_empty_of_length_zero, empty_builder_eaten] at lhs
      apply not_nice_of_eats_origin D p _ hnice
      use NoSteps p, 0, (by rw [nosteps_steps p]; norm_num)
      rw [List.mem_singleton.mp lhs]
      rfl
    · -- If rs is a wall cell, this leads to a contradiction because the
      -- x-coordinates don't match
      --rw [make_run_eaten_length, zero_add] at rhs
      have := west_wall_xcoord_of_mem p _ (0, 0) rhs
      dsimp at this
      linarith
  rename' nz => nnz; push_neg at nnz
  have hsnnil : (make_run D p n).sprints ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [make_run_sprints_length]
    exact Nat.pos_of_ne_zero nnz
  rw [next_sprint_make_run_def] at rsmem
  -- Use recursion to show that the run has thus far avoided blocked cells
  -- This will be required in order to use 'sprint_avoids_blocked'
  have hsafe : loc (final_state (make_run D p n)) ∉ make_block_list D p (n - 1) := by
    apply make_run_next_sprint_avoids_blocked_of_nice
    · assumption
    convert final_state_getLast_mem_of_nonnil (make_run D p n) hsnnil
    rw [List.getLast_congr _ _ (make_run_sprints_recurrence D p n (Nat.pos_of_ne_zero nnz))]; swap
    · apply List.append_ne_nil_of_right_ne_nil
      exact list_singleton_ne_nil _
    rw [List.getLast_append_right (list_singleton_ne_nil _)]
    exact (List.getLast_singleton (list_singleton_ne_nil _)).symm
  have fsmem := make_run_final_state_mem_next_state D p n (Nat.pos_of_ne_zero nnz)
  -- The induction step for our argument was proven separately: showing that any cell in
  -- 'next_sprint' that isn't in its own block list won't be in any future block list.
  have := make_run_next_sprint_avoids_later_block_list_of_nice D p (n - 1) hnice _ fsmem hsafe n (Nat.sub_le _ _)
  exact sprint_avoids_blocked p _ _ this rs rsmem lrsmem

-- The 'next_sprint' will never include a cell which appears on a later block list
lemma make_run_next_sprint_avoids_later_block_list
  (D : Devil) (p m n : Nat) (mle : m ≤ n) (hnice : nice D p) :
  ∀ rs ∈ next_sprint (make_run D p m), loc rs ∉ make_block_list D p n := by
  intro rs rsmem
  apply make_run_next_sprint_avoids_later_block_list_of_nice D p m hnice rs rsmem _ n mle
  exact make_run_next_sprint_avoids_blocked_of_nice D p m hnice rs rsmem

lemma make_run_journey_allowed_of_nice (D : Devil) (p n : Nat) (hnice : nice D p) :
  allowed D (make_run D p n).A := by
  let MR := make_run D p n
  change allowed D MR.A
  unfold allowed
  intro i j ilt jlt
  -- Introduce some helpful inequalities
  have jlt' : j < n + 1 := by
    rwa [make_run_journey_steps] at jlt
  have ilt' : i < n :=
    lt_of_lt_of_le ilt (Nat.le_of_lt_add_one jlt')
  have npos : 0 < n := Nat.zero_lt_of_lt ilt'
  have nnez : n ≠ 0 := Nat.ne_zero_of_lt npos
  -- Rewrite the left-hand side using the journey recurrence
  have lhs_rw : subjourney MR.A i (lt_trans ilt jlt) =
    subjourney (make_run D p (n - 1)).A i (by
      rwa [make_run_journey_steps, Nat.sub_one_add_one]
      exact Nat.ne_zero_of_lt ilt'
    ) := by
    rw [subjourney_congr_journey (make_run_journey_recurrence D p n npos)]
    rw [append_subjourney]
  -- If j ≠ n we can recurse, so handle that case first
  by_cases hjnn : n ≠ j
  · -- Now apply the journey recurrence on the right and recurse
    rw [lhs_rw, cell_congr_journey (make_run_journey_recurrence D p n npos)]
    rw [append_cell_ne_last]; swap
    · rw [make_run_journey_steps, Nat.sub_one_add_one nnez]
      exact lt_of_le_of_ne (Nat.le_of_lt_add_one jlt') hjnn.symm
    apply make_run_journey_allowed_of_nice
    · exact hnice
    · exact ilt
  rename' hjnn => hjn; push_neg at hjn
  subst hjn
  have last_exp := (final_state_loc_eq_journey_last (make_run D p n)).symm
  rw [last, ← cell_congr_idx _ (make_run_journey_steps D p n ).symm jlt] at last_exp
  rw [last_exp, make_run_subjourney D p i n (lt_trans ilt (Nat.lt_add_one _))]
  intro h
  let fs : RunState := final_state (make_run D p n)
  have lfsmem : loc fs ∈ (make_run D p (n - 1)).eaten := by
    apply @List.mem_of_mem_take _ (i + 1)
    rw [make_run_eaten_take]; swap
    · rwa [Nat.sub_one_add_one nnez]
    -- Handle the case where i = 0
    by_cases iz : i = 0
    · subst iz
      rw [make_run_eq_empty_of_length_zero] at *
      rw [empty_builder_journey] at h
      rw [empty_builder_eaten, h]
      exact List.mem_singleton_self _
    rename' iz => inz; push_neg at inz
    -- Otherwise, if i ≠ 0 we can use the 'eaten' recurrence
    rw [make_run_eaten_recurrence]; swap
    · exact Nat.pos_of_ne_zero inz
    apply List.mem_append_right
    rw [h]
    exact List.mem_singleton_self _
  apply make_run_next_sprint_avoids_blocked_of_nice D p (n - 1) hnice fs _ _
  · convert final_state_getLast_mem_of_nonnil (make_run D p n) (by
      apply List.ne_nil_of_length_pos
      rwa [make_run_sprints_length]
    )
    rw [List.getLast_congr _ _ (make_run_sprints_recurrence D p n npos)]; swap
    · apply List.ne_nil_of_length_pos
      rw [List.length_append, List.length_singleton]
      exact lt_of_le_of_lt (Nat.zero_le _) (Nat.lt_add_one _)
    rw [List.getLast_append_right]; swap
    · exact list_singleton_ne_nil _
    exact (List.getLast_singleton (list_singleton_ne_nil _)).symm
  · exact List.mem_union_iff.mpr (Or.inl lfsmem)

/- Construct the list of run states corresponding to the full route of the runner.
   Each sprint overlaps by one cell, so we need to remove the first state from all
   but the first sprint -/
def RunPath (D : Devil) (p n : Nat) : List RunState :=
  if hlz : (make_run D p n).sprints.length = 0 then [run_start] else
  ((make_run D p n).sprints.head (List.ne_nil_of_length_pos (Nat.pos_of_ne_zero hlz))) ++
  (List.flatten (List.map List.tail (make_run D p n).sprints.tail))

-- A RunPath of length zero is just the singleton list [run_start]
lemma run_path_of_length_zero (D : Devil) (p : Nat) :
  RunPath D p 0 = [run_start] := by
  unfold RunPath make_run
  rw [dif_pos]
  rw [if_pos rfl, empty_builder_sprints]
  exact List.length_nil

-- A RunPath based on a 'make_run' of zero sprints has a length of 1
lemma run_path_length_of_length_zero (D : Devil) (p : Nat) :
  (RunPath D p 0).length = 1 := by
  rw [run_path_of_length_zero]
  exact List.length_singleton

-- Any run state in the 'run path' must exist in some sprint of the run builder
lemma make_run_sprints_getElem_exists_of_run_path_mem (D : Devil) (p n : Nat)
  (npos : 0 < n) (rs : RunState) (hmem : rs ∈ RunPath D p n) :
  ∃ (i : Nat) (ilt : i < ((make_run D p n).sprints.length)),
  ∃ (j : Nat) (jlt : j < ((make_run D p n).sprints[i].length)),
  (make_run D p n).sprints[i][j] = rs := by
  unfold RunPath at hmem
  have hslnz : (make_run D p n).sprints.length ≠ 0 := by
    rw [make_run_sprints_length]
    exact Nat.ne_zero_iff_zero_lt.mpr npos
  have hslpos : 0 < (make_run D p n).sprints.length :=
    Nat.pos_of_ne_zero hslnz
  rw [dif_neg hslnz] at hmem
  rcases List.mem_append.mp hmem with lhs | rhs
  · -- Handle the case where 'rs' was in the first sprint
    rw [← List.getElem_zero_eq_head hslpos] at lhs
    rcases List.getElem_of_mem lhs with ⟨j, jlt, h⟩
    use 0, Nat.pos_of_ne_zero hslnz, j, jlt, h
  -- Otherwise use various list identities to get the original
  -- location of 'rs' within the sprints
  rcases List.mem_flatten.mp rhs with ⟨s, smem, hmem'⟩
  rcases List.mem_map.mp smem with ⟨s', s'mem, rfl⟩
  rcases List.getElem_of_mem (List.mem_of_mem_tail s'mem) with ⟨i, ilt, s'elem⟩
  rcases List.getElem_of_mem (List.mem_of_mem_tail hmem') with ⟨j, jlt, rselem⟩
  rw [← s'elem] at jlt
  use i, ilt, j, jlt
  rw [← getElem_congr_coll s'elem] at rselem
  exact rselem

-- Recursive definition of RunPath in terms of 'make_run' sprints
lemma run_path_recurrence (D : Devil) (p n : Nat) (npos : 0 < n) :
  (RunPath D p n) =
  (RunPath D p (n - 1)) ++ ((make_run D p n).sprints.getLast
    (by
      apply List.ne_nil_of_length_pos
      rwa [make_run_sprints_length]
    )).tail := by
  unfold RunPath
  have hnz : n ≠ 0 := Nat.ne_zero_of_lt npos
  have hlnz : (make_run D p n).sprints.length ≠ 0 := by
    rwa [make_run_sprints_length]
  have hlpos : 0 < (make_run D p n).sprints.length := by
    exact Nat.pos_of_ne_zero hlnz
  rw [dif_neg hlnz]
  -- Handle the case where n = 1
  by_cases n1 : n = 1
  · subst n1
    have hlz : (make_run D p (1 - 1)).sprints.length = 0 := by
      rw [make_run_sprints_length]
    rw [dif_pos hlz]
    have hstn : (make_run D p 1).sprints.tail = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [List.length_tail, make_run_sprints_length, Nat.sub_self]
    rw [hstn, List.map_nil, List.flatten_nil, List.append_nil, ← List.getElem_zero_eq_head]; swap
    · assumption
    have gE0nn : (make_run D p 1).sprints[0] ≠ [] := by
      apply (make_run D p 1).nonnil
      apply List.getElem_mem
    rw [← List.head_cons_tail _ gE0nn, List.singleton_append, ← List.getElem_zero_eq_head]; swap
    · -- Resolve bounds check
      exact List.length_pos_of_ne_nil gE0nn
    rw [(make_run D p 1).origin]; swap
    · -- Resolve bounds check
      exact List.ne_nil_of_length_pos hlpos
    rw [List.getLast_eq_getElem]; congr 2
    apply getElem_congr_idx
    rw [make_run_sprints_length, Nat.sub_self]
  rename' n1 => nne1; push_neg at nne1
  have h1ltn : 1 < n := by
    exact Nat.lt_of_le_of_ne (Nat.add_one_le_of_lt (Nat.pos_of_ne_zero hnz)) nne1.symm
  have hlnz' : (make_run D p (n - 1)).sprints.length ≠ 0 := by
    rw [make_run_sprints_length]
    exact Nat.sub_ne_zero_of_lt h1ltn
  have hlpos' : 0 < (make_run D p (n - 1)).sprints.length := by
    exact Nat.pos_of_ne_zero hlnz'
  -- First, manipulate each side of the equation so that the
  -- left-hand sides of the appends match, and we can 'congr'
  rw [dif_neg hlnz', List.append_assoc, ← List.getElem_zero_eq_head]; swap
  · assumption
  have := make_run_sprints_recurrence D p n (Nat.pos_of_ne_zero hnz)
  rw [getElem_congr_coll this]
  rw [List.getElem_append_left, List.getElem_zero_eq_head]; swap
  · -- Resolve bounds check
    exact Nat.pos_of_ne_zero hlnz'
  congr
  -- Apply more list identities until we can 'congr' again
  nth_rw 1 [this, List.tail_append_of_ne_nil, List.map_append, List.map_singleton]; swap
  · -- Resolve bounds check
    apply List.ne_nil_of_length_pos
    exact Nat.pos_of_ne_zero hlnz'
  rw [List.flatten_append, List.flatten_singleton]; congr
  rw [← make_run_sprint D p n, List.getLast_eq_getElem]
  · congr; rw [make_run_sprints_length]
  · exact Nat.sub_lt npos (by norm_num)

-- Recursive formula for the length of the run path
lemma run_path_length_recurrence (D : Devil) (p n : Nat) (npos : 0 < n) :
  (RunPath D p n).length =
  (RunPath D p (n - 1)).length +
  ((make_run D p n).sprints.getLast (by
    apply List.ne_nil_of_length_pos
    rwa [make_run_sprints_length]
  )).length - 1 := by
  rw [run_path_recurrence]; swap
  · assumption
  rw [List.length_append, List.length_tail, Nat.add_sub_assoc]
  exact Nat.add_one_le_of_lt (List.length_pos_of_ne_nil (RunBuilder.nonnil _ _ (List.getLast_mem _)))

-- This theorem handles the degenerate case where p = 0
lemma run_path_pzero (D : Devil) (n : Nat) : (RunPath D 0 n) = [run_start] := by
  by_cases nz : n = 0
  · subst nz
    rw [run_path_of_length_zero]
  rename' nz => nnz; push_neg at nnz
  have npos : 0 < n := Nat.pos_of_ne_zero nnz
  rw [run_path_recurrence D 0 n npos, run_path_pzero]
  convert List.append_nil _
  have hsnnil : (make_run D 0 n).sprints ≠ [] := by
    apply List.ne_nil_of_length_pos
    rwa [make_run_sprints_length]
  rw [make_run_of_pzero D n _ (List.getLast_mem _)]
  rfl

-- Every run path has positive length
lemma run_path_length_pos (D : Devil) (p n : Nat) : 0 < (RunPath D p n).length := by
  by_cases nz : n = 0
  · subst nz
    rw [run_path_length_of_length_zero]; norm_num
  rename' nz => nnz; push_neg at nnz
  rw [run_path_length_recurrence D p n (Nat.pos_of_ne_zero nnz)]
  rw [Nat.add_sub_assoc]; swap
  · exact Nat.add_one_le_of_lt (List.length_pos_of_ne_nil (RunBuilder.nonnil _ _ (List.getLast_mem _)))
  exact Nat.add_pos_left (run_path_length_pos D p (n - 1)) _

-- As the number of sprints in the run path increases, the length of
-- the run path also increases or remains constant.
lemma run_path_length_non_decreasing (D : Devil) (p n : Nat) (npos : 0 < n) :
  (RunPath D p (n - 1)).length ≤ (RunPath D p n).length := by
  rw [run_path_length_recurrence D p n npos, Nat.add_sub_assoc]; swap
  · apply Nat.add_one_le_of_lt (List.length_pos_of_ne_nil _)
    exact RunBuilder.nonnil _ _ (List.getLast_mem _)
  exact Nat.le_add_right _ _

-- As the number of sprints in the run path increases, so does the
-- length of the run path if the angel has non-zero power.
lemma run_path_length_increasing_of_ppos
  (D : Devil) (p n : Nat) (npos : 0 < n) (ppos : 0 < p) :
  (RunPath D p (n - 1)).length < (RunPath D p n).length := by
  rw [run_path_length_recurrence D p n npos, Nat.add_sub_assoc]; swap
  · apply Nat.add_one_le_of_lt (List.length_pos_of_ne_nil _)
    exact RunBuilder.nonnil _ _ (List.getLast_mem _)
  apply Nat.lt_add_of_pos_right
  have hnnil : (make_run D p n).sprints ≠ [] := by
    apply List.ne_nil_of_length_pos
    rwa [make_run_sprints_length]
  let s := ((make_run D p n).sprints.getLast hnnil)
  rcases make_run_sprint_is_sprint D p n s (List.getLast_mem hnnil) with ⟨start, blocked, h⟩
  change 0 < s.length - 1
  -- Use the sprint length lower bound to finish the goal
  exact lt_of_lt_of_le ppos (Nat.le_sub_one_of_lt (h ▸ (sprint_length_lb p start blocked)))

-- A predicate to check if 'rs' is an element of a particular sprint.
-- Argument is of type 'Fin (n - 1 + 1)' to make it compatible with
-- '_find_last' which requires an argument of type Fin (m+1) for some 'm'.
abbrev is_sprint_mem (D : Devil) (p n : Nat)
  (npos : 0 < n) (rs : RunState) : (i : Fin (n - 1 + 1)) → Prop :=
  fun i ↦ (rs ∈ (make_run D p n).sprints[i]'(by
    rw [make_run_sprints_length]
    convert i.2
    exact (Nat.sub_one_add_one (Nat.ne_zero_of_lt npos)).symm))

-- TODO: So.... which proof were these for? We don't seem to use them.
-- Returns the index of the last sprint of the 'make_run' of which 'rs' is an element
-- For the proof
def find_last_sprint_with_state (D : Devil) (p n : Nat)
  (npos : 0 < n) (rs : RunState) : Nat :=
  (find_last (is_sprint_mem D p n npos rs) (Nat.add_one_ne_zero _)).val

-- Prove that 'rs' appears in no later sprint than the one
-- found by 'find_last_sprint_with_state'
lemma last_sprint_with_state_is_last (D : Devil) (p n : Nat)
  (npos : 0 < n) (rs : RunState) : ∀ (i : Nat) (ilt : i < n),
  rs ∈ (make_run D p n).sprints[i]'(by rwa [make_run_sprints_length]) →
  i ≤ find_last_sprint_with_state D p n npos rs := by
  intro i ilt hmem
  unfold find_last_sprint_with_state
  -- First, work around Fin awkwardness
  have h₀ : n - 1 + 1 = n := Nat.sub_one_add_one (Nat.ne_zero_of_lt npos)
  have h₁ : (@Fin.mk (n - 1 + 1) i (by rwa [h₀])).val = i := by simp
  rw [← h₁]
  apply Fin.le_iff_val_le_val.mp
  -- Then apply the corresponding theorem for '_find_last'
  apply find_last_is_last
  exact hmem

-- The return value of 'find_last_sprint_with_state' is
-- less than the number of sprints in the 'make_run'
lemma last_sprint_with_state_lt_length (D : Devil) (p n : Nat)
  (npos : 0 < n) (rs : RunState) :
  find_last_sprint_with_state D p n npos rs < (make_run D p n).sprints.length := by
  unfold find_last_sprint_with_state
  rw [make_run_sprints_length]
  apply lt_of_lt_of_eq _ (Nat.sub_one_add_one (Nat.ne_zero_of_lt npos))
  exact (find_last (is_sprint_mem D p n npos rs) (Nat.add_one_ne_zero _)).2

-- The sprint indicated by 'find_last_sprint_with_state' does
-- in-fact contain the element 'rs'
lemma last_sprint_with_state_is_sat (D : Devil) (p n : Nat)
  (npos : 0 < n) (rs : RunState) :
  (∃ (i : Nat) (ilt : i < n), rs ∈ (make_run D p n).sprints[i]'(by
    rwa [make_run_sprints_length])) →
  rs ∈ (make_run D p n).sprints[find_last_sprint_with_state D p n npos rs]'(
    last_sprint_with_state_lt_length D p n npos rs
  ) := by
  rintro ⟨i, ilt, hmem⟩
  let i' : Fin (n - 1 + 1) := ⟨i, by rwa [(Nat.sub_one_add_one (Nat.ne_zero_of_lt npos))]⟩
  exact find_last_is_sat ((is_sprint_mem D p n npos rs)) ⟨i', hmem⟩

-- If the devil is "nice", the runner will never visit a cell that was previously eaten.
-- Note that this result is more general than 'make_run_journey_allowed_of_nice' in that
-- it applies to *all* cells visited by the runner, not just those in the journey.
lemma make_run_runner_avoids_eaten_cells_of_nice (D : Devil) (p n : Nat) (hnice : nice D p) :
  ∀ i (ilt : i < n) j (jlt : j < ((make_run D p n).sprints[i]'(by
    rwa [make_run_sprints_length])).length) k (kle : k ≤ i),
    (make_run D p n).eaten[k]'(by
      rw [make_run_eaten_length]
      exact lt_trans (lt_of_le_of_lt kle ilt) (Nat.lt_add_one _)
    ) ≠ loc (((make_run D p n).sprints[i]'(by rwa [make_run_sprints_length]))[j]'(jlt)) := by
  intro i ilt j jlt k kle
  rw [getElem_congr_coll (make_run_sprint D p n i ilt)]
  have lhs_rw : (make_run D p n).eaten[k]'(by
    rw [make_run_eaten_length]
    exact lt_trans (lt_of_le_of_lt kle ilt) (Nat.lt_add_one _)
  ) = ((make_run D p n).eaten.take (i + 1))[k]'(by
    rw [List.length_take_of_le]
    · exact Nat.lt_add_one_of_le kle
    · rw [make_run_eaten_length]
      apply Nat.add_one_le_of_lt
      exact lt_trans ilt (Nat.lt_add_one _)
  ) := by
    exact List.getElem_take.symm
  rw [lhs_rw]
  rw [getElem_congr_coll (make_run_eaten_take D p i n (lt_trans ilt (Nat.lt_add_one _)))]
  intro h
  rw [make_run_sprint D p n i ilt] at jlt
  let rs : RunState := (next_sprint (make_run D p i))[j]'jlt
  apply make_run_next_sprint_avoids_blocked_of_nice D p i hnice rs (List.getElem_mem jlt)
  apply List.mem_union_iff.mpr; left
  rw [← h]
  exact List.getElem_mem (by rw [make_run_eaten_length]; exact Nat.lt_add_one_of_le kle)

-- If the devil is "nice", then no cell visited by the runner was ever eaten by the devil.
lemma run_path_not_eaten_of_nice (D : Devil) (p n : Nat) (hnice : nice D p) :
  ∀ rs ∈ (RunPath D p n), (loc rs) ∉ (make_run D p n).eaten := by
  intro rs rsmem rseaten
  -- First handle the case where n = 0
  by_cases hnz : n = 0
  · subst hnz
    rw [run_path_of_length_zero, List.mem_singleton] at rsmem
    rw [make_run_eq_empty_of_length_zero, empty_builder_eaten, List.mem_singleton] at rseaten
    subst rsmem
    unfold loc run_start at rseaten; dsimp at rseaten
    apply not_nice_of_eats_origin D p _ hnice
    exact ⟨NoSteps p, 0, Nat.add_one_pos _, rseaten.symm⟩
  rename' hnz => hnnz; push_neg at hnnz
  have npos : 0 < n := Nat.pos_of_ne_zero hnnz
  -- Get the location of 'rs' within 'sprints'
  have mrsgEe_of_rpm :=
    make_run_sprints_getElem_exists_of_run_path_mem D p n npos rs rsmem
  rcases mrsgEe_of_rpm with ⟨i, ilt, j, jlt, hij⟩
  let MR : RunBuilder p := (make_run D p n)
  have snnil : MR.sprints ≠ [] := by
        apply List.ne_nil_of_length_pos
        rwa [make_run_sprints_length]
  have eatnnil : MR.eaten ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [make_run_eaten_length]
    exact Nat.add_one_pos _
  -- Next handle the case where the cell in question was eaten last
  by_cases hlast : loc rs = MR.eaten.getLast eatnnil
  · -- We will show that the devil is not in-fact nice: a contradiction
    apply not_nice_of_eats_close D p _ hnice
    have nlt : n < steps MR.A + 1 := by
      rw [make_run_journey_steps]
      exact Nat.lt_add_one _
    use MR.A, i, n, (by convert ilt; rw [make_run_sprints_length]), nlt
    -- Prove the rewrite of the right-hand cell
    have rwr : response D (subjourney MR.A n nlt) = loc rs := by
      rw [hlast, List.getLast_eq_getElem, make_run_eaten]; swap
      · -- Resolve bounds check
        rw [make_run_eaten_length, Nat.add_one_sub_one]
        exact Nat.lt_add_one _
      rw [make_run_eaten_length, Nat.add_one_sub_one]
      apply congrArg (fun A ↦ response D A)
      convert subjourney_full _
      rw [make_run_journey_steps]
    rw [rwr, close_comm]
    -- Apply the sprint-journey closeness theorem
    apply make_run_sprint_mem_journey_cell_close
    · exact List.mem_of_getElem hij
    · convert ilt
      rw [make_run_sprints_length]
  rename' hlast => hnl; push_neg at hnl
  -- If 'rs' wasn't eaten at the end, it must have
  -- been eaten in some shorter 'make_run'
  have rseaten' : loc rs ∈ (make_run D p (n - 1)).eaten := by
    rw [make_run_eaten_recurrence] at rseaten; swap
    · assumption
    rcases List.mem_append.mp rseaten with lhs | rhs
    · assumption
    apply False.elim (hnl _)
    rw [List.mem_singleton.mp rhs, List.getLast_eq_getElem, make_run_eaten]; swap
    · rw [make_run_eaten_length]
      exact Nat.sub_lt (Nat.add_one_pos _) (by norm_num)
    rw [make_run_eaten_length]; rfl
  -- Now, if the eaten cell was not visited in the last sprint, we can recurse
  by_cases hnmls : rs ∉ MR.sprints.getLast snnil
  · apply run_path_not_eaten_of_nice D p (n - 1) hnice rs _ rseaten'
    rw [run_path_recurrence] at rsmem; swap
    · assumption
    -- Lean weirdness work-around
    -- (for some reason "List.mem_append.mp rsmem" doesn't work)
    have := (@List.mem_append _ _ _ ((MR.sprints.getLast snnil).tail)).mp rsmem
    rcases this with lhs | rhs
    · assumption
    exact False.elim (hnmls (List.mem_of_mem_tail rhs))
  rename' hnmls => hmls; push_neg at hmls
  rw [List.getLast_eq_getElem] at hmls
  rw [getElem_congr_idx (by rw [make_run_sprints_length])] at hmls
  rcases List.getElem_of_mem hmls with ⟨j', j'lt, hnpj⟩
  rcases List.getElem_of_mem rseaten with ⟨k, klt, hk⟩
  -- Since we've already shown that 'loc rs' wasn't eaten last, k ≠ n
  have knen : k ≠ n := by
    contrapose! hnl
    symm at hnl; subst hnl
    rw [List.getLast_eq_getElem]
    convert hk.symm
    rw [make_run_eaten_length, Nat.add_one_sub_one]
  absurd hk; push_neg
  rw [← hnpj]
  apply make_run_runner_avoids_eaten_cells_of_nice
  · exact hnice
  · exact Nat.sub_one_lt hnnz
  · apply Nat.le_sub_one_of_lt
    rw [make_run_eaten_length] at klt
    exact lt_of_le_of_ne (Nat.le_of_lt_add_one klt) knen

-- Any RunPath is equal to the trace of the same length which begins at
-- 'run_start' and avoids all cells in the block list for that RunPath
-- Note that the block list used for the trace doesn't have to be the
-- last one used in the run path. Any later block list will also work.
-- The theorem is stated in this way because it allows us to recurse.
lemma run_path_eq_trace_of_nice (D : Devil) (p m n : Nat) (mle : m ≤ n - 1) (hnice : nice D p) :
  RunPath D p m =
  trace (RunPath D p m).length run_start (make_block_list D p n) := by
  -- Later in the argument we'll need to assume 0 < p,
  -- so deal with the degenerate case now.
  by_cases pz : p = 0
  · subst pz
    rw [run_path_pzero, List.length_singleton, trace_singleton]
  rename' pz => pnz; push_neg at pnz
  have ppos : 0 < p := Nat.pos_of_ne_zero pnz
  apply List.ext_getElem
  · rw [trace_length]
  intro k klt _
  let T := trace (RunPath D p m).length run_start (make_block_list D p n)
  change (RunPath D p m)[k] = T[k]
  -- Now handle the case where m = 0
  by_cases mz : m = 0
  · subst mz
    rw [getElem_congr_coll (run_path_of_length_zero D p)]
    rw [List.getElem_singleton]
    have hnnil : T ≠ [] := by
      apply List.ne_nil_of_length_eq_add_one
      rw [trace_length]
      exact run_path_length_of_length_zero _ _
    convert (trace_getElem_zero_of_nonnil _ _ _ hnnil).symm
    apply Nat.lt_one_iff.mp
    exact lt_of_lt_of_eq klt (run_path_length_of_length_zero D p)
  rename' mz => mnz; push_neg at mnz
  have mpos : 0 < m := Nat.pos_of_ne_zero mnz
  -- Generalize the recursion case, since we'll need it more than once
  have hrecurse : ∀ k' (k'lt : k' < (RunPath D p (m - 1)).length),
    (RunPath D p m)[k']'(by
      apply lt_of_lt_of_le k'lt
      exact run_path_length_non_decreasing _ _ _ mpos
    ) =
    T[k']'(by
      rw [trace_length]
      apply lt_of_lt_of_le k'lt
      exact run_path_length_non_decreasing _ _ _ mpos
    ) := by
    intro k' k'lt
    rw [getElem_congr_coll (run_path_recurrence D p m mpos)]
    rw [List.getElem_append_left k'lt]
    -- Rewrite 'T[k]' so the collections match and we can use 'congr'
    rw [← @List.getElem_take _ T (RunPath D p (m - 1)).length k']; swap
    · rwa [List.length_take, trace_length, min_eq_left]
      exact run_path_length_non_decreasing _ _ _ mpos
    congr
    rw [← trace_take]; swap
    · exact run_path_length_non_decreasing _ _ _ mpos
    rw [run_path_eq_trace_of_nice, trace_length]; swap
    · assumption
    exact le_trans (Nat.sub_le m 1) mle
  -- If the step indicated by 'k' doesn't fall in the last sprint, we can recurse
  by_cases klt' : k < (RunPath D p (m - 1)).length
  · exact hrecurse k klt'
  rename' klt' => lek; push_neg at lek
  rw [getElem_congr_coll (run_path_recurrence D p m mpos)]
  rw [List.getElem_append_right lek, List.getElem_tail]
  let i := (RunPath D p (m - 1)).length - 1
  have ilt : i < (RunPath D p m).length := by
    apply Nat.sub_one_lt_of_le (run_path_length_pos D p (m - 1))
    exact run_path_length_non_decreasing D p m mpos
  -- Split the trace so we can focus on the section that corresponds to the sprint
  have hsplit := trace_split i (RunPath D p m).length ilt run_start (make_block_list D p n)
  rw [getElem_congr_coll hsplit, List.getElem_append_right]; swap
  · rw [trace_length]
    exact le_trans (Nat.sub_le _ _) lek
  have hnnil : (make_run D p m).sprints ≠ [] := by
    apply List.ne_nil_of_length_pos
    rwa [make_run_sprints_length]
  -- Use the existing result to convert the last sprint into a raw sprint
  have hlast := make_run_sprints_get_last_eq_sprint D p m mpos
  -- Rewrite the last sprint as a raw sprint so we can eventually
  -- represent it as an equivalent trace.
  rw [getElem_congr_coll hlast]
  have npos : 0 < n := lt_of_lt_of_le mpos (le_trans mle (Nat.sub_le _ _))
  have mple : m - 1 ≤ n :=
    le_of_lt (lt_trans (Nat.sub_one_lt mnz) (Nat.lt_of_le_sub_one npos mle))
  -- Some useful abbreviations
  let fsmp := final_state (make_run D p (m - 1))
  let BL := make_block_list D p (m - 1)
  let N := (sprint p fsmp BL).length
  have seqt := sprint_eq_trace p N fsmp BL rfl
  -- Rewrite the sprint as a trace of the same length
  rw [getElem_congr_coll seqt]
  -- Now we can 'congr' but only once, since the block lists don't match yet
  congr 1; swap
  · -- First prove the indices are equal,
    -- since that is the simpler of the two branches
    rw [trace_length]; unfold i
    rw [Nat.sub_sub_right]; swap
    · exact (Nat.one_le_of_lt (run_path_length_pos D p (m - 1)))
    rw [Nat.sub_add_comm lek]
  -- Rewrite the trace on the left-hand side to use the later block list
  rw [trace_unchanged_of_block_unvisited_cells N fsmp BL (make_block_list D p n)]; swap
  · -- We've already proven that earlier block lists
    -- are subsets of later block lists, so apply that now.
    apply And.intro _ (make_block_list_subset D p (m - 1) n mple)
    intro rs rsmem
    -- We've proven that a sprint will avoid later block lists
    -- so use this fact to conclude that so will the equivalent trace.
    apply make_run_next_sprint_avoids_later_block_list D p (m - 1) n mple hnice rs
    rwa [next_sprint_make_run_def, seqt]
  -- Now that we've swapped the block list, we can 'congr' which will require us to
  -- show that the starting point and trace lengths match in order to close the goal.
  congr
  · -- First show that the lengths match
    unfold N i
    rw [run_path_length_recurrence D p m mpos, hlast, add_comm]
    rw [Nat.sub_sub_right]; swap
    · exact Nat.one_le_of_lt (run_path_length_pos D p (m - 1))
    rw [Nat.sub_one_add_one]; swap
    · exact Nat.ne_zero_of_lt (Nat.lt_add_right _ (sprint_length_lb _ _ _))
    rw [Nat.add_sub_cancel]
  · -- Now show that the starting points match
    -- We'll start by applying the recursion again
    have ilt' : i < (RunPath D p (m - 1)).length :=
      Nat.sub_lt (run_path_length_pos _ _ _) Nat.zero_lt_one
    rw [← hrecurse i ilt']
    rw [getElem_congr_coll (run_path_recurrence D p m mpos)]
    rw [List.getElem_append_left ilt']
    have hnnil' : RunPath D p (m - 1) ≠ [] := by
      apply List.ne_nil_of_length_pos
      exact run_path_length_pos _ _ _
    rw [← List.getLast_eq_getElem hnnil']
    -- TODO: It seems we shouldn't need to unfold final_state
    -- Maybe we should have a theorem for that instead?
    unfold fsmp final_state
    -- Use 'split_ifs' to handle the case where m - 1 = 0
    split_ifs with hsl
    · rw [make_run_sprints_length] at hsl
      convert (List.getLast_singleton (list_singleton_ne_nil run_start)).symm
      rw [hsl]
      exact run_path_of_length_zero D p
    push_neg at hsl
    rw [make_run_sprints_length] at hsl
    have mppos : 0 < m - 1 :=
      Nat.lt_of_le_of_ne (Nat.le_sub_one_of_lt mpos) hsl.symm
    -- Apply the run path recurrence a second time
    rw [List.getLast_congr _ _ (run_path_recurrence D p (m - 1) mppos)]; swap
    · apply List.append_ne_nil_of_left_ne_nil
      apply List.ne_nil_of_length_pos
      exact run_path_length_pos _ _ _
    rw [List.getLast_append_right]; swap
    · apply List.ne_nil_of_length_pos
      rw [List.length_tail]
      rw [make_run_sprints_get_last_eq_sprint D p (m - 1) mppos]
      -- To prove the last sprint has length greater than 1 we need to use
      -- the lower bound on sprint length combined with the fact that 0 < p.
      -- Note that *this* is why we had to handle the case where p = 0
      -- all the way back at the beginning of the proof!
      exact Nat.sub_pos_of_lt (lt_of_le_of_lt (Nat.one_le_of_lt ppos) (sprint_length_lb p _ _))
    rw [List.getLast_tail]

lemma run_path_x_nonneg (D : Devil) (p n : Nat) :
  ∀ rs ∈ (RunPath D p n), 0 ≤ rs.x := by
  intro rs rsmem
  by_cases nz : n = 0
  · subst nz
    rw [run_path_of_length_zero] at rsmem
    rw [List.mem_singleton.mp rsmem]
    unfold run_start; simp
  rename' nz => nnz; push_neg at nnz
  have npos : 0 < n := Nat.pos_of_ne_zero nnz
  -- Map 'rs' back into the run builder so we can use the previously-proven 'make_run_x_nonneg'
  rcases make_run_sprints_getElem_exists_of_run_path_mem D p n npos rs rsmem with ⟨i, ilt, j, jlt, hirs⟩
  exact hirs ▸ (make_run_x_nonneg D p n _ (List.getElem_mem ilt) _ (List.getElem_mem jlt))

-- If the runner ever wanders south of the x-axis, there must be some step
-- along their path where they are on the positive x-axis, facing south or west.
lemma run_path_intersects_xaxis_of_south (D : Devil) (p n : Nat) (hnice : nice D p) :
  ∀ (j : Nat) (jlt : j < (RunPath D p n).length), (RunPath D p n)[j].y < 0 →
  ∃ (i : Nat) (ilt : i < j), 0 ≤ (RunPath D p n)[i].x ∧ (RunPath D p n)[i].y = 0 ∧
  ((RunPath D p n)[i].u = uvec_down ∨ (RunPath D p n)[i].u = uvec_left) := by
  intro j jlt rpjneg
  let BL := make_block_list D p (n + 1)
  let L := (RunPath D p n).length
  let T := trace (j + 1) run_start BL
  have hnnil : T ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [trace_length]
    exact Nat.add_one_pos _
  -- Rewrite the run path as a trace
  have htrace := run_path_eq_trace_of_nice D p n (n + 1) (by rw [Nat.add_one_sub_one]) hnice
  -- Define two points on the trace, rs₀ and rs₁, so we can use the intermediate value theorem
  let rs₀ := T[j]'(by
      rw [trace_length]
      exact Nat.lt_add_one _
    )
  have rs₀mem : rs₀ ∈ T :=
    List.getElem_mem (by rw [trace_length]; exact Nat.lt_add_one _)
  let rs₁ := run_start
  have rs₁mem : rs₁ ∈ T :=
    List.mem_of_getElem (trace_getElem_zero_of_nonnil (j + 1) run_start BL hnnil)
  -- Use 'trace_take' to convert from a larger to smaller trace
  have htake := trace_take L run_start BL (j + 1) (Nat.add_one_le_of_lt jlt)
  have yle : rs₀.y ≤ -1 := by
    unfold rs₀ T
    rw [getElem_congr_coll htake, List.getElem_take, ← Int.zero_sub 1]
    apply Int.le_sub_one_of_lt
    convert rpjneg
    exact htrace.symm
  have ley : -1 ≤ rs₁.y := by
    unfold rs₁ run_start; simp
  -- Use the intermediate value theorem to get a point on the trace with y = -1
  rcases trace_intermediate_value_y (j + 1) run_start BL rs₀ rs₁ rs₀mem rs₁mem (-1) yle ley with ⟨rs₂, rs₂mem, rs₂y⟩
  rcases List.getElem_of_mem rs₂mem with ⟨k₀, k₀lt, hk₀rs⟩
  -- Now we need to get the *first* step with y < 0
  let k₁ := (find_first (fun i ↦ T[i].y < 0)
    (Nat.ne_zero_of_lt (List.length_pos_of_ne_nil hnnil))).val
  have k₁lt : k₁ < T.length := Fin.prop _
  have k₁lt' : k₁ < j + 1 := by
    unfold T at k₁lt
    rwa [trace_length] at k₁lt
  have hk₁y : T[k₁].y < 0 := by
    apply find_first_is_sat (fun i ↦ T[i].y < 0)
    use ⟨k₀, k₀lt⟩; simp
    rw [hk₀rs, rs₂y]
    norm_num
  have k₁nz : k₁ ≠ 0 := by
    intro k₁z
    absurd hk₁y
    rw [getElem_congr_idx k₁z]
    rw [trace_getElem_zero_of_nonnil (j + 1) run_start BL hnnil]
    unfold run_start; simp
  have k₁pos : 0 < k₁ := Nat.pos_of_ne_zero k₁nz
  -- Let 'i' be the step just before T[k₁]
  -- This will be the step that satisfies our goal
  -- Note that T[i].y = 0 since T[k₁] is the first step with y < 0
  let i := k₁ - 1
  have ilt : i < j := by
    apply lt_of_lt_of_le (Nat.sub_one_lt k₁nz)
    exact Nat.le_of_lt_add_one k₁lt'
  have ilt' : i < T.length := by
    unfold T
    rw [trace_length]
    exact lt_trans ilt (Nat.lt_add_one _)
  -- If T[i].y < 0, that violates 'find_first_is_first'
  have hleiy : 0 ≤ (T[i]'ilt').y := by
    by_contra! h
    absurd Fin.le_iff_val_le_val.mp (find_first_is_first (fun i ↦ T[i].y < 0) ⟨i, ilt'⟩ h); simp
    exact Nat.sub_one_lt k₁nz
  -- We'll need this inequality to evaluate 'natAbs' below
  have iyltky : (T[k₁]'k₁lt).y ≤ (T[i]'ilt').y :=
    le_of_lt (lt_of_lt_of_le hk₁y hleiy)
  -- Prove the relationship between T[k₁] and T[i]
  have hns : T[k₁]'k₁lt = next_step BL (T[i]'ilt') :=
    trace_getElem_recurrence' (j + 1) run_start BL k₁ k₁pos k₁lt'
  -- Show that if T[i].y ≥ 1, the distance between T[i] and T[k₁] is too great
  -- Therefore, T[i].y = 0
  have hiyz : (T[i]'ilt').y = 0 := by
    symm
    apply eq_of_le_of_not_lt hleiy
    intro iypos
    absurd next_step_dist_le_one BL (T[i]'ilt'); push_neg
    rw [← hns]
    apply lt_max_of_lt_right
    unfold loc; simp
    apply Int.ofNat_lt.mp
    rw [← Int.eq_natAbs_of_nonneg (Int.sub_nonneg.mpr iyltky), Int.natCast_one]
    apply Int.lt_sub_left_of_add_lt
    apply lt_of_le_of_lt (Int.add_one_le_of_lt hk₁y) iypos
  -- Prove equality between the RunPath and trace element
  have hrpi : (RunPath D p n)[i] = T[i] := by
    unfold T
    rw [getElem_congr_coll htrace, getElem_congr_coll htake, List.getElem_take]
  -- Use all the facts we know about 'i' so far
  use i, ilt, run_path_x_nonneg D p n _ (List.getElem_mem _)
  rw [hrpi]
  use hiyz
  -- Now we just need to consider the four possible values of T[i].u
  -- and show that only two don't lead to a contradiction.
  let u := T[i].u
  have leiys := le_trans hleiy (Int.le_add_of_nonneg_right Int.one_nonneg)
  rcases Finset.mem_insert.mp (uvec_finset_mem u) with hup | hrest
  · -- Show that we couldn't have moved down if we started facing up
    absurd hk₁y; push_neg
    rw [hns]
    unfold next_step
    unfold u at hup
    split_ifs with h₀ h₁
    · unfold turn_right; simpa
    · unfold move_forward; simp
      rw [hup]
      unfold uvec_up; simpa
    · unfold turn_left; simp
      rw [hup]
      unfold uvec_up; simpa
  rcases Finset.mem_insert.mp hrest with hdown | hrest
  · left; assumption
  rcases Finset.mem_insert.mp hrest with hleft | hright
  · right; assumption
  · -- Show that we couldn't have moved down if we started facing right
    have hright' : T[i].u = uvec_right := Finset.mem_singleton.mp hright
    absurd hk₁y; push_neg
    rw [hns]
    unfold next_step
    split_ifs with h₀ h₁
    · unfold turn_right; simpa
    · unfold move_forward; simp
      rw [hright']
      unfold uvec_right; simpa
    · unfold turn_left; simp
      rw [hright']
      unfold uvec_right; simpa

-- If the runner is ever on the positive x-axis facing west,
-- it was previously on the positive x-axis facing south
lemma run_path_xaxis_west_has_earlier_xaxis_south (D : Devil) (p n : Nat) (hnice : nice D p) :
  ∀ j (jlt : j < (RunPath D p n).length),
  0 ≤ (RunPath D p n)[j].x ∧ (RunPath D p n)[j].y = 0 ∧ (RunPath D p n)[j].u = uvec_left →
  ∃ i, ∃ (ilt : i < j),
  0 ≤ ((RunPath D p n)[i]'(lt_trans ilt jlt)).x ∧
  ((RunPath D p n)[i]'(lt_trans ilt jlt)).y = 0 ∧
  ((RunPath D p n)[i]'(lt_trans ilt jlt)).u = uvec_down := by
  intro j jlt ⟨hjxpos, hjyz, hjuleft⟩
  let BL := make_block_list D p (n + 1)
  let L := (RunPath D p n).length
  let T := trace (j + 1) run_start BL
  have Lpos : 0 < L := run_path_length_pos D p n
  have hnnil : T ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [trace_length]
    exact Nat.add_one_pos _
  -- Define a function that checks a step of the run path
  -- to see if it meets the requirements of 'j'
  let f : Fin L → Prop :=
    fun i ↦ 0 ≤ (RunPath D p n)[i].x ∧ (RunPath D p n)[i].y = 0 ∧ (RunPath D p n)[i].u = uvec_left
  -- Prove that f is satisfied by j
  have hsat : ∃ j, f j := by
    use ⟨j, jlt⟩
    exact ⟨hjxpos, hjyz, hjuleft⟩
  -- We'll use j' for the rest of the proof instead of j
  let j' := (find_first f (Nat.ne_zero_of_lt Lpos)).val
  let j'lt : j' < L := Fin.prop _
  have : f ⟨j', j'lt⟩ :=
    find_first_is_sat f hsat
  have hj'xpos : 0 ≤ (RunPath D p n)[j'].x :=
    (find_first_is_sat f hsat).1
  have hj'yz : (RunPath D p n)[j'].y = 0 :=
    (find_first_is_sat f hsat).2.1
  have hj'uleft : (RunPath D p n)[j'].u = uvec_left :=
    (find_first_is_sat f hsat).2.2
  have j'le : j' ≤ j := by
    exact Fin.le_iff_val_le_val.mp (find_first_is_first f ⟨j, jlt⟩ ⟨hjxpos, hjyz, hjuleft⟩)
  -- Rewrite the run path as a trace
  have htrace := run_path_eq_trace_of_nice D p n (n + 1) (by rw [Nat.add_one_sub_one]) hnice
  have j'nz : j' ≠ 0 := by
    intro j'z
    absurd hj'uleft; push_neg
    rw [getElem_congr_idx j'z, getElem_congr_coll htrace]
    rw [trace_getElem_zero_of_nonnil]; swap
    · apply List.ne_nil_of_length_pos
      rwa [trace_length]
    unfold run_start uvec_up uvec_left; simp
  have j'pos : 0 < j' := Nat.pos_of_ne_zero j'nz
  -- Write step j' in terms of the previous step
  have hns := trace_getElem_recurrence' L run_start BL j' (Nat.pos_of_ne_zero j'nz) j'lt
  have huns := congrArg (undo_next_step BL) hns
  have j'plt : j' - 1 < L :=
    lt_trans (Nat.sub_lt j'pos Nat.zero_lt_one) j'lt
  let rs := (trace L run_start BL)[j' - 1]'(by rwa [trace_length])
  have hvalid := run_start_valid_of_nice D p hnice (n + 1)
  -- In order to use 'undo_next_step' we need to show that the
  -- wall next to 'rs' is in-fact a wall.
  have hblocked : left_of_runner rs ∈ BL :=
    trace_wall_blocked_of_valid L run_start BL hvalid rs (List.getElem_mem _)
  -- We also need to show that 'rs' is not blocked
  have hnotblock : (loc rs) ∉ BL :=
    trace_avoids_blocked L run_start BL hvalid.1 rs (List.getElem_mem _)
  rw [next_step_undo_cancel _ _ hnotblock hblocked] at huns
  unfold rs at huns
  rw [← getElem_congr_coll htrace] at huns; swap; · exact j'lt
  rw [← getElem_congr_coll htrace] at huns; swap; · exact j'plt
  unfold undo_next_step at huns
  split_ifs at huns with h₀ h₁
  · -- If the move from 'rs' was a right turn, then
    -- rs was facing south, which satisfies the goal
    use (j' - 1)
    use lt_of_lt_of_le (Nat.sub_lt j'pos Nat.zero_lt_one) j'le
    rw [← huns]
    constructor
    · convert hj'xpos using 1
    constructor
    · convert hj'yz using 1
    · unfold undo_turn_right uvec_down; simp
      rw [hj'uleft]
      exact ⟨rfl, rfl⟩
  · -- If the move from 'rs' was a forward step, that contradicts
    -- the fact that rs was the first west-facing step on the x-axis
    -- First show that j'-1 also satisfies f
    have rssat : f ⟨j' - 1, j'plt⟩ := by
      unfold f; simp
      rw [← huns]
      unfold undo_move_forward; simp
      constructor
      · rw [hj'uleft]
        apply le_trans _ hj'xpos
        unfold uvec_left; simp
      constructor
      · convert hj'yz using 1
        rw [hj'uleft]
        unfold uvec_left; simp
      · exact hj'uleft
    -- Now demonstrate the contradiction
    absurd Fin.le_iff_val_le_val.mp (find_first_is_first f ⟨j' - 1, j'plt⟩ rssat); simp
    exact Nat.sub_lt (Nat.pos_of_ne_zero j'nz) (Nat.one_pos)
  · -- If the move from 'rs' was a left turn, then rs.y = -1 and we can
    -- use 'run_path_intersects_xaxis_of_south' to find either a previous
    -- step which satisfies the goal, or a previous step that was facing
    -- west on the x-axis (a contradiction)
    have hj'pyneg : (RunPath D p n)[j' - 1].y < 0 := by
      rw [← huns]
      unfold undo_turn_left; simp
      rw [hj'uleft, hj'yz]
      unfold uvec_left; simp
    rcases run_path_intersects_xaxis_of_south D p n hnice (j' - 1) j'plt hj'pyneg with ⟨i, ilt, hinn, hiyz, hiu⟩
    have ilt' : i < j' :=
      lt_trans ilt (Nat.sub_lt (Nat.pos_of_ne_zero j'nz) (Nat.one_pos))
    rcases hiu with hsouth | hwest
    · -- If on step 'i' the runner is on the x-axis facing south, we have our solution
      use i, lt_of_lt_of_le ilt' j'le
    -- Otherwise demonstrate a contradiction
    absurd Fin.le_iff_val_le_val.mp (find_first_is_first f ⟨i, lt_trans ilt' j'lt⟩ ⟨hinn, hiyz, hwest⟩); simp
    exact ilt'

-- If the run path loops, there is some step in the path on the
-- positive x-axis, facing south.
lemma run_path_xaxis_south_of_path_loops (D : Devil) (p n : Nat) (hnice : nice D p) :
  list_has_dupes (RunPath D p n) → ∃ rs ∈ (RunPath D p n),
  0 ≤ rs.x ∧ rs.y = 0 ∧ rs.u = uvec_down := by
  intro hdupes
  let ⟨_, _, _, blt, _⟩ := hdupes
  let BL := make_block_list D p (n + 1)
  let L := (RunPath D p n).length
  let T := trace L run_start BL
  have Lpos : 0 < L :=
    lt_of_le_of_lt (Nat.zero_le _) blt
  have hnnil : T ≠ [] := by
    apply List.ne_nil_of_length_pos
    rwa [trace_length]
  let i := (find_first_dupe T hnnil).1
  have ilt : i < T.length := Fin.prop _
  have ilt' : i < L := by
    unfold T at ilt
    rwa [trace_length] at ilt
  -- Get the equivalent trace
  have htrace := run_path_eq_trace_of_nice D p n (n + 1) (by rw [Nat.add_one_sub_one]) hnice
  have hvalid := run_start_valid_of_nice D p hnice (n + 1)
  have hdupes' : list_has_dupes T := by rwa [htrace] at hdupes
  -- As previously proven, the first repeated state is 'run_start', so T[i] = run_start
  have hTi : T[i] = run_start := trace_start_is_first_dupe L run_start BL hdupes' hvalid
  have ipos : 0 < i := by
    rcases first_dupe_is_dupe _ hdupes' with ⟨_, hlt, _⟩
    exact lt_of_le_of_lt (Nat.zero_le _) hlt
  have inz : i ≠ 0 := Nat.ne_zero_of_lt ipos
  have iplt : i - 1 < L :=
    lt_of_le_of_lt (Nat.sub_le _ _) ilt'
  have := congrArg (undo_next_step BL) ((trace_getElem_recurrence' L run_start BL i ipos ilt') ▸ hTi)
  -- In order to use 'undo_next_step' we need to show that the
  -- wall next to T[i-1] is in-fact a wall.
  have hblocked : left_of_runner T[i - 1] ∈ BL :=
    trace_wall_blocked_of_valid L run_start BL hvalid _ (List.getElem_mem _)
  -- We also need to show that 'T[i-1]' is not blocked
  have hnotblock : (loc T[i - 1]) ∉ BL :=
    trace_avoids_blocked L run_start BL hvalid.1 _ (List.getElem_mem _)
  rw [next_step_undo_cancel _ _ hnotblock hblocked] at this
  -- Applying 'undo_next_step' to 'run_start' will result in one of three
  -- possible states. One is impossible and the other two imply the goal.
  unfold undo_next_step at this
  split_ifs at this with h₀ h₁
  · -- If the path turned right to return to 'run_start', it was
    -- previously on the x-axis facing west. That means we can use
    -- 'run_path_xaxis_west_has_earlier_xaxis_south' to close the goal.
    unfold undo_turn_right run_start uvec_up at this; simp at this
    have hxnonneg : 0 ≤ (RunPath D p n)[i - 1].x := by
      rw [getElem_congr_coll htrace, this]
    have hyz : (RunPath D p n)[i - 1].y = 0 := by
      rw [getElem_congr_coll htrace, this]
    have hwest : (RunPath D p n)[i - 1].u = uvec_left := by
      rw [getElem_congr_coll htrace, this]
      unfold uvec_left; simp
    rcases run_path_xaxis_west_has_earlier_xaxis_south
      D p n hnice (i - 1) iplt ⟨hxnonneg, hyz, hwest⟩ with ⟨j, jlt, _⟩
    have jlt' : j < L := lt_trans jlt iplt
    use (RunPath D p n)[j], List.getElem_mem jlt'
  · -- If the path moved forward to return to 'run_start', it was
    -- previously south of the x-axis. That means we can use
    -- 'run_path_intersects_xaxis_of_south' to show that the path
    -- was previously on the x-axis.
    unfold undo_move_forward run_start uvec_up at this; simp at this
    have hyneg : (RunPath D p n)[i - 1].y < 0 := by
      rw [getElem_congr_coll htrace, this]; simp
    rcases run_path_intersects_xaxis_of_south D p n hnice (i - 1) iplt hyneg with ⟨j, jlt, hxnonneg, hyz, hudir⟩
    have jlt' : j < L := lt_trans jlt iplt
    rcases hudir with lhs | rhs
    · -- If the path was previously on the x-axis facing south, that closes the goal
      use (RunPath D p n)[j], List.getElem_mem jlt'
    · -- Otherwise we can find some earlier step on the path where
      -- the runner *was* on the x-axis facing south
      rcases run_path_xaxis_west_has_earlier_xaxis_south
        D p n hnice j jlt' ⟨hxnonneg, hyz, rhs⟩ with ⟨k, klt, _⟩
      have klt' : k < L := lt_trans klt jlt'
      use (RunPath D p n)[k], List.getElem_mem klt'
  · -- Lastly, if the path returned to 'run_start' by making a left turn
    -- it was previously west of the y-axis, which is impossible.
    unfold undo_turn_left run_start uvec_up at this; simp at this
    absurd run_path_x_nonneg D p n (RunPath D p n)[i - 1] (List.getElem_mem iplt); push_neg
    rw [getElem_congr_coll htrace, this]; simp
