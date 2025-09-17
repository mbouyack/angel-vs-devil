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
  u := 0
  v := 1
  unit := by simp

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
  ppos : 0 < p
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
def west_wall (p n : Nat) :=
  List.map (fun i : Nat ↦ (-1, (i : Int))) (List.range (p * n + 1))

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
  ∀ i (_ : i ≤ p * n), (-1, Int.ofNat i) ∈ west_wall p n := by
  intro i ile
  unfold west_wall
  apply List.mem_iff_getElem.mpr
  use i, (by rw [List.length_map, List.length_range]; exact Nat.lt_add_one_of_le ile)
  rw [List.getElem_map, List.getElem_range]; rfl

-- Get the next sprint to be added to the builder
-- Note that for the purposes of finding the next sprint, a wall of cells
-- is added along the y-axis that prevent the runner from ever moving that direction.
def next_sprint {p : Nat} (S : RunBuilder p) : List RunState :=
  sprint p (final_state S) (List.union S.eaten (west_wall p S.eaten.length))

lemma next_sprint_nonnil {p : Nat} (S : RunBuilder p) :
  next_sprint S ≠ [] := by
  apply sprint_nonnil_of_ppos
  exact S.ppos

-- The initial state of the next sprint is the
-- same as the final state of the builder
lemma next_sprint_first_eq_builder_last {p : Nat} (S : RunBuilder p) :
  final_state S = (next_sprint S)[0]'(by
    apply List.length_pos_of_ne_nil
    exact sprint_nonnil_of_ppos p (final_state S) _ S.ppos
  ) := by
  unfold next_sprint
  rw [sprint_getElem_zero_of_ppos]
  exact S.ppos

-- Every element of 'next_sprint' is close to its head
lemma next_sprint_close_mem_head {p : Nat} (S : RunBuilder p) :
  ∀ x ∈ (next_sprint S),
  close p (loc x) (loc ((next_sprint S).head (next_sprint_nonnil _))) := by
  intro x xmem
  apply sprint_close_mem_head
  · exact S.ppos
  · exact xmem

-- The last cell of the next sprint is "close" to the
-- last cell of the builder journey.
lemma next_sprint_last_close_builder_last {p : Nat} (S : RunBuilder p) :
  close p (loc ((next_sprint S).getLast (next_sprint_nonnil _))) (last S.A) := by
  rw [← final_state_loc_eq_journey_last, next_sprint_first_eq_builder_last S]
  rw [close_comm, List.getElem_zero]
  exact sprint_close_first_last _ S.ppos _ _

-- Define the base case for our builder construction:
-- The journey has no steps, there are no sprints, and the
-- Devil has only eaten one cell
def empty_builder (D : Devil) (p : Nat) (ppos : 0 < p) : RunBuilder p where
  D := D
  A := NoSteps p
  eaten := [response D (NoSteps p)]
  sprints := []
  nonnil := fun _ hs ↦ False.elim (List.not_mem_nil hs)
  ppos := ppos
  samelen := by rw [nosteps_steps, List.length_nil]
  origin := fun snn ↦ False.elim (snn rfl)
  dest := fun snn ↦ False.elim (snn rfl)

lemma empty_builder_sprints (D : Devil) (p : Nat) (ppos : 0 < p) :
  (empty_builder D p ppos).sprints = [] := by
  unfold empty_builder; dsimp

lemma empty_builder_journey (D : Devil) (p : Nat) (ppos : 0 < p) :
  (empty_builder D p ppos).A = NoSteps p := by
  unfold empty_builder; dsimp

lemma empty_builder_eaten (D : Devil) (p : Nat) (ppos : 0 < p) :
  (empty_builder D p ppos).eaten = [response D (NoSteps p)] := by
  unfold empty_builder; dsimp

-- Construct the journey that corresponds to appending the
-- last location of the next sprint
def builder_journey_extend {p : Nat} (S : RunBuilder p) : Journey p :=
  append_journey S.A (loc ((next_sprint S).getLast (sprint_nonnil_of_ppos p _ _ S.ppos)))
  ((close_comm p _ _).mp (next_sprint_last_close_builder_last S))

-- Why doesn't this theorem aleady exist?
-- TODO: If this is needed elsewhere, move it into 'Basic.lean' or 'Util.lean'
lemma list_singleton_ne_nil {α : Type} (x : α) : [x] ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [List.length_singleton]
  norm_num

/- Add another sprint to a 'RunBuilder'
   Originally this was named 'make_run' and used recursion to
   directly construct the RunBuilder (rather than taking 'S' as an argument).
   Unfortunately this caused timeouts, so now 'make_run' handles the recursion
   separately and wraps 'extend_run' -/
def extend_run (D : Devil) (p : Nat) (ppos : 0 < p) (S : RunBuilder p) : RunBuilder p:=
  RunBuilder.mk D
    (builder_journey_extend S)
    (S.eaten ++ [response D (builder_journey_extend S)])
    (S.sprints ++ [next_sprint S])
    ppos
    (by
      intro s smem
      rcases List.mem_append.mp smem with lhs | rhs
      · exact RunBuilder.nonnil _ s lhs
      · exact (List.mem_singleton.mp rhs) ▸ (sprint_nonnil_of_ppos p _ _ ppos)
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
def make_run (D : Devil) (p n : Nat) (ppos : 0 < p) : RunBuilder p :=
  if n = 0 then empty_builder D p ppos else
  extend_run D p ppos (make_run D p (n - 1) ppos)

-- A run of length zero is represented by the 'empty_builder'
lemma make_run_eq_empty_of_length_zero (D : Devil) (p : Nat) (ppos : 0 < p) :
  make_run D p 0 ppos = empty_builder D p ppos := by
  unfold make_run
  rw [if_pos rfl]

-- The recursive definition of the runner's journey:
-- Append the last cell of the 'next_sprint' to the journey to extend it.
lemma make_run_journey_recurrence (D : Devil) (p n : Nat) (ppos : 0 < p) (npos : 0 < n) :
  (make_run D p n ppos).A =
  append_journey
    (make_run D p (n - 1) ppos).A
    (loc ((next_sprint (make_run D p (n - 1) ppos)).getLast (sprint_nonnil_of_ppos p _ _ ppos)))
    ((close_comm p _ _).mp (next_sprint_last_close_builder_last (make_run D p (n - 1) ppos))) := by
  nth_rw 1 [make_run]
  rw [if_neg (Nat.ne_zero_iff_zero_lt.mpr npos)]
  rfl

-- The recursive definition of the runner's sprints
-- Just append the 'next_sprint' to the existing list of sprints.
lemma make_run_sprints_recurrence (D : Devil) (p n : Nat) (ppos : 0 < p) (npos : 0 < n) :
  (make_run D p n ppos).sprints =
  (make_run D p (n - 1) ppos).sprints ++ [(next_sprint (make_run D p (n - 1) ppos))] := by
  nth_rw 1 [make_run]
  rw [if_neg (Nat.ne_zero_iff_zero_lt.mpr npos)]
  rfl

-- The recursive definition of the cells eaten in response to the runner
-- This is just the devil's response to the new journey append to the old list
lemma make_run_eaten_recurrence (D : Devil) (p n : Nat) (ppos : 0 < p) (npos : 0 < n) :
  (make_run D p n ppos).eaten =
  (make_run D p (n - 1) ppos).eaten ++ [response D (make_run D p n ppos).A] := by
  nth_rw 1 [make_run]
  rw [if_neg (Nat.ne_zero_iff_zero_lt.mpr npos)]
  rw [make_run_journey_recurrence D p n ppos npos];
  rfl

-- The number of steps in the journey is just 'n'
lemma make_run_journey_steps (D : Devil) (p n : Nat) (ppos : 0 < p) :
  steps (make_run D p n ppos).A = n := by
  by_cases hnz : n = 0
  · subst hnz
    rw [make_run_eq_empty_of_length_zero, empty_builder_journey, nosteps_steps]
  rename' hnz => hnnz; push_neg at hnnz
  have hpos : 0 < n := Nat.zero_lt_of_ne_zero hnnz
  rwa [make_run_journey_recurrence, append_steps, make_run_journey_steps, Nat.sub_one_add_one hnnz]

-- The number of eaten cells is just n+1
lemma make_run_eaten_length (D : Devil) (p n : Nat) (ppos : 0 < p) :
  (make_run D p n ppos).eaten.length = n + 1 := by
  by_cases hnz : n = 0
  · subst hnz
    rw [make_run_eq_empty_of_length_zero, empty_builder_eaten, List.length_singleton]
  rename' hnz => hnnz; push_neg at hnnz
  have npos : 0 < n := Nat.ne_zero_iff_zero_lt.mp hnnz
  rw [make_run_eaten_recurrence D p n ppos npos, List.length_append]
  rw [List.length_singleton]
  apply Nat.add_one_inj.mpr
  nth_rw 2 [← Nat.sub_one_add_one hnnz]
  exact make_run_eaten_length D p (n - 1) ppos

-- The number of sprints in the RunBuilder is 'n'
lemma make_run_sprints_length (D : Devil) (p n : Nat) (ppos : 0 < p) :
  (make_run D p n ppos).sprints.length = n := by
  rw [← (make_run D p n ppos).samelen]
  exact make_run_journey_steps _ _ _ _

-- The subjourney of a 'make_run' journey is just the
-- 'make_run' journey of that length
lemma make_run_subjourney (D : Devil) (p m n : Nat) (ppos : 0 < p) (mlt : m < n + 1) :
  subjourney (make_run D p n ppos).A m (by rwa [make_run_journey_steps]) =
  (make_run D p m ppos).A := by
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
  have hrecurse := make_run_journey_recurrence D p n ppos (Nat.pos_of_ne_zero nnz)
  rw [subjourney_congr_journey hrecurse, append_subjourney]
  · -- Do the recursion
    exact make_run_subjourney D p m (n - 1) ppos (by rwa [Nat.sub_one_add_one nnz])

-- The first 'm+1' cells eaten in response to the runner moving 'n' steps
-- will correspond to all the cells eaten in response to the runner moving
-- 'm' steps.
lemma make_run_eaten_take (D : Devil) (p m n : Nat) (ppos : 0 < p) (mlt : m < n + 1) :
  (make_run D p n ppos).eaten.take (m+1) = (make_run D p m ppos).eaten := by
  -- First handle the case where m = n
  by_cases hmn : m = n
  · subst hmn
    convert List.take_length
    exact (make_run_eaten_length D p m ppos).symm
  push_neg at hmn
  -- If m ≠ n, n ≠ 0
  have nnz : n ≠ 0 :=
    fun nz ↦ False.elim (Nat.not_lt_zero _ (nz ▸ (lt_of_le_of_ne (Nat.le_of_lt_add_one mlt) hmn)))
  -- Prove a tighter bound on m
  have mlt' : m < n :=
    lt_of_le_of_ne (Nat.le_of_lt_add_one mlt) hmn
  have hrecurse := make_run_eaten_recurrence D p n ppos (Nat.pos_of_ne_zero nnz)
  rw [hrecurse, List.take_append_of_le_length]
  · -- Do the recursion
    exact make_run_eaten_take D p m (n - 1) ppos (by rwa [Nat.sub_one_add_one nnz])
  -- Prove the remaining bounds check
  rw [make_run_eaten_length, Nat.sub_one_add_one nnz]
  exact Nat.add_one_le_of_lt mlt'

-- The first 'm' sprints of a run of 'n' sprints are the same as
-- the full list of sprints in a run of 'm' sprints
lemma make_run_sprints_take (D : Devil) (p m n : Nat) (ppos : 0 < p) (mlt : m < n + 1) :
  (make_run D p n ppos).sprints.take m = (make_run D p m ppos).sprints := by
  -- First handle the case where m = n
  by_cases hmn : m = n
  · subst hmn
    convert List.take_length
    exact (make_run_sprints_length D p m ppos).symm
  push_neg at hmn
  -- If m ≠ n, n ≠ 0
  have nnz : n ≠ 0 :=
    fun nz ↦ False.elim (Nat.not_lt_zero _ (nz ▸ (lt_of_le_of_ne (Nat.le_of_lt_add_one mlt) hmn)))
  -- Prove a tighter bound on m
  have mlt' : m < n :=
    lt_of_le_of_ne (Nat.le_of_lt_add_one mlt) hmn
  have hrecurse := make_run_sprints_recurrence D p n ppos (Nat.pos_of_ne_zero nnz)
  rw [hrecurse, List.take_append_of_le_length]
  · -- Do the recursion
    exact make_run_sprints_take D p m (n - 1) ppos (by rwa [Nat.sub_one_add_one nnz])
  -- Prove the remaining bounds check
  rw [make_run_sprints_length]
  apply Nat.le_of_lt_add_one
  rwa [Nat.sub_one_add_one nnz]

-- Extract the runner's journey from the RunBuilder
-- TODO: Is there any reason for this actually?
def Runner (D : Devil) (p n : Nat) (ppos : 0 < p) : Journey p :=
  (make_run D p n ppos).A

-- Each cell in the runner's journey (other than the first)
-- corresponds to the final location of the previous sprint.
lemma make_run_journey_cell (D : Devil) (p n : Nat) (ppos : 0 < p) :
  ∀ i (ilt : i < n),
  cell (make_run D p n ppos).A (i + 1)
    (by rw [make_run_journey_steps]; exact Nat.add_one_lt_add_one_iff.mpr ilt) =
  (loc (((make_run D p n ppos).sprints[i]'
    (by rwa [make_run_sprints_length])).getLast
      (by
        apply (make_run D p n ppos).nonnil
        apply List.getElem_mem
      ))) := by
  intro i ilt
  -- Prove sprints is nonnil so we can use RunBuilder.dest below
  have hsnn : (make_run D p (i + 1) ppos).sprints ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [make_run_sprints_length]
    exact Nat.add_one_pos _
  have islt : i + 1 < n + 1 :=
    Nat.add_one_lt_add_one_iff.mpr ilt
  rw [← subjourney_last_cell, make_run_subjourney]; swap
  · assumption -- bounds check
  rw [((make_run D p (i + 1) ppos).dest hsnn).symm]
  congr
  -- Rewrite the sprints of the sub-run as 'take' of the sprints of the full run.
  rw [List.getLast_congr _ _ (make_run_sprints_take D p (i + 1) n ppos islt).symm]; swap
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
lemma make_run_eaten (D : Devil) (p n : Nat) (ppos : 0 < p) :
  ∀ i (ilt : i < n + 1),
  (make_run D p n ppos).eaten[i]'(by rwa [make_run_eaten_length]) =
  (response D (make_run D p i ppos).A) := by
  intro i ilt
  -- If i ≠ n, we can recurse
  by_cases ilt' : i < n
  · have npos : 0 < n := Nat.zero_lt_of_lt ilt'
    have nnz : n ≠ 0 := Nat.ne_zero_of_lt npos
    rw [getElem_congr_coll (make_run_eaten_recurrence D p n ppos npos)]
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
    have rwl : (make_run D p 0 ppos).eaten = [response D (NoSteps p)] := by
      rw [make_run_eq_empty_of_length_zero, empty_builder_eaten]
    have rwr : (make_run D p 0 ppos).A = (NoSteps p) := by
      rw [make_run_eq_empty_of_length_zero, empty_builder_journey]
    rw [getElem_congr_coll rwl, rwr, List.getElem_singleton]
  rename' iz => inz; push_neg at inz
  have ipos : 0 < i := Nat.zero_lt_of_ne_zero inz
  rw [getElem_congr_coll (make_run_eaten_recurrence D p i ppos ipos)]
  rw [List.getElem_append_right]; swap
  · -- Resolve bounds check
    rw [make_run_eaten_length, Nat.sub_one_add_one inz]
  rw [List.getElem_singleton]

-- Each sprint is created by calling 'next_sprint' on some shorter 'make_run'
lemma make_run_sprint (D : Devil) (p n : Nat) (ppos : 0 < p) :
  ∀ i (ilt : i < n),
  (make_run D p n ppos).sprints[i]'(by rwa [make_run_sprints_length]) =
  (next_sprint (make_run D p i ppos)) := by
  intro i ilt
  rw [getElem_congr_coll (make_run_sprints_recurrence D p n ppos (Nat.zero_lt_of_lt ilt))]
  by_cases ilt' : i < n - 1
  · rw [← List.getElem_append_left']; swap
    · rwa [make_run_sprints_length]
    · convert make_run_sprint D p (n-1) ppos i ilt'
  rename' ilt' => nple; push_neg at nple
  have inp := le_antisymm (Nat.le_sub_one_of_lt ilt) nple
  rw [List.getElem_append_right, List.getElem_singleton, inp]
  rwa [make_run_sprints_length]

-- Every element of a sprint is close to the head of that sprint
lemma make_run_close_sprint_mem_head (D : Devil) (p n : Nat) (ppos : 0 < p) :
  ∀ s, (smem : s ∈ (make_run D p n ppos).sprints) → ∀ x ∈ s,
  close p (loc x) (loc (s.head (RunBuilder.nonnil _ _ smem))) := by
  intro s smem x xmem
  rcases List.getElem_of_mem smem with ⟨i, ilt, rfl⟩
  rw [make_run_sprints_length] at ilt
  have nseq := make_run_sprint D p n ppos i ilt
  convert next_sprint_close_mem_head (make_run D p i ppos) x (nseq ▸ xmem)

-- The last element of each sprint equals the first element of the next
-- TODO: This seems longer than it should need to be.
-- Perhaps we're missing some useful 'sprints' theorems?
lemma make_run_sprint_last_eq_sprint_head (D : Devil) (p n : Nat) (ppos : 0 < p) :
  ∀ i (islt : i + 1 < n),
  ((make_run D p n ppos).sprints[i]'(by
    rw [make_run_sprints_length]; exact lt_trans (Nat.lt_add_one _) islt)).getLast
    (by apply RunBuilder.nonnil _ _ (List.getElem_mem _)) =
  ((make_run D p n ppos).sprints[i+1]'(by rwa [make_run_sprints_length])).head
    (by apply RunBuilder.nonnil _ _ (List.getElem_mem _)) := by
  intro i islt
  have nnz : n ≠ 0 := by
    intro nz; subst nz
    exact (Nat.not_lt_zero _) islt
  -- If i + 1 ≠ n - 1, we can close the goal with recursion
  by_cases islt' : i + 1 < n - 1
  · convert make_run_sprint_last_eq_sprint_head D p (n - 1) ppos i islt' using 2
    repeat
    rw [getElem_congr_coll (make_run_sprints_recurrence D p n ppos (Nat.pos_of_ne_zero nnz))]
    rw [← List.getElem_append_left']
  rename' islt' => nple; push_neg at nple
  have iseq := le_antisymm (Nat.le_sub_one_of_lt islt) nple
  rw [List.head_eq_getElem]
  rw [getElem_congr_coll (make_run_sprint D p n ppos (i+1) islt)]
  rw [← next_sprint_first_eq_builder_last]
  unfold final_state
  have lnz : (make_run D p (i + 1) ppos).sprints.length ≠ 0 := by
    rw [make_run_sprints_length]
    exact Nat.add_one_ne_zero _
  rw [dif_neg lnz]; congr
  have mrst := make_run_sprints_take D p (i + 1) n ppos (lt_trans islt (Nat.lt_add_one _))
  rw [← List.getLast_congr _ _ mrst]; swap
  · -- Resolve nil check
    intro hnil
    rcases List.take_eq_nil_iff.mp hnil with lhs | rhs
    · exact (Nat.add_one_ne_zero _) lhs
    · apply nnz
      rw [← make_run_sprints_length D p n ppos]
      exact List.length_eq_zero_iff.mpr rhs
  rw [List.getLast_eq_getElem, List.getElem_take]; congr
  rw [List.length_take_of_le, Nat.add_one_sub_one]
  rw [make_run_sprints_length]
  exact le_of_lt islt

-- Every element of a sprint is "close" to the corresponding journey cell
lemma make_run_sprint_mem_journey_cell_close (D : Devil) (p n : Nat) (ppos : 0 < p) :
  ∀ i (ilt : i < n), ∀ rs ∈ (make_run D p n ppos).sprints[i]'(by rwa [make_run_sprints_length]),
  close p (loc rs) (cell (make_run D p n ppos).A i
    (by rw [make_run_journey_steps]; exact lt_trans ilt (Nat.lt_add_one _))) := by
  intro i ilt rs hmem
  -- First handle the case where i = 0
  by_cases iz : i = 0
  · subst iz
    rw [journey_start]
    convert make_run_close_sprint_mem_head D p n ppos _ (List.getElem_mem _) rs hmem using 1
    have hnnil : (make_run D p n ppos).sprints ≠ [] := by
      apply List.ne_nil_of_length_pos
      rwa [make_run_sprints_length]
    rw [List.head_eq_getElem_zero, RunBuilder.origin _ hnnil]; rfl
  rename' iz => inz; push_neg at inz
  -- If i ≠ 0, swap in '(i-1)+1' for 'i' and rewrite with 'make_run_journey_cell'
  have iplt : i - 1 < n := by
    apply lt_of_le_of_lt _ ilt
    exact Nat.sub_le _ _
  have := make_run_journey_cell D p n ppos (i-1) iplt
  rw [cell_congr_idx _ (Nat.sub_one_add_one inz)] at this
  rw [this, make_run_sprint_last_eq_sprint_head]; swap
  · -- Resolve bounds check
    rwa [Nat.sub_one_add_one inz]
  apply make_run_close_sprint_mem_head D p n ppos
  · apply List.getElem_mem
  · convert hmem
    exact Nat.sub_one_add_one inz

-- List of blocked cells used to generate 'next_sprint (make_run D p n ppos)'
def make_block_list (D : Devil) (p n : Nat) (ppos : 0 < p) : List (Int × Int) :=
  List.union (make_run D p n ppos).eaten (west_wall p (make_run D p n ppos).eaten.length)

-- Expand the 'next_sprint' of a 'make_run' using 'make_block_list'
lemma next_sprint_make_run_def (D : Devil) (p n : Nat) (ppos : 0 < p) :
  next_sprint (make_run D p n ppos) =
  sprint p (final_state (make_run D p n ppos)) (make_block_list D p n ppos) := rfl

/- Note that it *is* possible to force the runner to remain on a blocked cell
   if the devil is not nice. Technically, even with a devil that isn't nice,
   the runner can never be forced onto a 'wall' cell (cells with x = -1, 0 ≤ y)
   but that proof is more difficult and we're only concerned with nice devils
   for this section of the proof so we can make our work easier by assuming such. -/
lemma make_run_next_sprint_avoids_blocked_of_nice (D : Devil) (p n : Nat) (ppos : 0 < p) (hnice : nice D p) :
  ∀ rs ∈ next_sprint (make_run D p n ppos), (loc rs) ∉ make_block_list D p n ppos := by
  intro rs rsmem lrsmem
  -- First handle the case where n = 0
  -- This mostly involves showing that the origin will never be on the block list
  by_cases nz : n = 0
  · subst nz
    apply sprint_avoids_blocked p _ (make_block_list D p 0 ppos) _ rs rsmem lrsmem
    rw [make_run_eq_empty_of_length_zero]
    rw [final_state_of_sprints_nil _ (empty_builder_sprints D p ppos)]
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
  have hsnnil : (make_run D p n ppos).sprints ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [make_run_sprints_length]
    exact Nat.pos_of_ne_zero nnz
  rw [next_sprint_make_run_def] at rsmem
  -- Use recursion to show that the run has thus far avoided blocked cells
  -- This will be required in order to use 'sprint_avoids_blocked'
  have hsafe : loc (final_state (make_run D p n ppos)) ∉ make_block_list D p (n - 1) ppos := by
    apply make_run_next_sprint_avoids_blocked_of_nice
    · assumption
    convert final_state_getLast_mem_of_nonnil (make_run D p n ppos) hsnnil
    rw [List.getLast_congr _ _ (make_run_sprints_recurrence D p n ppos (Nat.pos_of_ne_zero nnz))]; swap
    · apply List.append_ne_nil_of_right_ne_nil
      exact list_singleton_ne_nil _
    rw [List.getLast_append_right (list_singleton_ne_nil _)]
    exact (List.getLast_singleton (list_singleton_ne_nil _)).symm
  -- Strengthen the statement of 'hsafe' by including the devil's last response and
  -- an extra 'p' cells in the west wall. This section constitutes the majority of the proof.
  have hsafe' : loc (final_state (make_run D p n ppos)) ∉ make_block_list D p n ppos := by
    intro lfsmem
    rcases List.mem_union_iff.mp lfsmem with lhs | rhs
    · -- Handle the case where the final state is on the 'eaten' list
      rcases List.getElem_of_mem lhs with ⟨i, ilt, hi⟩
      rw [make_run_eaten_length] at ilt
      rw [getElem_congr_coll (make_run_eaten_recurrence D p n ppos (Nat.pos_of_ne_zero nnz))] at hi
      -- Handle the case where the final state was eaten last
      by_cases hin : i = n
      · rw [List.getElem_append_right] at hi; swap
        · rw [make_run_eaten_length, hin, Nat.sub_one_add_one nnz]
        -- Prove a bound needed for 'getElem_singleton'
        have lt1 : i - (make_run D p (n - 1) ppos).eaten.length < 1 := by
          rw [make_run_eaten_length, Nat.sub_one_add_one nnz, hin, Nat.sub_self]
          norm_num
        rw [List.getElem_singleton lt1, final_state_loc_eq_journey_last] at hi
        -- We will show that a journey cell is eaten, which is contradiction with 'hnice'
        apply not_nice_of_eats_journey_cell D p _ hnice
        use (make_run D p n ppos).A, n, n, le_refl n
        use (by rw [make_run_journey_steps]; exact Nat.lt_add_one _)
        have hsj := subjourney_full (make_run D p n ppos).A
        rw [subjourney_congr_idx _ (make_run_journey_steps D p n ppos)] at hsj
        rw [hsj]
        convert hi
        rw [last]
        congr
        rw [make_run_journey_steps]
      · rename' hin => inen; push_neg at inen
        -- If i ≠ n, we will show that the final state was on the old eaten list - a contradiction
        apply hsafe
        apply List.mem_union_iff.mpr; left
        have ilt' : i < (make_run D p (n - 1) ppos).eaten.length := by
          rw [make_run_eaten_length, Nat.sub_one_add_one nnz]
          exact lt_of_le_of_ne (Nat.le_of_lt_add_one ilt) inen
        rw [List.getElem_append_left ilt'] at hi
        exact List.mem_of_getElem hi
    · -- Now handle the case where the final state is a wall cell
      unfold west_wall at rhs
      rcases List.getElem_of_mem rhs with ⟨i, ilt, hi⟩
      rw [List.length_map, List.length_range, make_run_eaten_length] at ilt
      rw [List.getElem_map, final_state_loc_eq_journey_last] at hi
      -- Handle the case where 'i' is so large, it exceeds the bound proven in Bound.lean
      by_cases pni : p * n < i
      · apply (lt_self_iff_false n).mp
        nth_rw 2 [← make_run_journey_steps D p n ppos]
        apply journey_lb _ _ (lt_of_lt_of_le pni (le_trans _ (le_max_right _ _)))
        simp
        rw [← (Prod.ext_iff.mp hi).2, List.getElem_range]
        exact (le_refl i)
      rename' pni => ilepn; push_neg at ilepn
      · -- If i ≤ p * n, show that the final state was in the old west wall
        apply hsafe (List.mem_union_iff.mpr _); right
        rw [List.getElem_range] at hi
        rw [final_state_loc_eq_journey_last, ← hi]
        apply west_wall_mem
        rwa [make_run_eaten_length, Nat.sub_one_add_one nnz]
  exact sprint_avoids_blocked p _ _ hsafe' rs rsmem lrsmem

lemma make_run_journey_allowed_of_nice (D : Devil) (p n : Nat) (ppos : 0 < p) (hnice : nice D p) :
  allowed D (make_run D p n ppos).A := by
  let MR := make_run D p n ppos
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
  -- Re-write the left-hand side using the journey recurrence
  have lhs_rw : subjourney MR.A i (lt_trans ilt jlt) =
    subjourney (make_run D p (n - 1) ppos).A i (by
      rwa [make_run_journey_steps, Nat.sub_one_add_one]
      exact Nat.ne_zero_of_lt ilt'
    ) := by
    rw [subjourney_congr_journey (make_run_journey_recurrence D p n ppos npos)]
    rw [append_subjourney]
  -- If j ≠ n we can recurse, so handle that case first
  by_cases hjnn : n ≠ j
  · -- Now apply the journey recurrence on the right and recurse
    rw [lhs_rw, cell_congr_journey (make_run_journey_recurrence D p n ppos npos)]
    rw [append_cell_ne_last]; swap
    · rw [make_run_journey_steps, Nat.sub_one_add_one nnez]
      exact lt_of_le_of_ne (Nat.le_of_lt_add_one jlt') hjnn.symm
    apply make_run_journey_allowed_of_nice
    · exact hnice
    · exact ilt
  rename' hjnn => hjn; push_neg at hjn
  subst hjn
  have last_exp := (final_state_loc_eq_journey_last (make_run D p n ppos)).symm
  rw [last, ← cell_congr_idx _ (make_run_journey_steps D p n ppos).symm jlt] at last_exp
  rw [last_exp, make_run_subjourney D p i n ppos (lt_trans ilt (Nat.lt_add_one _))]
  intro h
  let fs : RunState := final_state (make_run D p n ppos)
  have lfsmem : loc fs ∈ (make_run D p (n - 1) ppos).eaten := by
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
  apply make_run_next_sprint_avoids_blocked_of_nice D p (n - 1) ppos hnice fs _ _
  · convert final_state_getLast_mem_of_nonnil (make_run D p n ppos) (by
      apply List.ne_nil_of_length_pos
      rwa [make_run_sprints_length]
    )
    rw [List.getLast_congr _ _ (make_run_sprints_recurrence D p n ppos npos)]; swap
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
def RunPath (D : Devil) (p n : Nat) (ppos : 0 < p) : List RunState :=
  if hlz : (make_run D p n ppos).sprints.length = 0 then [run_start] else
  ((make_run D p n ppos).sprints.head (List.ne_nil_of_length_pos (Nat.pos_of_ne_zero hlz))) ++
  (List.flatten (List.map List.tail (make_run D p n ppos).sprints.tail))

-- A RunPath of length zero is just the singleton list [run_start]
lemma run_path_of_length_zero (D : Devil) (p : Nat) (ppos : 0 < p) :
  RunPath D p 0 ppos = [run_start] := by
  unfold RunPath make_run
  rw [dif_pos]
  rw [if_pos rfl, empty_builder_sprints]
  exact List.length_nil

-- Any run state in the 'run path' must exist in some sprint of the run builder
lemma make_run_sprints_getElem_exists_of_run_path_mem (D : Devil) (p n : Nat) (ppos : 0 < p)
  (npos : 0 < n) (rs : RunState) (hmem : rs ∈ RunPath D p n ppos) :
  ∃ (i : Nat) (ilt : i < ((make_run D p n ppos).sprints.length)),
  ∃ (j : Nat) (jlt : j < ((make_run D p n ppos).sprints[i].length)),
  (make_run D p n ppos).sprints[i][j] = rs := by
  unfold RunPath at hmem
  have hslnz : (make_run D p n ppos).sprints.length ≠ 0 := by
    rw [make_run_sprints_length]
    exact Nat.ne_zero_iff_zero_lt.mpr npos
  have hslpos : 0 < (make_run D p n ppos).sprints.length :=
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
lemma run_path_recurrence (D : Devil) (p n : Nat) (ppos : 0 < p) (npos : 0 < n) :
  (RunPath D p n ppos) =
  (RunPath D p (n - 1) ppos) ++ ((make_run D p n ppos).sprints.getLast
    (by
      apply List.ne_nil_of_length_pos
      rwa [make_run_sprints_length]
    )).tail := by
  unfold RunPath
  have hnz : n ≠ 0 := Nat.ne_zero_of_lt npos
  have hlnz : (make_run D p n ppos).sprints.length ≠ 0 := by
    rwa [make_run_sprints_length]
  have hlpos : 0 < (make_run D p n ppos).sprints.length := by
    exact Nat.pos_of_ne_zero hlnz
  rw [dif_neg hlnz]
  -- Handle the case where n = 1
  by_cases n1 : n = 1
  · subst n1
    have hlz : (make_run D p (1 - 1) ppos).sprints.length = 0 := by
      rw [make_run_sprints_length]
    rw [dif_pos hlz]
    have hstn : (make_run D p 1 ppos).sprints.tail = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [List.length_tail, make_run_sprints_length, Nat.sub_self]
    rw [hstn, List.map_nil, List.flatten_nil, List.append_nil, ← List.getElem_zero_eq_head]; swap
    · assumption
    have gE0nn : (make_run D p 1 ppos).sprints[0] ≠ [] := by
      apply (make_run D p 1 ppos).nonnil
      apply List.getElem_mem
    rw [← List.head_cons_tail _ gE0nn, List.singleton_append, ← List.getElem_zero_eq_head]; swap
    · -- Resolve bounds check
      exact List.length_pos_of_ne_nil gE0nn
    rw [(make_run D p 1 ppos).origin]; swap
    · -- Resolve bounds check
      exact List.ne_nil_of_length_pos hlpos
    rw [List.getLast_eq_getElem]; congr 2
    apply getElem_congr_idx
    rw [make_run_sprints_length, Nat.sub_self]
  rename' n1 => nne1; push_neg at nne1
  have h1ltn : 1 < n := by
    exact Nat.lt_of_le_of_ne (Nat.add_one_le_of_lt (Nat.pos_of_ne_zero hnz)) nne1.symm
  have hlnz' : (make_run D p (n - 1) ppos).sprints.length ≠ 0 := by
    rw [make_run_sprints_length]
    exact Nat.sub_ne_zero_of_lt h1ltn
  have hlpos' : 0 < (make_run D p (n - 1) ppos).sprints.length := by
    exact Nat.pos_of_ne_zero hlnz'
  -- First, manipulate each side of the equation so that the
  -- left-hand sides of the appends match, and we can 'congr'
  rw [dif_neg hlnz', List.append_assoc, ← List.getElem_zero_eq_head]; swap
  · assumption
  have := make_run_sprints_recurrence D p n ppos (Nat.pos_of_ne_zero hnz)
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
  rw [← make_run_sprint D p n ppos, List.getLast_eq_getElem]
  · congr; rw [make_run_sprints_length]
  · exact Nat.sub_lt npos (by norm_num)

-- A predicate to check if 'rs' is an element of a particular sprint.
-- Argument is of type 'Fin (n - 1 + 1)' to make it compatible with
-- '_find_last' which requires an argument of type Fin (m+1) for some 'm'.
abbrev is_sprint_mem (D : Devil) (p n : Nat) (ppos : 0 < p)
  (npos : 0 < n) (rs : RunState) : (i : Fin (n - 1 + 1)) → Prop :=
  fun i ↦ (rs ∈ (make_run D p n ppos).sprints[i]'(by
    rw [make_run_sprints_length]
    convert i.2
    exact (Nat.sub_one_add_one (Nat.ne_zero_of_lt npos)).symm))

-- Returns the index of the last sprint of the 'make_run' of which 'rs' is an element
-- For the proof
def find_last_sprint_with_state (D : Devil) (p n : Nat) (ppos : 0 < p)
  (npos : 0 < n) (rs : RunState) : Nat :=
  (_find_last (is_sprint_mem D p n ppos npos rs)).val

-- Prove that 'rs' appears in no later sprint than the one
-- found by 'find_last_sprint_with_state'
lemma last_sprint_with_state_is_last (D : Devil) (p n : Nat)
  (ppos : 0 < p) (npos : 0 < n) (rs : RunState) : ∀ (i : Nat) (ilt : i < n),
  rs ∈ (make_run D p n ppos).sprints[i]'(by rwa [make_run_sprints_length]) →
  i ≤ find_last_sprint_with_state D p n ppos npos rs := by
  intro i ilt hmem
  unfold find_last_sprint_with_state
  -- First, work around Fin awkwardness
  have h₀ : n - 1 + 1 = n := Nat.sub_one_add_one (Nat.ne_zero_of_lt npos)
  have h₁ : (@Fin.mk (n - 1 + 1) i (by rwa [h₀])).val = i := by simp
  rw [← h₁]
  apply Fin.le_iff_val_le_val.mp
  -- Then apply the corresponding theorem for '_find_last'
  apply _find_last_is_last
  exact hmem

-- The return value of 'find_last_sprint_with_state' is
-- less than the number of sprints in the 'make_run'
lemma last_sprint_with_state_lt_length (D : Devil) (p n : Nat)
  (ppos : 0 < p) (npos : 0 < n) (rs : RunState) :
  find_last_sprint_with_state D p n ppos npos rs < (make_run D p n ppos).sprints.length := by
  unfold find_last_sprint_with_state
  rw [make_run_sprints_length]
  apply lt_of_lt_of_eq _ (Nat.sub_one_add_one (Nat.ne_zero_of_lt npos))
  exact (_find_last (is_sprint_mem D p n ppos npos rs)).2

-- The sprint indicated by 'find_last_sprint_with_state' does
-- in-fact contain the element 'rs'
lemma last_sprint_with_state_is_sat (D : Devil) (p n : Nat)
  (ppos : 0 < p) (npos : 0 < n) (rs : RunState) :
  (∃ (i : Nat) (ilt : i < n), rs ∈ (make_run D p n ppos).sprints[i]'(by
    rwa [make_run_sprints_length])) →
  rs ∈ (make_run D p n ppos).sprints[find_last_sprint_with_state D p n ppos npos rs]'(
    last_sprint_with_state_lt_length D p n ppos npos rs
  ) := by
  rintro ⟨i, ilt, hmem⟩
  let i' : Fin (n - 1 + 1) := ⟨i, by rwa [(Nat.sub_one_add_one (Nat.ne_zero_of_lt npos))]⟩
  exact _find_last_is_sat ((is_sprint_mem D p n ppos npos rs)) ⟨i', hmem⟩

-- If the devil is "nice", the runner will never visit a cell that was previously eaten.
-- Note that this result is more general than 'make_run_journey_allowed_of_nice' in that
-- it applies to *all* cells visited by the runner, not just those in the journey.
lemma make_run_runner_avoids_eaten_cells_of_nice (D : Devil) (p n : Nat) (ppos : 0 < p) (hnice : nice D p) :
  ∀ i (ilt : i < n) j (jlt : j < ((make_run D p n ppos).sprints[i]'(by
    rwa [make_run_sprints_length])).length) k (kle : k ≤ i),
    (make_run D p n ppos).eaten[k]'(by
      rw [make_run_eaten_length]
      exact lt_trans (lt_of_le_of_lt kle ilt) (Nat.lt_add_one _)
    ) ≠ loc (((make_run D p n ppos).sprints[i]'(by rwa [make_run_sprints_length]))[j]'(jlt)) := by
  intro i ilt j jlt k kle
  rw [getElem_congr_coll (make_run_sprint D p n ppos i ilt)]
  have lhs_rw : (make_run D p n ppos).eaten[k]'(by
    rw [make_run_eaten_length]
    exact lt_trans (lt_of_le_of_lt kle ilt) (Nat.lt_add_one _)
  ) = ((make_run D p n ppos).eaten.take (i + 1))[k]'(by
    rw [List.length_take_of_le]
    · exact Nat.lt_add_one_of_le kle
    · rw [make_run_eaten_length]
      apply Nat.add_one_le_of_lt
      exact lt_trans ilt (Nat.lt_add_one _)
  ) := by
    exact List.getElem_take.symm
  rw [lhs_rw]
  rw [getElem_congr_coll (make_run_eaten_take D p i n ppos (lt_trans ilt (Nat.lt_add_one _)))]
  intro h
  rw [make_run_sprint D p n ppos i ilt] at jlt
  let rs : RunState := (next_sprint (make_run D p i ppos))[j]'jlt
  apply make_run_next_sprint_avoids_blocked_of_nice D p i ppos hnice rs (List.getElem_mem jlt)
  apply List.mem_union_iff.mpr; left
  rw [← h]
  exact List.getElem_mem (by rw [make_run_eaten_length]; exact Nat.lt_add_one_of_le kle)

-- If the devil is "nice", then no cell visited by the runner was ever eaten by the devil.
lemma run_path_not_eaten_of_nice (D : Devil) (p n : Nat) (ppos : 0 < p) (hnice : nice D p) :
  ∀ rs ∈ (RunPath D p n ppos), (loc rs) ∉ (make_run D p n ppos).eaten := by
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
    make_run_sprints_getElem_exists_of_run_path_mem D p n ppos npos rs rsmem
  rcases mrsgEe_of_rpm with ⟨i, ilt, j, jlt, hij⟩
  let MR : RunBuilder p := (make_run D p n ppos)
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
  have rseaten' : loc rs ∈ (make_run D p (n - 1) ppos).eaten := by
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
  · apply run_path_not_eaten_of_nice D p (n - 1) ppos hnice rs _ rseaten'
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
