import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import AngelDevil.Defs
import AngelDevil.Basic
import AngelDevil.Append
import AngelDevil.Nice

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
  (hnnil : sprint_partial p ns start eaten rs ≠ []) →
  (sprint_partial p ns start eaten rs)[0]'(List.length_pos_iff.mpr hnnil) = rs := by
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

-- Any element of a partial sprint is close to the start of the sprint
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
  sprint_partial p 0 (loc rs₀) eaten rs₀

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
    · linarith
    · exact close_self p (loc rs₀)
  exact List.cons_ne_nil _ _

lemma sprint_getElem_zero_of_ppos (p : Nat) (rs₀ : RunState) (eaten : List (Int × Int)) :
  (ppos : 0 < p) → (sprint p rs₀ eaten)[0]'(by
    apply List.length_pos_of_ne_nil
    exact sprint_nonnil_of_ppos p rs₀ eaten ppos
  ) = rs₀ :=
  fun ppos ↦ sprint_partial_getElem_zero_of_nonnil p 0 (loc rs₀) eaten rs₀
    (sprint_nonnil_of_ppos p rs₀ eaten ppos)

-- Prove that the first and last cells in a sprint are "close"
lemma sprint_close_first_last (p : Nat) (hpos : 0 < p) (rs₀ : RunState) (eaten : List (Int × Int)) :
  close p
  (loc ((sprint p rs₀ eaten).head (sprint_nonnil_of_ppos p rs₀ eaten hpos)))
  (loc ((sprint p rs₀ eaten).getLast (sprint_nonnil_of_ppos p rs₀ eaten hpos))) := by
  have hnnil := sprint_nonnil_of_ppos p rs₀ eaten hpos
  unfold sprint at *
  rw [List.head_eq_getElem_zero hnnil, sprint_partial_getElem_zero_of_nonnil]
  · exact sprint_partial_mem_close p 0 (loc rs₀) eaten _ _ (List.getLast_mem hnnil)
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

-- The location given by 'final_state' matches the last cell in the builder journey
lemma final_state_loc_eq_journey_last {p : Nat} (S : RunBuilder p) :
  loc (final_state S) = last S.A := by
  unfold final_state
  split_ifs with hlz
  · exact (journey_last_of_steps_zero S.A (Eq.trans S.samelen hlz)).symm
  · push_neg at hlz
    exact S.dest (List.ne_nil_of_length_pos (Nat.pos_of_ne_zero hlz))

-- Get the next sprint to be added to the builder
def next_sprint {p : Nat} (S : RunBuilder p) : List RunState :=
  sprint p (final_state S) S.eaten

-- The initial state of the next sprint is the
-- same as the final state of the builder
lemma next_sprint_first_eq_builder_last {p : Nat} (S : RunBuilder p) :
  final_state S = (next_sprint S)[0]'(by
    apply List.length_pos_of_ne_nil
    exact sprint_nonnil_of_ppos p (final_state S) S.eaten S.ppos
  ) := by
  unfold next_sprint
  rw [sprint_getElem_zero_of_ppos]
  exact S.ppos

-- The last cell of the next sprint is "close" to the
-- last cell of the builder journey.
lemma next_sprint_last_close_builder_last {p : Nat} (S : RunBuilder p) :
  close p (loc ((next_sprint S).getLast (sprint_nonnil_of_ppos p (final_state S) S.eaten S.ppos))) (last S.A) := by
  rw [← final_state_loc_eq_journey_last]
  nth_rw 2 [next_sprint_first_eq_builder_last S]
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
   Original this was named 'make_run' and used recursion to
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
  ∀ (i : Fin n),
  cell (make_run D p n ppos).A i.succ
    (by rw [make_run_journey_steps]; exact Nat.add_one_lt_add_one_iff.mpr i.2) =
  (loc (((make_run D p n ppos).sprints[i]'
    (by rw [make_run_sprints_length]; exact i.2)).getLast
      (by
        apply (make_run D p n ppos).nonnil
        apply List.getElem_mem
      ))) := by
  intro i
  rw [cell_congr_idx (make_run D p n ppos).A (Fin.val_succ i)]
  -- Prove sprints is nonnil so we can use RunBuilder.dest below
  have hsnn : (make_run D p (i.val + 1) ppos).sprints ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [make_run_sprints_length]
    exact Nat.add_one_pos _
  have islt : i.val + 1 < n + 1 :=
    Nat.add_one_lt_add_one_iff.mpr i.2
  rw [← subjourney_last_cell, make_run_subjourney]; swap
  · assumption -- bounds check
  rw [((make_run D p (i.val + 1) ppos).dest hsnn).symm]
  congr
  -- Rewrite the sprints of the sub-run as 'take' of the sprints of the full run.
  rw [List.getLast_congr _ _ (make_run_sprints_take D p (i.val + 1) n ppos islt).symm]; swap
  · -- Resolve pending bounds check
    apply List.ne_nil_of_length_pos
    have ispos : 0 < i.val + 1 := Nat.add_one_pos _
    rwa [List.length_take_of_le]
    rw [make_run_sprints_length]
    exact Nat.add_one_le_of_lt i.2
  -- Apply list identities to resolve goal
  rw [List.getLast_eq_getElem, List.getElem_take]; congr
  rw [List.length_take_of_le]
  · exact Nat.add_one_sub_one _
  · rw [make_run_sprints_length]
    exact Nat.add_one_le_of_lt i.2

/- Construct the list of run states corresponding to the full route of the runner.
   Each sprint overlaps by one cell, so we need to remove the first state from all
   but the first sprint -/
def RunPath (D : Devil) (p n : Nat) (ppos : 0 < p) : List RunState :=
  if hlz : (make_run D p n ppos).sprints.length = 0 then [run_start] else
  ((make_run D p n ppos).sprints.head (List.ne_nil_of_length_pos (Nat.pos_of_ne_zero hlz))) ++
  (List.flatten (List.map List.tail (make_run D p n ppos).sprints.tail))

-- A RunPath of length zero is just the single list [run_start]
lemma run_path_of_length_zero (D : Devil) (p : Nat) (ppos : 0 < p) :
  RunPath D p 0 ppos = [run_start] := by
  unfold RunPath make_run
  rw [dif_pos]
  rw [if_pos rfl, empty_builder_sprints]
  exact List.length_nil

-- Any run state in the 'run path' must exist in some sprint of the run builder
lemma make_run_sprints_getElem_exists_of_run_path_mem (D : Devil) (p n : Nat) (ppos : 0 < p)
  (npos : 0 < n) (rs : RunState) (hmem : rs ∈ RunPath D p n ppos) :
  ∃ (i : Fin ((make_run D p n ppos).sprints.length)),
  ∃ (j : Fin ((make_run D p n ppos).sprints[i].length)),
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
    use ⟨0, Nat.pos_of_ne_zero hslnz⟩, ⟨j, jlt⟩, h
  -- Otherwise use various list identities to get the original
  -- location of 'rs' within the sprints
  rcases List.mem_flatten.mp rhs with ⟨s, smem, hmem'⟩
  rcases List.mem_map.mp smem with ⟨s', s'mem, rfl⟩
  rcases List.getElem_of_mem (List.mem_of_mem_tail s'mem) with ⟨i, ilt, s'elem⟩
  rcases List.getElem_of_mem (List.mem_of_mem_tail hmem') with ⟨j, jlt, rselem⟩
  rw [← s'elem] at jlt
  use ⟨i, ilt⟩, ⟨j, jlt⟩
  rw [← getElem_congr_coll s'elem] at rselem
  exact rselem
