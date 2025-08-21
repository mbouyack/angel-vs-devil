import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import AngelDevil.Defs
import AngelDevil.Basic
import AngelDevil.Append
import AngelDevil.Subjourney

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
  -- They are only included to facilitate the definition of 'build run' (below)
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

-- Construct the journey that corresponds to appending the
-- last location of the next sprint
def builder_journey_extend {p : Nat} (S : RunBuilder p) : Journey p :=
  AppendJourney S.A (loc ((next_sprint S).getLast (sprint_nonnil_of_ppos p _ _ S.ppos)))
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

def make_run (D : Devil) (p n : Nat) (ppos : 0 < p) : RunBuilder p :=
  if n = 0 then empty_builder D p ppos else
  extend_run D p ppos (make_run D p (n - 1) ppos)
