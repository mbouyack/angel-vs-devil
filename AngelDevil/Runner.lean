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

-- Turning right doesn't change the location, only the direction
lemma turn_right_loc (rs : RunState) : loc (turn_right rs) = loc rs := rfl

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

-- Prove that a partial sprint never steps on an eaten cell
lemma sprint_partial_avoids_eaten (p ns : Nat) (start : Int × Int)
  (eaten : List (Int × Int)) (rs : RunState) (hsafe : loc rs ∉ eaten) :
  ∀ x ∈ sprint_partial p ns start eaten rs, loc x ∉ eaten := by
  intro x hmem₀ hmem₁
  unfold sprint_partial at hmem₀
  split_ifs at hmem₀ with h₀
  · exact (List.mem_nil_iff _).mp hmem₀
  push_neg at h₀
  rcases List.mem_cons.mp hmem₀ with lhs | rhs
  · subst lhs; contradiction
  -- This next part is the most technical:
  -- We have to go through each of the advancement cases and
  -- show that we never step on an eaten cell
  have hsafe' : loc (next_step eaten rs) ∉ eaten := by
    intro hmem₂
    unfold next_step at hmem₂
    split_ifs at hmem₂ with h₁ h₂
    · rw [turn_right_loc] at hmem₂
      contradiction
    · unfold blocked at h₂
      push_neg at h₂
      exact h₂.2 hmem₂
    · unfold blocked at h₁
      push_neg at h₁
      exact h₁.2 hmem₂
  exact sprint_partial_avoids_eaten p (ns + 1) start eaten (next_step eaten rs) hsafe' x rhs hmem₁
termination_by 2 * p + 1 - ns
decreasing_by
  rw [Nat.sub_add_eq]
  apply Nat.sub_one_lt (Nat.sub_ne_zero_of_lt (Nat.lt_add_one_of_le _))
  push_neg at h₀
  exact h₀.1

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

-- All run states in a sprint are close to the start of that sprint
lemma sprint_close_mem_head (p : Nat) (hpos : 0 < p) (rs₀ : RunState) (eaten : List (Int × Int)) :
  ∀ x ∈ (sprint p rs₀ eaten), close p (loc x)
  (loc ((sprint p rs₀ eaten).head (sprint_nonnil_of_ppos p rs₀ eaten hpos))) := by
  intro x xmem
  have hnnil := sprint_nonnil_of_ppos p rs₀ eaten hpos
  unfold sprint at *
  rw [close_comm]
  convert sprint_partial_mem_close p 0 (loc rs₀) eaten rs₀ x xmem
  rwa [List.head_eq_getElem_zero hnnil, sprint_partial_getElem_zero_of_nonnil]

-- Prove that the first and last cells in a sprint are "close"
lemma sprint_close_first_last (p : Nat) (hpos : 0 < p) (rs₀ : RunState) (eaten : List (Int × Int)) :
  close p
  (loc ((sprint p rs₀ eaten).head (sprint_nonnil_of_ppos p rs₀ eaten hpos)))
  (loc ((sprint p rs₀ eaten).getLast (sprint_nonnil_of_ppos p rs₀ eaten hpos))) := by
  have hnnil := sprint_nonnil_of_ppos p rs₀ eaten hpos
  rw [close_comm]
  exact sprint_close_mem_head p hpos rs₀ eaten _ (List.getLast_mem hnnil)

-- The runner never visits an eaten cell
-- (as long as they don't start on an eaten cell)
lemma sprint_avoids_eaten (p : Nat) (rs₀ : RunState)
  (eaten : List (Int × Int)) (hsafe : loc rs₀ ∉ eaten) :
  ∀ x, x ∈ (sprint p rs₀ eaten) → loc x ∉ eaten :=
  fun x smem emem ↦
  sprint_partial_avoids_eaten p 0 (loc rs₀) eaten rs₀ hsafe x smem emem

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

lemma next_sprint_nonnil {p : Nat} (S : RunBuilder p) :
  next_sprint S ≠ [] := by
  apply sprint_nonnil_of_ppos
  exact S.ppos

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

-- The 'make_run' journey is "allowed" if the devil is "nice".
-- That is, it never visits an eaten cell.
-- TODO: Can we simplify this proof at all? It's rather lengthy.
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
  rw [lhs_rw]
  -- If j ≠ n we can recurse, so handle that case first
  by_cases hjnn : n ≠ j
  · -- Now apply the journey recurrence on the right and recurse
    rw [cell_congr_journey (make_run_journey_recurrence D p n ppos npos)]
    rw [append_cell_ne_last]; swap
    · rw [make_run_journey_steps, Nat.sub_one_add_one nnez]
      exact lt_of_le_of_ne (Nat.le_of_lt_add_one jlt') hjnn.symm
    apply make_run_journey_allowed_of_nice
    · exact hnice
    · exact ilt
  rename' hjnn => hjn; push_neg at hjn
  subst hjn
  -- Now we can also use recursion and the fact that the devil is nice
  -- to prove that the second-to-last cell in the journey is not in
  -- the eaten list.
  let MR' := (make_run D p (n - 1) ppos)
  let rs₀ := final_state MR'
  have : loc rs₀ ∉ MR'.eaten := by
    intro h
    rcases List.getElem_of_mem h with ⟨k, klt, h⟩
    rw [make_run_eaten_length] at klt
    rw [make_run_eaten] at h; swap
    · assumption
    rw [← make_run_subjourney D p k (n - 1) ppos] at h; swap
    · assumption
    unfold rs₀ at h
    rw [final_state_loc_eq_journey_last, last] at h
    rw [cell_congr_idx MR'.A (make_run_journey_steps D p (n - 1) ppos)] at h
    -- Show that k < n - 1 or else D is not "nice" - a contradiction
    have klt' : k < n - 1 := by
      apply lt_of_le_of_ne (Nat.le_of_lt_add_one klt)
      contrapose! hnice
      subst hnice
      apply not_nice_of_eats_journey_cell
      use MR'.A, (n - 1), (n - 1), le_rfl, (by
        rw [make_run_journey_steps, Nat.sub_one_add_one nnez]
        exact Nat.sub_one_lt nnez
      )
    -- Now recurse
    apply make_run_journey_allowed_of_nice D p (n - 1) ppos hnice _ _ klt' _ h
  -- Rewrite the left-hand_side as an element of the 'eaten' list
  rw [make_run_subjourney, ← make_run_eaten D p n]
  -- Resolve bounds checks first
  pick_goal 2; pick_goal 3
  · rwa [Nat.sub_one_add_one nnez]
  · exact lt_trans ilt (Nat.lt_add_one _)
  -- Re-write the right-hand side so that we can apply 'sprint_avoids_eaten'
  have nplt : n - 1 < n := Nat.sub_lt npos (by norm_num)
  have nplt' : n - 1 < MR.sprints.length := by rwa [make_run_sprints_length]
  have rhs_rw : cell MR.A n jlt =
    loc (((make_run D p n ppos).sprints[n - 1]'nplt').getLast
      (MR.nonnil _ (List.getElem_mem _))) := by
    rw [cell_congr_idx _ (Nat.sub_one_add_one nnez).symm]
    exact make_run_journey_cell D p n ppos (n - 1) nplt
  rw [rhs_rw]
  -- Apply the eaten recurrence
  rw [getElem_congr_coll (make_run_eaten_recurrence D p n ppos npos)]
  rw [List.getElem_append_left]; swap
  · -- Resolve bounds check
    rwa [make_run_eaten_length, Nat.sub_one_add_one nnez]
  by_contra! h
  -- Finally, apply 'sprint_avoids_eaten' which states that a sprint never
  -- visits a cell from the eaten list used to create it.
  apply sprint_avoids_eaten p rs₀ MR'.eaten this _ _ (List.mem_of_getElem h)
  rw [List.getLast_congr _ (next_sprint_nonnil _) (make_run_sprint D p n ppos (n - 1) nplt)]
  exact List.getLast_mem (next_sprint_nonnil _)

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
