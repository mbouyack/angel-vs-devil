import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import AngelDevil.Util
import AngelDevil.Defs
import AngelDevil.Basic
import AngelDevil.Subjourney

set_option linter.style.longLine false
set_option linter.style.multiGoal false

/-
  This file builds the concept of a "reduced" journey and related objects
  and proofs. In particular, it defines the 'reduced list' (which holds the
  raw cells of a reduced journey), the reduced journey itself (which is
  built from the reduced list), and the 'reduced map' (which maps cells in
  the reduced journey to cells in the original journey).

  See Máthé definition 2.5 for a detailed explanation of the reduced journey.
-/

-- Indicates that a cell at a particular index is "close" to (last A)
/- Note that 'find_first' uses 'Fin' instead of 'Nat' so that
   this function has type 'α → Prop' as required by DecidablePred. -/
abbrev last_close_fun {p : Nat} (A : Journey p) :=
  fun (i : Fin (steps A + 1)) ↦ close p (cell A i.val i.2) (last A)

-- 'last_close_fun' is satisfied by the cell of the journey
-- because each cell is close to itself
lemma last_close_fun_sat {p : Nat} (A : Journey p) :
  last_close_fun A (Fin.last (steps A)) := by
  unfold last_close_fun
  rw [last];
  exact close_self _ _

-- Find the first cell in the journey close to the last cell
def find_first_close_to_last {p : Nat} (A : Journey p) : Nat :=
  (_find_first (last_close_fun A)).val

-- Upper bound on the value of 'find_first_close_to_last'
lemma first_close_to_last_lt {p : Nat} (A : Journey p) :
  find_first_close_to_last A < steps A + 1 :=
  (_find_first (last_close_fun A)).2

-- 'first_close_to_last' is in-fact close to last
lemma first_close_to_last_is_close {p : Nat} (A : Journey p) :
  close p (cell A (find_first_close_to_last A) (first_close_to_last_lt A)) (last A) :=
  _find_first_is_sat (last_close_fun A) ⟨_, last_close_fun_sat A⟩

-- 'first_close_to_last' is in-fact the first such cell
lemma first_close_to_last_is_first {p : Nat} (A : Journey p) (i : Nat) (ilt : i < steps A + 1) :
  close p (cell A i ilt) (last A) → find_first_close_to_last A ≤ i :=
  fun h ↦ Fin.le_iff_val_le_val.mp (_find_first_is_first (last_close_fun A) ⟨i, ilt⟩ h)

-- The first cell close to the last cell of the journey
-- is not the last cell itself unless the journey has steps = 0
-- This is required to prove termination of 'reduced_steps' below.
lemma first_close_to_last_ne_last {p : Nat} {A : Journey p} :
  (steps A) ≠ 0 → find_first_close_to_last A ≠ steps A := by
  intro snz
  apply Nat.ne_of_lt (Nat.lt_of_le_sub_one (Nat.pos_of_ne_zero snz) _)
  apply first_close_to_last_is_first A (steps A - 1) (Nat.lt_trans (Nat.sub_one_lt snz) (Nat.lt_add_one _))
  convert journey_steps_close A ((steps A)-1) (Nat.sub_one_lt snz)
  rw [last]; congr
  exact (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr snz)).symm

-- Slightly tighter upper bound on 'find_first_close_to_last' when steps A ≠ 0
lemma first_close_to_last_lt' {p : Nat} (A : Journey p) (snz : steps A ≠ 0) :
  find_first_close_to_last A < steps A :=
  lt_of_le_of_ne (Nat.le_of_lt_add_one (first_close_to_last_lt A)) (first_close_to_last_ne_last snz)

-- A common strategy for proving properties of the reduced list / journey / map
-- is to show that if the property holds for this particular subjourney, then
-- it holds for the original journey.
abbrev recurrence_subjourney {p : Nat} (A : Journey p) : Journey p :=
  subjourney A (find_first_close_to_last A) (first_close_to_last_lt A)

/- The 'reduced list reversed' is constructed by starting with the last cell
   in the journey and repeatedly choosing the earliest "close" cell. This will
   be used to construct the 'reduced journey', which will be proven to have
   several useful properties. Each entry is a key-value pair with an index
   into the original journey and the coordinates of the corresponding cell. -/
def reduced_list_rev {p : Nat} (A : Journey p) : List (Nat × (Int × Int)) :=
  if _ : steps A = 0 then [⟨0, (last A)⟩] else
  ⟨steps A, (last A)⟩ :: reduced_list_rev (recurrence_subjourney A)
termination_by (steps A)
decreasing_by
  rename ¬steps A = 0 => snz
  rw [subjourney_steps]
  exact first_close_to_last_lt' A snz

-- The reduced list reversed is not empty
lemma redlist_rev_not_nil {p : Nat} (A : Journey p) : reduced_list_rev A ≠ [] := by
  unfold reduced_list_rev
  split_ifs with _ <;> simp

-- The length of the reduced list is positive
lemma redlist_rev_length_pos {p : Nat} (A : Journey p) : 0 < (reduced_list_rev A).length :=
  List.length_pos_iff.mpr (redlist_rev_not_nil _)

-- The length of the reduced list is non-zero
lemma redlist_rev_length_ne_zero {p : Nat} (A : Journey p) : (reduced_list_rev A).length ≠ 0 :=
  Nat.ne_zero_of_lt (redlist_rev_length_pos _)

-- The last cell in the reduced list reversed is the origin
lemma redlist_rev_last_origin {p : Nat} (A : Journey p) :
  (reduced_list_rev A).getLast (redlist_rev_not_nil A) = ⟨0, (0, 0)⟩ := by
  unfold reduced_list_rev
  split_ifs with h
  · simp
    convert journey_start A
    rw [last]; congr
  · rw [List.getLast_cons (redlist_rev_not_nil _), redlist_rev_last_origin]
termination_by (steps A)
decreasing_by
  rename ¬steps A = 0 => snz
  rw [subjourney_steps]
  exact first_close_to_last_lt' A snz

-- The head of the reduced list reversed is the last cell in 'A'
lemma redlist_rev_head_last {p : Nat} (A : Journey p) :
  ((reduced_list_rev A).head (redlist_rev_not_nil _)) = ⟨steps A, (last A)⟩ := by
  unfold reduced_list_rev
  split_ifs with h <;> simp
  exact h.symm

-- The first cell in the reduced list reversed is the last cell in 'A'
lemma redlist_rev_getElem_zero_last {p : Nat} (A : Journey p) :
  ((reduced_list_rev A)[0]' (redlist_rev_length_pos A)) = ⟨steps A, (last A)⟩ := by
  rw [← List.head_eq_getElem (redlist_rev_not_nil A), redlist_rev_head_last]

-- The length of the reduced list reversed is '1' if-and-only-if
-- the original journey has zero steps.
lemma redlist_rev_rlrl1_iff_sz {p : Nat} (A : Journey p) :
  (reduced_list_rev A).length = 1 ↔ steps A = 0 := by
  unfold reduced_list_rev
  constructor
  · intro h
    by_contra! snz
    rw [dif_neg snz, List.length_cons, Nat.add_eq_right] at h
    exact redlist_rev_not_nil _ (List.eq_nil_of_length_eq_zero h)
  · intro h
    rw [dif_pos h]
    exact List.length_singleton

-- Recursive formula for the length of the reduced list
lemma redlist_rev_recursive_length {p : Nat} (A : Journey p) (snz : steps A ≠ 0) :
  (reduced_list_rev A).length =
  (reduced_list_rev (recurrence_subjourney A)).length + 1 := by
  let sjA := recurrence_subjourney A
  change (reduced_list_rev A).length = (reduced_list_rev sjA).length + 1
  unfold reduced_list_rev
  rw [dif_neg snz, List.length_cons, subjourney_steps, Nat.add_one_inj]
  by_cases h : find_first_close_to_last A = 0
  · rw [dif_pos h, List.length_singleton]
    apply (redlist_rev_rlrl1_iff_sz _).mpr
    rwa [subjourney_steps]
  · have : find_first_close_to_last sjA < find_first_close_to_last A + 1:= by
      apply lt_of_lt_of_eq (first_close_to_last_lt sjA) (Nat.add_one_inj.mpr _)
      apply subjourney_steps
    unfold sjA recurrence_subjourney
    rw [dif_neg h, List.length_cons, subjourney_subjourney A this]
    apply redlist_rev_recursive_length _ (by rwa [subjourney_steps])
termination_by (steps A)
decreasing_by
  rename ¬steps A = 0 => snz
  rw [subjourney_steps]
  exact first_close_to_last_lt' A snz

-- Recursive head::tail representation of the reversed reduced list
lemma redlist_rev_cons {p : Nat} (A : Journey p) (snz : steps A ≠ 0) : reduced_list_rev A =
  ⟨steps A, (last A)⟩ :: reduced_list_rev (recurrence_subjourney A) := by
  rw [reduced_list_rev, dif_neg snz]

-- Recursive formula for getting an element of the reversed reduced list
lemma redlist_rev_recursive_getElem {p : Nat} (A : Journey p) (i : Nat)
  (islt : i + 1 < (reduced_list_rev A).length) :
  (reduced_list_rev A)[i + 1] =
  ((reduced_list_rev (recurrence_subjourney A))[i]'
  (by
    have snz : steps A ≠ 0 :=
      fun h ↦ ne_of_lt (Nat.lt_of_add_left_lt islt) ((redlist_rev_rlrl1_iff_sz A).mpr h).symm
    apply Nat.add_one_lt_add_one_iff.mp
    rwa [← redlist_rev_recursive_length A snz]
  )) := by
  have snz : steps A ≠ 0 :=
    fun h ↦ ne_of_lt (Nat.lt_of_add_left_lt islt) ((redlist_rev_rlrl1_iff_sz A).mpr h).symm
  rw [List.getElem_of_eq (redlist_rev_cons A snz), List.getElem_cons_succ]

-- The indices ("keys") in the reduced list reversed are less than 'steps A + 1'
lemma redlist_rev_idx_lt {p : Nat} (A : Journey p) (i : Nat) (ilt : i < (reduced_list_rev A).length) :
  (reduced_list_rev A)[i].1 < steps A + 1 := by
  -- First handle the case where i = 0
  by_cases iz : i = 0
  · rw [getElem_congr_idx iz]
    exact lt_of_eq_of_lt (Prod.ext_iff.mp (redlist_rev_getElem_zero_last A)).1 (Nat.lt_add_one _)
  rename' iz => inz; push_neg at inz
  -- Note that if i ≠ 0, steps A ≠ 0
  have snz := fun sz ↦ inz (Nat.lt_one_iff.mp (lt_of_lt_of_eq ilt ((redlist_rev_rlrl1_iff_sz A).mpr sz)))
  -- If i ≠ 0, we can expand the recursive definition of 'getElem'
  rw [getElem_congr_idx (Nat.sub_one_add_one inz).symm]
  rw [redlist_rev_recursive_getElem A _ (lt_of_eq_of_lt (Nat.sub_one_add_one inz) ilt)]
  -- Then recursively apply the theorem statement
  apply lt_trans (redlist_rev_idx_lt _ _ _)
  rw [subjourney_steps]
  exact Nat.add_one_lt_add_one_iff.mpr (first_close_to_last_lt' A snz)

-- Each key-value pair, ⟨key, val⟩, in the reduced list reversed corresponds to a cell
-- in the original journey with 'cell A idx = val'
lemma redlist_rev_cell {p : Nat} (A : Journey p) (i : Nat) (ilt : i < (reduced_list_rev A).length) :
  cell A ((reduced_list_rev A)[i]' ilt).1 (redlist_rev_idx_lt A i ilt) = ((reduced_list_rev A)[i]' ilt).2 := by
  -- First handle the case where i = 0
  by_cases iz : i = 0
  · have helem : (reduced_list_rev A)[i] = (steps A, last A) :=
      Eq.trans (getElem_congr_idx iz) (redlist_rev_getElem_zero_last A)
    rw [cell_congr_idx A (Prod.ext_iff.mp helem).1]
    nth_rw 3 [(Prod.ext_iff.mp helem).2]; rfl
  rename' iz => inz; push_neg at inz
  have hip : (reduced_list_rev A)[i] = (reduced_list_rev A)[i-1+1] := getElem_congr_idx (Nat.sub_one_add_one inz).symm
  have helem := Eq.trans hip (redlist_rev_recursive_getElem A (i-1) _)
  rw [cell_congr_idx A (Prod.ext_iff.mp helem).1]
  nth_rw 3 [(Prod.ext_iff.mp helem).2]
  -- Recurse to complete the goal
  -- Note that we give the first argument explicitly because Lean is unable to infer it
  exact redlist_rev_cell (recurrence_subjourney A) (i-1) _

-- The index in the second entry of the reduced list (reversed)
-- is given by 'find_first_close_to_last A'
lemma redlist_rev_snd_idx {p : Nat} (A : Journey p) (lgt1 : 1 < (reduced_list_rev A).length) :
  (reduced_list_rev A)[1].1 = find_first_close_to_last A := by
  have := redlist_rev_recursive_getElem A 0 (lt_of_eq_of_lt (Nat.zero_add _) lgt1)
  rw [redlist_rev_getElem_zero_last, subjourney_steps, getElem_congr_idx (Nat.zero_add _)] at this
  exact (Prod.ext_iff.mp this).1

-- Lemma which describes the relationship between the indices of
-- consecutive elements of the reduced list reversed
lemma redlist_rev_consecutive {p : Nat} (A : Journey p) (i : Nat) (islt : i + 1 < (reduced_list_rev A).length) :
  (reduced_list_rev A)[i+1].1 =
  find_first_close_to_last (subjourney A (reduced_list_rev A)[i].1 (redlist_rev_idx_lt _ _ _)) := by
  -- First handle the case where i = 0
  by_cases iz : i = 0
  · rw [getElem_congr_idx (Eq.trans (Nat.add_one_inj.mpr iz) (Nat.zero_add _))]
    have helem : (reduced_list_rev A)[i] = (steps A, last A) :=
      Eq.trans (getElem_congr_idx iz) (redlist_rev_getElem_zero_last A)
    rw [subjourney_congr_idx A (Prod.ext_iff.mp helem).1, redlist_rev_snd_idx, subjourney_full]
  rename' iz => inz; push_neg at inz
  -- Otherwise, i ≠ 0 so replace i with '(i-1)+1', rewrite with
  -- 'redlist_rev_recursive_getElem' on both the left and right-hand sides
  -- of the goal, and then recurse to complete the proof.
  rw [getElem_congr_idx (Nat.add_one_inj.mpr (Nat.sub_one_add_one inz).symm)]
  have : (reduced_list_rev A)[i].1 = (reduced_list_rev A)[i - 1 + 1].1 :=
    (Prod.ext_iff.mp (getElem_congr_idx (Nat.sub_one_add_one inz).symm)).1
  rw [redlist_rev_recursive_getElem] at this
  rw [subjourney_congr_idx A this (redlist_rev_idx_lt _ _ _), redlist_rev_recursive_getElem]
  apply redlist_rev_consecutive

-- The "keys" in the reduced list (reverse) are monotonically decreasing
lemma redlist_rev_mono {p : Nat} (A : Journey p) (i j : Nat) (ilt : i < j) (jlt : j < (reduced_list_rev A).length) :
  (reduced_list_rev A)[j].1 < (reduced_list_rev A)[i].1 := by
  have snz : steps A ≠ 0 := by
    intro sz
    rw [(redlist_rev_rlrl1_iff_sz A).mpr sz] at jlt
    linarith
  -- 0 < j, so rewrite the left-hand side in terms of the recurrence subjourney
  rw [(getElem_congr_idx (Nat.sub_one_add_one (Nat.ne_zero_of_lt ilt))).symm]
  rw [redlist_rev_recursive_getElem A (j-1)]
  -- Handle the case where i = 0
  by_cases iz : i = 0
  · subst iz
    apply Nat.lt_of_lt_of_le (redlist_rev_idx_lt _ (j-1) _)
    rw [redlist_rev_getElem_zero_last, subjourney_steps]
    exact Nat.add_one_le_of_lt (first_close_to_last_lt' A snz)
    -- Prove the pending bounds check
    exact fun _ ilt ↦ lt_of_eq_of_lt (Nat.sub_one_add_one (Nat.ne_zero_of_lt ilt)) jlt
  rename' iz => inz; push_neg at inz
  -- Now we can assume 0 < i, so rewrite the left-hand side in the same way
  rw [(getElem_congr_idx (Nat.sub_one_add_one inz)).symm]
  rw [redlist_rev_recursive_getElem A (i-1)]
  -- Finally, recurse
  apply redlist_rev_mono
  -- Prove the pending bounds checks
  · apply Nat.sub_lt_sub_right (le_of_eq_of_le (Nat.zero_add _).symm (Nat.add_one_le_of_lt (Nat.pos_of_ne_zero inz)))
    assumption
  · rw [Nat.sub_one_add_one inz]
    exact lt_trans ilt jlt

-- Consucutive cells in the reduced list are close
lemma redlist_rev_close {p : Nat} (A : Journey p) (i : Nat) (islt : i + 1 < (reduced_list_rev A).length) :
  close p (reduced_list_rev A)[i].2 (reduced_list_rev A)[i+1].2 := by
  rw [← redlist_rev_cell, ← redlist_rev_cell, cell_congr_idx _ (redlist_rev_consecutive A i _), close_comm]
  nth_rw 2 [← subjourney_last_cell]
  rw [← subjourney_cell A _ _ _ (Nat.le_of_lt_add_one (first_close_to_last_lt _))]
  apply first_close_to_last_is_close

/- The reduced journey is formed by starting at the destination and moving backward
   along the cells of the original journey, always choosing the earliest cell which
   is "close". This construction is used to prove both Conway's Theorem 8.1 and
   Máthé's Theorem 2.7 .-/
def reduced {p : Nat} (A : Journey p) : Journey p where
  n := (reduced_list_rev A).length - 1
  seq := fun i ↦ ((reduced_list_rev A).reverse[i.val]' (by
    rw [List.length_reverse]
    nth_rw 2 [← Nat.sub_one_add_one (redlist_rev_length_ne_zero A)]
    exact i.2)).2
  start := by
    have nonnil := List.reverse_ne_nil_iff.mpr (redlist_rev_not_nil A)
    rwa [← List.head_eq_getElem, List.head_reverse, redlist_rev_last_origin]
  plimit := by
    intro i ilt
    rw [List.getElem_reverse, List.getElem_reverse, close_comm]
    rw [getElem_congr_idx (Nat.sub_one_add_one (Nat.sub_ne_zero_iff_lt.mpr ilt)).symm]
    rw [getElem_congr_idx (Nat.sub_add_eq _ _ _)]
    apply redlist_rev_close

-- The reduced journey has zero steps if-and-only-if the original journey has zero steps
lemma redsteps_zero_steps_zero_iff {p : Nat} {A : Journey p} : steps (reduced A) = 0 ↔ steps A = 0 := by
  rw [← redlist_rev_rlrl1_iff_sz A, ← Nat.zero_add 1]
  rw [← Nat.sub_one_add_one (redlist_rev_length_ne_zero A), Nat.add_one_inj]
  rfl

-- The reduced journey has a non-zero number of steps if-and-only-if
-- the original journey also has a non-zero number of steps.
lemma redsteps_ne_zero_steps_ne_zero_iff {p : Nat} {A : Journey p} : steps (reduced A) ≠ 0 ↔ steps A ≠ 0 :=
  ⟨fun rsnz sz ↦ rsnz (redsteps_zero_steps_zero_iff.mpr sz),
  fun snz rsz ↦ snz (redsteps_zero_steps_zero_iff.mp rsz)⟩

-- Recursive definition of 'steps (reduced A)'
lemma redsteps_recurrence {p : Nat} (A : Journey p) (snz : steps A ≠ 0) : steps (reduced A) =
  steps (reduced (recurrence_subjourney A)) + 1 := by
  unfold steps reduced; simp
  rw [redlist_rev_recursive_length A snz, ← one_add_one_eq_two, ← add_assoc]
  rw [Nat.sub_one_add_one (redlist_rev_length_ne_zero _)]

-- The number of steps in the reduced journey is less than or equal to
-- the number of steps in the original journey.
-- TODO: I don't think we're using this yet. Do we need it?
lemma redsteps_le_steps {p : Nat} (A : Journey p) : steps (reduced A) ≤ steps A := by
  by_cases sz : steps A = 0
  · rw [sz, redsteps_zero_steps_zero_iff.mpr sz]
  rename' sz => snz; push_neg at snz
  rw [redsteps_recurrence A snz]
  apply Nat.add_one_le_iff.mpr
  apply lt_of_le_of_lt (redsteps_le_steps _)
  rw [subjourney_steps]
  exact first_close_to_last_lt' A snz
termination_by (steps A)
decreasing_by
  rename' sz => snz
  rw [subjourney_steps]
  exact first_close_to_last_lt' A snz

-- Lemma to relate the steps in the reduced journey and the
-- length of the reduced list. This should only be used for
-- proving the most basic facts about the reduced journey.
lemma redsteps_eq_redlist_length_sub_one {p : Nat} (A : Journey p) :
  steps (reduced A) = (reduced_list_rev A).length - 1 := rfl

-- The last cell in the reduced journey is the same as the last cell of the original journey
lemma reduced_last {p : Nat} (A : Journey p) : last (reduced A) = last A := by
  unfold last cell reduced steps; dsimp
  rw [List.getElem_reverse, getElem_congr_idx (Nat.sub_self _), redlist_rev_getElem_zero_last]
  rfl

-- Recursive formula for a cell in the reduced journey
-- TODO: We don't currently use this anywhere. Consider removing it.
lemma reduced_recurrence {p : Nat} (A : Journey p) (i : Nat) (ilt : i < steps (reduced A)) :
  cell (reduced A) i (lt_trans ilt (Nat.lt_add_one _)) =
  cell (reduced (recurrence_subjourney A)) i (by
    rwa [← redsteps_recurrence A (redsteps_ne_zero_steps_ne_zero_iff.mp (Nat.ne_zero_of_lt ilt))]
  ) := by
  have rsnz := Nat.ne_zero_of_lt ilt
  have snz := redsteps_ne_zero_steps_ne_zero_iff.mp rsnz
  unfold cell reduced steps; dsimp
  rw [List.getElem_reverse, List.getElem_reverse]
  -- First rewrite the left-hand side index
  have lhsidx := Eq.trans
    (Nat.sub_one_add_one (Nat.sub_ne_zero_iff_lt.mpr (lt_of_lt_of_eq ilt (redsteps_eq_redlist_length_sub_one A)))).symm
    (Nat.add_one_inj.mpr (Nat.sub_right_comm _ i 1))
  rw [getElem_congr_idx lhsidx]
  -- Now rewrite the right-hand side index
  have rhsidx := congrArg (fun x ↦ x - 1 - 1 - i) (redlist_rev_recursive_length A snz); dsimp at rhsidx
  rw [← getElem_congr_idx rhsidx]
  -- Now our goal matches the recursive 'getElem' definition we proved for the reduced list
  exact (Prod.ext_iff.mp (redlist_rev_recursive_getElem _ _ _)).2

/- This function maps from an index in the reduced journey to the index
   of the corresponding cell in the original journey. Note that the
   reversed reduced list is defined as a list of key-value pairs
   specifically to fascilitate the definition of this function. -/
def reduced_map {p : Nat} (A : Journey p) : (i : Nat) → (i < steps (reduced A) + 1) → Nat :=
  fun i ilt ↦ ((reduced_list_rev A).reverse[i]' (by
    convert ilt
    rw [List.length_reverse, redsteps_eq_redlist_length_sub_one, Nat.sub_add_cancel]
    exact Nat.one_le_of_lt (redlist_rev_length_pos A)
  )).1

-- The reduced map takes 0 ↦ 0
lemma redmap_zero {p : Nat} (A : Journey p) : reduced_map A 0 (Nat.add_one_pos _) = 0 := by
  unfold reduced_map
  rw [List.getElem_reverse]
  convert (Prod.ext_iff.mp (redlist_rev_last_origin A)).1
  exact Eq.trans (getElem_congr_idx (Nat.sub_zero _)) (List.getLast_eq_getElem _).symm

-- The reduced map takes last ↦ last
-- That is, the last cell of the reduced journey maps to the
-- last cell of the original journey.
lemma redmap_last {p : Nat} (A : Journey p) :
  reduced_map A (steps (reduced A)) (Nat.lt_add_one _) = steps A := by
  unfold reduced_map; simp
  convert (Prod.ext_iff.mp (redlist_rev_getElem_zero_last A)).1
  exact Nat.sub_eq_zero_iff_le.mpr (le_of_eq (redsteps_eq_redlist_length_sub_one A).symm)

-- Values in the range of the reduced map are less than 'steps A + 1'
lemma redmap_lt {p : Nat} (A : Journey p) (i : Nat) (ilt : i < steps (reduced A) + 1) :
  reduced_map A i ilt < steps A + 1 := by
  unfold reduced_map; simp
  apply redlist_rev_idx_lt

-- The reduced map takes cells in the reduced journey to the corresponding
-- cells in the original journey.
lemma redmap_cell {p : Nat} (A : Journey p) (i : Nat) (ilt : i < steps (reduced A) + 1) :
  cell A (reduced_map A i ilt) (redmap_lt A _ _) = cell (reduced A) i ilt := by
  unfold reduced_map reduced; simp
  rw [redlist_rev_cell]
  unfold cell; rfl

-- Invocations of 'reduced_map' with equivalent journies are equal
lemma redmap_congr_journey {p : Nat} {A B : Journey p} (hAB : A = B) (i : Nat) (ilt : i < steps (reduced B) + 1) :
  reduced_map A i (by convert ilt) = reduced_map B i ilt := by congr

-- Invocations of 'reduced_map' with equal indices are equal
lemma redmap_congr_idx {p : Nat} (A : Journey p) {i j : Nat} (hij : i = j) (ilt : i < steps (reduced A) + 1) :
  reduced_map A i ilt = reduced_map A j (hij ▸ ilt) := by congr

-- Lemma describing the relationship between 'reduced_map i' and 'reduced_map (i+1)'
lemma redmap_consecutive {p : Nat} (A : Journey p) (i : Nat) (islt : i + 1 < steps (reduced A) + 1) :
  find_first_close_to_last (subjourney A (reduced_map A (i+1) islt) (redmap_lt A (i+1) islt)) =
  reduced_map A i (lt_trans (Nat.lt_add_one _) islt) := by
  unfold reduced_map
  have islt' : i + 1 < (reduced_list_rev A).length := by
    convert islt
    rw [redsteps_eq_redlist_length_sub_one]
    exact (Nat.sub_one_add_one (redlist_rev_length_ne_zero _)).symm
  have lhs : ((reduced_list_rev A).reverse[i+1]' (by rwa [List.length_reverse])).1 = _ :=
    (Prod.ext_iff.mp (Eq.trans (List.getElem_reverse _) (getElem_congr_idx (Nat.sub_add_eq _ i 1)))).1
  -- Rewrite the index of the left-hand side
  rw [subjourney_congr_idx A lhs]
  symm
  rw [(Prod.ext_iff.mp (List.getElem_reverse _)).1]
  have rhs := Nat.sub_ne_zero_of_lt ((redsteps_eq_redlist_length_sub_one A) ▸ (Nat.add_one_lt_add_one_iff.mp islt))
  -- Rewrite the index of (what was originally) the right-hand side
  rw [getElem_congr_idx ((Nat.sub_one_add_one rhs).symm)]
  -- Finish the proof with the corresponding theorem on the reduced list
  apply redlist_rev_consecutive

-- Recurrence for the reduced map in terms of the recurrence subjourney
lemma redmap_recurrence {p : Nat} (A : Journey p) (snz : steps A ≠ 0) (i : Nat) (ilt : i < steps (reduced A)) :
  reduced_map A i (lt_trans ilt (Nat.lt_add_one _)) =
  reduced_map (recurrence_subjourney A) i (by rwa [← redsteps_recurrence A snz]) := by
  -- First handle the case where i = 0
  by_cases iz : i = 0
  · subst iz
    rw [redmap_zero, redmap_zero]
  rename' iz => inz; push_neg at inz
  unfold reduced_map
  rw [List.getElem_reverse, List.getElem_reverse]
  rw [redsteps_eq_redlist_length_sub_one] at ilt
  apply (Prod.ext_iff.mp _).1
  -- Rewrite the index on the left-hand side
  rw [getElem_congr_idx (Nat.sub_one_add_one (Nat.sub_ne_zero_iff_lt.mpr ilt)).symm]
  -- Rewrite the index on the right-hand side
  have rhs := Eq.trans (congrArg (fun x ↦ x - 1 - 1 - i) (redlist_rev_recursive_length A snz)) (Nat.add_one_sub_one _)
  dsimp at rhs
  rw [Nat.sub_right_comm _ 1 i] at rhs
  rw [getElem_congr_idx rhs.symm]
  -- Use the corresponding redlist theorem to complete the goal
  exact redlist_rev_recursive_getElem A ((reduced_list_rev A).length - 1 - i - 1) _

-- The reduced map is monotonically increasing
lemma redmap_mono {p : Nat} (A : Journey p) {i j : Nat} (ilt : i < j) (jlt : j < steps (reduced A) + 1) :
  reduced_map A i (lt_trans ilt jlt) < reduced_map A j jlt := by
  unfold reduced_map
  have := Nat.sub_one_add_one (redlist_rev_length_ne_zero A)
  rw [redsteps_eq_redlist_length_sub_one, this] at jlt
  rw [List.getElem_reverse, List.getElem_reverse]
  -- Apply the corresponding 'redlist' theorem
  apply redlist_rev_mono
  apply Nat.sub_lt_sub_left _ ilt
  apply Nat.add_one_lt_add_one_iff.mp; rw [this]
  exact lt_of_le_of_lt (Nat.add_one_le_of_lt ilt) jlt

-- The converse of redmap_mono
lemma redmap_mono' {p : Nat} (A : Journey p) {i j : Nat}
  (ilt : i < steps (reduced A) + 1) (jlt : j < steps (reduced A) + 1) :
  reduced_map A i ilt < reduced_map A j jlt → i < j := by
  intro h
  contrapose! h
  rcases lt_or_eq_of_le h with jlti | hji
  · exact Nat.le_of_lt (redmap_mono A jlti ilt)
  · apply le_of_eq
    congr

-- It follows from 'redmap_mono' that the reduced map is injective
lemma redmap_inj {p : Nat} (A : Journey p) (i j : Nat) (ilt : i < steps (reduced A) + 1) (jlt : j < steps (reduced A) + 1) :
  reduced_map A i ilt = reduced_map A j jlt → i = j :=
  fun h ↦ le_antisymm
    (le_of_not_gt (fun jlt ↦ (ne_of_lt (redmap_mono A jlt ilt)).symm h))
    (le_of_not_gt (fun ilt ↦ ne_of_lt (redmap_mono A ilt jlt) h))

-- Take the inverse of zero over the reduced map
lemma redmap_zero_inv {p : Nat} (A : Journey p) (i : Nat) (ilt : i < steps (reduced A) + 1) :
  reduced_map A i ilt = 0 → i = 0 :=
  fun h ↦ redmap_inj A i 0 ilt (Nat.add_one_pos _) (Eq.trans h (redmap_zero A).symm)

-- An identity on the length of a reduced subjourney which applies when that
-- subjourney ends with an element that appears in the full reduced journey
-- Primarily, this is used to prove 'redmap_sub_redmap' (below).
lemma redsteps_sub_redmap {p : Nat} (A : Journey p) (i : Nat) (ilt : i < steps (reduced A) + 1) :
  steps (reduced (subjourney A (reduced_map A i ilt) (redmap_lt _ _ _))) = i := by
  by_cases iz : i = 0
  · subst iz
    apply redsteps_zero_steps_zero_iff.mpr
    rw [subjourney_steps, redmap_zero]
  rename' iz => inz; push_neg at inz
  -- Prove that this subjourney has a non-zero number of steps
  have sjsnz : steps (subjourney A (reduced_map A i ilt) (redmap_lt A i ilt)) ≠ 0 := by
    rw [subjourney_steps]
    exact fun h ↦ inz ((redmap_zero_inv A i ilt) h)
  rw [redsteps_recurrence, recurrence_subjourney, subjourney_subjourney]
  apply Nat.sub_one_cancel (Nat.pos_of_ne_zero (Nat.add_one_ne_zero _)) (Nat.pos_of_ne_zero _)
  rw [Nat.add_one_sub_one]
  -- Using recursion and 'redmap_consecutive' to close the goal
  convert redsteps_sub_redmap A (i-1) (lt_trans (Nat.sub_one_lt inz) ilt)
  convert redmap_consecutive A (i-1) (by rwa [Nat.sub_one_add_one inz])
  -- Now prove all the bounds checks:
  · exact (Nat.sub_one_add_one inz).symm
  · exact first_close_to_last_lt _
  · assumption
  · assumption

-- The reduced map of a subjourney is a narrowing of the original reduced map
-- if the last element of the subjourney corresponds to an element of the reduced journey
lemma redmap_sub_redmap {p : Nat} (A : Journey p) (n : Nat) (nlt : n < steps (reduced A) + 1) :
  ∀ i, (ilt : i < n+1) →
  reduced_map (subjourney A (reduced_map A n nlt) (redmap_lt A n nlt)) i (by rwa [redsteps_sub_redmap]) =
  reduced_map A i (Nat.lt_of_le_of_lt (Nat.le_of_lt_add_one ilt) nlt) := by
  intro i ilt
  -- Handle the case where n = i
  have ilt' : i < steps (reduced A) + 1 := lt_of_le_of_lt (Nat.le_of_lt_add_one ilt) nlt
  by_cases hni : n = i
  · subst hni
    rw [redmap_congr_idx _ (redsteps_sub_redmap A n ilt').symm, redmap_last, subjourney_steps]
  rename' hni => hnni; push_neg at hnni
  -- Show that n ≠ 0
  have nnz : n ≠ 0 := by
    contrapose! hnni
    subst hnni
    exact (Nat.lt_one_iff.mp ((Nat.zero_add 1) ▸ ilt)).symm
  -- Handle the case where n = steps (reduced A)
  by_cases nl : n = steps (reduced A)
  · congr; subst nl
    rw [redmap_last]; rfl
  rename' nl => nnl; push_neg at nnl
  -- Prove bounds on i and n
  have snz : steps A ≠ 0 := by
    intro sz
    rw [redsteps_zero_steps_zero_iff.mpr sz, Nat.add_zero] at nlt
    exact nnz (Nat.lt_one_iff.mp nlt)
  have nlt' : n < steps (reduced A) :=
    lt_of_le_of_ne (Nat.le_of_lt_add_one nlt) nnl
  have ilt'' : i < steps (reduced A) := by
    apply lt_of_le_of_ne (Nat.le_of_lt_add_one ilt')
    exact ne_of_lt (lt_of_lt_of_le ilt (Nat.add_one_le_of_lt nlt'))
  have nlt'' : n < steps (reduced (recurrence_subjourney A)) + 1 := by
    rwa [← redsteps_recurrence _ snz]
  -- Rewrite the right-hand side in terms of the recurrence subjourney
  rw [redmap_recurrence A snz i ilt'']
  /- Rewriting the left-hand side is done in two steps:
     First we prepare an equation ('lhs') that rewrites the invocation
     of the reduced map of A to an invocation of the reduced map of the
     recurrence subjourney instead. -/
  have lhs := subjourney_congr_idx A (redmap_recurrence A snz n nlt') (redmap_lt A n nlt)
  have rmrsnlt : reduced_map (recurrence_subjourney A) n nlt'' < find_first_close_to_last A + 1 := by
    rw [← subjourney_steps A (find_first_close_to_last A) (first_close_to_last_lt A)]
    exact redmap_lt _ n nlt''
  -- Then rewrite the subjourney of 'A' to be a subjourney of the
  -- recurrence subjourney instead.
  rw [← subjourney_subjourney A rmrsnlt (first_close_to_last_lt A)] at lhs
  -- Finally, we use 'lhs' to rewrite the goal to a form where we can apply recursion
  rw [redmap_congr_journey lhs i _]
  exact redmap_sub_redmap (recurrence_subjourney A) n nlt'' i ilt
termination_by (steps A + 1)
decreasing_by
  apply Nat.add_one_lt_add_one_iff.mpr
  rw [subjourney_steps]
  exact first_close_to_last_lt' A snz

lemma redmap_redsub_comm {p : Nat} (A : Journey p) (i : Nat) (ilt : i < steps (reduced A) + 1) :
  subjourney (reduced A) i ilt = reduced (subjourney A (reduced_map A i ilt) (redmap_lt A i ilt)) := by
  apply (journey_ext_iff _ _).mpr; push_neg
  use (by rw [subjourney_steps, redsteps_sub_redmap])
  intro j jlt; symm
  rw [subjourney_steps] at jlt;
  rw [← redmap_cell, subjourney_cell, subjourney_cell]
  rw [cell_congr_idx A (redmap_sub_redmap A i ilt j jlt), redmap_cell]
  -- Now prove the pending bounds checks
  · exact Nat.le_of_lt_add_one jlt
  · -- NOTE: We have to provide all the arguments for
    -- 'redmap_sub_redmap' to work around a language bug
    -- ("declaration has metavariables")
    rw [redmap_sub_redmap A i ilt j jlt]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_add_one jlt) with jlti | hji
    · apply Nat.le_of_lt (redmap_mono A jlti ilt)
    · subst hji; rfl

-- Any reduced journey with more than one step never returns to the origin
lemma reduced_start_no_repeat {p : Nat} (A : Journey p) (sgt : 1 < steps (reduced A)) :
  ∀ i (ilt : i < steps (reduced A) + 1), i ≠ 0 → cell (reduced A) i ilt ≠ (0, 0) := by
  intro i ilt inz hcio
  rw [← redmap_cell] at hcio
  have soao := Nat.sub_one_add_one inz
  /- The outline for this proof is as follows:
     1) The first cell is close to cell 'i' (both are the origin)
     2) Cell 'i-1' was selected as the earliest cell close to cell 'i'
     3) Therefore, i = 1
     4) Since 1 < steps (reduced A) + 1, the reduced journey has a third cell
     5) Cell 1 was selected as the earliest cell close to cell 2
     6) Since cells 0 and 1 are both the origin, cell 0 is also close to cell 2
        which is a contradiction to (5) -/
  let sjA := subjourney A (reduced_map A (i - 1 + 1) (by linarith)) (redmap_lt A _ (by linarith))
  have h₀ : find_first_close_to_last sjA = reduced_map A (i - 1) (by linarith) := by
    exact redmap_consecutive A (i-1) _
  have h₁ : close p (cell sjA 0 (Nat.add_one_pos _)) (last sjA) := by
    -- TODO: Find a way to avoid this cell_congr / redmap_congr verbosity
    rw [cell_congr_idx A (redmap_congr_idx A (Nat.sub_one_add_one inz).symm ilt) (redmap_lt A _ (by linarith))] at hcio
    rw [journey_start, subjourney_last_cell, hcio]
    exact close_self _ _
  have h₂ := (redmap_consecutive A (i-1) _) ▸ Nat.le_zero.mp (first_close_to_last_is_first sjA 0 (Nat.add_one_pos _) h₁)
  have h₃ := redmap_zero_inv A (i-1) (by linarith) h₂
  apply Nat.add_one_inj.mpr at h₃
  rw [Nat.sub_one_add_one inz, Nat.zero_add] at h₃
  subst h₃
  -- Now that we've proven i = 1, we can clear most of the context
  clear h₂; clear h₁; clear h₀; clear sjA; clear inz
  have twolt : 1 + 1 < steps (reduced A) + 1 := Nat.add_one_lt_add_one_iff.mpr sgt
  let sjA := subjourney A (reduced_map A (1 + 1) twolt) (redmap_lt A _ twolt)
  have h₀ : find_first_close_to_last sjA = reduced_map A 1 ilt := redmap_consecutive A 1 twolt
  have h₁ : close p (cell sjA 0 (Nat.add_one_pos _)) (last sjA) := by
    rw [journey_start]
    convert first_close_to_last_is_close sjA using 1
    rw [subjourney_cell]
    convert hcio.symm
    rw [h₀]
    apply le_of_lt (redmap_mono A (by norm_num) twolt)
  -- Since cell 1 must be the first close to cell 2 and cell 0 is
  -- close to cell 2 (both are the origin) we reach a contradiction.
  have h₂ := (redmap_consecutive A 1 twolt) ▸ Nat.le_zero.mp (first_close_to_last_is_first sjA 0 (Nat.add_one_pos _) h₁)
  exact one_ne_zero (redmap_zero_inv A 1 ilt h₂)

/- An "efficient" journey will be one in which the angel never visits a cell they
   could have visited earlier. Both Máthé and Conway use this idea, though neither
   gives it a name.

   Formally, this states that any two distinct cells in the journey within distance
   'p' of each-other must appear consecutively in the journey. -/
def efficient {p : Nat} (A : Journey p) : Prop := ∀ i j (ilt : i < j) (jlt : j < steps A + 1),
  close p (cell A i (lt_trans ilt jlt)) (cell A j jlt) → i + 1 = j

-- A reduced journey is an efficient journey
lemma reduced_efficient {p : Nat} (A : Journey p) : efficient (reduced A) := by
  unfold efficient
  intro i₀ j₀ i₀lt j₀lt hclose
  rw [← redmap_cell, ← redmap_cell] at hclose
  -- Some useful definitions and results
  -- i₁, j₁, and k₁ correspond to the reduced map of i₀, j₀, and j₀-1 respectively
  let i₁ := reduced_map A i₀ (lt_trans i₀lt j₀lt)
  let j₁ := reduced_map A j₀ j₀lt
  have j₀plt := Nat.lt_of_le_of_lt (Nat.sub_le j₀ 1) j₀lt
  let k₁ := reduced_map A (j₀-1) j₀plt
  have j₁lt : j₁ < steps A + 1 := redmap_lt A j₀ j₀lt
  have i₁lt : i₁ < j₁ := redmap_mono A i₀lt j₀lt
  let sjA := subjourney A j₁ j₁lt
  have ssjA : steps sjA = j₁ := by rw [subjourney_steps]
  have i₁lt' : i₁ < steps sjA + 1 := lt_trans (lt_of_lt_of_eq i₁lt ssjA.symm) (Nat.lt_add_one _)
  -- Use the fact that 'first_close_to_last_is_first' to prove a lower bound on i₁
  have lei₁ := first_close_to_last_is_first sjA i₁ i₁lt' hclose
  have j₀ps : j₀ - 1 + 1 = j₀ := Nat.sub_one_add_one (Nat.ne_zero_of_lt i₀lt)
  -- 'j₀-1' maps to 'find_first_close_to_last sjA'
  have ffctl : find_first_close_to_last sjA = k₁ := by
    convert redmap_consecutive A (j₀ - 1) (j₀ps ▸ j₀lt)
    exact j₀ps.symm
  rw [ffctl] at lei₁; rename' lei₁ => k₁le
  -- If k₁ = i₁ we can use injectivity of the reduced map to close the goal
  by_cases hki : k₁ = i₁
  · rwa [← redmap_inj A (j₀-1) i₀ j₀plt (lt_trans i₀lt j₀lt) hki]
  rename' hki => hkni; push_neg at hkni
  -- If k₁ ≠ i₁, we can reach a contradiction
  have : j₀ - 1 < i₀ :=
    redmap_mono' A j₀plt (lt_trans i₀lt j₀lt) (lt_of_le_of_ne k₁le hkni)
  linarith
