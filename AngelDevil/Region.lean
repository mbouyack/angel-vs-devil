import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import AngelDevil.Util
import AngelDevil.Dupes

set_option linter.style.longLine false

def up (a : Int × Int) := (a.1, a.2 + 1)
def down (a : Int × Int) := (a.1, a.2 - 1)
def right (a : Int × Int) := (a.1 + 1, a.2)
def left (a : Int × Int) := (a.1 - 1, a.2)

lemma up_ne_self (a : Int × Int) : up a ≠ a := by
  unfold up
  intro h
  have := (Prod.ext_iff.mp h).2; dsimp at this
  absurd this; push_neg
  exact Int.ne_of_gt (Int.lt_succ _)

lemma down_ne_self (a : Int × Int) : down a ≠ a := by
  unfold down
  intro h
  have := (Prod.ext_iff.mp h).2; dsimp at this
  absurd this; push_neg
  exact Int.ne_of_lt (Int.pred_self_lt _)

lemma right_ne_self (a : Int × Int) : right a ≠ a := by
  unfold right
  intro h
  have := (Prod.ext_iff.mp h).1; dsimp at this
  absurd this; push_neg
  exact Int.ne_of_gt (Int.lt_succ _)

lemma left_ne_self (a : Int × Int) : left a ≠ a := by
  unfold left
  intro h
  have := (Prod.ext_iff.mp h).1; dsimp at this
  absurd this; push_neg
  exact Int.ne_of_lt (Int.pred_self_lt _)

lemma down_up (a : Int × Int) : down (up a) = a := by
  unfold down up; simp

lemma up_down (a : Int × Int) : up (down a) = a := by
  unfold down up; simp

lemma left_right (a : Int × Int) : left (right a) = a := by
  unfold left right; simp

lemma right_left (a : Int × Int) : right (left a) = a := by
  unfold left right; simp

def adjacent (a b : Int × Int) : Prop :=
  up a = b ∨ down a = b ∨ left a = b ∨ right a = b

-- 'a' is adjacent to 'b' if-and-only-if 'b' is adjacent to 'a'
lemma adjacent_comm (a b : Int × Int) :
  adjacent a b ↔ adjacent b a := by
  unfold adjacent
  constructor
  repeat
  · intro h
    rcases h with h₀ | h₁ | h₂ | h₃
    · right; left
      rw [← h₀, down_up]
    · left
      rw [← h₁, up_down]
    · right; right; right
      rw [← h₂, right_left]
    · right; right; left
      rw [← h₃, left_right]

lemma adjacent_ne (a b : Int × Int) :
  adjacent a b → a ≠ b := by
  unfold adjacent
  intro h
  contrapose! h; subst h
  exact ⟨up_ne_self a, down_ne_self a, left_ne_self a, right_ne_self a⟩

structure Path where
  route : List (Int × Int)
  hadj : ∀ i (ilt : i < route.length - 1),
    adjacent (route[i]'(
      lt_of_lt_of_le ilt (Nat.sub_le _ _)
    )) (route[i+1]'(
      Nat.add_lt_of_lt_sub ilt
    ))

-- Construct a path with just a single element
def path_mk_singleton (c : Int × Int) : Path where
  route := [c]
  hadj := by
    intro i ilt
    rw [List.length_singleton, Nat.sub_self] at ilt
    exact False.elim (Nat.not_lt_zero i ilt)

lemma path_mk_singleton_ne_nil (c : Int × Int) :
  (path_mk_singleton c).route ≠ [] := by
  unfold path_mk_singleton; dsimp
  exact List.cons_ne_nil c []

lemma path_mk_singleton_route (c : Int × Int) :
  (path_mk_singleton c).route = [c] := rfl

-- Extend an existing path by adding a new cell on the front
def path_extend (P : Path) (hnnil : P.route ≠ [])
  (c : Int × Int) (hadj : adjacent c (P.route.head hnnil)) : Path where
  route := c :: P.route
  hadj := by
    intro i ilt
    match i with
    | 0     =>
      rw [List.getElem_cons_zero, List.getElem_cons_succ]
      rwa [← List.head_eq_getElem_zero hnnil]
    | i + 1 =>
      rw [List.getElem_cons_succ, List.getElem_cons_succ]
      rw [List.length_cons, Nat.add_one_sub_one] at ilt
      exact P.hadj i (Nat.lt_sub_of_add_lt ilt)

-- Split an existing path and keep the latter section
def path_split_right (P : Path) (i : Nat) : Path where
  route := P.route.drop i
  hadj := by
    intro j jlt
    rw [List.getElem_drop, List.getElem_drop]
    rw [List.length_drop, Nat.sub_right_comm] at jlt
    convert P.hadj _ (Nat.add_lt_of_lt_sub jlt) using 2
    · exact Nat.add_comm _ _
    · rw [Nat.add_assoc, Nat.add_left_comm]

-- If 'i' is less than the length of the original path, the split path is non-nil
lemma path_split_right_ne_nil (P : Path) (i : Nat) (ilt : i < P.route.length) :
  (path_split_right P i).route ≠ [] := by
  apply List.ne_nil_of_length_pos
  unfold path_split_right; dsimp
  rw [List.length_drop]
  exact Nat.sub_pos_of_lt ilt

lemma path_split_right_length (P : Path) (i : Nat) :
  (path_split_right P i).route.length = P.route.length - i := by
  unfold path_split_right; dsimp
  rw [List.length_drop]

-- The head of the split path is the 'ith' cell of the old path
lemma path_split_right_head (P : Path) (i : Nat) (ilt : i < P.route.length) :
  (path_split_right P i).route.head (path_split_right_ne_nil P i ilt) = P.route[i]'ilt := by
  unfold path_split_right; dsimp
  rw [List.head_drop]

-- The last cell of the split path is the last cell of the original path
lemma path_split_right_getLast (P : Path) (i : Nat) (ilt : i < P.route.length) :
  (path_split_right P i).route.getLast (path_split_right_ne_nil P i ilt) =
  P.route.getLast (List.ne_nil_of_length_pos (Nat.zero_lt_of_lt ilt)) := by
  unfold path_split_right; dsimp
  rw [List.getLast_drop]

lemma path_split_right_subset (P : Path) (i : Nat) :
  (path_split_right P i).route ⊆ P.route := by
  unfold path_split_right; dsimp
  exact fun c cmem ↦ List.mem_of_mem_drop cmem

lemma path_split_right_getElem (P : Path) (i j : Nat) (jlt : j < P.route.length - i) :
  (path_split_right P i).route[j]'(by rwa [path_split_right_length]) =
  P.route[j + i]'(Nat.add_lt_of_lt_sub jlt) := by
  unfold path_split_right; dsimp
  rw [List.getElem_drop]; congr 1
  exact Nat.add_comm _ _

-- Indicates that a path exists from 'a' to 'b' using cells in 'L'
def path_exists (a b : Int × Int) (L : List (Int × Int)) : Prop :=
  ∃ (P : Path) (hnnil : P.route ≠ []),
  P.route ⊆ L ∧ P.route.head hnnil = a ∧ P.route.getLast hnnil = b

-- If a path exists in L₁, and L₁ ⊆ L₂, a path also exists in L₂
lemma path_exists_subset (a b : Int × Int) (L₁ L₂ : List (Int × Int)) (hss : L₁ ⊆ L₂) :
  path_exists a b L₁ → path_exists a b L₂ := by
  rintro ⟨P, hnnil, hss', hhead, hlast⟩
  exact ⟨P, hnnil, fun x xmem ↦ hss (hss' xmem), hhead, hlast⟩

-- If a path exists from 'a' to 'b', then a path exists from 'b' to 'a'
lemma path_exists_comm (a b : Int × Int) (L : List (Int × Int)) :
  path_exists a b L ↔ path_exists b a L := by
  constructor
  repeat
  · rintro ⟨P, hnnil, hss, hhead, hlast⟩
    -- Define P' as P, but with the direction reversed
    let P' := Path.mk P.route.reverse (fun i ilt ↦ by
      rw [List.getElem_reverse, List.getElem_reverse, adjacent_comm]
      rw [List.length_reverse] at ilt
      have ilt' : P.route.length - 1 - (i + 1) < P.route.length - 1 := by
        exact Nat.sub_lt (Nat.zero_lt_of_lt ilt) (Nat.add_one_pos _)
      convert P.hadj _ (Nat.sub_lt (Nat.zero_lt_of_lt ilt) (Nat.add_one_pos _)) using 2
      rw [← Nat.sub_sub, Nat.sub_one_add_one]
      exact Nat.sub_ne_zero_of_lt ilt
    )
    have hnnil' := List.reverse_ne_nil_iff.mpr hnnil
    use P', hnnil'
    unfold P'; dsimp
    rw [List.head_reverse hnnil', List.getLast_reverse hnnil']
    exact ⟨List.reverse_subset.mpr hss, hlast, hhead⟩

-- NOTE: Ideally we would use 'Finset' in the RegionBuilder instead of
-- 'List' with 'nodupe' assertions, but many of the operations and theorems
-- we would need are either missing, awkward, or non-computable.

-- This will be used by 'make_region' to build a region of contiguous cell
structure RegionBuilder where
  start : Int × Int
  region : List (Int × Int)
  pending : List (Int × Int)
  unvisited : List (Int × Int)
  -- 'start' is always in the region or about to be added to the region
  hstart : start ∈ region ++ pending
  -- 'region' has no duplicate elements
  hregion_nd : list_nodupes region
  -- 'pending' has no duplicate elements
  hpending_nd : list_nodupes pending
  -- 'unvisited' has no duplicate elements
  hunvisited_nd : list_nodupes unvisited
  -- There are no duplicate elements across all three lists
  hnodupes : list_nodupes (region ++ pending ++ unvisited)
  -- If a path exists from some cell to 'start' then either
  -- that cell is in the region, or there is a path from
  -- that cell to some cell in the region.
  hpath :
    ∀ a, path_exists a start (region ++ pending ++ unvisited) →
    a ∈ (region ++ pending) ∨
    ∃ b ∈ pending, path_exists b a (pending ++ unvisited)

def region_builder_all_cells (RB : RegionBuilder) : List (Int × Int) :=
  RB.region ++ RB.pending ++ RB.unvisited

-- In a RegionBuilder, no item will be an element of both 'pending' and 'unvisited'
lemma region_builder_notmem_pending_and_unvisited (RB : RegionBuilder) :
  ∀ c, ¬(c ∈ RB.pending ∧ c ∈ RB.unvisited) := by
  intro c ⟨hmem₀, hmem₁⟩
  apply list_nodupes_append_dupes_iff.mpr _ RB.hnodupes
  right; right
  exact ⟨c, List.mem_append_right _ hmem₀, hmem₁⟩

-- In a RegionBuilder, no item will be an element of both 'region' and 'unvisited'
lemma region_builder_notmem_region_and_unvisited (RB : RegionBuilder) :
  ∀ c, ¬(c ∈ RB.region ∧ c ∈ RB.unvisited) := by
  intro c ⟨hmem₀, hmem₁⟩
  apply list_nodupes_append_dupes_iff.mpr _ RB.hnodupes
  right; right
  exact ⟨c, List.mem_append_left _ hmem₀, hmem₁⟩

-- In a RegionBuilder, no item will be an element of both 'region' and 'pending'
lemma region_builder_notmem_region_and_pending (RB : RegionBuilder) :
  ∀ c, ¬(c ∈ RB.region ∧ c ∈ RB.pending) := by
  intro c ⟨hmem₀, hmem₁⟩
  apply list_nodupes_append_dupes_iff.mpr _ RB.hnodupes; left
  apply list_nodupes_append_dupes_iff.mpr; right; right
  exact ⟨c, hmem₀, hmem₁⟩

-- RegionBuilder corresponding to the initial state of the region building algorithm.
def region_builder_init (L : List (Int × Int)) (_start : (Int × Int)) : RegionBuilder where
  start := _start
  region := []
  pending := [_start]
  hstart := List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
  unvisited := (list_rm_dupes L).erase _start
  hregion_nd := list_nodupes_nil
  hpending_nd := list_nodupes_singleton _
  hunvisited_nd :=
    list_nodupes_erase_of_nodupes (list_rm_dupes L) (list_rm_dupes_nodupes L) _start
  hnodupes := by
    rw [List.nil_append]
    apply (list_nodupes_singleton_append_iff _ _).mpr
    constructor
    · apply list_nodupes_not_mem_erase_of_nodupes
      exact list_rm_dupes_nodupes L
    · apply list_nodupes_erase_of_nodupes
      exact list_rm_dupes_nodupes L
  hpath := by
    rw [List.nil_append]
    intro a pathex
    right
    use _start, List.mem_singleton_self _
    rwa [path_exists_comm]

lemma region_builder_init_subset_all_cells (L : List (Int × Int)) (start : (Int × Int)) :
  L ⊆ region_builder_all_cells (region_builder_init L start) := by
  unfold region_builder_init region_builder_all_cells; dsimp
  intro c cmem
  by_cases cs : c = start
  · subst cs
    exact List.mem_cons_self
  rename' cs => cns; push_neg at cns
  apply List.mem_cons_of_mem _ ((List.mem_erase_of_ne cns).mpr _)
  exact (list_rm_dupes_mem_iff _ _).mpr cmem

-- 'start' in 'region_builder_init' is as given
lemma region_builder_init_start (L : List (Int × Int)) (start : (Int × Int)) :
  (region_builder_init L start).start = start := rfl

-- In the region builder operations defined below, it is common to move an element
-- from the list on the right-hand side of an append, to the left. Showing that
-- membership is preserved across this operation is useful.
lemma list_mem_append_move_left_iff {α : Type} [BEq α] [LawfulBEq α]
  (L₁ : List α) {L₂ : List α} {a : α} (amem : a ∈ L₂) :
  ∀ (x : α), x ∈ L₁ ++ L₂ ↔ x ∈ (L₁ ++ [a]) ++ (List.erase L₂ a) := by
  intro x
  constructor
  · intro xmem
    by_cases xa : x = a
    · subst xa
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
    rename' xa => xnea; push_neg at xnea
    rcases List.mem_append.mp xmem with lhs | rhs
    · exact List.mem_append_left _ (List.mem_append_left _ lhs)
    · exact List.mem_append_right _ ((List.mem_erase_of_ne xnea).mpr rhs)
  · intro xmem
    rcases List.mem_append.mp xmem with lhs | rhs
    · rcases List.mem_append.mp lhs with lhs' | rhs'
      · exact List.mem_append_left _ lhs'
      · have xa := List.mem_singleton.mp rhs'
        subst xa
        exact List.mem_append_right _ amem
    · exact List.mem_append_right _ (List.mem_of_mem_erase rhs)

-- Try moving a cell from 'unvisited' to 'pending'
def region_builder_try_add_cell (RB : RegionBuilder) (c : Int × Int) : RegionBuilder :=
  if hmem : c ∈ RB.unvisited then RegionBuilder.mk
    RB.start
    RB.region
    (RB.pending ++ [c])
    (RB.unvisited.erase c)
    (by
      rcases List.mem_append.mp RB.hstart with lhs | rhs
      · exact List.mem_append_left _ lhs
      · exact List.mem_append_right _ (List.mem_append_left _ rhs)
    )
    RB.hregion_nd
    (by
      apply (list_nodupes_append_singleton_iff _ _).mpr
      exact ⟨
        fun hmem' ↦ region_builder_notmem_pending_and_unvisited RB c ⟨hmem', hmem⟩,
        RB.hpending_nd⟩
    )
    (list_nodupes_erase_of_nodupes _ RB.hunvisited_nd _)
    (by
      by_contra h₀
      rcases list_nodupes_append_dupes_iff.mp h₀ with h₁ | h₁ | h₁
      · rcases list_nodupes_append_dupes_iff.mp h₁ with h₂ | h₂| h₂
        · exact h₂ RB.hregion_nd
        · apply h₂
          apply (list_nodupes_append_singleton_iff _ _).mpr
          constructor
          · exact fun hmem' ↦ region_builder_notmem_pending_and_unvisited RB c ⟨hmem', hmem⟩
          · exact RB.hpending_nd
        · rcases h₂ with ⟨d, meml, memr⟩
          rcases List.mem_append.mp memr with lhs | rhs
          · exact region_builder_notmem_region_and_pending RB d ⟨meml, lhs⟩
          · exact region_builder_notmem_region_and_unvisited RB c ⟨(List.mem_singleton.mp rhs) ▸ meml, hmem⟩
      · exact h₁ (list_nodupes_erase_of_nodupes _ (RB.hunvisited_nd) _)
      · rcases h₁ with ⟨d, meml, memr⟩
        have memr' : d ∈ RB.unvisited := List.erase_subset memr
        rcases List.mem_append.mp meml with lhs | rhs
        · exact region_builder_notmem_region_and_unvisited RB d ⟨lhs, memr'⟩
        · rcases List.mem_append.mp rhs with lhs' | rhs'
          · exact region_builder_notmem_pending_and_unvisited RB d ⟨lhs', memr'⟩
          · exact list_nodupes_not_mem_erase_of_nodupes _ RB.hunvisited_nd _ ((List.mem_singleton.mp rhs') ▸ memr)
    )
    (by
      intro a pathex₀
      -- Some useful abbreviations
      let L₁ := (RB.pending ++ RB.unvisited)
      let L₁' := RB.region ++ L₁
      let L₂ := (RB.pending ++ [c]) ++ RB.unvisited.erase c
      let L₂' := RB.region ++ L₂
      -- We need to be able to transform paths in the old cells to paths in the new cells
      -- and vice-versa. We'll do this by showing each is a subset of the other.
      have hss₁₂ : L₁ ⊆ L₂ := by
        unfold L₁ L₂
        intro x xmem
        exact (list_mem_append_move_left_iff _ hmem x).mp xmem
      have hss₂₁ : L₂' ⊆ L₁' := by
        unfold L₁' L₂' L₁ L₂
        intro x xmem
        rcases List.mem_append.mp xmem with lhs | rhs
        · exact List.mem_append_left _ lhs
        · exact List.mem_append_right _ ((list_mem_append_move_left_iff _ hmem x).mpr rhs)
      -- Now we can use 'RB.hpath' to split into cases
      rw [List.append_assoc] at pathex₀
      have pathex₁ := path_exists_subset a RB.start L₂' L₁' hss₂₁ pathex₀
      unfold L₁' L₁ at pathex₁
      rw [← List.append_assoc] at pathex₁
      rcases RB.hpath a pathex₁ with lhs | rhs
      · left
        rcases List.mem_append.mp lhs with lhs' | rhs'
        · exact List.mem_append_left _ lhs'
        · exact List.mem_append_right _ (List.mem_append_left _ rhs')
      · right
        rcases rhs with ⟨b, bmem, pathex₂⟩
        exact ⟨b, List.mem_append_left _ bmem, path_exists_subset b a _ L₂ hss₁₂ pathex₂⟩
    )
  else RB

-- Moving a cell from 'unvisited' to 'pending' will always result in
-- and non-empty pending list if the original pending list was non-empty
lemma region_builder_try_add_cell_pending_ne_nil (RB : RegionBuilder) (c : Int × Int) :
  RB.pending ≠ [] → (region_builder_try_add_cell RB c).pending ≠ [] := by
  unfold region_builder_try_add_cell
  intro h
  split_ifs with h'
  · exact List.append_ne_nil_of_left_ne_nil h _
  · exact h

-- Calling 'region_builder_try_add_cell' on a RegionBuilder has no effect
-- on the sum of the lengths of the 'pending' and 'unvisited' lists
lemma region_builder_try_add_cell_length_invariant (RB : RegionBuilder) (c : Int × Int) :
  (region_builder_try_add_cell RB c).pending.length +
  (region_builder_try_add_cell RB c).unvisited.length =
  RB.pending.length + RB.unvisited.length := by
  unfold region_builder_try_add_cell
  split_ifs with h
  · dsimp
    rw [List.length_append, List.length_singleton]
    rw [add_assoc, add_comm 1, List.length_erase_of_mem h]
    rw [Nat.sub_one_add_one (Nat.ne_zero_of_lt (List.length_pos_of_mem h))]
  · rfl

-- Any member of the partial region in 'RB' will still be present
-- after calling region_builder_try_add_cell
lemma region_builder_mem_try_add_cell_of_mem
  (RB : RegionBuilder) (oldc newc : Int × Int) (oldcmem : oldc ∈ RB.region) :
  oldc ∈ (region_builder_try_add_cell RB newc).region := by
  unfold region_builder_try_add_cell
  split_ifs with h
  · dsimp; assumption
  · assumption

-- Calling 'region_builder_try_add_cell' has no effect on 'start'
lemma region_builder_try_add_cell_start (RB : RegionBuilder) (c : Int × Int) :
  (region_builder_try_add_cell RB c).start = RB.start := by
  unfold region_builder_try_add_cell
  split_ifs with h
  · dsimp
  · rfl

-- Proves the conditions under which a cell will not be an element of 'unvisited'
-- after calling 'region_builder_try_add_cell'
lemma region_builder_try_add_cell_not_mem_unvisited (RB : RegionBuilder) (c : Int × Int) :
  ∀ a, a = c ∨ a ∉ RB.unvisited → a ∉ (region_builder_try_add_cell RB c).unvisited := by
  unfold region_builder_try_add_cell
  intro a h
  rcases h with lhs | rhs
  · subst lhs
    split_ifs with h
    · dsimp
      apply list_nodupes_not_mem_erase_of_nodupes
      exact RB.hunvisited_nd
    · assumption
  · split_ifs with h
    · dsimp
      exact fun amem ↦ rhs (List.erase_subset amem)
    · assumption

-- If the pending list is non-nil, adding more cells to it will not change the head
lemma region_builder_try_add_cell_pending_head
  (RB : RegionBuilder) (c : Int × Int) (hnnil : RB.pending ≠ []) :
  (region_builder_try_add_cell RB c).pending.head
  (region_builder_try_add_cell_pending_ne_nil _ _ hnnil) = RB.pending.head hnnil := by
  unfold region_builder_try_add_cell
  split_ifs with h
  · exact List.head_append_left hnnil
  · rfl

-- All cells in the region builder prior to call 'try_add_cells' will still be in the region builder after.
lemma region_builder_try_add_cell_subset_all_cells
  (RB : RegionBuilder) (c : Int × Int) :
  region_builder_all_cells RB ⊆ region_builder_all_cells (region_builder_try_add_cell RB c) := by
  unfold region_builder_try_add_cell
  split_ifs with h
  · unfold region_builder_all_cells; dsimp
    intro x xmem
    rcases List.mem_append.mp xmem with lhs | rhs
    · rcases List.mem_append.mp lhs with lhs' | rhs'
      · exact List.mem_append_left _ (List.mem_append_left _ lhs')
      · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ rhs'))
    · by_cases xc : x = c
      · subst xc
        apply List.mem_append_left _ (List.mem_append_right _ _)
        exact List.mem_append_right _ (List.mem_singleton_self _)
      · rename' xc => xnc; push_neg at xnc
        apply List.mem_append_right
        exact (List.mem_erase_of_ne xnc).mpr rhs
  · unfold region_builder_all_cells
    intro x xmem
    assumption

-- Missing list theorem
lemma list_mem_tail_of_mem_of_ne_head {α : Type} (L : List α) (hnnil : L ≠ []) :
  ∀ x ∈ L, x ≠ L.head hnnil → x ∈ L.tail := by
  intro x xmem xneh
  rw [← List.head_cons_tail L hnnil] at xmem
  exact Or.elim (List.mem_cons.mp xmem) (fun h ↦ False.elim (xneh h)) id

-- Adds the first pending cell to the region.
-- This requires that 'pending' by non-nil and 'unvisited' contain
-- no elements adjacent to the first pending cell.
def region_builder_add_pending_of_ne_nil (RB : RegionBuilder) (hnnil : RB.pending ≠ [])
  (hnadj : ∀ c ∈ RB.unvisited, ¬adjacent c (RB.pending.head hnnil)) : RegionBuilder where
  start := RB.start
  region := (RB.pending.head hnnil)::RB.region
  pending := RB.pending.tail
  unvisited := RB.unvisited
  hstart := by
    rcases List.mem_append.mp RB.hstart with lhs | rhs
    · exact List.mem_append_left _ (List.mem_cons.mpr (Or.inr lhs))
    · rcases List.mem_cons.mp ((List.head_cons_tail _ hnnil) ▸ rhs) with lhs' | rhs'
      · exact List.mem_cons.mpr (Or.inl lhs')
      · exact List.mem_cons.mpr (Or.inr (List.mem_append_right _ rhs'))
  hregion_nd := by
    apply (list_nodupes_cons_iff _ _).mpr
    constructor
    · intro h
      exact region_builder_notmem_region_and_pending _ _ ⟨h, List.head_mem hnnil⟩
    · exact RB.hregion_nd
  hpending_nd :=
    list_nodupes_tail_of_nodupes RB.pending RB.hpending_nd
  hunvisited_nd :=
    RB.hunvisited_nd
  hnodupes := by
    by_contra! h₀
    rcases list_nodupes_append_dupes_iff.mp h₀ with h₁ | h₁ | h₁
    · rcases list_nodupes_append_dupes_iff.mp h₁ with h₂ | h₂ | h₂
      · exact h₂ ((list_nodupes_cons_iff _ _).mpr ⟨
          fun h ↦ region_builder_notmem_region_and_pending _ _ ⟨h, List.head_mem hnnil⟩,
          RB.hregion_nd⟩)
      · exact h₂ (((list_nodupes_cons_iff _ _).mp ((List.head_cons_tail RB.pending hnnil) ▸ RB.hpending_nd)).2)
      · rcases h₂ with ⟨a, lmem, rmem⟩
        rcases List.mem_cons.mp lmem with h₃ | h₃
        · subst h₃
          exact ((list_nodupes_head_tail_iff RB.pending hnnil).mp RB.hpending_nd).1 rmem
        · apply region_builder_notmem_region_and_pending RB a
          exact ⟨h₃, List.mem_of_mem_tail rmem⟩
    · exact h₁ RB.hunvisited_nd
    · rcases h₁ with ⟨a, lmem, rmem⟩
      rcases List.mem_append.mp lmem with h₁ | h₁
      · rcases List.mem_cons.mp h₁ with h₂ | h₂
        · subst h₂
          exact region_builder_notmem_pending_and_unvisited _ _ ⟨List.head_mem hnnil, rmem⟩
        · exact region_builder_notmem_region_and_unvisited _ _ ⟨h₂, rmem⟩
      · exact region_builder_notmem_pending_and_unvisited _ _ ⟨List.mem_of_mem_tail h₁, rmem⟩
  hpath := by
    let L₁ := RB.region ++ RB.pending
    let L₁' := L₁ ++ RB.unvisited
    let L₂ := RB.pending.head hnnil :: RB.region ++ RB.pending.tail
    let L₂' := L₂ ++ RB.unvisited
    have hss₂₁ : L₂' ⊆ L₁' := by
      unfold L₁' L₂' L₁ L₂
      intro c cmem
      rcases List.mem_append.mp cmem with lhs | rhs
      · rcases List.mem_append.mp lhs with lhs' | rhs'
        · rcases List.mem_cons.mp lhs' with lhs'' | rhs''
          · subst lhs''
            exact List.mem_append_left _ (List.mem_append_right _ (List.head_mem hnnil))
          · exact List.mem_append_left _ (List.mem_append_left _ rhs'')
        · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_of_mem_tail rhs'))
      · exact List.mem_append_right _ rhs
    intro a pathex₀
    -- Move the new path back to the old cells
    have pathex₁ := path_exists_subset a RB.start L₂' L₁' hss₂₁ pathex₀
    -- The logic here is a bit awkward since we need the negation of the
    -- left-hand-side to prove the right-hand-side. The trick is to split
    -- into cases based on the left-hand side and show the goal follows
    -- trivially. Then we can prove the left-hand side by contradiction.
    -- This leaves us with the setup we need for the right-hand side.
    by_cases amem : a ∈ RB.pending.head hnnil :: RB.region ++ RB.pending.tail
    · left; assumption
    right
    rename' amem => anmem
    -- Now split into cases based on RB.hpath
    rcases RB.hpath a pathex₁ with lhs | rhs
    · absurd anmem
      rcases List.mem_append.mp lhs with lhs' | rhs'
      · exact List.mem_append_left _ (List.mem_cons_of_mem _ lhs')
      · rw [← List.head_cons_tail _ hnnil] at rhs'
        rcases List.mem_cons.mp rhs' with lhs'' | rhs''
        · subst lhs''
          exact List.mem_append_left _ List.mem_cons_self
        · exact List.mem_append_right _ rhs''
    · rcases rhs with ⟨b, bmem, P, hnnil', hss, hhead, hlast⟩
      -- If the first pending cell was not on the old route, we can reuse it
      by_cases hhnotin : RB.pending.head hnnil ∉ P.route
      · -- Since 'b' is on P, it can't be the first pending cell
        have bneh : b ≠ RB.pending.head hnnil := by
          contrapose! hhnotin; subst hhnotin
          rw [← hhead]
          exact List.head_mem _
        have btail := list_mem_tail_of_mem_of_ne_head RB.pending hnnil b bmem bneh
        use b, btail, P, hnnil'
        apply And.intro _ (And.intro hhead hlast)
        intro x xmem
        rcases List.mem_append.mp (hss xmem) with lhs | rhs
        · apply List.mem_append_left
          have xneh : x ≠ RB.pending.head hnnil := by
            intro h; subst h
            exact hhnotin xmem
          exact list_mem_tail_of_mem_of_ne_head RB.pending hnnil x lhs xneh
        · exact List.mem_append_right _ rhs
      rename' hhnotin => hheadin; push_neg at hheadin
      have lennz : P.route.length ≠ 0 :=
        Nat.ne_zero_of_lt (List.length_pos_of_ne_nil hnnil')
      -- Define a function to check if a cell in P is pending.head
      let f : Fin (P.route.length - 1 + 1) → Prop :=
        fun i ↦ RB.pending.head hnnil = P.route[i.1]'(by
          convert i.2; rwa [Nat.sub_one_add_one]
        )
      -- Get the location within the existing path of RB.pending.head
      -- To handle the case where pending.head appears more than once
      -- in the path, we'll need to get the last instance.
      rcases List.getElem_of_mem hheadin with ⟨i, ilt, hri⟩
      let j := (_find_last f).1
      let jlt : j < P.route.length - 1 + 1 := (_find_last f).2
      rw [Nat.sub_one_add_one lennz] at jlt
      have fsat : ∃ x, f x :=
        ⟨⟨i, by rwa [Nat.sub_one_add_one lennz]⟩, hri.symm⟩
      have hrj : P.route[j]'jlt = RB.pending.head hnnil :=
        (_find_last_is_sat f fsat).symm
      -- If i + 1 = P.route.length, a = RB.pending.head, which is a contradiction
      have jslt : j + 1 < P.route.length := by
        apply Nat.add_lt_of_lt_sub (Nat.lt_of_le_of_ne (Nat.le_sub_one_of_lt jlt) _)
        push_neg
        intro jrlp
        apply anmem
        rw [← hrj, getElem_congr_idx jrlp, ← List.getLast_eq_getElem hnnil', hlast]
        exact List.mem_append_left _ List.mem_cons_self
      -- Define P' as the path that begins just after RB.pending.head
      let P' := path_split_right P (j + 1)
      have hnnil'' : P'.route ≠ [] := path_split_right_ne_nil P (j + 1) jslt
      have hhnotin : RB.pending.head hnnil ∉ P'.route := by
        intro h
        -- Suppose pending.head still appears in P'
        -- Let 'k' be its location within the route
        rcases List.getElem_of_mem h with ⟨k, klt, hrk⟩
        rw [path_split_right_length] at klt
        rw [path_split_right_getElem _ _ _ klt] at hrk
        have kh1lt : k + (j + 1) < P.route.length - 1 + 1 := by
          rw [Nat.sub_one_add_one lennz]
          exact Nat.add_lt_of_lt_sub klt
        -- Use the fact that 'j' should be the last location of
        -- pending.head in P to get a contradiction
        have hk1le : k + (j + 1) ≤ j := by
          have := Fin.val_le_of_le (_find_last_is_last f ⟨k + (j + 1), kh1lt⟩ hrk.symm)
          simp at this
          exact this
        absurd hk1le; push_neg
        rw [Nat.add_comm, Nat.add_assoc, Nat.add_comm 1]
        apply Nat.lt_add_right_iff_pos.mpr
        exact Nat.add_one_pos _
      -- Define 'c' as the head of the new path
      let c := P'.route.head hnnil''
      have cmem : c ∈ RB.pending.tail := by
        have cadj : adjacent c (RB.pending.head hnnil) := by
          unfold c
          rw [← hrj, path_split_right_head P (j + 1) jslt, adjacent_comm]
          exact P.hadj j (Nat.lt_sub_of_add_lt jslt)
        -- First show that 'c' is in either 'pending' or 'unvisited'
        have cmem : c ∈ RB.pending ++ RB.unvisited :=
          hss (path_split_right_subset P (j + 1) (List.head_mem hnnil''))
        -- Show that if c were in 'unvisited' it would be
        -- adjacent to pending.head - a contradiction
        have cnmem : c ∉ RB.unvisited := by
          by_contra! cmem'
          exact hnadj c cmem' cadj
        apply Or.elim (List.mem_append.mp cmem) _ (fun h ↦ False.elim (cnmem h))
        intro cmem'
        exact list_mem_tail_of_mem_of_ne_head _ hnnil c cmem' (adjacent_ne _ _ cadj)
      use c, cmem, P', hnnil''
      apply And.intro _ (And.intro rfl (by rwa [path_split_right_getLast _ _ jslt]))
      -- Finish the goal by showing P'.route ⊆ RB.pending.tail ++ RB.unvisited
      intro x xmem
      rcases List.mem_append.mp (hss (path_split_right_subset _ _ xmem)) with lhs | rhs
      · apply List.mem_append_left _ (list_mem_tail_of_mem_of_ne_head _ hnnil x lhs _)
        contrapose! hhnotin
        rwa [← hhnotin]
      · exact List.mem_append_right _ rhs

-- The length of 'pending' + 'unvisted' after moving the first
-- pending cell to 'region' will be one less than it was previously.
lemma region_builder_add_pending_of_ne_nil_length (RB : RegionBuilder) (hnnil : RB.pending ≠ [])
  (hnadj : ∀ c ∈ RB.unvisited, ¬adjacent c (RB.pending.head hnnil)) :
  (region_builder_add_pending_of_ne_nil RB hnnil hnadj).pending.length +
  (region_builder_add_pending_of_ne_nil RB hnnil hnadj).unvisited.length =
  RB.pending.length + RB.unvisited.length - 1 := by
  unfold region_builder_add_pending_of_ne_nil; dsimp
  rw [List.length_tail]
  rw [← Nat.sub_add_comm _]
  exact Nat.add_one_le_of_lt (List.length_pos_of_ne_nil hnnil)

-- Any member of the partial region in 'RB' will still be present
-- after calling region_builder_add_pending_of_ne_nil
lemma region_builder_mem_add_pending_of_mem
  (RB : RegionBuilder) (hnnil : RB.pending ≠ []) (c : Int × Int) (cmem : c ∈ RB.region)
  (hnadj : ∀ c ∈ RB.unvisited, ¬adjacent c (RB.pending.head hnnil)) :
  c ∈ (region_builder_add_pending_of_ne_nil RB hnnil hnadj).region := by
  unfold region_builder_add_pending_of_ne_nil; dsimp
  apply List.mem_cons_of_mem _ cmem

lemma region_builder_add_pending_start (RB : RegionBuilder) (hnnil : RB.pending ≠ [])
  (hnadj : ∀ c ∈ RB.unvisited, ¬adjacent c (RB.pending.head hnnil)) :
  (region_builder_add_pending_of_ne_nil RB hnnil hnadj).start = RB.start := by
  unfold region_builder_add_pending_of_ne_nil; dsimp

-- All cells in the region builder prior to call 'add_pending' will still be in the region builder after.
lemma region_builder_add_pending_subset_all_cells (RB : RegionBuilder) (hnnil : RB.pending ≠ [])
  (hnadj : ∀ c ∈ RB.unvisited, ¬adjacent c (RB.pending.head hnnil)) :
  region_builder_all_cells RB ⊆
  region_builder_all_cells (region_builder_add_pending_of_ne_nil RB hnnil hnadj) := by
  unfold region_builder_add_pending_of_ne_nil region_builder_all_cells; dsimp
  intro x xmem
  rcases List.mem_append.mp xmem with lhs | rhs
  · rcases List.mem_append.mp lhs with lhs' | rhs'
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ lhs'))
    · by_cases xh : x = RB.pending.head hnnil
      · subst xh
        exact List.mem_cons_self
      · rename' xh => xnh; push_neg at xnh
        apply List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ _))
        exact list_mem_tail_of_mem_of_ne_head _ hnnil x rhs' xnh
  · exact List.mem_cons_of_mem _ (List.mem_append_right _ rhs)

-- Main processing step of the 'make_region' algorithm.
-- This moves the head of the 'pending' list into the region and
-- attempts to add the four orthogonally adjacent cells to the
-- 'pending' list if they are in the 'unvisited' list.
-- This is defined separately from 'make_region_impl' to make it
-- easier to prove termination.
def make_region_step (RB : RegionBuilder) (hnnil : RB.pending ≠ []) : RegionBuilder :=
  (region_builder_add_pending_of_ne_nil (
    region_builder_try_add_cell (
    region_builder_try_add_cell (
    region_builder_try_add_cell (
    region_builder_try_add_cell RB
      ((RB.pending.head hnnil).1 + 1, (RB.pending.head hnnil).2))
      ((RB.pending.head hnnil).1 - 1, (RB.pending.head hnnil).2))
      ((RB.pending.head hnnil).1, (RB.pending.head hnnil).2 + 1))
      ((RB.pending.head hnnil).1, (RB.pending.head hnnil).2 - 1))
    (by
      apply region_builder_try_add_cell_pending_ne_nil
      apply region_builder_try_add_cell_pending_ne_nil
      apply region_builder_try_add_cell_pending_ne_nil
      exact region_builder_try_add_cell_pending_ne_nil _ _ hnnil)
    (by
      intro c cadj
      contrapose! cadj
      -- Use the magic of 'repeat' to show that 'c' must be
      -- adjacent to the original RB.pending.head
      repeat rw [region_builder_try_add_cell_pending_head _ _ (by
        repeat apply region_builder_try_add_cell_pending_ne_nil
        assumption)] at cadj
      rw [adjacent_comm] at cadj
      -- Now we just need to handle each of the 4 directions in
      -- the appropriate order to unwind the goal.
      apply region_builder_try_add_cell_not_mem_unvisited
      by_cases hdown : c = down (RB.pending.head hnnil)
      · left; exact hdown
      right
      apply region_builder_try_add_cell_not_mem_unvisited
      by_cases hup : c = up (RB.pending.head hnnil)
      · left; exact hup
      right
      apply region_builder_try_add_cell_not_mem_unvisited
      by_cases hleft : c = left (RB.pending.head hnnil)
      · left; exact hleft
      right
      apply region_builder_try_add_cell_not_mem_unvisited
      by_cases hright : c = right (RB.pending.head hnnil)
      · left; exact hright
      -- Now that we've ruled out all possible adjacencies,
      -- we can find a contradiction with 'cadj'
      absurd cadj
      unfold adjacent; push_neg at *
      exact ⟨hup.symm, hdown.symm, hleft.symm, hright.symm⟩
    ))

-- All cells in the region builder prior to call 'make_region_step' will still be in the region builder after.
lemma make_region_step_subset_all_cells (RB : RegionBuilder) (hnnil : RB.pending ≠ []) :
  region_builder_all_cells RB ⊆
  region_builder_all_cells (make_region_step RB hnnil) := by
  unfold make_region_step
  intro x xmem
  apply region_builder_add_pending_subset_all_cells
  repeat apply region_builder_try_add_cell_subset_all_cells
  assumption

-- Reusable termination proof for 'make_region' and related theorems
lemma make_region_terminates (RB : RegionBuilder) (hnnil : RB.pending ≠ []) :
  (make_region_step RB hnnil).pending.length +
  (make_region_step RB hnnil).unvisited.length <
  RB.pending.length + RB.unvisited.length := by
  unfold make_region_step
  rw [region_builder_add_pending_of_ne_nil_length]
  repeat rw [region_builder_try_add_cell_length_invariant]
  exact Nat.sub_one_lt (Nat.ne_zero_of_lt (Nat.add_pos_left (List.length_pos_of_ne_nil hnnil) _))

-- Main loop of the region builder algorithm
-- The algorithm terminates if there are no pending cells, otherwise
-- it tries to add the four cells orthogonally connected to the current
-- pending cell, adds the current pending cell to the region, and then
-- recurses.
def make_region_impl (RB : RegionBuilder) :=
  if hnil : RB.pending = [] then RB else
  make_region_impl (make_region_step RB hnil)
termination_by RB.pending.length + RB.unvisited.length
decreasing_by
  exact make_region_terminates _ _

-- The RegionBuilder returned by 'make_region_impl' has pending = []
lemma make_region_impl_pending_nil (RB : RegionBuilder) :
  (make_region_impl RB).pending = [] := by
  unfold make_region_impl
  split_ifs with h
  · assumption
  apply make_region_impl_pending_nil
termination_by RB.pending.length + RB.unvisited.length
decreasing_by
  exact make_region_terminates _ _

-- 'start' in 'make_region_impl' is as given
lemma make_region_impl_start (RB : RegionBuilder) :
  (make_region_impl RB).start = RB.start := by
  unfold make_region_impl make_region_step
  split_ifs with h
  · rfl
  rw [make_region_impl_start]
  rw [region_builder_add_pending_start]
  repeat rw [region_builder_try_add_cell_start]
termination_by RB.pending.length + RB.unvisited.length
decreasing_by
  exact make_region_terminates _ _

-- Any member of the partial region in 'RB' will still be present
-- after calling make_region_impl
lemma make_region_impl_mem_of_mem
  (RB : RegionBuilder) (c : Int × Int) (cmem : c ∈ RB.region) :
  c ∈ (make_region_impl RB).region := by
  unfold make_region_impl
  split_ifs with h
  · assumption
  push_neg at h
  apply make_region_impl_mem_of_mem
  apply region_builder_mem_add_pending_of_mem
  repeat apply region_builder_mem_try_add_cell_of_mem
  assumption
termination_by RB.pending.length + RB.unvisited.length
decreasing_by
  exact make_region_terminates _ _

-- All cells in the region builder prior to call 'make_region_impl' will still be in the region builder after.
lemma make_region_impl_subset_all_cells (RB : RegionBuilder) :
  region_builder_all_cells RB ⊆ region_builder_all_cells (make_region_impl RB) := by
  unfold make_region_impl
  intro x xmem
  split_ifs with h
  · assumption
  · apply make_region_impl_subset_all_cells
    apply make_region_step_subset_all_cells
    assumption
termination_by RB.pending.length + RB.unvisited.length
decreasing_by
  exact make_region_terminates _ _

-- Find the region of orthogonally connected cells in 'L' which contains 'start'
-- Note that if start ∉ L it will return a 1-cell region with just 'start'.
def make_region (L : List (Int × Int)) (start : (Int × Int)) : RegionBuilder :=
  make_region_impl (region_builder_init L start)

-- 'start' in a 'make_region' is as given
lemma make_region_start (L : List (Int × Int)) (start : (Int × Int)) :
  (make_region L start).start = start := by
  unfold make_region
  rw [make_region_impl_start, region_builder_init_start]

-- 'pending' in a 'make_region' is nil
lemma make_region_pending_nil (L : List (Int × Int)) (start : (Int × Int)) :
  (make_region L start).pending = [] := by
  unfold make_region
  exact make_region_impl_pending_nil _

def Region (L : List (Int × Int)) (start : (Int × Int)) : List (Int × Int) :=
  (make_region L start).region

-- The starting cell is a member of the resulting region
lemma region_start_mem (L : List (Int × Int)) (start : (Int × Int)) :
  start ∈ Region L start := by
  unfold Region
  apply Or.elim (List.mem_append.mp (make_region L start).hstart)
  · intro h
    rwa [make_region_start] at h
  · intro h
    rw [make_region_pending_nil L start] at h
    exact False.elim (List.not_mem_nil h)

-- No region is empty (since it contains at least 'start')
lemma region_ne_nil (L : List (Int × Int)) (start : (Int × Int)) :
  Region L start ≠ [] :=
  List.ne_nil_of_mem (region_start_mem L start)

lemma region_mem_of_path_exists (L : List (Int × Int)) (start : (Int × Int)) :
  ∀ a, (path_exists a start L) → a ∈ Region L start := by
  unfold Region make_region
  intro a pathex
  have hss : L ⊆ region_builder_all_cells (make_region_impl (region_builder_init L start)) := by
    intro x xmem
    apply make_region_impl_subset_all_cells
    exact region_builder_init_subset_all_cells _ _ xmem
  have pathex' := path_exists_subset a start _ _ hss pathex
  have hpath := (make_region_impl (region_builder_init L start)).hpath a
  rw [make_region_impl_start, region_builder_init_start] at hpath
  rcases hpath pathex' with lhs | rhs
  · rcases List.mem_append.mp lhs with lhs' | rhs'
    · assumption
    · absurd rhs'
      convert List.not_mem_nil
      exact make_region_pending_nil _ _
  · rcases rhs with ⟨b, bmem, _⟩
    absurd bmem
    convert List.not_mem_nil
    exact make_region_pending_nil _ _
