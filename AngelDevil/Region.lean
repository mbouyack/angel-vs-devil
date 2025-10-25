import Mathlib.Algebra.Group.Prod
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import AngelDevil.Unit
import AngelDevil.Util
import AngelDevil.Dupes

set_option linter.style.longLine false

def up (a : Int × Int) := (a.1 + 0, a.2 + 1)
def down (a : Int × Int) := (a.1 + 0, a.2 + -1)
def right (a : Int × Int) := (a.1 + 1, a.2 + 0)
def left (a : Int × Int) := (a.1 - 1, a.2 + 0)

-- Two cells are orthogonally adjacent if adding some
-- unit vector to one results in the other.
def adjacent (a b : Int × Int) : Prop :=
  ∃ u : UVec, a + u = b

-- 'a' is adjacent to 'b' if-and-only-if 'b' is adjacent to 'a'
lemma adjacent_comm (a b : Int × Int) :
  adjacent a b ↔ adjacent b a := by
  constructor
  · intro h
    rcases h with ⟨u, rfl⟩
    use uvec_neg u
    rw [uvec_coe_neg, add_assoc, add_neg_cancel, add_zero]
  · intro h
    rcases h with ⟨u, rfl⟩
    use uvec_neg u
    rw [uvec_coe_neg, add_assoc, add_neg_cancel, add_zero]

lemma up_adjacent (a : Int × Int) :
  adjacent (up a) a := by
  rw [adjacent_comm]
  use uvec_up
  rw [Prod.add_def]; rfl

lemma down_adjacent (a : Int × Int) :
  adjacent (down a) a := by
  rw [adjacent_comm]
  use uvec_down
  rw [Prod.add_def]; rfl

lemma right_adjacent (a : Int × Int) :
  adjacent (right a) a := by
  rw [adjacent_comm]
  use uvec_right
  rw [Prod.add_def]; rfl

lemma left_adjacent (a : Int × Int) :
  adjacent (left a) a := by
  rw [adjacent_comm]
  use uvec_left
  rw [Prod.add_def]; rfl

lemma adjacent_eq_dir_iff (a b : Int × Int) :
  a = up b ∨ a = down b ∨ a = left b ∨ a = right b ↔ adjacent a b := by
  constructor
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · exact up_adjacent _
    · exact down_adjacent _
    · exact left_adjacent _
    · exact right_adjacent _
  · intro h
    rw [adjacent_comm] at h
    rcases h with ⟨u, rfl⟩
    rw [Prod.add_def]
    rcases uvec_coe_eq u with h₀ | h₁ | h₂ | h₃
    · left; rw [h₀]; rfl
    · right; left; rw [h₁]; rfl
    · right; right; left; rw [h₂]; rfl
    · right; right; right; rw [h₃]; rfl

-- If two cells are adjacent they are different cells
lemma adjacent_ne (a b : Int × Int) :
  adjacent a b → a ≠ b := by
  rintro ⟨u, hu⟩
  by_contra! hab
  rw [← hab, add_eq_left] at hu
  obtain ⟨h₀, h₁⟩ := Prod.ext_iff.mp hu
  rcases uvec_xnez_or_ynez u with lhs | rhs
  · apply lhs
    simp at h₀
    rw [← h₀]; rfl
  · apply rhs
    simp at h₁
    rw [← h₁]; rfl

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

lemma path_extend_ne_nil (P : Path) (hnnil : P.route ≠ [])
  (c : Int × Int) (hadj : adjacent c (P.route.head hnnil)) :
  (path_extend P hnnil c hadj).route ≠ [] := by
  unfold path_extend; dsimp
  exact List.cons_ne_nil _ _

lemma path_extend_head (P : Path) (hnnil : P.route ≠ [])
  (c : Int × Int) (hadj : adjacent c (P.route.head hnnil)) :
  (path_extend P hnnil c hadj).route.head (path_extend_ne_nil _ _ _ _) = c := by
  unfold path_extend; dsimp

lemma path_extend_getLast (P : Path) (hnnil : P.route ≠ [])
  (c : Int × Int) (hadj : adjacent c (P.route.head hnnil)) :
  (path_extend P hnnil c hadj).route.getLast (path_extend_ne_nil _ _ _ _) =
  P.route.getLast hnnil := by
  unfold path_extend; dsimp
  rw [List.getLast_cons hnnil]

lemma path_extend_route (P : Path) (hnnil : P.route ≠ [])
  (c : Int × Int) (hadj : adjacent c (P.route.head hnnil)) :
  (path_extend P hnnil c hadj).route = c :: P.route := rfl

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
  -- 'start' is at the end of 'region' or is the head of 'pending'
  -- The statement is slightly awkward due to the conversion from '∧' to '→'
  hstart :
    if hnnil : region = [] then
    ¬((hnnil : pending ≠ []) → start ≠ pending.head hnnil) else
    start = region.getLast hnnil
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
  -- For every cell in the region, there is a path from that
  -- cell to the starting cell. The constraint is stated in
  -- such a way as to exclude the last cell added to the region
  -- from the path cells. This will be crucial for proving
  -- the 'region_recurrence' later.
  hpath' :
    ∀ a ∈ region ++ pending,
    path_exists a start (a :: (pending.reverse ++ region).tail)

def region_builder_all_cells (RB : RegionBuilder) : List (Int × Int) :=
  RB.region ++ RB.pending ++ RB.unvisited

-- In a RegionBuilder, no item will be an element of both 'pending' and 'unvisited'
lemma region_builder_notmem_pending_and_unvisited (RB : RegionBuilder) :
  ∀ c, ¬(c ∈ RB.pending ∧ c ∈ RB.unvisited) := by
  intro c ⟨hmem₀, hmem₁⟩
  apply ((list_not_nodupes _).mpr (list_has_dupes_append_iff.mpr _)) RB.hnodupes
  right; right
  exact ⟨c, List.mem_append_right _ hmem₀, hmem₁⟩

-- In a RegionBuilder, no item will be an element of both 'region' and 'unvisited'
lemma region_builder_notmem_region_and_unvisited (RB : RegionBuilder) :
  ∀ c, ¬(c ∈ RB.region ∧ c ∈ RB.unvisited) := by
  intro c ⟨hmem₀, hmem₁⟩
  apply ((list_not_nodupes _).mpr (list_has_dupes_append_iff.mpr _)) RB.hnodupes
  right; right
  exact ⟨c, List.mem_append_left _ hmem₀, hmem₁⟩

-- In a RegionBuilder, no item will be an element of both 'region' and 'pending'
lemma region_builder_notmem_region_and_pending (RB : RegionBuilder) :
  ∀ c, ¬(c ∈ RB.region ∧ c ∈ RB.pending) := by
  intro c ⟨hmem₀, hmem₁⟩
  apply ((list_not_nodupes _).mpr (list_has_dupes_append_iff.mpr _)) RB.hnodupes; left
  apply list_has_dupes_append_iff.mpr; right; right
  exact ⟨c, hmem₀, hmem₁⟩

-- RegionBuilder corresponding to the initial state of the region building algorithm.
def region_builder_init (L : List (Int × Int)) (_start : (Int × Int)) : RegionBuilder where
  start := _start
  region := []
  pending := [_start]
  hstart := by
    split_ifs with h
    · push_neg
      exact ⟨(List.cons_ne_nil _ _), List.head_singleton.symm⟩
    · exact False.elim (h rfl)
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
  hpath' := by
    simp
    use path_mk_singleton _start, path_mk_singleton_ne_nil _;
    constructor
    · rw [path_mk_singleton_route]
      exact fun _ ↦ id
    constructor
    · exact List.head_singleton
    · exact List.getLast_singleton _

-- TODO: Ideally we would replace this with List.Perm,
-- but there doesn't seem to actually be a theorem for 'perm'
-- that matches this definition.
def list_mem_iff {α : Type} (L₁ L₂ : List α) : Prop :=
  ∀ a : α, a ∈ L₁ ↔ a ∈ L₂

-- Cells will be in 'region_builder_init' if-and-only-if they are in the original list.
lemma region_builder_init_all_cells_mem_iff
  (L : List (Int × Int)) (start : (Int × Int)) (smem : start ∈ L) :
  list_mem_iff L (region_builder_all_cells (region_builder_init L start)) := by
  intro c
  unfold region_builder_init region_builder_all_cells; dsimp
  constructor
  · intro cmem
    by_cases cs : c = start
    · subst cs
      exact List.mem_cons_self
    rename' cs => cns; push_neg at cns
    apply List.mem_cons_of_mem _ ((List.mem_erase_of_ne cns).mpr _)
    exact (list_rm_dupes_mem_iff _ _).mpr cmem
  · intro cmem
    rcases List.mem_cons.mp cmem with lhs | rhs
    · subst lhs
      assumption
    · exact (list_rm_dupes_mem_iff L c).mp (List.mem_of_mem_erase rhs)

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
def region_builder_try_add_cell (RB : RegionBuilder) (a c : Int × Int)
  (hadj : adjacent c a) (amem : a ∈ RB.region ++ RB.pending) : RegionBuilder :=
  if cmem : c ∈ RB.unvisited then RegionBuilder.mk
    RB.start
    RB.region
    (RB.pending ++ [c])
    (RB.unvisited.erase c)
    (by
      split_ifs with h
      · push_neg
        use (by
          apply List.ne_nil_of_length_pos
          rw [List.length_append, List.length_singleton]
          exact Nat.add_one_pos _
        )
        rw [h, List.nil_append] at amem
        have hnnil := List.ne_nil_of_mem amem
        rw [List.head_append_left hnnil]
        have := RB.hstart
        rw [dif_pos h] at this
        push_neg at this
        rcases this with ⟨_, h'⟩
        assumption
      · have := RB.hstart
        rwa [dif_neg h] at this
    )
    RB.hregion_nd
    (by
      apply (list_nodupes_append_singleton_iff _ _).mpr
      exact ⟨
        fun cmem' ↦ region_builder_notmem_pending_and_unvisited RB c ⟨cmem', cmem⟩,
        RB.hpending_nd⟩
    )
    (list_nodupes_erase_of_nodupes _ RB.hunvisited_nd _)
    (by
      by_contra h₀
      rcases list_has_dupes_append_iff.mp ((list_not_nodupes _).mp h₀) with h₁ | h₁ | h₁
      · rcases list_has_dupes_append_iff.mp h₁ with h₂ | h₂| h₂
        · exact (list_not_nodupes _).mpr h₂ RB.hregion_nd
        · apply (list_not_nodupes _).mpr h₂
          apply (list_nodupes_append_singleton_iff _ _).mpr
          constructor
          · exact fun cmem' ↦ region_builder_notmem_pending_and_unvisited RB c ⟨cmem', cmem⟩
          · exact RB.hpending_nd
        · rcases h₂ with ⟨d, meml, memr⟩
          rcases List.mem_append.mp memr with lhs | rhs
          · exact region_builder_notmem_region_and_pending RB d ⟨meml, lhs⟩
          · exact region_builder_notmem_region_and_unvisited RB c ⟨(List.mem_singleton.mp rhs) ▸ meml, cmem⟩
      · rw [← list_not_nodupes] at h₁
        exact h₁ (list_nodupes_erase_of_nodupes _ (RB.hunvisited_nd) _)
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
        exact (list_mem_append_move_left_iff _ cmem x).mp xmem
      have hss₂₁ : L₂' ⊆ L₁' := by
        unfold L₁' L₂' L₁ L₂
        intro x xmem
        rcases List.mem_append.mp xmem with lhs | rhs
        · exact List.mem_append_left _ lhs
        · exact List.mem_append_right _ ((list_mem_append_move_left_iff _ cmem x).mpr rhs)
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
    (by
      intro x xmem; simp
      -- We need this subset property to apply 'path_exists_subset' below
      have hss : ∀ y,
        (y :: (RB.pending.reverse ++ RB.region).tail) ⊆ (y :: (RB.pending.reverse ++ RB.region)) := by
        intro y z zmem
        rcases List.mem_cons.mp zmem with lhs | rhs
        · subst lhs
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_of_mem_tail rhs)
      by_cases xnec : x ≠ c
      · -- If x ≠ c, we can show that the old path still works
        have xmem' : x ∈ RB.region ++ RB.pending := by
          rw [← List.append_assoc] at xmem
          rcases List.mem_append.mp xmem with lhs | rhs
          · assumption
          · absurd xnec
            exact List.mem_singleton.mp rhs
        exact path_exists_subset x RB.start _ _ (hss x) (RB.hpath' x xmem')
      rename' xnec => xc; push_neg at xc
      subst xc
      -- Get the path which connects 'a' to 'start'
      rcases path_exists_subset a RB.start _ _ (hss a) (RB.hpath' a amem) with ⟨P, hnnil, hpss, hhead, hlast⟩
      -- Add 'x' to 'P' to get a path from 'x' to 'start'
      let P' := path_extend P hnnil x (hhead ▸ hadj)
      use P', by apply path_extend_ne_nil
      -- Resolve the 2nd and 3rd requirements, leaving the subset condition to prove
      apply And.intro _ (And.intro (by rw [path_extend_head]) (by rwa [path_extend_getLast P hnnil]))
      rw [path_extend_route]
      intro y ymem
      rcases List.mem_cons.mp ymem with lhs | rhs
      · subst lhs
        exact List.mem_cons_self
      · apply List.mem_cons_of_mem
        rcases List.mem_cons.mp (hpss rhs) with lhs' | rhs'
        · subst lhs'
          rcases List.mem_append.mp amem with lhs'' | rhs''
          · exact List.mem_append_right _ lhs''
          · exact List.mem_append_left _ (List.mem_reverse.mpr rhs'')
        · assumption
    )
  else RB

-- Moving a cell from 'unvisited' to 'pending' will always result in
-- and non-empty pending list if the original pending list was non-empty
lemma region_builder_try_add_cell_pending_ne_nil (RB : RegionBuilder) (a c : Int × Int)
  (hadj : adjacent c a) (amem : a ∈ RB.region ++ RB.pending) :
  RB.pending ≠ [] → (region_builder_try_add_cell RB a c hadj amem).pending ≠ [] := by
  unfold region_builder_try_add_cell
  intro h
  split_ifs with h'
  · exact List.append_ne_nil_of_left_ne_nil h _
  · exact h

-- Calling 'region_builder_try_add_cell' on a RegionBuilder has no effect
-- on the sum of the lengths of the 'pending' and 'unvisited' lists
lemma region_builder_try_add_cell_length_invariant (RB : RegionBuilder) (a c : Int × Int)
  (hadj : adjacent c a) (amem : a ∈ RB.region ++ RB.pending) :
  (region_builder_try_add_cell RB a c hadj amem).pending.length +
  (region_builder_try_add_cell RB a c hadj amem).unvisited.length =
  RB.pending.length + RB.unvisited.length := by
  unfold region_builder_try_add_cell
  split_ifs with h
  · dsimp
    rw [List.length_append, List.length_singleton]
    rw [add_assoc, add_comm 1, List.length_erase_of_mem h]
    rw [Nat.sub_one_add_one (Nat.ne_zero_of_lt (List.length_pos_of_mem h))]
  · rfl

-- Calling 'region_builder_try_add_cell' has no effect on 'start'
lemma region_builder_try_add_cell_start (RB : RegionBuilder) (a c : Int × Int)
  (hadj : adjacent c a) (amem : a ∈ RB.region ++ RB.pending) :
  (region_builder_try_add_cell RB a c hadj amem).start = RB.start := by
  unfold region_builder_try_add_cell
  split_ifs with h
  · dsimp
  · rfl

-- Proves the conditions under which a cell will not be an element of 'unvisited'
-- after calling 'region_builder_try_add_cell'
lemma region_builder_try_add_cell_not_mem_unvisited (RB : RegionBuilder) (a c : Int × Int)
  (hadj : adjacent c a) (amem : a ∈ RB.region ++ RB.pending) :
  ∀ x, x = c ∨ x ∉ RB.unvisited → x ∉ (region_builder_try_add_cell RB a c hadj amem).unvisited := by
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
  (RB : RegionBuilder) (a c : Int × Int) (hnnil : RB.pending ≠ [])
  (hadj : adjacent c a) (amem : a ∈ RB.region ++ RB.pending) :
  (region_builder_try_add_cell RB a c hadj amem).pending.head
  (region_builder_try_add_cell_pending_ne_nil RB a c hadj amem hnnil) = RB.pending.head hnnil := by
  unfold region_builder_try_add_cell
  split_ifs with h
  · exact List.head_append_left hnnil
  · rfl

-- Cells will be in 'try_add_cell' if-and-only-if they are in the original region builder
lemma region_builder_try_add_cell_all_cells_mem_iff
  (RB : RegionBuilder) (a c : Int × Int)
  (hadj : adjacent c a) (amem : a ∈ RB.region ++ RB.pending) :
  list_mem_iff (region_builder_all_cells RB)
  (region_builder_all_cells (region_builder_try_add_cell RB a c hadj amem)) := by
  unfold region_builder_try_add_cell region_builder_all_cells
  intro x
  constructor
  · split_ifs with h
    · dsimp
      intro xmem
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
    · intro xmem
      assumption
  · split_ifs with h
    · dsimp
      intro xmem
      rcases List.mem_append.mp xmem with lhs | rhs
      · rcases List.mem_append.mp lhs with lhs' | rhs'
        · exact List.mem_append_left _ (List.mem_append_left _ lhs')
        · rcases List.mem_append.mp rhs' with lhs'' | rhs''
          · exact List.mem_append_left _ (List.mem_append_right _ lhs'')
          · have xc : x = c := List.mem_singleton.mp rhs''
            subst xc
            exact List.mem_append_right _ h
      · exact List.mem_append_right _ (List.mem_of_mem_erase rhs)
    · exact id

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
    rw [dif_neg (List.cons_ne_nil _ _)]
    by_cases hrnil : RB.region = []
    · rw [hrnil, List.getLast_singleton]
      have := RB.hstart
      rw [dif_pos hrnil] at this; push_neg at this
      rcases this with ⟨_, h'⟩
      assumption
    · rename' hrnil => hnnil'; push_neg at hnnil'
      rw [List.getLast_cons hnnil']
      -- Why does this have to be 'convert' rather than 'exact'?
      convert (dif_neg hnnil') ▸ RB.hstart
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
    rw [list_not_nodupes] at h₀
    rcases list_has_dupes_append_iff.mp h₀ with h₁ | h₁ | h₁
    · rcases list_has_dupes_append_iff.mp h₁ with h₂ | h₂ | h₂
      · rw [← list_not_nodupes] at h₂
        exact h₂ ((list_nodupes_cons_iff _ _).mpr ⟨
          fun h ↦ region_builder_notmem_region_and_pending _ _ ⟨h, List.head_mem hnnil⟩,
          RB.hregion_nd⟩)
      · rw [← list_not_nodupes] at h₂
        exact h₂ (((list_nodupes_cons_iff _ _).mp ((List.head_cons_tail RB.pending hnnil) ▸ RB.hpending_nd)).2)
      · rcases h₂ with ⟨a, lmem, rmem⟩
        rcases List.mem_cons.mp lmem with h₃ | h₃
        · subst h₃
          exact ((list_nodupes_head_tail_iff RB.pending hnnil).mp RB.hpending_nd).1 rmem
        · apply region_builder_notmem_region_and_pending RB a
          exact ⟨h₃, List.mem_of_mem_tail rmem⟩
    · rw [← list_not_nodupes] at h₁
      exact h₁ RB.hunvisited_nd
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
      let j := (find_last f (Nat.add_one_ne_zero _)).1
      let jlt : j < P.route.length - 1 + 1 := (find_last f (Nat.add_one_ne_zero _)).2
      rw [Nat.sub_one_add_one lennz] at jlt
      have fsat : ∃ x, f x :=
        ⟨⟨i, by rwa [Nat.sub_one_add_one lennz]⟩, hri.symm⟩
      have hrj : P.route[j]'jlt = RB.pending.head hnnil :=
        (find_last_is_sat f fsat).symm
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
          have := Fin.val_le_of_le (find_last_is_last f ⟨k + (j + 1), kh1lt⟩ hrk.symm)
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
  hpath' := by
    intro a amem
    have amem' : a ∈ RB.region ++ RB.pending := by
      rcases List.mem_cons.mp amem with lhs | rhs
      · rw [lhs]
        exact List.mem_append_right _ (List.head_mem hnnil)
      · rcases List.mem_append.mp rhs with lhs' | rhs'
        · exact List.mem_append_left _ lhs'
        · exact List.mem_append_right _ (List.mem_of_mem_tail rhs')
    -- Use 'path_exists_subset' to apply the existing path
    apply path_exists_subset _ _ _ _ _ (RB.hpath' a amem')
    -- This leaves just the subset property to prove
    intro x xmem
    rw [List.append_cons, ← List.reverse_singleton, ← List.reverse_append]
    rwa [List.singleton_append, List.head_cons_tail]

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

-- Cells will be in 'add_pending' if-and-only-if they are in the original region builder.
lemma region_builder_add_pending_all_cells_mem_iff (RB : RegionBuilder) (hnnil : RB.pending ≠ [])
  (hnadj : ∀ c ∈ RB.unvisited, ¬adjacent c (RB.pending.head hnnil)) :
  list_mem_iff (region_builder_all_cells RB)
  (region_builder_all_cells (region_builder_add_pending_of_ne_nil RB hnnil hnadj)) := by
  unfold region_builder_add_pending_of_ne_nil region_builder_all_cells; dsimp
  intro x
  constructor
  · intro xmem
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
  · intro xmem
    rcases List.mem_cons.mp xmem with lhs | rhs
    · apply List.mem_append_left _ (List.mem_append_right _ _)
      rw [lhs]
      exact List.head_mem hnnil
    · rcases List.mem_append.mp rhs with lhs' | rhs'
      · rcases List.mem_append.mp lhs' with lhs'' | rhs''
        · exact List.mem_append_left _ (List.mem_append_left _ lhs'')
        · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_of_mem_tail rhs''))
      · exact List.mem_append_right _ rhs'

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
      (RB.pending.head hnnil) (right (RB.pending.head hnnil))
        (right_adjacent _) (List.mem_append_right _ (List.head_mem hnnil)))
      (RB.pending.head hnnil) (left (RB.pending.head hnnil))
        (left_adjacent _) (by
          apply List.mem_append_right
          convert List.head_mem _ using 1
          · rw [region_builder_try_add_cell_pending_head]
          apply region_builder_try_add_cell_pending_ne_nil
          assumption
        ))
      (RB.pending.head hnnil) (up (RB.pending.head hnnil))
        (up_adjacent _) (by
          apply List.mem_append_right
          convert List.head_mem _ using 1
          · repeat rw [region_builder_try_add_cell_pending_head]
          · repeat apply region_builder_try_add_cell_pending_ne_nil
            assumption
        ))
      (RB.pending.head hnnil) (down (RB.pending.head hnnil))
        (down_adjacent _) (by
          apply List.mem_append_right
          convert List.head_mem _ using 1
          · repeat rw [region_builder_try_add_cell_pending_head]
          · repeat apply region_builder_try_add_cell_pending_ne_nil
            assumption
        ))
    (by
      repeat apply region_builder_try_add_cell_pending_ne_nil
      assumption)
    (by
      intro c cadj
      contrapose! cadj
      -- Use the magic of 'repeat' to show that 'c' must be
      -- adjacent to the original RB.pending.head
      repeat rw [region_builder_try_add_cell_pending_head _ _ _ (by
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
      absurd (adjacent_eq_dir_iff _ _).mpr ((adjacent_comm _ _).mp cadj); push_neg
      exact ⟨hup, hdown, hleft, hright⟩
    ))

-- All cells in the region builder prior to call 'make_region_step' will still be in the region builder after.
lemma make_region_step_all_cells_mem_iff (RB : RegionBuilder) (hnnil : RB.pending ≠ []) :
  list_mem_iff (region_builder_all_cells RB)
  (region_builder_all_cells (make_region_step RB hnnil)) := by
  intro x
  unfold make_region_step
  rw [← region_builder_add_pending_all_cells_mem_iff]
  repeat rw [← region_builder_try_add_cell_all_cells_mem_iff]

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

-- All cells in the region builder prior to call 'make_region_impl' will still be in the region builder after.
lemma make_region_impl_all_cells_mem_iff (RB : RegionBuilder) :
  list_mem_iff (region_builder_all_cells RB)
  (region_builder_all_cells (make_region_impl RB)) := by
  unfold make_region_impl
  intro x
  constructor
  repeat
  · split_ifs with h
    · exact id
    · rw [← make_region_impl_all_cells_mem_iff]
      rw [← make_region_step_all_cells_mem_iff]
      exact id
termination_by RB.pending.length + RB.unvisited.length
decreasing_by
  repeat exact make_region_terminates _ _

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

lemma make_region_region_ne_nil (L : List (Int × Int)) (start : (Int × Int)) :
  (make_region L start).region ≠ [] := by
  have := (make_region L start).hstart
  split_ifs at this with h
  · absurd this
    intro hnnil
    exact False.elim (hnnil (make_region_pending_nil L start))
  · assumption

-- The last element of the region is 'start'
lemma make_region_region_last (L : List (Int × Int)) (start : (Int × Int)) :
  (make_region L start).region.getLast (make_region_region_ne_nil L start) = start := by
  have := (make_region L start).hstart
  rw [dif_neg (make_region_region_ne_nil L start), make_region_start] at this
  exact this.symm

-- If a region has at least two elements, the first is not 'start'
-- Note that this result is implementation dependent and not generally true.
lemma make_region_region_head_ne_start (L : List (Int × Int)) (start : (Int × Int))
  (hlen : 1 < (make_region L start).region.length) :
  (make_region L start).region.head (
    List.ne_nil_of_length_pos (lt_trans Nat.zero_lt_one hlen)) ≠ start := by
  have hnnil : (make_region L start).region ≠ [] :=
    List.ne_nil_of_length_pos (lt_trans Nat.zero_lt_one hlen)
  nth_rw 4 [← make_region_region_last L start]
  rw [List.head_eq_getElem_zero hnnil, List.getLast_eq_getElem]
  let last_idx := (make_region L start).region.length - 1
  have hpos : 0 < last_idx := by
    unfold last_idx
    exact Nat.lt_sub_of_add_lt hlen
  exact (make_region L start).hregion_nd 0 last_idx hpos _

-- Define a 'Region' as the finite set of cells in the 'region' list of a 'make_region'
-- We can perform this construction because 'region' is guaranteed to have no duplicates.
def Region (L : List (Int × Int)) (start : (Int × Int)) : Finset (Int × Int) :=
  Finset.mk (Multiset.ofList (make_region L start).region) (by
    apply Multiset.nodup_iff_pairwise.mpr
    apply (Multiset.pairwise_coe_iff_pairwise (fun _ _ h ↦ h.symm)).mpr
    apply List.pairwise_iff_getElem.mpr
    intro i j ilt jlt iltj
    exact (make_region L start).hregion_nd i j iltj jlt
  )

-- The starting cell is a member of the resulting region
lemma region_start_mem (L : List (Int × Int)) (start : (Int × Int)) :
  start ∈ Region L start := by
  unfold Region; simp
  nth_rw 2 [← make_region_region_last L start]
  exact List.getLast_mem (make_region_region_ne_nil L start)

-- No region is empty (since it contains at least 'start')
lemma region_ne_empty (L : List (Int × Int)) (start : (Int × Int)) :
  Region L start ≠ ∅ :=
  Finset.ne_empty_of_mem (region_start_mem L start)

lemma region_card_eq (L : List (Int × Int)) (start : (Int × Int)) :
  (Region L start).card = (make_region L start).region.length := by
  unfold Region; simp

-- A cell is an element of a region if and only if there is
-- a path from the cell to the start of that region.
lemma region_mem_iff (L : List (Int × Int)) (start : (Int × Int)) (smem : start ∈ L) :
  ∀ a, (path_exists a start L) ↔ a ∈ Region L start := by
  unfold Region make_region
  intro a
  constructor
  · intro pathex
    have hss : L ⊆ region_builder_all_cells (make_region_impl (region_builder_init L start)) := by
      intro x xmem
      rw [← make_region_impl_all_cells_mem_iff]
      rwa [← region_builder_init_all_cells_mem_iff]
      assumption
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
  · intro amem; simp at amem
    have hpath :=
      (make_region_impl (region_builder_init L start)).hpath' a (List.mem_append.mpr (Or.inl amem))
    rw [make_region_impl_start, region_builder_init_start] at hpath
    rw [make_region_impl_pending_nil, List.reverse_nil, List.nil_append] at hpath
    apply path_exists_subset _ _ _ _ _ hpath
    intro x xmem
    rw [region_builder_init_all_cells_mem_iff _ start smem]
    rw [make_region_impl_all_cells_mem_iff]
    apply List.mem_append_left _ (List.mem_append_left _ _)
    rcases List.mem_cons.mp xmem with lhs | rhs
    · subst lhs
      assumption
    · exact List.mem_of_mem_tail rhs

-- Every cell on a path to 'start' is in the corresponding region
lemma region_mem_of_path_mem (L : List (Int × Int)) (start : (Int × Int)) (smem : start ∈ L)
  (P : Path) (hnnil : P.route ≠ []) (hss : P.route ⊆ L) (hstart : P.route.getLast hnnil = start) :
  ∀ a ∈ P.route, a ∈ Region L start := by
  intro a amem
  apply (region_mem_iff _ _ smem _).mp
  rcases List.getElem_of_mem amem with ⟨i, ilt, hri⟩
  use path_split_right P i, path_split_right_ne_nil P i ilt
  constructor
  · exact fun x xmem ↦ hss (path_split_right_subset P i xmem)
  constructor
  · exact Eq.trans (path_split_right_head P i ilt) hri
  exact Eq.trans (path_split_right_getLast P i ilt) hstart

-- Any cell in a region will be present in the list used to create that region
lemma region_subset_list (L : List (Int × Int)) (start : (Int × Int)) (smem : start ∈ L) :
  ∀ (a : Int × Int), a ∈ (Region L start) → a ∈ L := by
  intro a amem
  apply (region_builder_init_all_cells_mem_iff L start smem a).mpr
  apply (make_region_impl_all_cells_mem_iff _ a).mpr
  exact List.mem_append_left _ (List.mem_append_left _ amem)

-- Formula for removing a single cell from a region such that the result is still a region.
lemma region_recurrence_exists
  (L : List (Int × Int)) (start : (Int × Int)) (smem : start ∈ L) (llb : 1 < (Region L start).card) :
  ∃ a, a ≠ start ∧ Region L start = insert a (Region ((list_rm_dupes L).erase a) start) := by
  have hnnil : (make_region L start).region ≠ [] :=
    List.ne_nil_of_mem (region_start_mem L start)
  have llb' : 1 < (make_region L start).region.length := by
    rwa [region_card_eq] at llb
  have hnes : (make_region L start).region.head hnnil ≠ start :=
    make_region_region_head_ne_start _ _ llb'
  use (make_region L start).region.head hnnil, hnes
  ext x
  -- A similar technique is used for both directions of the proof:
  -- 1) Construct a path from 'x' to start using 'region_mem_iff' or hpath
  -- 2) Apply 'region_mem_iff' to the goal
  -- 3) Apply path_exists_subset to the goal with the path created in (1)
  -- 4) Show that the list of allowed cells for the path in (1) is a subset
  --    of the allowed cells in the goal
  constructor
  · intro xmem
    unfold Region at xmem; simp at xmem
    by_cases xhead : x = (make_region L start).region.head hnnil
    · subst xhead
      exact Finset.mem_insert_self _ _
    rename' xhead => hnhead; push_neg at hnhead
    apply Finset.mem_insert.mpr; right
    apply (region_mem_iff _ _ _ _).mp; swap
    · exact (List.mem_erase_of_ne hnes.symm).mpr ((list_rm_dupes_mem_iff _ _).mpr smem)
    have := (make_region L start).hpath' x (List.mem_append.mpr (Or.inl xmem))
    rw [make_region_start] at this
    apply path_exists_subset x start _ _ _ this
    -- Now we just need to prove the subset requirement
    rw [make_region_pending_nil, List.reverse_nil, List.nil_append]
    intro y ymem
    have yneh : y ≠ (make_region L start).region.head hnnil := by
      rcases List.mem_cons.mp ymem with lhs | rhs
      · subst lhs; assumption
      · rcases List.getElem_of_mem rhs with ⟨i, ilt, rfl⟩
        rw [List.length_tail] at ilt
        rw [List.getElem_tail, List.head_eq_getElem_zero]; symm
        exact (make_region L start).hregion_nd 0 (i + 1) (Nat.add_one_pos _) _
    have ymem' : y ∈ L := by
      rcases List.mem_cons.mp ymem with lhs | rhs
      · subst lhs
        exact region_subset_list L start smem _ xmem
      · exact region_subset_list L start smem _ (List.mem_of_mem_tail rhs)
    exact (List.mem_erase_of_ne yneh).mpr ((list_rm_dupes_mem_iff L y).mpr ymem')
  · intro h
    rcases Finset.mem_insert.mp h with lhs | rhs
    · subst lhs
      unfold Region; simp
    · apply (region_mem_iff L start smem x).mp
      let L' := ((list_rm_dupes L).erase ((make_region L start).region.head hnnil))
      have smem' : start ∈ L' := by
        apply (List.mem_erase_of_ne _).mpr ((list_rm_dupes_mem_iff L start).mpr smem)
        exact (make_region_region_head_ne_start L start llb').symm
      apply path_exists_subset x start _ _ _ ((region_mem_iff L' start smem' x).mpr rhs)
      exact fun y ymem ↦ (list_rm_dupes_mem_iff L y).mp (List.mem_of_mem_erase ymem)

-- For every cell in the region, there is some other
-- cell adjacent to it which is also in the region.
lemma region_adjacent_exists_of_mem
  (L : List (Int × Int)) (start : (Int × Int)) (smem : start ∈ L) (llb : 1 < (Region L start).card) :
  ∀ a ∈ Region L start, ∃ b ∈ Region L start, adjacent a b := by
  intro a amem
  unfold Region
  have hnnil := make_region_region_ne_nil L start
  have llb' : 1 < (make_region L start).region.length := by
    rwa [region_card_eq] at llb
  by_cases hsa : start = a
  · subst hsa
    -- Pick a cell in the region known to be distinct from 'start'
    -- and find a path from that cell to start.
    let c := (make_region L start).region.head hnnil
    have cmem : c ∈ Region L start := List.head_mem hnnil
    rcases (region_mem_iff L start smem c).mpr cmem with ⟨P, pnnil, pss, hhead, hlast⟩
    -- Because c ≠ start, the path must have at least two elements
    have pllb : 1 < P.route.length := by
      by_contra! h
      apply make_region_region_head_ne_start L start llb'
      change c = start
      rw [← hhead, ← hlast, List.head_eq_getElem_zero, List.getLast_eq_getElem]
      rw [getElem_congr_idx (Nat.sub_eq_zero_of_le h)]
    -- Show that the second-to-last cell in the path is adjacent to 'start'
    let d := P.route[P.route.length - 2]'(Nat.sub_lt (List.length_pos_of_ne_nil pnnil) (by norm_num))
    have hadj : adjacent d start := by
      rw [← hlast, List.getLast_eq_getElem]
      unfold d
      have hlt : P.route.length - 2 < P.route.length - 1 := by
        rw [← one_add_one_eq_two, Nat.sub_add_eq]
        exact Nat.sub_lt (Nat.lt_sub_of_add_lt pllb) (by norm_num)
      convert P.hadj (P.route.length - 2) hlt using 2
      rw [← one_add_one_eq_two, Nat.sub_add_eq, Nat.sub_one_add_one]
      exact Nat.sub_ne_zero_of_lt pllb
    have hmem : d ∈ (make_region L start).region :=
      region_mem_of_path_mem L start smem P pnnil pss hlast d (List.getElem_mem _)
    exact ⟨d, hmem, (adjacent_comm _ _).mp hadj⟩
  · rename' hsa => snea; push_neg at snea
    -- Get the path from 'a' to start
    rcases (region_mem_iff L start smem a).mpr amem with ⟨P, pnnil, pss, hhead, hlast⟩
    -- Since a ≠ start, the path must have at least two elements
    have pllb : 1 < P.route.length := by
      contrapose! snea; rename' snea => lle
      rw [← hlast, ← hhead, List.getLast_eq_getElem, List.head_eq_getElem_zero]
      congr
      exact Nat.sub_eq_zero_of_le lle
    let b := P.route[1]'pllb
    have hadj : adjacent a b := by
      rw [← hhead, List.head_eq_getElem_zero]
      exact P.hadj 0 (Nat.sub_pos_of_lt pllb)
    have hmem : b ∈ (make_region L start).region :=
      region_mem_of_path_mem L start smem P pnnil pss hlast b (List.getElem_mem _)
    exact ⟨b, hmem, hadj⟩
