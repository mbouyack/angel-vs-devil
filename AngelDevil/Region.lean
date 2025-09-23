import Mathlib.Data.List.Basic
import AngelDevil.Dupes

set_option linter.style.longLine false

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

-- Try moving a cell from 'unvisited' to 'pending'
def region_builder_try_add_cell (RB : RegionBuilder) (c : Int × Int) : RegionBuilder :=
  if hmem : c ∈ RB.unvisited then RegionBuilder.mk
    RB.start
    RB.region
    ([c] ++ RB.pending)
    (RB.unvisited.erase c)
    (by
      rcases List.mem_append.mp RB.hstart with lhs | rhs
      · exact List.mem_append_left _ lhs
      · exact List.mem_append_right _ (List.mem_append_right _ rhs)
    )
    RB.hregion_nd
    (by
      apply (list_nodupes_singleton_append_iff _ _).mpr
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
          apply (list_nodupes_singleton_append_iff _ _).mpr
          constructor
          · exact fun hmem' ↦ region_builder_notmem_pending_and_unvisited RB c ⟨hmem', hmem⟩
          · exact RB.hpending_nd
        · rcases h₂ with ⟨d, meml, memr⟩
          rcases List.mem_append.mp memr with lhs | rhs
          · exact region_builder_notmem_region_and_unvisited RB c ⟨(List.mem_singleton.mp lhs) ▸ meml, hmem⟩
          · exact region_builder_notmem_region_and_pending RB d ⟨meml, rhs⟩
      · exact h₁ (list_nodupes_erase_of_nodupes _ (RB.hunvisited_nd) _)
      · rcases h₁ with ⟨d, meml, memr⟩
        have memr' : d ∈ RB.unvisited := List.erase_subset memr
        rcases List.mem_append.mp meml with lhs | rhs
        · exact region_builder_notmem_region_and_unvisited RB d ⟨lhs, memr'⟩
        · rcases List.mem_append.mp rhs with lhs' | rhs'
          · exact list_nodupes_not_mem_erase_of_nodupes _ RB.hunvisited_nd _ ((List.mem_singleton.mp lhs') ▸ memr)
          · exact region_builder_notmem_pending_and_unvisited RB d ⟨rhs', memr'⟩
    )
  else RB

-- Moving a cell from 'unvisited' to 'pending' will always result in
-- and non-empty pending list if the original pending list was non-empty
lemma region_builder_try_add_cell_pending_ne_nil (RB : RegionBuilder) (c : Int × Int) :
  RB.pending ≠ [] → (region_builder_try_add_cell RB c).pending ≠ [] := by
  unfold region_builder_try_add_cell
  intro h
  split_ifs with h'
  · exact List.cons_ne_nil _ _
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
    rw [add_assoc, add_comm 1, List.length_erase_of_mem h]
    rw [Nat.sub_one_add_one (Nat.ne_zero_of_lt (List.length_pos_of_mem h))]
  · rfl

def region_builder_add_pending_of_ne_nil (RB : RegionBuilder) (hnnil : RB.pending ≠ []) : RegionBuilder where
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

lemma region_builder_add_pending_of_ne_nil_length (RB : RegionBuilder) (hnnil : RB.pending ≠ []) :
  (region_builder_add_pending_of_ne_nil RB hnnil).pending.length +
  (region_builder_add_pending_of_ne_nil RB hnnil).unvisited.length =
  RB.pending.length + RB.unvisited.length - 1 := by
  unfold region_builder_add_pending_of_ne_nil; dsimp
  rw [List.length_tail]
  rw [← Nat.sub_add_comm _]
  exact Nat.add_one_le_of_lt (List.length_pos_of_ne_nil hnnil)

-- Main loop of the region builder algorithm
-- The algorithm terminates if there are no pending cells, otherwise
-- it tries to add the four cells orthogonally connected to the current
-- pending cell, adds the current pending cell to the region, and then
-- recurses.
def make_region_impl (RB : RegionBuilder) :=
  if hnil : RB.pending = [] then RB else make_region_impl
  (region_builder_add_pending_of_ne_nil (
    region_builder_try_add_cell (
    region_builder_try_add_cell (
    region_builder_try_add_cell (
    region_builder_try_add_cell RB
      ((RB.pending.head hnil).1 + 1, (RB.pending.head hnil).2))
      ((RB.pending.head hnil).1 - 1, (RB.pending.head hnil).2))
      ((RB.pending.head hnil).1, (RB.pending.head hnil).2 + 1))
      ((RB.pending.head hnil).1, (RB.pending.head hnil).2 - 1)) (by
    apply region_builder_try_add_cell_pending_ne_nil
    apply region_builder_try_add_cell_pending_ne_nil
    apply region_builder_try_add_cell_pending_ne_nil
    exact region_builder_try_add_cell_pending_ne_nil _ _ hnil
  ))
termination_by RB.pending.length + RB.unvisited.length
decreasing_by
  rw [region_builder_add_pending_of_ne_nil_length]
  repeat rw [region_builder_try_add_cell_length_invariant]
  exact Nat.sub_one_lt (Nat.ne_zero_of_lt (Nat.add_pos_left (List.length_pos_of_ne_nil hnil) _))

-- Find the region of orthogonally connected cells in 'L' which contains 'start'
-- Note that if start ∉ L it will return a 1-cell region with just 'start'.
def make_region (L : List (Int × Int)) (start : (Int × Int)) : RegionBuilder :=
  make_region_impl (region_builder_init L start)
