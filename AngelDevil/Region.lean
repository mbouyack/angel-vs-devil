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
    list_nodupes_erase_of_nodupes (list_rm_dupes L) (list_rm_dupes_no_dupes L) _start
  hnodupes := by
    rw [List.nil_append]
    apply (list_nodupes_singleton_append_iff _ _).mpr
    constructor
    · apply list_nodupes_not_mem_erase_of_nodupes
      exact list_rm_dupes_no_dupes L
    · apply list_nodupes_erase_of_nodupes
      exact list_rm_dupes_no_dupes L

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
