import Mathlib.Tactic.NormNum.Core
import Mathlib.Data.List.Basic

set_option linter.style.longLine false

/- This file contains theorems related to removing duplicates from a list
   and proving that a list is free of duplicates. This will be used as
   an alternative 'Finset' -/

-- Note that List.dedup should do the same thing, but the implementation
-- is complicated and there seem to be no existing theorems which reference it.
def list_rm_dupes {α : Type} [DecidableEq α] (L : List α) : List α :=
  match L with
  | []    => []
  | x::xs => if x ∈ xs then list_rm_dupes xs else x::(list_rm_dupes xs)

lemma list_rm_dupes_nil {α : Type} [DecidableEq α] : list_rm_dupes ([] : List α) = [] := rfl

def list_nodupes {α : Type} [DecidableEq α] (L : List α) : Prop :=
  ∀ i j (_ : i < j) (_ : j < L.length), L[i] ≠ L[j]

-- The empty list has no duplicates
lemma list_nodupes_nil {α : Type} [DecidableEq α] : list_nodupes ([] : List α) :=
  fun _ _ _ jlt ↦ False.elim (Nat.not_lt_zero _ (List.length_nil ▸ jlt))

-- Any singleton list has no duplicates
lemma list_nodupes_singleton {α : Type} [DecidableEq α] (x : α) : list_nodupes [x] := by
  intro i j ilt jlt
  rw [List.length_singleton, ← Nat.zero_add 1] at jlt
  have jz : j = 0 := Nat.le_zero.mp (Nat.le_of_lt_add_one jlt)
  exact False.elim (Nat.not_lt_zero _ (jz ▸ ilt))

-- Two conclusion that follow from a list 'x::xs' having no duplicates
lemma list_nodupes_cons {α : Type} [DecidableEq α] (x : α) (xs : List α) (h : list_nodupes (x::xs)) :
  x ∉ xs ∧ list_nodupes xs := by
  constructor
  · intro xmem
    unfold list_nodupes at h
    rcases List.getElem_of_mem xmem with ⟨i, ilt, hi⟩
    have islt : i + 1 < (x :: xs).length := by
      rw [List.length_cons]
      exact Nat.add_one_lt_add_one_iff.mpr ilt
    apply h 0 (i + 1) (Nat.add_one_pos _) islt
    rw [List.getElem_cons_zero, List.getElem_cons_succ]
    exact hi.symm
  · unfold list_nodupes at *
    contrapose! h
    rcases h with ⟨i, j, ilt, jlt, h⟩
    use (i + 1), (j + 1), (Nat.add_one_lt_add_one_iff.mpr ilt), (by
      rw [List.length_cons]
      exact Nat.add_one_lt_add_one_iff.mpr jlt
    )
    rwa [List.getElem_cons_succ, List.getElem_cons_succ]

-- If a list has no duplicates, erasing an element from that list
-- results in a list which also has no duplicates.
-- NOTE: This turns out to be a bit lengthy as we need to rewrite
-- 'erase' as 'eraseIdx' and then complete the proof by cases
-- depending on the relationship between i, j, and k
-- TODO: Do we need all three of the 'Eq' instances listed here?
lemma list_nodupes_erase_of_nodupes {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
  (L : List α) (hnd : list_nodupes L) (a : α) : list_nodupes (L.erase a) := by
  intro i j ilt jlt
  by_cases hmem : a ∉ L
  · repeat rw [getElem_congr_coll (List.erase_of_not_mem hmem)]
    rw [List.erase_of_not_mem hmem] at jlt
    exact hnd i j ilt jlt
  push_neg at hmem
  let k := List.idxOf a L
  have kdef : List.idxOf a L = k := rfl
  repeat rw [getElem_congr_coll (List.erase_eq_eraseIdx_of_idxOf kdef)]
  rw [List.length_erase_of_mem hmem] at jlt
  have klt : k < L.length := List.idxOf_lt_length_of_mem hmem
  have ilt'' : i < (L.eraseIdx k).length := by
    rw [List.length_eraseIdx_of_lt klt]
    exact lt_trans ilt jlt
  have jlt' : j < (L.eraseIdx k).length := by
    rw [List.length_eraseIdx_of_lt klt]
    exact jlt
  by_cases kle : k ≤ i
  · rw [List.getElem_eraseIdx_of_ge ilt'' kle]
    rw [List.getElem_eraseIdx_of_ge jlt' (le_trans kle (le_of_lt ilt))]
    apply hnd (i + 1) (j + 1) (Nat.add_one_lt_add_one_iff.mpr ilt)
  rename' kle => ilt'''; push_neg at ilt'''
  rw [List.getElem_eraseIdx_of_lt ilt'' ilt''']
  by_cases kle : k ≤ j
  · rw [List.getElem_eraseIdx_of_ge jlt' kle]
    apply hnd i (j + 1) (lt_trans ilt (Nat.lt_add_one _))
  rename' kle => jlt''; push_neg at jlt''
  rw [List.getElem_eraseIdx_of_lt jlt' jlt'']
  apply hnd i j ilt

-- If a list has no duplicates, then erasing an element will
-- result in a list which does not contain that element.
lemma list_nodupes_not_mem_erase_of_nodupes {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
  (L : List α) (hnd : list_nodupes L) (a : α) : a ∉ L.erase a := by
  -- Not that we didn't assume a ∈ L
  -- Handle the negation of that case now
  by_cases amem : a ∉ L
  · exact fun h ↦ amem (List.erase_subset h )
  push_neg at amem
  match L with
  | []    => exact False.elim (List.not_mem_nil amem)
  | x::xs =>
    intro h
    have anx : a ≠ x := by
      intro ax
      subst ax
      rw [List.erase_cons_head] at h
      exact False.elim ((list_nodupes_cons a xs hnd).1 h)
    rw [List.erase_cons_tail (fun bneq ↦ anx ((beq_iff_eq.mp bneq).symm))] at h
    have amem' : a ∈ xs.erase a :=
      Or.elim (List.mem_cons.mp h) (fun ax ↦ False.elim (anx ax)) id
    exact list_nodupes_not_mem_erase_of_nodupes xs (list_nodupes_cons x xs hnd).2 a amem'

-- Proves the conditions under which an appended list has dupes
lemma list_nodupes_append_dupes_iff {α : Type} [DecidableEq α] {L₀ L₁ : List α} :
  ¬list_nodupes (L₀ ++ L₁) ↔
  ¬list_nodupes L₀ ∨ ¬list_nodupes L₁ ∨ ∃ a, a ∈ L₀ ∧ a ∈ L₁ := by
  unfold list_nodupes
  constructor
  · intro h
    push_neg at h
    rcases h with ⟨i, j, ilt, jlt, h⟩
    by_cases ilt' : i < L₀.length
    · rw [List.getElem_append_left ilt'] at h
      by_cases jlt' : j < L₀.length
      · left; push_neg
        use i, j, ilt, jlt'
        rw [h, List.getElem_append_left]
      · rename' jlt' => lej; push_neg at lej
        right; right
        use L₀[i], List.getElem_mem ilt'
        rw [h, List.getElem_append_right lej]
        exact List.getElem_mem _
    · rename' ilt' => lei; push_neg at lei
      right; left
      push_neg
      have lej : L₀.length ≤ j := le_of_lt (lt_of_le_of_lt lei ilt)
      use (i - L₀.length), (j - L₀.length), (Nat.sub_lt_sub_right lei ilt)
      use (by
        apply Nat.sub_lt_right_of_lt_add lej
        rwa [List.length_append, add_comm] at jlt
      )
      rwa [List.getElem_append_right lei, List.getElem_append_right lej] at h
  · intro h; push_neg
    rcases h with h | h | h
    · push_neg at h
      rcases h with ⟨i, j, ilt, jlt, h⟩
      use i, j, ilt, (by
        rw [List.length_append]
        exact lt_of_lt_of_le jlt (Nat.le_add_right _ _)
      )
      have ilt' : i < L₀.length := lt_trans ilt jlt
      rwa [List.getElem_append_left ilt', List.getElem_append_left jlt]
    · push_neg at h
      rcases h with ⟨i, j, ilt, jlt, h⟩
      use (i + L₀.length), (j + L₀.length), (Nat.add_lt_add_right ilt _)
      use (by
        rw [List.length_append, add_comm]
        exact Nat.add_lt_add_left jlt _
      )
      rw [List.getElem_append_right (Nat.le_add_left _ _)]
      rw [List.getElem_append_right (Nat.le_add_left _ _)]
      convert h
      · rw [Nat.add_sub_cancel]
      · rw [Nat.add_sub_cancel]
    · rcases h with ⟨a, amem₀, amem₁⟩
      rcases List.getElem_of_mem amem₀ with ⟨i, ilt, h₀⟩
      rcases List.getElem_of_mem amem₁ with ⟨j, jlt, h₁⟩
      use i, (j + L₀.length), (lt_of_lt_of_le ilt (Nat.le_add_left _ _))
      use (by
        rw [List.length_append, add_comm]
        exact Nat.add_lt_add_left jlt _
      )
      rw [List.getElem_append_left ilt, List.getElem_append_right]; swap
      · exact Nat.le_add_left _ _
      convert Eq.trans h₀ h₁.symm
      rw [Nat.add_sub_cancel]

-- Appending a single element to the left of a list will result
-- in a list with no duplicates if that element is not in the original
-- list and the original list already has no duplicates.
lemma list_nodupes_singleton_append_of_notmem_of_nodupes
  {α : Type} [DecidableEq α] (L : List α) (a : α)
  (hmem : a ∉ L) (hnd : list_nodupes L) : list_nodupes ([a] ++ L) := by
  by_contra! h
  rcases list_nodupes_append_dupes_iff.mp h with h' | h' | h'
  · exact h' (list_nodupes_singleton a)
  · exact h' hnd
  · rcases h' with ⟨b, meml, memr⟩
    exact hmem ((List.mem_singleton.mp meml) ▸ memr)

-- An element of 'list_rm_dupes L' is always an element of L and vice-versa
lemma list_rm_dupes_mem_iff {α : Type} [DecidableEq α] (L : List α) :
  ∀ a, a ∈ list_rm_dupes L ↔ a ∈ L := by
  intro a
  constructor
  · intro amem
    match L with
    | []    => rwa [list_rm_dupes_nil] at amem
    | x::xs =>
      unfold list_rm_dupes at amem
      split_ifs at amem with h
      · exact List.mem_cons.mpr (Or.inr ((list_rm_dupes_mem_iff xs a).mp amem))
      · rcases List.mem_cons.mp amem with lhs | rhs
        · exact List.mem_cons.mpr (Or.inl lhs)
        · exact List.mem_cons.mpr (Or.inr ((list_rm_dupes_mem_iff xs a).mp rhs))
  · intro amem
    match L with
    | []    => exact False.elim (List.not_mem_nil amem)
    | x::xs =>
      unfold list_rm_dupes
      split_ifs with h
      · rcases List.mem_cons.mp amem with lhs | rhs
        · convert (list_rm_dupes_mem_iff xs x).mpr h
        · exact (list_rm_dupes_mem_iff xs a).mpr rhs
      · rcases List.mem_cons.mp amem with lhs | rhs
        · exact List.mem_cons.mpr (Or.inl lhs)
        · exact List.mem_cons.mpr (Or.inr ((list_rm_dupes_mem_iff xs a).mpr rhs))

-- Prove that 'rm_dupes' does in-fact remove all duplicates
lemma list_rm_dupes_no_dupes {α : Type} [DecidableEq α] (L : List α) :
  list_nodupes (list_rm_dupes L) := by
  intro i j ilt jlt
  match L with
  | []      =>
    rw [list_rm_dupes_nil, List.length_nil] at jlt
    exact False.elim (Nat.not_lt_zero _ jlt)
  | x::xs   =>
    unfold list_rm_dupes at *
    split_ifs with h
    · rw [if_pos h] at jlt
      exact list_rm_dupes_no_dupes xs i j ilt jlt
    intro h'
    rcases Nat.exists_eq_add_one_of_ne_zero (Nat.ne_zero_of_lt ilt) with ⟨jpred, hjp⟩
    subst hjp
    by_cases iz : i = 0
    · subst iz
      rw [List.getElem_cons_zero, List.getElem_cons_succ] at h'
      rw [if_neg h, List.length_cons] at jlt
      exact h ((list_rm_dupes_mem_iff xs x).mp (List.mem_of_getElem h'.symm))
    rename' iz => inz; push_neg at inz
    rcases Nat.exists_eq_add_one_of_ne_zero inz with ⟨ipred, hip⟩
    subst hip
    rw [List.getElem_cons_succ, List.getElem_cons_succ] at h'
    rw [if_neg h, List.length_cons] at jlt
    have ipredlt := Nat.add_one_lt_add_one_iff.mp ilt
    have jpredlt := Nat.add_one_lt_add_one_iff.mp jlt
    exact list_rm_dupes_no_dupes xs ipred jpred ipredlt jpredlt h'
