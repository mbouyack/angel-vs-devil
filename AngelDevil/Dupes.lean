import Mathlib.Tactic.NormNum.Core
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Find

set_option linter.style.longLine false

/- This file contains theorems related to removing duplicates from a list
   and proving that a list is free of duplicates. -/

-- Note that List.dedup should do the same thing, but the implementation
-- is complicated and there seem to be no existing theorems which reference it.
-- TODO: There *are* theorems on 'dedup'. You just have to import
-- Mathlib.Data.List.Dedup
def list_rm_dupes {α : Type} [DecidableEq α] (L : List α) : List α :=
  match L with
  | []    => []
  | x::xs => if x ∈ xs then list_rm_dupes xs else x::(list_rm_dupes xs)

lemma list_rm_dupes_nil {α : Type} [DecidableEq α] : list_rm_dupes ([] : List α) = [] := rfl

def list_nodupes {α : Type} [DecidableEq α] (L : List α) : Prop :=
  ∀ i j (_ : i < j) (_ : j < L.length), L[i] ≠ L[j]

def list_has_dupes {α : Type} [DecidableEq α] (L : List α) : Prop :=
  ∃ i j, ∃ (_ : i < j) (_ : j < L.length), L[i] = L[j]

@[simp] lemma list_not_nodupes {α : Type} [DecidableEq α] (L : List α) :
  ¬list_nodupes L ↔ list_has_dupes L := by
  unfold list_nodupes; push_neg; rfl

@[simp] lemma list_not_has_dupes {α : Type} [DecidableEq α] (L : List α) :
  ¬list_has_dupes L ↔ list_nodupes L := by
  unfold list_has_dupes; push_neg; rfl

-- The empty list has no duplicates
lemma list_nodupes_nil {α : Type} [DecidableEq α] : list_nodupes ([] : List α) :=
  fun _ _ _ jlt ↦ False.elim (Nat.not_lt_zero _ (List.length_nil ▸ jlt))

-- Any singleton list has no duplicates
lemma list_nodupes_singleton {α : Type} [DecidableEq α] (x : α) : list_nodupes [x] := by
  intro i j ilt jlt
  rw [List.length_singleton, ← Nat.zero_add 1] at jlt
  have jz : j = 0 := Nat.le_zero.mp (Nat.le_of_lt_add_one jlt)
  exact False.elim (Nat.not_lt_zero _ (jz ▸ ilt))

-- Proves the conditions under which an appended list has dupes
lemma list_has_dupes_append_iff {α : Type} [DecidableEq α] {L₀ L₁ : List α} :
  list_has_dupes (L₀ ++ L₁) ↔
  list_has_dupes L₀ ∨ list_has_dupes L₁ ∨ ∃ a, a ∈ L₀ ∧ a ∈ L₁ := by
  unfold list_has_dupes
  constructor
  · intro h
    push_neg at h
    rcases h with ⟨i, j, ilt, jlt, h⟩
    by_cases ilt' : i < L₀.length
    · rw [List.getElem_append_left ilt'] at h
      by_cases jlt' : j < L₀.length
      · left
        use i, j, ilt, jlt'
        rw [h, List.getElem_append_left]
      · rename' jlt' => lej; push_neg at lej
        right; right
        use L₀[i], List.getElem_mem ilt'
        rw [h, List.getElem_append_right lej]
        exact List.getElem_mem _
    · rename' ilt' => lei; push_neg at lei
      right; left
      have lej : L₀.length ≤ j := le_of_lt (lt_of_le_of_lt lei ilt)
      use (i - L₀.length), (j - L₀.length), (Nat.sub_lt_sub_right lei ilt)
      use (by
        apply Nat.sub_lt_right_of_lt_add lej
        rwa [List.length_append, add_comm] at jlt
      )
      rwa [List.getElem_append_right lei, List.getElem_append_right lej] at h
  · intro h
    rcases h with h | h | h
    · rcases h with ⟨i, j, ilt, jlt, h⟩
      use i, j, ilt, (by
        rw [List.length_append]
        exact lt_of_lt_of_le jlt (Nat.le_add_right _ _)
      )
      have ilt' : i < L₀.length := lt_trans ilt jlt
      rwa [List.getElem_append_left ilt', List.getElem_append_left jlt]
    · rcases h with ⟨i, j, ilt, jlt, h⟩
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
-- in a list with no duplicates if-and-only-if that element is not
-- in the original list and the original list already has no duplicates.
lemma list_nodupes_singleton_append_iff
  {α : Type} [DecidableEq α] (L : List α) (a : α) :
  list_nodupes ([a] ++ L) ↔ a ∉ L ∧ list_nodupes L := by
  constructor
  · intro h
    contrapose! h;
    rw [list_not_nodupes] at *
    apply list_has_dupes_append_iff.mpr
    by_cases hmem : a ∈ L
    · exact Or.inr (Or.inr ⟨a, List.mem_singleton_self a, hmem⟩)
    exact Or.inr (Or.inl (h hmem))
  · intro ⟨hmem, hnd⟩
    by_contra! h
    rw [list_not_nodupes] at h
    rcases list_has_dupes_append_iff.mp h with h' | h' | h'
    · exact (list_not_nodupes _).mpr h' (list_nodupes_singleton a)
    · exact (list_not_nodupes _).mpr h' hnd
    · rcases h' with ⟨b, meml, memr⟩
      exact hmem ((List.mem_singleton.mp meml) ▸ memr)

-- Appending a single element to the right of a list will result
-- in a list with no duplicates if-and-only-if that element is not
-- in the original list and the original list already has no duplicates.
lemma list_nodupes_append_singleton_iff
  {α : Type} [DecidableEq α] (L : List α) (a : α) :
  list_nodupes (L ++ [a]) ↔ a ∉ L ∧ list_nodupes L := by
  constructor
  · intro h
    contrapose! h
    rw [list_not_nodupes] at *
    apply list_has_dupes_append_iff.mpr
    by_cases hmem : a ∈ L
    · exact Or.inr (Or.inr ⟨a, hmem, List.mem_singleton_self a⟩)
    exact Or.inl (h hmem)
  · intro ⟨hmem, hnd⟩
    by_contra! h
    rw [list_not_nodupes] at h
    rcases list_has_dupes_append_iff.mp h with h' | h' | h'
    · exact (list_not_nodupes _).mpr h' hnd
    · exact (list_not_nodupes _).mpr h' (list_nodupes_singleton a)
    · rcases h' with ⟨b, meml, memr⟩
      exact hmem ((List.mem_singleton.mp memr) ▸ meml)

-- Two conclusion that follow from a list 'x::xs' having no duplicates
lemma list_nodupes_cons_iff {α : Type} [DecidableEq α] (x : α) (xs : List α) :
  list_nodupes (x::xs) ↔ x ∉ xs ∧ list_nodupes xs :=
  list_nodupes_singleton_append_iff _ _

lemma list_nodupes_head_tail_iff {α : Type} [DecidableEq α] (L : List α) (hnnil : L ≠ []) :
  list_nodupes L ↔ L.head hnnil ∉ L.tail ∧ list_nodupes L.tail := by
  nth_rw 1 [← List.head_cons_tail L hnnil, list_nodupes_cons_iff (L.head hnnil) L.tail]

-- I haven't been able to prove directly that 'list_nodupes' is decidable
-- so we will show that this trivially decidable definition is equivalent.
abbrev list_nodupes_decidable {α : Type} [DecidableEq α] (L : List α) : Prop :=
  ∀ (i j : Fin L.length), i = j ∨ L[i] ≠ L[j]

-- Show that the trivially decidable definition of 'nodupe' is equivalent
-- to the original definition.
lemma list_nodupes_iff {α : Type} [DecidableEq α] (L : List α) :
  list_nodupes L ↔ list_nodupes_decidable L := by
  constructor
  · intro h i j
    by_cases ilt : i.val < j.val
    · right
      exact h i.val j.val ilt j.2
    rename' ilt => jle; push_neg at jle
    by_cases hij : i = j
    · left; assumption
    push_neg at hij
    have jlt := Nat.lt_of_le_of_ne jle (Fin.val_ne_iff.mpr hij).symm
    right; symm
    exact h j i jlt i.2
  · intro h i j ilt jlt
    let i' : Fin L.length := ⟨i, lt_trans ilt jlt⟩
    let j' : Fin L.length := ⟨j, jlt⟩
    rcases h i' j' with lhs | rhs
    · exact False.elim ((ne_of_lt ilt) (Fin.val_eq_of_eq lhs))
    · assumption

-- Prove that 'list_nodupes' is decidable
instance {α : Type} [DecidableEq α] : DecidablePred (@list_nodupes α _) := fun L ↦ by
  rw [list_nodupes_iff]
  apply inferInstance

-- Prove that 'list_has_dupes' is decidable
instance {α : Type} [DecidableEq α] : DecidablePred (@list_has_dupes α _) := fun L ↦ by
  rw [← list_not_nodupes]
  apply inferInstance

-- If a list has no duplicate values, then neither does its tail
lemma list_nodupes_tail_of_nodupes {α : Type} [DecidableEq α] (L : List α) :
  list_nodupes L → list_nodupes L.tail := by
  intro h
  by_cases hnil : L = []
  · subst hnil
    rwa [List.tail_nil]
  rename' hnil => hnnil; push_neg at hnnil
  exact ((list_nodupes_head_tail_iff L hnnil).mp h).2

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
      exact False.elim (((list_nodupes_cons_iff a xs).mp hnd).1 h)
    rw [List.erase_cons_tail (fun bneq ↦ anx ((beq_iff_eq.mp bneq).symm))] at h
    have amem' : a ∈ xs.erase a :=
      Or.elim (List.mem_cons.mp h) (fun ax ↦ False.elim (anx ax)) id
    exact list_nodupes_not_mem_erase_of_nodupes xs ((list_nodupes_cons_iff x xs).mp hnd).2 a amem'

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
lemma list_rm_dupes_nodupes {α : Type} [DecidableEq α] (L : List α) :
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
      exact list_rm_dupes_nodupes xs i j ilt jlt
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
    exact list_rm_dupes_nodupes xs ipred jpred ipredlt jpredlt h'

-- Removing duplicates from a list results in a list that is
-- no longer than the original.
lemma list_rm_dupes_length_le {α : Type} [DecidableEq α] (L : List α) :
  (list_rm_dupes L).length ≤ L.length := by
  unfold list_rm_dupes
  match L with
  | []    =>
    simp
  | x::xs =>
    simp
    split_ifs with h
    · exact le_trans (list_rm_dupes_length_le xs) (Nat.le_add_right _ _)
    · rw [List.length_cons]
      exact Nat.add_le_add_right (list_rm_dupes_length_le xs) _

-- A list with duplicates is non-empty
lemma list_ne_nil_of_has_dupes
  {α : Type} [DecidableEq α] (L : List α) (hdupe : list_has_dupes L) : L ≠ [] := by
  rcases hdupe with ⟨_, _, ilt, jlt, _⟩
  exact List.ne_nil_of_length_pos (lt_of_le_of_lt (Nat.zero_le _) jlt)

-- Note that this will return true for the last element
-- since 'find_first_dupe' assumes at least one dupe exists
abbrev first_dupe_helper {α : Type} [DecidableEq α] (L : List α) : Nat → Prop :=
  fun i ↦ (ilt : i < L.length - 1) → list_has_dupes (L.take (i + 1))

-- If some element repeats in L, 'first_dupe_helper' will identify it as a dupe
lemma first_dupe_helper_of_dupe {α : Type} [DecidableEq α] (L : List α) :
  ∀ i j (ilt : i < j) (jlt : j < L.length), L[i]'(lt_trans ilt jlt) = L[j]'jlt →
  first_dupe_helper L j := by
  intro i j ilt jlt hij
  intro jlt'
  use i, j, ilt
  use by rw [List.length_take_of_le (Nat.add_one_le_of_lt jlt)]; exact Nat.lt_add_one _
  rwa [List.getElem_take, List.getElem_take]

-- L.length - 1 satisfies 'first_dupe_helper'
lemma first_dupe_helper_sat_len_pred {α : Type} [DecidableEq α] (L : List α) :
  first_dupe_helper L (L.length - 1) := by
  unfold first_dupe_helper
  intro h
  absurd h; push_neg
  exact le_refl _

-- 'first_dupe_helper' can be satisfied
lemma first_dupe_helper_is_sat {α : Type} [DecidableEq α] (L : List α) :
  ∃ i, first_dupe_helper L i := ⟨L.length - 1, first_dupe_helper_sat_len_pred L⟩

-- Find the first element which appears earlier in the list
def find_first_dupe {α : Type} [DecidableEq α] (L : List α) (hnnil : L ≠ []) : Fin L.length :=
  ⟨Nat.find (first_dupe_helper_is_sat L), by
    apply Nat.lt_of_le_sub_one (List.length_pos_of_ne_nil hnnil)
    exact Nat.find_min' (first_dupe_helper_is_sat L) (first_dupe_helper_sat_len_pred L)
  ⟩

-- Prove that the dupe found by 'find_first_dupe' is in-fact first
-- Note that the second element of the pair is used to determine the order.
lemma first_dupe_is_first {α : Type} [DecidableEq α] (L : List α) (hdupe : list_has_dupes L) :
  ∀ i j (ilt : i < j) (jlt : j < L.length), L[i]'(lt_trans ilt jlt) = L[j]'jlt →
  find_first_dupe L (list_ne_nil_of_has_dupes L hdupe) ≤ j := by
  intro i j ilt jlt hij
  apply Nat.find_min' (first_dupe_helper_is_sat L)
  exact first_dupe_helper_of_dupe L i j ilt jlt hij

-- Prove that the value at the location indicated by 'find_first_dupe' is
-- in-fact a duplicate.
lemma first_dupe_is_dupe {α : Type} [DecidableEq α] (L : List α) (hdupe : list_has_dupes L) :
  (fun (j : Fin L.length) ↦ ∃ (i : Nat) (ilt : i < j.val), L[i]'(lt_trans ilt j.2) = L[j])
  (find_first_dupe L (list_ne_nil_of_has_dupes L hdupe)) := by
  dsimp
  have hnnil : L ≠ [] := list_ne_nil_of_has_dupes L hdupe
  let j := (find_first_dupe L hnnil).val
  have jlt : j < L.length := Fin.prop _
  -- Define a function to find the location, 'i', of an element that matches
  -- the one in location 'j'
  let f : Nat → Prop := fun i ↦ (ile : i ≤ j) → L[i]'(lt_of_le_of_lt ile jlt) = L[j]
  have fsatj : f j := by intro _; rfl
  have fsat : ∃ i, f i := by use j
  -- Define 'i' and show it has the desired properties (i ≤ j, L[i] = L[j])
  let i := Nat.find fsat
  have ilej : i ≤ j := Nat.find_min' fsat fsatj
  have hij : L[i] = L[j] := Nat.find_spec fsat ilej
  -- If at any point we find a duplicate that would
  -- come before (i, j), it must actually be (i, j)
  have : ∀ i' j' (i'lt : i' < j') (j'le : j' ≤ j),
    L[i'] = L[j'] → j = j' := by
    intro i' j' i'lt j'le h
    by_contra! jnej'
    have j'ltj := Nat.lt_of_le_of_ne j'le jnej'.symm
    have j'nsat := Nat.find_min (first_dupe_helper_is_sat L) j'ltj
    exact False.elim (j'nsat (first_dupe_helper_of_dupe L i' j' i'lt (lt_trans j'ltj jlt) h))
  -- If there is no duplicate, j = L.length - 1, but that
  -- is also a valid value for j, so handle that case first
  by_cases jeq : j = L.length - 1
  · -- If 'j' is at the end of the list, we can use the duplicate
    -- indicated by 'hdupe' to satisfy the goal
    rcases hdupe with ⟨i', j', i'lt, j'lt, h⟩
    have j'lej := jeq ▸ (Nat.le_sub_one_of_lt j'lt)
    have jeqj' := this i' j' i'lt j'lej h
    use i', jeqj' ▸ i'lt
    convert h
  rename' jeq => jne; push_neg at jne
  have jlt' : j < L.length - 1 := lt_of_le_of_ne (Nat.le_sub_one_of_lt jlt) jne
  have inej : i ≠ j := by
    by_contra! ieqj
    -- If there is some other candiate duplicate,
    -- we can use "this" to show that j = j'
    rcases Nat.find_spec (first_dupe_helper_is_sat L) jlt' with ⟨i', j', i'lt, j'lt, h⟩
    rw [List.getElem_take, List.getElem_take] at h
    have j'lt' : j' < L.length := lt_of_lt_of_le j'lt (List.length_take_le' _ _)
    have j'le : j' ≤ j :=
      Nat.le_of_lt_add_one (lt_of_lt_of_le j'lt (List.length_take_le _ _))
    have j'eq := this i' j' i'lt j'le h
    apply Nat.find_min fsat (lt_of_lt_of_eq i'lt (Eq.trans j'eq.symm ieqj.symm))
    intro _; convert h
  use i, lt_of_le_of_ne ilej inej

-- Taking the first 'n' elements from a list with duplicates
-- results in a list of no duplicates if-and-only if
-- n ≤ find_first_dupe
lemma first_dupe_gt_iff_no_dupes_take
  {α : Type} [DecidableEq α] (L : List α) (hdupe : list_has_dupes L) :
  ∀ n ≤ L.length, list_nodupes (L.take n) ↔
  n ≤ find_first_dupe L (list_ne_nil_of_has_dupes _ hdupe) := by
  intro n nle
  have hnnil : L ≠ [] := list_ne_nil_of_has_dupes _ hdupe
  let i := (find_first_dupe L hnnil).1
  have ilt : i < L.length := Fin.prop _
  rcases first_dupe_is_dupe L hdupe with ⟨j, jlt, hij⟩
  have jlt' : j < L.length := lt_trans jlt ilt
  constructor
  · intro h
    contrapose! h
    rw [list_not_nodupes]
    use j, i, jlt
    use by rwa [List.length_take_of_le nle]
    rwa [List.getElem_take, List.getElem_take]
  · intro h
    contrapose! h
    rw [list_not_nodupes] at h
    rcases h with ⟨a, b, alt, blt, hab⟩
    have blt' : b < n := by
      rwa [List.length_take_of_le nle] at blt
    rw [List.getElem_take, List.getElem_take] at hab
    -- Since 'find_first_dupe' is the first duplicate,
    -- it must be less-than or equal to 'b'
    -- (which is also the location of a duplicate)
    apply lt_of_le_of_lt _ blt'
    exact first_dupe_is_first L hdupe a b alt (lt_of_lt_of_le blt' nle) hab

-- If every element in L₁ is also in L₂ and L₁
-- has no duplicates, then L₁.length ≤ L₂.length
lemma list_nodupes_length_le_of_sublist
  {α : Type} [DecidableEq α] (L₁ L₂ : List α)
  (hnd : list_nodupes L₁) (hss : L₁ ⊆ L₂) :
  L₁.length ≤ L₂.length :=
  match L₂ with
  | []      => by
    rw [List.length_nil]
    by_contra! h
    rcases List.exists_mem_of_length_pos h with ⟨a, amem⟩
    exact (List.mem_nil_iff a).mp (hss amem)
  | a :: xs => by
    rw [List.length_cons]
    by_cases amem : a ∉ L₁
    · have hss' : L₁ ⊆ xs := by
        intro b bmem
        rcases List.mem_cons.mp (hss bmem) with lhs | rhs
        · subst lhs
          exact False.elim (amem bmem)
        · assumption
      apply le_trans _ (Nat.le_add_right _ 1)
      exact list_nodupes_length_le_of_sublist _ _ hnd hss'
    push_neg at amem
    have L₁lpos: 0 < L₁.length :=
      List.length_pos_of_mem amem
    have onele := (Nat.zero_add _) ▸ (Nat.add_one_le_add_one_iff.mpr (Nat.zero_le xs.length))
    apply (Nat.sub_le_sub_iff_right onele).mp
    rw [Nat.add_one_sub_one]
    rw [← List.length_erase_of_mem amem]
    have hss' : (L₁.erase a) ⊆ xs := by
      intro b bmem
      rcases List.mem_cons.mp (hss (List.mem_of_mem_erase bmem)) with lhs | rhs
      · subst lhs
        exact False.elim (list_nodupes_not_mem_erase_of_nodupes L₁ hnd b bmem)
      · assumption
    have hnd' := list_nodupes_erase_of_nodupes _ hnd a
    exact list_nodupes_length_le_of_sublist _ _ hnd' hss'
