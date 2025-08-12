import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith
-- TODO: Figure out a more appropriate import (rather than 'Linarith')

set_option linter.style.longLine false
set_option linter.style.multiGoal false

-- Useful helper function for adding one to the value of a 'Fin'
-- if it is not "last"
def fin_add_one_of_ne_last {n : Nat} (i : Fin (n + 1)) (hinl : i ≠ Fin.last n) : Fin (n + 1) :=
  ⟨i.val + 1, Nat.add_one_lt_add_one_iff.mpr (Fin.lt_iff_val_lt_val.mp (Fin.lt_last_iff_ne_last.mpr hinl))⟩

@[simp] lemma fin_add_one_of_ne_last_val {n : Nat} (i : Fin (n + 1)) (hinl : i ≠ Fin.last n) :
  (fin_add_one_of_ne_last i hinl).val = i.val + 1 := by
  unfold fin_add_one_of_ne_last; simp

-- Improved 'can_sat'
def _can_sat_impl {n : Nat} (f : Fin (n + 1) → Prop) [DecidablePred f] (start : Fin (n + 1)) : Prop :=
  if snl : start = Fin.last _ then f start else
  f start ∨ _can_sat_impl f (fin_add_one_of_ne_last start snl)
termination_by (n+1) - start
decreasing_by
  simp
  apply Nat.sub_lt_sub_right (Nat.le_of_lt_add_one start.2) (Nat.lt_add_one _)

-- Wrapper to always start the search at 0
def _can_sat {n : Nat} (f : Fin (n + 1) → Prop) [DecidablePred f] : Prop := _can_sat_impl f 0

lemma _can_sat_iff_impl {n : Nat} (f : Fin (n + 1) → Prop) [DecidablePred f] (start : Fin (n + 1)) :
  _can_sat_impl f start ↔ ∃ i, start ≤ i ∧ f i := by
  unfold _can_sat_impl
  -- Helper function for adding one to a Fin (n+1)
  -- TODO: There's *got* to be a better way!
  /-let finsucc_of_nelast : (i : Fin (n + 1)) → (hinl : i ≠ Fin.last n) → Fin (n + 1) := fun i hinl ↦
    ⟨i.val + 1, by
      exact Nat.add_one_lt_add_one_iff.mpr
        (Nat.lt_of_le_of_ne (Nat.le_of_lt_add_one i.2) (Fin.val_ne_iff.mpr hinl))
    ⟩-/
  constructor
  · split_ifs with h
    · exact fun ssat ↦ ⟨start, Fin.le_refl start, ssat⟩
    · intro h'
      rcases h' with ssat | hrecurse
      · exact ⟨start, Fin.le_refl start, ssat⟩
      · push_neg at h
        rcases (_can_sat_iff_impl f (fin_add_one_of_ne_last start h)).mp hrecurse with ⟨i, lei, isat⟩
        apply Fin.le_iff_val_le_val.mp at lei; simp at lei
        exact ⟨i, Fin.le_iff_val_le_val.mpr (Nat.le_of_lt (Nat.lt_of_add_one_le lei)), isat⟩
  intro h
  rcases h with ⟨i, lei, isat⟩
  split_ifs with h
  · convert isat
    subst h
    exact (Fin.last_le_iff.mp lei).symm
  · rcases Fin.lt_or_eq_of_le lei with slt | seq
    · right; push_neg at h
      apply (_can_sat_iff_impl f (fin_add_one_of_ne_last start h)).mpr
      use i
      constructor
      · apply Fin.le_iff_val_le_val.mpr
        exact Nat.add_one_le_of_lt (Fin.lt_iff_val_lt_val.mp slt)
      · assumption
    · left
      rwa [seq]
termination_by (n+1) - start
decreasing_by
  repeat
  simp
  apply Nat.sub_lt_sub_right (Nat.le_of_lt_add_one start.2) (Nat.lt_add_one _)

-- Prove that 'can_sat' behaves as expected
lemma _can_sat_iff {n : Nat} (f : Fin (n + 1) → Prop) [DecidablePred f] : _can_sat f ↔ ∃ i, f i := by
  unfold _can_sat
  constructor
  · intro h
    rcases (_can_sat_iff_impl f 0).mp h with ⟨i, _, isat⟩
    exact ⟨i, isat⟩
  · intro h
    rcases h with ⟨i, isat⟩
    exact (_can_sat_iff_impl f 0).mpr ⟨i, Fin.zero_le _, isat⟩

-- Prove that _can_sat_impl is decidable
instance {n : Nat} (f : Fin (n + 1) → Prop) [DecidablePred f] (start : Fin (n + 1)) :
  Decidable (_can_sat_impl f start) := by
  unfold _can_sat_impl
  induction' start using Fin.reverseInduction with i ih
  · rw [dif_pos rfl]
    exact if h : f (Fin.last n) then isTrue h else isFalse h
  · rw [dif_neg (Fin.castSucc_ne_last i)]
    by_cases icssat : f i.castSucc
    · exact isTrue (Or.inl icssat)
    · have iseq : i.succ = fin_add_one_of_ne_last i.castSucc (Fin.castSucc_ne_last i) := by
        apply (Fin.val_eq_val _ _).mp; simp
      rw [← iseq]
      by_cases isl : i.succ = Fin.last n
      · exact if issat : f i.succ then isTrue (
          Or.inr ((_can_sat_iff_impl f i.succ).mpr ⟨i.succ, Fin.le_refl _, issat⟩)
        ) else isFalse (by
          push_neg; use icssat
          contrapose! issat; rename' issat => h
          rcases (_can_sat_iff_impl f i.succ).mp h with ⟨j, lej, jsat⟩
          convert jsat
          rw [isl] at *; symm
          exact Fin.last_le_iff.mp lej
        )
      · rename' isl => isnl; push_neg at isnl
        unfold _can_sat_impl
        rw [dif_neg isnl] at *
        rwa [or_iff_right icssat]

-- Prove that _can_sat is decidable
instance {n : Nat} (f : Fin (n + 1) → Prop) [DecidablePred f] : Decidable (_can_sat f) := by
  unfold _can_sat
  exact if h : _can_sat_impl f 0 then isTrue h else isFalse h

-- Improved find
-- (simpler implementation / proofs and no requirement for a satisfying index)

def _find_first_impl {n : Nat} (f : Fin (n + 1) → Prop) [DecidablePred f] (start : Fin (n + 1)) : Fin (n+1) :=
  if (f start) then start else
  if hinl : start ≠ Fin.last n then _find_first_impl f (start+1) else 0
termination_by ((n+1) - start.val)
decreasing_by
  rw [Fin.val_add_one_of_lt (Fin.lt_last_iff_ne_last.mpr hinl), Nat.sub_add_eq]
  exact Nat.sub_lt (Nat.sub_pos_iff_lt.mpr start.2) Nat.zero_lt_one

def _find_first {n : Nat} (f : Fin (n + 1) → Prop) [DecidablePred f] : Fin (n+1) :=
  _find_first_impl f 0

-- Prove that no element which satisfies 'f' appears earlier than
-- the one returned by 'find_first_impl' but not earlier than 'start'
lemma _find_first_is_first_impl {n : Nat} (f : Fin (n + 1) → Prop) [DecidablePred f] (start : Fin (n + 1)) :
  ∀ i, start ≤ i → f i → _find_first_impl f start ≤ i := by
  intro i ige isat
  unfold _find_first_impl
  split_ifs with h₀ h₁
  · assumption
  · -- Prove the necessary inequalities
    have ins : i ≠ start := by
      intro is
      rw [is] at isat
      contradiction
    have ssle : start + 1 ≤ i := by
      apply Fin.add_one_le_of_lt
      exact Fin.lt_iff_val_lt_val.mpr (lt_of_le_of_ne (Fin.le_iff_val_le_val.mp ige) (Fin.val_ne_iff.mpr ins.symm))
    -- Recurse to complete the goal
    exact _find_first_is_first_impl f (start+1) i ssle isat
  · exact Fin.zero_le _
termination_by ((n+1) - start.val)
decreasing_by
  rw [Fin.val_add_one_of_lt (Fin.lt_last_iff_ne_last.mpr h₁), Nat.sub_add_eq]
  exact Nat.sub_lt (Nat.sub_pos_iff_lt.mpr start.2) Nat.zero_lt_one

-- Prove that no element which satisfies 'f' appears earlier than
-- the one returned by 'find_first'
lemma _find_first_is_first {n : Nat} (f : Fin (n + 1) → Prop) [DecidablePred f] :
  ∀ i, f i → _find_first f ≤ i :=
  fun i isat ↦ _find_first_is_first_impl f 0 i (Fin.zero_le _) isat

-- Prove that the element returned by 'find_first_impl' actually satisfies 'f'
lemma _find_first_is_sat_impl {n : Nat} (f : Fin (n + 1) → Prop) [DecidablePred f]
  (start : Fin (n + 1)) (exsat : ∃ i, start ≤ i ∧ f i) : f (_find_first_impl f start) := by
  rcases exsat with ⟨i, ige, isat⟩
  unfold _find_first_impl
  split_ifs with h₀ h₁
  · assumption
  · -- Prove the necessary inequalities
    have ins : i ≠ start := by
      intro is
      rw [is] at isat
      contradiction
    have ssle : start + 1 ≤ i := by
      apply Fin.add_one_le_of_lt
      exact Fin.lt_iff_val_lt_val.mpr (lt_of_le_of_ne (Fin.le_iff_val_le_val.mp ige) (Fin.val_ne_iff.mpr ins.symm))
    -- Recurse to complete the goal
    exact _find_first_is_sat_impl f (start+1) ⟨i, ssle, isat⟩
  · -- If we reach the end of the search without finding
    -- a satisfying index, that implies a contradiction
    push_neg at h₁
    have hil := Fin.last_le_iff.mp (h₁ ▸ ige)
    rw [hil] at isat
    rw [h₁] at h₀
    contradiction
termination_by ((n+1) - start.val)
decreasing_by
  rw [Fin.val_add_one_of_lt (Fin.lt_last_iff_ne_last.mpr h₁), Nat.sub_add_eq]
  exact Nat.sub_lt (Nat.sub_pos_iff_lt.mpr start.2) Nat.zero_lt_one

-- Prove that the element returned by 'find_first' actually satisfies 'f'
lemma _find_first_is_sat {n : Nat} (f : Fin (n + 1) → Prop) [DecidablePred f] (exsat : ∃ i, f i) :
  f (_find_first f) := by
  rcases exsat with ⟨i, isat⟩
  exact _find_first_is_sat_impl f 0 ⟨i, Fin.zero_le _, isat⟩

-- Narrows the domain of a function on 'Fin' by one
abbrev narrow_fin_fun {n : Nat} (f : Fin (n + 1) → Prop) [DecidablePred f] (nnz : n ≠ 0) : Fin (n - 1 + 1) → Prop :=
  fun i ↦ f ⟨i.val, (lt_trans (lt_of_lt_of_eq i.2 (Nat.sub_one_add_one nnz)) (Nat.lt_add_one _))⟩

-- Count the number of inputs which satisfy 'f'
def count_sat {n : Nat} (f : Fin (n + 1) → Prop) [DecidablePred f] : Nat :=
  (if nz : n = 0 then 0 else count_sat (narrow_fin_fun f nz)) +
  (if (f ⟨n, Nat.lt_add_one _⟩) then 1 else 0)

-- The function 'f' is satisfiable if-and-only-if the
-- count of inputs which satisfy f is positive
lemma sat_iff_count_pos {n : Nat} (f : Fin (n + 1) → Prop) [DecidablePred f] :
  (∃ i, f i) ↔ 0 < count_sat f := by
  constructor
  · rintro ⟨i, isat⟩
    unfold count_sat
    split_ifs with h₀ h₁ h₂
    · norm_num
    · apply False.elim (h₁ _)
      convert isat; symm
      subst h₀
      exact Nat.le_zero.mp (Nat.le_of_lt_add_one i.2)
    · exact Nat.succ_pos _
    · by_cases hni : n = i.val
      · apply False.elim (h₂ _)
        convert isat
      rename' hni => nni; push_neg at nni
      rw [add_zero]
      apply (sat_iff_count_pos _).mp
      use ⟨i.val, lt_of_lt_of_eq (lt_of_le_of_ne (Nat.le_of_lt_add_one i.2) nni.symm) (Nat.sub_one_add_one h₀).symm⟩
  · unfold count_sat
    split_ifs with h₀ h₁ h₂
    · intro _
      use 0
      subst n
      exact h₁
    · rw [add_zero]
      exact fun h ↦ False.elim ((lt_self_iff_false _).mp h)
    · intro _
      use ⟨n, Nat.lt_add_one _⟩
    · rw [add_zero]
      intro h
      rcases (sat_iff_count_pos _).mpr h with ⟨i, isat⟩
      unfold narrow_fin_fun at isat
      use ⟨i.val, lt_trans (lt_of_lt_of_eq i.2 (Nat.sub_one_add_one h₀)) (Nat.lt_add_one _)⟩
