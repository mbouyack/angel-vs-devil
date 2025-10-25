import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith
-- TODO: Figure out a more appropriate import (rather than 'Linarith')

set_option linter.style.longLine false

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

-- Improved, improved find (don't require "Fin (n + 1)")

def find_first {n : Nat} (f : Fin n → Prop) [DecidablePred f] (nnz : n ≠ 0) : Fin n :=
  if hn1 : n = 1 then ⟨0, Nat.pos_of_ne_zero nnz⟩ else
  if f ⟨0, Nat.pos_of_ne_zero nnz⟩ then ⟨0, Nat.pos_of_ne_zero nnz⟩ else
  Fin.cast (Nat.sub_one_add_one nnz) (find_first
    (fun (i : Fin (n - 1)) ↦ f (Fin.cast (Nat.sub_one_add_one nnz) i.succ))
    (by
      push_neg at hn1
      have onelt : 1 < n :=
        lt_of_le_of_ne (Nat.one_le_of_lt (Nat.pos_of_ne_zero nnz)) hn1.symm
      exact Nat.sub_ne_zero_of_lt onelt)
  ).succ

-- Prove that the element returned by 'find_first' actually satisfies 'f'
lemma find_first_is_sat {n : Nat} (f : Fin n → Prop) [DecidablePred f] (exsat : ∃ i, f i) :
  f (find_first f (by obtain ⟨i, _⟩ := exsat; exact Nat.ne_zero_of_lt (Fin.pos i))) := by
  unfold find_first
  rcases exsat with ⟨i, isat⟩
  have nnez : n ≠ 0 := Nat.ne_zero_of_lt (Fin.pos i)
  split_ifs with h₀ h₁
  · convert isat
  · exact h₁
  · -- Define f' to be the function used in the recursion step then recurse
    let f' := fun (i : Fin (n - 1)) ↦ f (Fin.cast (Nat.sub_one_add_one nnez) i.succ)
    apply find_first_is_sat f'
    -- Prove some inequalities on i
    have inez : i.val ≠ 0 := by
      symm; contrapose! h₁
      convert isat
    have iplt : i.val - 1 < n - 1 :=
      Nat.sub_lt_sub_right (Nat.one_le_of_lt (Nat.pos_of_ne_zero inez)) i.2
    -- Now show that i-1 satisfies f'
    use Fin.mk (i.val - 1) iplt
    unfold f'
    convert isat
    apply (Fin.val_eq_val _ _).mp; simp
    exact Nat.sub_one_add_one inez

-- Prove that no element which satisfies 'f' appears earlier than
-- the one returned by 'find_first'
lemma find_first_is_first {n : Nat} (f : Fin n → Prop) [DecidablePred f] :
  ∀ i, f i → find_first f (Nat.ne_zero_of_lt (Fin.pos i)) ≤ i := by
  intro i isat
  have nnez : n ≠ 0 := Nat.ne_zero_of_lt (Fin.pos i)
  unfold find_first
  split_ifs with h₀ h₁; repeat apply Fin.le_iff_val_le_val.mpr; simp
  -- Prove some inequalities on i
  have inez : i.val ≠ 0 := by
    symm; contrapose! h₁
    convert isat
  have onele : 1 ≤ i.val := Nat.one_le_of_lt (Nat.pos_of_ne_zero inez)
  have iplt : i.val - 1 < n - 1 :=
    Nat.sub_lt_sub_right onele i.2
  -- Rearrange the goal so we can apply recursion
  apply Nat.add_le_of_le_sub onele
  rw [← Fin.val_mk iplt]
  apply Fin.le_iff_val_le_val.mp
  apply find_first_is_first
  convert isat
  apply (Fin.val_eq_val _ _).mp; simp
  exact Nat.sub_one_add_one inez

-- Implment 'find_last' by reversing the direction of search with 'find_first'
def find_last {n : Nat} (f : Fin n → Prop) [DecidablePred f] (nnz : n ≠ 0) : Fin n :=
  ⟨n - 1, Nat.sub_one_lt nnz⟩ - (find_first (fun i ↦ f (⟨n - 1, Nat.sub_one_lt nnz⟩ - i)) nnz)

-- Proving that (a - (a - b)) = b is non-trivial when working with 'Fin'
lemma fin_sub_sub_self {n : Nat} (nnez : n ≠ 0) (i : Fin n) :
  ⟨n - 1, Nat.sub_one_lt nnez⟩ - (⟨n - 1, Nat.sub_one_lt nnez⟩ - i) = i := by
  have ile : i ≤ ⟨n - 1, Nat.sub_one_lt nnez⟩ := Nat.le_sub_one_of_lt i.2
  apply (Fin.val_eq_val _ _).mp
  rw [Fin.sub_val_of_le]
  · rw [Fin.sub_val_of_le ile]
    exact Nat.sub_sub_self ile
  · apply Fin.le_iff_val_le_val.mpr
    rw [Fin.sub_val_of_le ile]
    simp

-- Prove that the element returned by 'find_last' actually satisfies 'f'
lemma find_last_is_sat {n : Nat} (f : Fin n → Prop) [DecidablePred f] (exsat : ∃ i, f i) :
  f (find_last f (by obtain ⟨i, _⟩ := exsat; exact Nat.ne_zero_of_lt (Fin.pos i))) := by
  rcases exsat with ⟨i, isat⟩
  have nnez : n ≠ 0 := Nat.ne_zero_of_lt (Fin.pos i)
  unfold find_last
  let np : Fin n := ⟨n - 1, Nat.sub_one_lt nnez⟩
  apply find_first_is_sat (fun i ↦ f (np - i))
  use np - i;
  convert isat
  exact fin_sub_sub_self nnez _

-- Prove that no element which satisfies 'f' appears later than
-- the one returned by 'find_last'
lemma find_last_is_last {n : Nat} (f : Fin n → Prop) [DecidablePred f] :
  ∀ i, f i → i ≤ find_last f (Nat.ne_zero_of_lt (Fin.pos i)) := by
  intro i isat
  have nnez : n ≠ 0 := Nat.ne_zero_of_lt (Fin.pos i)
  unfold find_last
  -- Manipulate the goal into a form where we can use 'find_first_is_first'
  apply Fin.le_iff_val_le_val.mpr
  rw [Fin.sub_val_of_le]; swap
  · apply Fin.le_iff_val_le_val.mpr; simp
    exact Nat.le_sub_one_of_lt (Fin.prop _)
  apply Nat.le_sub_of_add_le
  rw [add_comm]
  have ile : i ≤ ⟨n - 1, Nat.sub_one_lt nnez⟩ := Nat.le_sub_one_of_lt i.2
  apply Nat.add_le_of_le_sub ile
  rw [← Fin.sub_val_of_le ile]
  apply Fin.le_iff_val_le_val.mp
  -- Finally, apply find_first_is_first
  apply find_first_is_first
  convert isat
  exact fin_sub_sub_self nnez _

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
