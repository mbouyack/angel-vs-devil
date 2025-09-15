import Mathlib.Data.Fin.Basic
import AngelDevil.Util

set_option linter.style.longLine false

-- This file includes miscellaneous results used elsewhere in the proof.

-- The 'intermediate value theorem' holds for a funcion from 'Fin' to Int
-- for which consecutive values are always "adjacent" (differ by 1 or less).
-- NOTE: 'wlog' doesn't seem to work in the same theorem as recursion so
-- the proof must be broken into two separate parts.
lemma fin_intermediate_value_of_consec_adj_of_le {n : Nat} (f : Fin (n + 1) → Int)
  (hadj : ∀ i : Fin n, (f i.succ - f i.castSucc).natAbs ≤ 1)
  (hle : f 0 ≤ f (Fin.last n)) :
  ∀ x,
  ∀ (_ : min (f 0) (f (Fin.last n)) ≤ x),
  ∀ (_ : x ≤ max (f 0) (f (Fin.last n))),
  ∃ j, f j = x := by
  intro x lex xle
  rw [min_eq_left hle] at lex
  rw [max_eq_right hle] at xle
  -- Handle a trivial case whose negation is required to recurse
  by_cases flx : f (Fin.last n) = x
  · use Fin.last n
  rename' flx => flnex; push_neg at flnex
  -- If n = 0, then f 0 = f (Fin.last n) which would be a contradiction
  -- Conclude that n ≠ 0
  have nnz : n ≠ 0 := by
    intro nz
    subst nz
    apply flnex (le_antisymm _ xle)
    convert lex
  -- Some useful results that follow from n ≠ 0
  have onele : 1 ≤ n :=
    Nat.add_one_le_of_lt (Nat.pos_of_ne_zero nnz)
  have onemodns : 1 % (n + 1) = 1 :=
    Nat.mod_eq_of_lt (Nat.lt_add_one_of_le onele)
  -- If x ≤ f (Fin.last n - 1) we can recurse
  by_cases xleflp : x ≤ f (Fin.last n - 1)
  · -- In order to recurse, we need to wrap 'f' in a function
    -- which takes Fin (n - 1 + 1) as input and casts it to Fin (n + 1)
    let f' : Fin (n - 1 + 1) → Int :=
      fun i ↦ f ⟨i.val, lt_trans (lt_of_lt_of_eq i.2 (Nat.sub_one_add_one nnz)) (Nat.lt_add_one _)⟩
    -- Prove the "adjacency" requirement for f'
    have hadj' : ∀ (i : Fin (n - 1)), (f' i.succ - f' i.castSucc).natAbs ≤ 1 := by
      intro i
      unfold f'
      have ivlt : i.val < n := lt_trans i.2 (Nat.sub_one_lt nnz)
      have ivslt : i.val + 1 < n + 1 :=
        Nat.add_one_lt_add_one_iff.mpr ivlt
      let i' := Fin.mk i.val ivlt
      have finid₀ : Fin.mk i.succ.val ivslt = i'.succ := by
        apply (Fin.val_eq_val _ _).mp; dsimp
      have finid₁ : Fin.mk i.castSucc.val (lt_trans ivlt (Nat.lt_add_one _)) = i'.castSucc := by
        apply (Fin.val_eq_val _ _).mp; dsimp
      rw [finid₀, finid₁]
      exact hadj i'
    -- Prove that the 'head' is still less than or equal to the 'tail'
    have hle' : f' 0 ≤ f' (Fin.last (n - 1)) := by
      unfold f'
      convert le_trans lex xleflp using 2
      apply (Fin.val_eq_val _ _).mp; dsimp
      rw [Fin.sub_val_of_le]
      · dsimp
        rw [onemodns]
      · apply Fin.le_iff_val_le_val.mpr; dsimp
        rw [onemodns]
        exact onele
    -- Prove the bounds on x for f'
    have lex' : min (f' 0) (f' (Fin.last (n - 1))) ≤ x := min_le_of_left_le lex
    have xle' : x ≤ max (f' 0) (f' (Fin.last (n - 1))) := by
      unfold f'
      apply le_max_of_le_right
      convert xleflp using 2
      apply (Fin.val_eq_val _ _).mp
      rw [Fin.sub_val_of_le]
      · dsimp; congr 1
        exact onemodns.symm
      · apply Fin.le_iff_val_le_val.mpr; dsimp
        rwa [onemodns]
    -- Recurse to get the value of j which satisfies the goal
    have := fin_intermediate_value_of_consec_adj_of_le f' hadj' hle' x lex' xle'
    rcases this with ⟨j, hj⟩
    use Fin.mk j.val (lt_trans j.2 (lt_of_eq_of_lt (Nat.sub_one_add_one nnz) (Nat.lt_add_one _)))
  rename' xleflp => flpltx; push_neg at flpltx
  -- Finally, show that in order to satisfy both the adjacency requirement
  -- and the bounds we have proven (or assumed) for x, it must be the case
  -- that f (Fin.mk (n-1)) = x
  let i' : Fin n := Fin.mk (n - 1) (Nat.sub_one_lt nnz)
  have finid₀ : Fin.last n - 1 = i'.castSucc := by
    apply (Fin.val_eq_val _ _).mp; dsimp
    rw [Fin.sub_val_of_le]
    · unfold i'; dsimp
      rw [onemodns]
    · apply Fin.le_iff_val_le_val.mpr; dsimp
      rwa [onemodns]
  have finid₁ : Fin.last n = i'.succ := by
    unfold i'
    apply (Fin.val_eq_val _ _).mp; dsimp
    exact (Nat.sub_one_add_one nnz).symm
  rw [finid₀] at flpltx
  rw [finid₁] at xle
  use i'.succ
  apply le_antisymm _ xle
  have := Int.ofNat_le_ofNat_of_le (hadj i')
  simp at this
  rw [abs_of_pos] at this
  · exact le_trans (Int.le_add_of_sub_left_le this) (Int.add_one_le_of_lt flpltx)
  · exact Int.sub_pos_of_lt (lt_of_lt_of_le flpltx xle)
termination_by n
decreasing_by
  exact Nat.sub_one_lt nnz

-- This is the same result as the above theorem, but without the
-- requirement that f 0 ≤ f (Fin.last n)
-- Essentially, this is a "wlog" argument: proving that if
-- ¬f 0 ≤ f (Fin.last n), we can build a new function, f', such that
-- f' 0 ≤ f' (Fin.last n) and all other requirements hold.
lemma fin_intermediate_value_of_consec_adj {n : Nat} (f : Fin (n + 1) → Int)
  (hadj : ∀ i : Fin n, (f i.succ - f i.castSucc).natAbs ≤ 1) :
  ∀ x,
  ∀ (_ : min (f 0) (f (Fin.last n)) ≤ x),
  ∀ (_ : x ≤ max (f 0) (f (Fin.last n))),
  ∃ j, f j = x := by
  intro x lex xle
  -- If f 0 ≤ f (Fin.last n) we can use the restricted verion of the
  -- theorem proven above.
  by_cases hle : f 0 ≤ f (Fin.last n)
  · exact fin_intermediate_value_of_consec_adj_of_le f hadj hle x lex xle
  push_neg at hle
  replace hle := le_of_lt hle
  -- To prove the symmetry, we define f', which is just the reverse of f
  let f' := fun i ↦ f ((Fin.last n) - i)
  have hadj' : ∀ (i : Fin n), (f' i.succ - f' i.castSucc).natAbs ≤ 1 := by
    intro i
    unfold f'
    have hlscsnz : Fin.last n - i.castSucc ≠ 0 := by
      apply Fin.val_ne_zero_iff.mp
      rw [Fin.sub_val_of_le (Fin.le_iff_val_le_val.mpr (le_of_lt i.2))]
      apply Nat.sub_ne_zero_iff_lt.mpr
      exact i.2
    -- Define i for the reverse function
    let i' := (Fin.last n - i.castSucc).pred hlscsnz
    -- Now prove two identities we'll need in order to show that
    -- 'h' holds for the reverse function.
    have finid₀ : Fin.last n - i.succ = i'.castSucc := by
      unfold i'
      apply (Fin.val_eq_val _ _).mp; dsimp
      rw [Fin.sub_val_of_le (Fin.le_iff_val_le_val.mpr (Nat.add_one_le_of_lt i.2))]; dsimp
      rw [Fin.sub_val_of_le (Fin.le_iff_val_le_val.mpr (le_of_lt i.2)), Nat.sub_add_eq]; dsimp
    have finid₁ : Fin.last n - i.castSucc = i'.succ := by
      unfold i'
      apply (Fin.val_eq_val _ _).mp; dsimp
      rw [Fin.sub_val_of_le (Fin.le_iff_val_le_val.mpr (le_of_lt i.2)), Nat.sub_one_add_one]; dsimp
      exact Nat.sub_ne_zero_of_lt i.2
    rw [finid₀, finid₁, ← neg_sub, Int.natAbs_neg]
    exact hadj i'
  have hf'z : f' 0 = f (Fin.last n) := by
    unfold f'; congr
    apply (Fin.val_eq_val _ _).mp
    rw [Fin.sub_val_of_le (Fin.le_iff_val_le_val.mpr (Nat.zero_le _))]; simp
  have hf'l : f' (Fin.last n) = f 0 := by
    unfold f'; congr
    exact Fin.sub_self
  have lex' : min (f' 0) (f' (Fin.last n)) ≤ x := by
    rwa [hf'z, hf'l, min_comm]
  have xle' : x ≤ max (f' 0) (f' (Fin.last n)) := by
    rwa [hf'z, hf'l, max_comm]
  rw [← hf'z, ← hf'l] at hle
  rcases fin_intermediate_value_of_consec_adj_of_le f' hadj' hle x lex' xle' with ⟨j, hj⟩
  use (Fin.last n) - j
