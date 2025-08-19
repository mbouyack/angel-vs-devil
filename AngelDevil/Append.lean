import Mathlib.Data.Fin.Basic
import AngelDevil.Basic

set_option linter.style.longLine false

/- This file defines the 'append' operation on a Journey
   This will be used to construct the Runner's journey in Runner.lean.
-/

def AppendJourney {p : Nat} (A : Journey p) (u : Int × Int) (hclose : close p (last A) u) : Journey p where
  n := A.n + 1
  seq := fun i ↦ if h : i = Fin.last (A.n + 1) then u else A.seq (Fin.castPred i h)
  start := A.start
  plimit := by
    intro i ilt
    have inl : ⟨i, lt_trans ilt (Nat.lt_add_one _)⟩ ≠ Fin.last (A.n + 1) := by
      apply Fin.val_ne_iff.mp; simp
      exact ne_of_lt ilt
    rw [dif_neg inl]
    split_ifs with h
    · apply (Fin.val_eq_val _ _).mpr at h; simp at h
      subst h
      exact hclose
    · apply Fin.val_ne_iff.mpr at h; simp at h
      push_neg at h
      exact A.plimit i (lt_of_le_of_ne (Nat.le_of_lt_add_one ilt) h)

-- The number of steps in the append journey is one more than the original
lemma append_steps {p : Nat} (A : Journey p) (u : Int × Int) (hclose : close p (last A) u) :
  steps (AppendJourney A u hclose) = steps A + 1 := by
  unfold AppendJourney steps; dsimp

-- The last cell in the append journey is 'u'
lemma append_last {p : Nat} (A : Journey p) (u : Int × Int) (hclose : close p (last A) u) :
  last (AppendJourney A u hclose) = u := by
  unfold last cell steps AppendJourney; dsimp
  rw [dif_pos _]
  apply (Fin.val_eq_val _ _).mp; simp
