import Mathlib.Tactic.Linarith

set_option linter.style.longLine false
set_option linter.style.multiGoal false

/-
  This file contains the minimal definitions required to state the main result
  of Máthé's paper. That is, "The Angel of power 2 wins." In verifying the
  correctness of this proof, it should therefore be sufficient to confirm the
  following:
  1) The definitions below accurately represent the concepts described in the paper
  2) The statement at the end of this file matches the main result of the paper
     and the final proof in Main.lean
  3) All proofs in this project are validated by the Lean kernel
-/

-- The "distance" between two cells is either the vertical
-- difference or horizontal difference - whichever is greater.
abbrev dist (u v : Int × Int) := max (Int.natAbs (u.1 - v.1)) (Int.natAbs (u.2 - v.2))

-- Two cells are "close" if their distance is is no more than 'r'
abbrev close (r : Nat) (u v : Int × Int) : Prop := dist u v ≤ r

-- Structure describing the journey of an angel
-- 'p' indicates the "power" of the angel
-- (how far it can travel in a single step)
@[ext] structure Journey (p : Nat) where
  n : Nat
  seq : Fin (n+1) → Int × Int
  start : seq ⟨0, Nat.add_one_pos _⟩ = (0, 0)
  plimit : ∀ i, (ilt : i < n) →
    close p (seq ⟨i, by linarith⟩) (seq ⟨i+1, by linarith⟩)

-- Get the number of steps in the journey
def steps {p : Nat} (A : Journey p) := A.n

-- Get the 'i'th cell of the journey
def cell {p : Nat} (A : Journey p) (i : Nat) (ilt : i < steps A + 1) : Int × Int := A.seq ⟨i, ilt⟩

-- Construct the journey formed by the first 'n' steps of 'A'
def subjourney {p : Nat} (A : Journey p) (n : Nat) (nlt : n < steps A + 1) : Journey p where
  n := n
  seq := fun i ↦ cell A i.val (lt_of_lt_of_le i.2 (Nat.add_one_le_of_lt nlt))
  start := A.start
  plimit := fun i ilt ↦ A.plimit i (lt_of_lt_of_le ilt (Nat.le_of_lt_add_one nlt))

/- The devil responds to an angel's journey by "eating" one cell. This
   suggests that the devil should be of type (Journey p) → (Int × Int).
   However, that would require the type of the devil to be dependent on 'p'
   and would introduce a distinction between different classes of devil that
   doesn't exist in Máthé's proof.

   The solution is to bundle the angel's power along with its journey
   in a new structure. -/
structure JourneyP where
  p : Nat
  A : Journey p

def Devil : Type := JourneyP → (Int × Int)

-- Indicates the response by devil 'D' to journey 'A'
def response (D : Devil) {p : Nat} (A : Journey p) : Int × Int := D ⟨p, A⟩

-- A journey 'A' is "allowed" under some devil strategy 'D', if no cell
-- in the angel's journey was previously eaten by the devil.
def allowed {p : Nat} (D : Devil) (A : Journey p) : Prop :=
  ∀ i j (ilt : i < j) (jlt : j < steps A + 1),
  response D (subjourney A i (lt_trans ilt jlt)) ≠ cell A j jlt

/- A devil wins over angels of power 'p', if there exists some natural number 'N'
   such that every angel journey of power p longer than N is not "allowed" -/
def devil_wins (D : Devil) (p : Nat) : Prop := ∃ N : Nat, ∀ A : Journey p, N < steps A → ¬allowed D A

-- Statement of the main result of Máthé's paper:
-- There does not exist a devil which wins over the angel of power 2.
-- Or in other words, "The angel of power 2 wins".
#check ¬∃ (D : Devil), devil_wins D 2
