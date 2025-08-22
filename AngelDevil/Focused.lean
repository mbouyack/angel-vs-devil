import Mathlib.Logic.Function.Defs
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Basic
import AngelDevil.Util
import AngelDevil.Defs
import AngelDevil.Basic
import AngelDevil.Subjourney

set_option linter.style.longLine false
set_option linter.style.multiGoal false

/- A devil is "focused" of size N if it never eats the same cell twice and
  for the first (2N+1)² responses, only eats cells are no farther than
  distance N from the origin

  That is, the devil attempts to catch the angel by eating a square region
  (2N+1) cells on a side, centered at the origin. -/
def focused (D : Devil) (N : Nat) : Prop :=
  ∀ (p : Nat) (A : Journey p), (∀ i j (ilt : i < steps A + 1) (jlt : j < steps A + 1), i ≠ j →
  response D (subjourney A i ilt) ≠ response D (subjourney A j jlt)) ∧
  (∀ n (nlt : n < (2*N + 1)^2 ∧ n < steps A + 1), close N (0, 0) (response D (subjourney A n nlt.2)))

-- B(N) is the notation use by Máthé to donate the cells at
-- distance N or less from the origin.
-- TODO: Consider moving this definition to a more prominent location.
def B (N : Nat) : Set (Int × Int) := {u | close N (0, 0) u}

-- Bijective function from Fin (2N+1)² to B N (the escape square)
def square_iter (N : Nat) : Fin ((2*N + 1) ^ 2) → B N :=
  fun i ↦ ⟨(i % (2*N + 1) - N, i / (2*N + 1) - N), by
    apply close_origin_of_bounds; dsimp
    constructor
    · rw [neg_sub]
      exact Int.sub_le_self _ (Int.zero_le_ofNat _)
    constructor
    · apply (Int.add_le_add_iff_right (N : Int)).mp
      rw [Int.sub_add_cancel, ← two_mul]
      apply Int.le_of_lt_add_one
      apply Int.emod_lt_of_pos
      linarith
    constructor
    · rw [neg_sub]
      exact Int.sub_le_self _ (Int.zero_le_ofNat _)
    · apply (Int.add_le_add_iff_right (N : Int)).mp
      rw [Int.sub_add_cancel, ← two_mul]
      apply Int.le_of_lt_add_one (Int.ediv_lt_of_lt_mul (by linarith) _)
      rw [← pow_two]
      have ilt := Int.ofNat_lt_ofNat_of_lt i.2; simp at ilt
      assumption
  ⟩

-- Bound useful for proving 'square_iter' is an equivalence
lemma square_iter_inv_val_nonneg (N : Nat) (u : Int × Int) (hclose : close N (0, 0) u) :
  (0 : Int) ≤ (2 * ↑N + 1) * (u.2 + ↑N) + u.1 + ↑N := by
  have negxle := close_origin_negxle N u hclose
  have negyle := close_origin_negyle N u hclose
  rw [add_assoc]
  exact Int.add_nonneg (Int.mul_nonneg (by linarith) (by linarith)) (by linarith)

-- This function is the inverse of 'square_iter'.
-- We'll use it to show an equivalence between B (N) and Fin (2N+1)²
def square_iter_inv (N : Nat) : B N → Fin ((2*N + 1) ^ 2) :=
  fun u ↦ ⟨Int.natAbs ((2 * N + 1) * ((u : Int × Int).2 + N) + (u : Int × Int).1 + N), by
    let u' : Int × Int := u
    -- First prove the bounds on u'
    have hclose : close N (0, 0) u' := Subtype.coe_prop u
    have negxle := close_origin_negxle N u' hclose
    have xle := close_origin_xle N u' hclose
    have negyle := close_origin_negyle N u' hclose
    have yle := close_origin_yle N u' hclose
    apply Int.ofNat_lt.mp; simp
    -- Some cases below require 0 < N, so handle the case where N = 0
    by_cases nle : (N : Int) ≤ 0
    · have nz := le_antisymm nle (Int.zero_le_ofNat N)
      rw [nz, mul_zero, zero_add, one_mul, add_zero, add_zero, one_pow]
      have u'1z : u'.1 = 0 := by
        apply le_antisymm
        · exact nz ▸ xle
        · apply neg_le_neg_iff.mp
          rw [neg_zero]
          exact nz ▸ negxle
      have u'2z : u'.2 = 0 := by
        apply le_antisymm
        · exact nz ▸ yle
        · apply neg_le_neg_iff.mp
          rw [neg_zero]
          exact nz ▸ negyle
      rw [u'1z, u'2z, zero_add, abs_zero]; norm_num
    rename' nle => npos; push_neg at npos
    -- Now prove the range of the function is [0, (2N+1)²)
    rw [abs_of_nonneg]
    · -- First prove the upper bound
      rw [pow_two]
      nth_rw 2 [mul_add]
      rw [mul_one, ← add_assoc, add_assoc]
      apply Int.lt_add_one_of_le (add_le_add _ (by linarith))
      exact (Int.mul_le_mul_left (by linarith)).mpr (by linarith)
    · -- We've already proven the lower bound separately
      exact square_iter_inv_val_nonneg N u' hclose
  ⟩

-- Prove the equivalence between Fin (2N+1)² and B(N)
def square_equiv (N : Nat) : B N ≃ Fin ((2 * N + 1) ^ 2) where
  toFun := square_iter_inv N
  invFun := square_iter N
  left_inv := by
    unfold Function.LeftInverse square_iter square_iter_inv
    intro x
    let x' : Int × Int := x
    have hclose : close N (0, 0) x' := Subtype.coe_prop x
    have xle := close_origin_xle N x' hclose
    have negxle := close_origin_negxle N x' hclose
    ext
    · simp
      rw [abs_of_nonneg (square_iter_inv_val_nonneg N x' hclose)]
      rw [add_assoc, Int.mul_add_emod_self_left]
      rw [Int.emod_eq_of_lt]; repeat linarith
    · simp
      rw [abs_of_nonneg (square_iter_inv_val_nonneg N x' hclose)]
      rw [add_assoc, Int.mul_add_ediv_left]
      rw [Int.ediv_eq_zero_of_lt]; repeat linarith
  right_inv := by
    unfold Function.RightInverse Function.LeftInverse square_iter square_iter_inv
    intro x
    apply (Fin.val_eq_val _ _).mp
    dsimp
    rw [add_assoc, sub_add_cancel, sub_add_cancel, EuclideanDomain.div_add_mod]
    rw [Int.natAbs_natCast]

-- 'square_iter' is injective
-- TODO: Do we still need this now that we've prove 'square_iter' is an equivalence?
lemma square_iter_inj (N : Nat) : Function.Injective (square_iter N) := by
  rw [Function.Injective]
  intro a₁ a₂ h
  unfold square_iter at h
  simp at h
  have nz : 2 * (N : Int) + 1 ≠ 0 := by linarith
  apply (Fin.val_eq_val _ _).mp
  apply Int.ofNat_inj.mp
  rw [← EuclideanDomain.div_add_mod (a₁.val : Int) ((2 : Int) * N + 1)]
  rw [← EuclideanDomain.div_add_mod (a₂.val : Int) ((2 : Int) * N + 1)]
  rw [h.1, h.2]

-- 'square_iter' is surjective
lemma square_iter_surj (N : Nat) : Function.Surjective (square_iter N) := by
  rw [Function.Surjective]
  intro u
  let u' : Int × Int := ↑u
  have hclose : u' ∈ B N := Subtype.coe_prop u
  unfold B at hclose; dsimp at hclose
  let ival := (u'.2 + N)*(2*N + 1) + (u'.1 + N)
  have ipos : 0 ≤ ival := by
    apply Int.add_nonneg
    · apply Int.mul_nonneg
      · apply Int.le_add_of_sub_left_le
        rw [Int.zero_sub]
        exact close_origin_negyle N u hclose
      · linarith
    · apply Int.le_add_of_sub_left_le
      rw [Int.zero_sub]
      exact close_origin_negxle N u hclose
  have ilt : ival < ((2*N + 1) ^ 2 : Nat) := by
    rw [pow_two]; dsimp
    rw [add_one_mul, ← add_assoc]
    apply Int.lt_add_one_of_le
    unfold ival
    apply add_le_add
    · apply (mul_le_mul_right _).mpr
      · rw [two_mul]
        apply add_le_add_right
        exact close_origin_yle N u hclose
      · linarith
    · rw [two_mul]
      apply add_le_add_right
      exact close_origin_xle N u hclose
  use ⟨Int.toNat ival, (Int.toNat_lt ipos).mpr ilt⟩
  unfold square_iter
  apply SetCoe.ext; simp
  apply Prod.eq_iff_fst_eq_snd_eq.mpr; dsimp
  have bound₀ : 0 ≤ u'.1 + ↑N := by linarith [close_origin_negxle N u hclose]
  have bound₁ : u'.1 + ↑N < 2 * ↑N + 1 := by linarith [close_origin_xle N u hclose]
  constructor
  · rw [max_eq_left ipos, Int.mul_add_emod_self_right]
    rw [Int.emod_eq_of_lt bound₀ bound₁, Int.add_sub_cancel]
  · rw [max_eq_left ipos, Int.mul_add_ediv_right _ _ (by linarith)]
    rw [Int.ediv_eq_zero_of_lt bound₀ bound₁, add_zero, Int.add_sub_cancel]

-- 'square_iter' is bijective
lemma square_iter_bij (N : Nat) : Function.Bijective (square_iter N) :=
  ⟨square_iter_inj N, square_iter_surj N⟩

-- As hoped, now that we've switched the codomain of 'square_iter'
-- to be B(N), this result is now trivial.
lemma square_iter_close (N : Nat) :
  ∀ i, close N (0, 0) (square_iter N i) :=
  fun i ↦ Subtype.coe_prop (square_iter N i)

-- Checks if a particular element of a list has a particular value
abbrev list_elem_fun {α : Type} (L : List α) (a : α) [DecidableEq α]
  (lnz : L.length ≠ 0) : Fin (L.length - 1 + 1) → Prop :=
  fun i ↦ L[i.val]'(lt_of_lt_of_eq i.2 (Nat.sub_one_add_one lnz)) = a

-- Checks to see if a list contains a particular element
-- TODO: This is literally just List.find - there's no reason to write your own thing
abbrev list_has_elem {α : Type} [DecidableEq α] (L : List α) (a : α) : Prop :=
  if lz : L.length = 0 then False else _can_sat (list_elem_fun L a lz)

-- Used to cast back and forth between the Fin type needed by
-- 'find_cell_in_square' and the type needed by 'square_iter'
lemma find_cell_fin_cast_eq (N : Nat) :
  (2 * N + 1) ^ 2 = (2 * N + 1) * (2 * N) + 2 * N + 1 := by
  rw [pow_two, Nat.mul_add_one, ← add_assoc]

def find_cell_fin_cast (N : Nat) (i : Fin ((2 * N + 1) * (2 * N) + 2 * N + 1)) : Fin ((2*N + 1)^2) :=
  Fin.cast (find_cell_fin_cast_eq N).symm i

def find_cell_fin_cast' (N : Nat) (i : Fin ((2 * N + 1) ^ 2)) : Fin ((2 * N + 1) * (2 * N) + 2 * N + 1) :=
  Fin.cast (find_cell_fin_cast_eq N) i

-- Search the escape square for a cell which satisfies 'f'
def find_cell_in_square (N : Nat) (f : (Int × Int) → Prop) [DecidablePred f] : (Int × Int) :=
  square_iter N (find_cell_fin_cast N
  (_find_first (fun i ↦ f (square_iter N (find_cell_fin_cast N i)))))

-- The cell found by "find_cell_in_square" does in-fact satisfy 'f'
lemma cell_in_square_is_sat (N : Nat) (f : (Int × Int) → Prop) [DecidablePred f]
  (exsat : ∃ u, f u ∧ close N (0, 0) u) : f (find_cell_in_square N f) := by
  unfold find_cell_in_square
  let f' := fun i ↦ f (square_iter N (find_cell_fin_cast N i))
  rcases exsat with ⟨u, hsat, hclose⟩
  rcases square_iter_surj N ⟨u, hclose⟩ with ⟨i, hiter⟩
  let i' := find_cell_fin_cast' N i
  have exsat' : ∃ i, f' i := by
    use i'
    unfold f' i' find_cell_fin_cast find_cell_fin_cast'; simp
    rwa [hiter]
  exact _find_first_is_sat f' exsat'

-- The cell found by "find_cell_in_square" is in-fact close to the origin
lemma cell_in_square_is_close (N : Nat) (f : (Int × Int) → Prop) [DecidablePred f] :
  close N (0, 0) (find_cell_in_square N f) := by
  unfold find_cell_in_square
  exact square_iter_close N _

abbrev close_and_uneaten (N : Nat) (eaten : List (Int × Int)) : (Int × Int) → Prop :=
  fun u ↦ close N (0, 0) u ∧ u ∉ eaten

-- If the original devil's response is focused, use that cell, otherwise use
-- 'find_cell_in_square' to locate a cell which *is* focused
abbrev pick_focused_cell (D : Devil) (N : Nat) {p : Nat} (A : Journey p)
  (eaten : List (Int × Int)) : (Int × Int) :=
  if close_and_uneaten N eaten (response D A) then (response D A) else
  find_cell_in_square N (close_and_uneaten N eaten)

/- Given a devil and a journey, determine the cells that will be eaten
   by the focused version of the devil. This will be used to create the
   focused devil. -/
def focused_cells (D : Devil) (N : Nat) {p : Nat} (A : Journey p) : List (Int × Int) :=
  if sz : steps A = 0 then
    -- For the base case, follow the original devil's response if it is "focused"
    -- or begin eating cells in the bottom left corner of the "escape square" if
    -- it is not.
    (if close N (0, 0) (response D A) then [(response D A)] else [(-N, -N)])
  else (
    -- Once the escape square is full, just eat cells along the x-axis forever
    if (2*N + 1)^2 ≤ steps A then (steps A, 0) else
    -- Otherwise, pick a focused cell, with preference given for the
    -- original devil's response
    pick_focused_cell D N A (focused_cells D N (subjourney_drop_last A sz))
  ) :: focused_cells D N (subjourney_drop_last A sz)
termination_by (steps A)
decreasing_by
  rw [subjourney_drop_last_steps]
  exact Nat.sub_one_lt sz

/- Indicates that a cell has not appeared previously in the 'focused_cells' list
   and is "close" to the origin. Note that we would have preferred to use this
   in the definition of focused_cells (above), but doing so would have created
   a dependency loop. -/
abbrev cell_is_focused (D : Devil) (N : Nat) {p : Nat} (A : Journey p)
  (snz : steps A ≠ 0) : (Int × Int) → Prop :=
  fun u ↦ close_and_uneaten N (focused_cells D N (subjourney_drop_last A snz)) u

-- If a cell is "focused" it is close to the origin
lemma close_of_focused (D : Devil) (N : Nat) {p : Nat} (A : Journey p)
  (snz : steps A ≠ 0) {u : Int × Int} (h : cell_is_focused D N A snz u) :
  close N (0, 0) u := h.1

/- If eating a particular cell would be considered a "focused" response
   that cell must not appear in the list of cells which have already
   been eaten -/
lemma uneaten_of_focused (D : Devil) (N : Nat) {p : Nat} (A : Journey p)
  {u : Int × Int} (snz : steps A ≠ 0) (h : cell_is_focused D N A snz u) :
  u ∉ focused_cells D N (subjourney_drop_last A snz) := h.2

-- The length of the 'focused_cells' list is one more than the number of
-- steps in the journey from which it was generated
lemma focused_cells_length (D : Devil) (N : Nat) {p : Nat} (A : Journey p) :
  (focused_cells D N A).length = steps A + 1 := by
  unfold focused_cells pick_focused_cell
  split_ifs with h₀ h₁ h₂ h₃
  repeat
  rw [List.length_singleton, h₀, zero_add]
  repeat
  rw [List.length_cons, focused_cells_length, subjourney_drop_last_steps]
  rw [Nat.sub_one_add_one h₀]
termination_by (steps A)
decreasing_by
  repeat
  rw [subjourney_drop_last_steps]
  exact Nat.sub_one_lt h₀

lemma focused_cells_length_pos (D : Devil) (N : Nat) {p : Nat} (A : Journey p) :
  0 < (focused_cells D N A).length := by
  rw [focused_cells_length]; exact Nat.succ_pos _

-- Get the first element of the focused cells list when the journey
-- has zero steps and the original devil responds with a "close" cell
lemma focused_cells_getElem_zero_of_steps_zero_of_close_response
  (D : Devil) (N : Nat) {p : Nat} (A : Journey p) :
  close N (0, 0) (response D A) → steps A = 0 → (focused_cells D N A)[0]'(
    focused_cells_length_pos D N A) = (response D A) := by
  intro hclose sz
  have : focused_cells D N A = focused_cells D N A := rfl
  nth_rw 2 [focused_cells] at this
  rw [dif_pos sz, if_pos hclose] at this
  rw [getElem_congr_coll this]
  rfl

-- Get the first element of the focused cells list when the journey
-- has zero steps and the original devil responds with a "far" cell
lemma focused_cells_getElem_zero_of_steps_zero_of_far_response
  (D : Devil) (N : Nat) {p : Nat} (A : Journey p) :
  ¬close N (0, 0) (response D A) → steps A = 0 → (focused_cells D N A)[0]'(
    focused_cells_length_pos D N A) = (-(N : Int), -(N : Int)) := by
  intro hfar sz
  have : focused_cells D N A = focused_cells D N A := rfl
  nth_rw 2 [focused_cells] at this
  rw [dif_pos sz, if_neg hfar] at this
  rw [getElem_congr_coll this]
  rfl

-- Get the first element of the focused cells list when the journey
-- has at least as many steps as there are cells in the escape square
lemma focused_cells_getElem_zero_of_long_journey
  (D : Devil) (N : Nat) {p : Nat} (A : Journey p) : (2*N + 1)^2 ≤ steps A →
  (focused_cells D N A)[0]'(focused_cells_length_pos D N A) = ((steps A : Int), 0) := by
  intro hlong
  have snz : steps A ≠ 0 := by
    rw [pow_two, mul_add, mul_one, ← add_assoc] at hlong
    exact Nat.ne_zero_of_lt (Nat.add_one_lt_add_one_iff.mp (Nat.lt_add_one_of_le hlong))
  have : focused_cells D N A = focused_cells D N A := rfl
  nth_rw 2 [focused_cells] at this
  rw [dif_neg snz, if_pos hlong] at this
  rw [getElem_congr_coll this, List.getElem_cons_zero]

-- Get the first element of the focused cells list when the journey
-- is of "normal" length and the original devil gives a focused response.
-- In this case, a journey of normal length is one with at least one
-- step, but fewer than (2N+1)² steps
lemma focused_cells_getElem_zero_of_normal_journey_of_focused_response
  (D : Devil) (N : Nat) {p : Nat} (A : Journey p) :
  (snz : steps A ≠ 0) → steps A < (2*N + 1) ^ 2 →
  cell_is_focused D N A snz (response D A) →
  (focused_cells D N A)[0]'(focused_cells_length_pos D N A) = (response D A) := by
  intro snz slt hfocused
  have : focused_cells D N A = focused_cells D N A := rfl
  nth_rw 2 [focused_cells] at this
  unfold pick_focused_cell at this
  rw [dif_neg snz, if_neg (Nat.not_le.mpr slt), if_pos hfocused] at this
  rw [getElem_congr_coll this, List.getElem_cons_zero]

-- Get the first element of the focused cells list when the journey
-- is of "normal" length and the original devil gives an unfocused response.
-- In this case, a journey of normal length is one with at least one
-- step, but fewer than (2N+1)² steps
lemma focused_cells_getElem_zero_of_normal_journey_of_unfocused_response
  (D : Devil) (N : Nat) {p : Nat} (A : Journey p) :
  (snz : steps A ≠ 0) → steps A < (2*N + 1) ^ 2 →
  ¬cell_is_focused D N A snz (response D A) →
  (focused_cells D N A)[0]'(focused_cells_length_pos D N A) =
  find_cell_in_square N (cell_is_focused D N A snz) := by
  intro snz slt hunfocused
  have : focused_cells D N A = focused_cells D N A := rfl
  nth_rw 2 [focused_cells] at this
  unfold pick_focused_cell at this
  rw [dif_neg snz, if_neg (Nat.not_le.mpr slt), if_neg hunfocused] at this
  rw [getElem_congr_coll this, List.getElem_cons_zero]

-- TODO: This should be done with theorems on sets (probably Finset)
-- but I haven't figure out how that works yet, so we're just
-- proving it manually.
lemma focused_cell_exists_helper {n : Nat} (f : Fin (n + 1) → (Int × Int)) (L : List (Int × Int))
  (hlt : L.length < n + 1) (finj : Function.Injective f) : ∃ i, f i ∉ L := by
  -- If L.length = 0, nothing is in L, so in particular f i ∉ L
  by_cases hz : L.length = 0
  · rw [List.length_eq_zero_iff] at hz
    rw [hz]
    exact ⟨0, List.not_mem_nil⟩
  rename' hz => hnz; push_neg at hnz
  by_cases h : f 0 ∈ L
  · -- If f 0 ∈ L, remove that element from L and recurse.
    -- Note that this works even if L contains more than one of that element.
    have nnz : n ≠ 0 := by
      contrapose! hnz
      subst hnz
      apply Nat.lt_one_iff.mp
      exact lt_of_lt_of_eq hlt (Nat.zero_add _)
    rcases Nat.exists_eq_add_one_of_ne_zero nnz with ⟨npred, hp⟩
    have ltnpred : (L.erase (f 0)).length < npred + 1 := by
      apply Nat.add_lt_add_iff_right.mp
      rwa [List.length_erase_of_mem h, ← hp, Nat.sub_one_add_one hnz]
    -- Define a function, 'g', which represents a narrowing of f
    let g := fun i : Fin (npred + 1) ↦ f (Fin.cast hp.symm i).succ
    -- Prove 'g' is injective because 'f' is injective
    have ginj : Function.Injective g := by
      intro i j hij
      unfold g at hij
      apply finj at hij
      apply (Fin.val_eq_val _ _).mpr at hij; simp at hij
      exact (Fin.val_eq_val _ _).mp hij
    -- Recurse to get f i ∉ L.erase (f 0)
    have := focused_cell_exists_helper g (L.erase (f 0)) ltnpred ginj
    rcases this with ⟨i, iprop⟩
    let i' := (Fin.cast hp.symm i).succ
    use i'
    -- Show that f i' ∉ L
    contrapose! iprop
    apply (List.mem_erase_of_ne _).mpr iprop
    have i'ne0 : i' ≠ 0 := Fin.succ_ne_zero _
    contrapose! i'ne0
    exact finj i'ne0
  · -- If f 0 ∉ L, the proof is trivial
    exact ⟨0, h⟩

-- If the journey is "normal" (that is, 0 < steps A < (2N+1)²)
-- then the head of the focused cells list is "focused"
lemma focused_cells_getElem_zero_is_focused_of_normal_journey
  (D : Devil) (N : Nat) {p : Nat} (A : Journey p) :
  (snz : steps A ≠ 0) → steps A < (2*N + 1) ^ 2 →
  cell_is_focused D N A snz ((focused_cells D N A)[0]'(focused_cells_length_pos D N A)) := by
  intro snz slt
  by_cases h : cell_is_focused D N A snz (response D A)
  · rwa [focused_cells_getElem_zero_of_normal_journey_of_focused_response D N A snz slt h]
  · rw [focused_cells_getElem_zero_of_normal_journey_of_unfocused_response D N A snz slt h]
    apply cell_in_square_is_sat N (cell_is_focused D N A snz) _
    -- Here we'll use 'focused_cell_exists_helper' to complete the goal
    -- Wrap 'square_iter' in a function which takes an argument of the form 'Fin (n+1)'
    let f : Fin _ → (Int × Int) := fun i ↦ square_iter N (Fin.cast (find_cell_fin_cast_eq N).symm i)
    -- Prove f is injective (we've already proven 'square_iter' is injective)
    have finj : Function.Injective f := by
      intro i j hij
      unfold f at hij
      apply (Fin.val_eq_val _ _).mp
      have cicj := (Fin.val_eq_val _ _).mpr (square_iter_inj N (SetCoe.ext hij))
      simpa
    have hlt : (focused_cells D N (subjourney_drop_last A snz)).length < (2 * N + 1) * (2 * N) + 2 * N + 1:= by
      rw [focused_cells_length, subjourney_drop_last_steps]
      rwa [Nat.sub_one_add_one snz, ← find_cell_fin_cast_eq N]
    rcases focused_cell_exists_helper f (focused_cells D N (subjourney_drop_last A snz)) hlt finj with ⟨i, iprop⟩
    use (f i)
    -- We've already proven that 'square_iter' only iterates over "close" cells
    have hclose : close N (0, 0) (f i) := square_iter_close N _
    exact ⟨⟨hclose, iprop⟩, hclose⟩

-- For any journey of at least one step, the tail of the focused cells list
-- is just the focused cells list for the subjourney which excludes the
-- final step.
lemma focused_cells_tail
  (D : Devil) (N : Nat) {p : Nat} (A : Journey p) (snz : steps A ≠ 0) :
  (focused_cells D N A).tail = (focused_cells D N (subjourney_drop_last A snz)) := by
  rw [focused_cells, dif_neg snz, List.tail_cons]

-- Recurrence for getting an element of 'focused_cells'
-- TODO: We're not using this yet. Make sure if we keep it that we are.
lemma focused_cells_getElem_recurrence
  (D : Devil) (N : Nat) {p : Nat} (A : Journey p) :
  ∀ i, (inz : i ≠ 0) → (ilt : i < steps A + 1) →
  (focused_cells D N A)[i]'(by rwa [focused_cells_length]) =
  (focused_cells D N (subjourney_drop_last A (
    Nat.ne_zero_of_lt (lt_of_lt_of_le (Nat.pos_of_ne_zero inz) (Nat.le_of_lt_add_one ilt))
  )))[i-1]'(by
    have snz : steps A ≠ 0 :=
      Nat.ne_zero_of_lt (lt_of_lt_of_le (Nat.pos_of_ne_zero inz) (Nat.le_of_lt_add_one ilt))
    rw [focused_cells_length, subjourney_drop_last_steps, Nat.sub_one_add_one snz]
    apply Nat.add_one_lt_add_one_iff.mp
    rwa [Nat.sub_one_add_one inz]
  ) := by
  intro i inz ilt
  have iplt : i - 1 < (focused_cells D N A).tail.length := by
    rw [List.length_tail, focused_cells_length]
    apply (Nat.sub_lt_sub_iff_right _).mpr ilt
    apply Nat.add_one_le_of_lt (Nat.pos_of_ne_zero inz)
  have := (Eq.trans (List.getElem_tail iplt) (getElem_congr_idx (Nat.sub_one_add_one inz))).symm
  rw [this]
  congr
  have snz : steps A ≠ 0 :=
    Nat.ne_zero_of_lt (lt_of_lt_of_le (Nat.pos_of_ne_zero inz) (Nat.le_of_lt_add_one ilt))
  exact focused_cells_tail D N A snz

-- The 'focused_cells' list of a subjourney is a suffix of the
-- focused_cells list for the full journey
lemma focused_cells_subjourney (D : Devil) (N : Nat) {p : Nat} (A : Journey p)
  (n : Nat) (nlt : n < steps A + 1) :
  focused_cells D N (subjourney A n nlt) = (focused_cells D N A).drop ((focused_cells D N A).length - n - 1) := by
  -- If n ≠ steps A, we can rewrite everything in terms of the
  -- 'drop_last' subjourney and recurse:
  by_cases nnesA : n ≠ steps A
  · -- Start with some useful bounds / conditions on 'n' and 'steps A'
    have snz : steps A ≠ 0 := by
      contrapose! nnesA
      rw [nnesA, zero_add] at nlt
      rw [Nat.lt_one_iff.mp nlt, nnesA.symm]
    have splt : steps A - 1 < steps A + 1 := by
      exact lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_add_one _)
    have nlt' : n < steps A := by
      exact Nat.lt_of_le_of_ne (Nat.le_of_lt_add_one nlt) nnesA
    have nlt'' : n < steps (subjourney A (steps A - 1) splt) + 1 := by
      rwa [subjourney_steps, Nat.sub_one_add_one snz]
    -- Rewrite the left-hand side relative to the 'drop_last' subjourney
    have lhs : subjourney A n nlt = subjourney (subjourney_drop_last A snz) n nlt'' := by
      rwa [subjourney_drop_last_subjourney]
    -- Recurse and simplify
    rw [lhs, focused_cells_subjourney, focused_cells_length, ← focused_cells_tail]
    rw [subjourney_drop_last_steps, List.drop_tail]
    congr
    -- Now show the number of dropped cells matches
    rw [focused_cells_length, Nat.sub_one_add_one snz, ← Nat.sub_add_eq]
    rw [← Nat.sub_add_comm (Nat.add_one_le_of_lt nlt'), Nat.sub_add_eq]
  · rename' nnesA => nsA; push_neg at nsA
    subst nsA
    -- For n = steps A, the result is trivial
    rw [subjourney_full, focused_cells_length]
    rw [Nat.add_sub_cancel_left, Nat.sub_self, List.drop_zero]
termination_by (steps A)
decreasing_by
  rw [subjourney_drop_last_steps]
  exact Nat.sub_one_lt snz

-- Rewrite an element of 'focused_cells' as the head of the
-- focused cells list for some subjourney
lemma focused_cells_getElem (D : Devil) (N : Nat) {p : Nat} (A : Journey p)
  (n : Nat) (nlt : n < steps A + 1) :
  (focused_cells D N A)[n]'(by rwa [focused_cells_length]) =
  (focused_cells D N (subjourney A (steps A - n)
    (lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_add_one _))))[0]'(focused_cells_length_pos _ _ _) := by
  have sAsnlt : steps A - n < steps A + 1 :=
    (lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_add_one _))
  rw [getElem_congr_coll (focused_cells_subjourney D N A (steps A - n) sAsnlt), List.getElem_drop]
  congr
  -- Now show the indices match
  rw [focused_cells_length, add_zero, Nat.sub_sub_right _ (Nat.le_of_lt_add_one nlt)]
  rw [add_comm _ n, add_comm (steps A), ← add_assoc, Nat.add_sub_cancel, Nat.add_sub_cancel]

lemma focused_cells_close_iff (D : Devil) (N : Nat) {p : Nat} (A : Journey p)
  (i : Nat) (ilt : i < steps A + 1) :
  close N (0, 0) ((focused_cells D N A)[i]'(by rwa [focused_cells_length])) ↔ steps A - i < (2*N + 1) ^ 2 := by
  constructor
  · intro lei
    contrapose! lei
    have sAsipos : 0 < steps A - i := by
      rw [pow_two, mul_add, mul_one, ← add_assoc] at lei
      exact Nat.pos_of_ne_zero (Nat.ne_zero_of_lt (Nat.lt_of_add_one_le lei))
    have snz : steps A ≠ 0 := by
      contrapose! sAsipos
      rw [sAsipos]
      exact Nat.sub_le _ _
    rw [focused_cells_getElem D N A, focused_cells_getElem_zero_of_long_journey]
    · -- Prove the goal holds for "long" journies
      rw [subjourney_steps]
      unfold close dist; dsimp
      rw [zero_sub, Int.natAbs_neg, Int.natAbs_natCast, Nat.max_zero]; push_neg
      apply lt_of_lt_of_le _ lei
      rw [pow_two, mul_add, mul_one, ← add_assoc]
      apply Nat.lt_add_one_of_le
      rw [add_comm, two_mul, add_assoc]
      exact Nat.le_add_right _ _
    · rwa [subjourney_steps]
    · assumption
  · intro h
    have sAsilt : steps A - i < steps A + 1 :=
      lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_add_one _)
    -- Rewrite the goal in terms of the subjourney of length 'steps A - i'
    rw [focused_cells_getElem D N A i ilt]
    let sjA := subjourney A (steps A - i) sAsilt
    change close N (0, 0) ((focused_cells D N sjA)[0]'(_))
    -- Handle the case where steps sjA = 0
    by_cases sz : steps sjA = 0
    · -- Handle the two sub-cases where the devil's initial response
      -- is either close or far
      by_cases hclose : close N (0, 0) (response D sjA)
      · rwa [focused_cells_getElem_zero_of_steps_zero_of_close_response D N sjA hclose sz]
      · rw [focused_cells_getElem_zero_of_steps_zero_of_far_response D N sjA hclose sz]
        unfold close dist; simp
    rename' sz => snz; push_neg at snz
    have ssjA : steps sjA = steps A - i := by
      unfold sjA; rw [subjourney_steps]
    have ssjAlt : steps sjA < (2 * N + 1) ^ 2 := by
      rwa [ssjA]
    -- We have two different cases depending on whether the
    -- devil's response is "focused"
    by_cases hfocused : cell_is_focused D N sjA snz (response D sjA)
    · rw [focused_cells_getElem_zero_of_normal_journey_of_focused_response D N sjA snz ssjAlt hfocused]
      exact close_of_focused D N sjA snz hfocused
    rw [focused_cells_getElem_zero_of_normal_journey_of_unfocused_response D N sjA snz ssjAlt hfocused]
    exact cell_in_square_is_close N _

-- The focused cells list contains no duplicate cells
lemma focused_cells_nodupes (D : Devil) (N : Nat) {p : Nat} (A : Journey p)
  (i j : Nat) (ilt : i < steps A + 1) (jlt : j < steps A + 1) : i ≠ j →
  (focused_cells D N A)[i]'(by rwa [focused_cells_length]) ≠
  (focused_cells D N A)[j]'(by rwa [focused_cells_length]) := by
  -- Without loss of generality, i < j
  wlog hlt : i < j generalizing i j
  · intro inej; push_neg at hlt
    exact (this j i jlt ilt (lt_of_le_of_ne hlt inej.symm) inej.symm).symm
  intro h
  contrapose! h
  -- Split into three cases depending on whether the cells corresponding
  -- to 'i' and 'j' appear inside the escape square, or outside.
  by_cases lesAsi : (2 * N + 1) ^ 2 ≤ steps A - i
  · by_cases sAsjlt : steps A - j < (2 * N + 1) ^ 2
    · -- Handle the case where 'j' is "inside" and 'i' is "outside"
      -- If they correspond to the same cell this leads to a contradiction
      have hclose := (focused_cells_close_iff D N A j jlt).mpr sAsjlt
      rw [← h] at hclose
      linarith [(focused_cells_close_iff D N A i ilt).mp hclose]
    · rename' sAsjlt => lesAsj; push_neg at lesAsj
      -- Next handle the case where both 'i' and 'j' are "outside"
      rw [focused_cells_getElem, focused_cells_getElem _ _ A] at h
      repeat rw [focused_cells_getElem_zero_of_long_journey, subjourney_steps] at h
      simp at h
      apply @Nat.add_left_cancel ((steps A - i) + (steps A - j))
      rw [Nat.add_right_comm, Nat.sub_add_cancel (Nat.le_of_lt_add_one ilt)]
      rw [add_assoc, Nat.sub_add_cancel (Nat.le_of_lt_add_one jlt), add_comm]
      apply Nat.add_right_cancel_iff.mpr; symm
      assumption
      -- Now prove the pending bounds checks
      · rwa [subjourney_steps]
      · rwa [subjourney_steps]
      · assumption
      · assumption
  -- Now the main case, where 'i' and 'j' are both inside the escape square
  rename' lesAsi => sAsilt; push_neg at sAsilt
  -- From here, all cases eventually lead to a contradiction
  exfalso
  have hlt' : steps A - j < steps A - i := by
    apply Nat.add_lt_add_iff_right.mp
    rw [← add_assoc, Nat.sub_add_cancel (Nat.le_of_lt_add_one jlt)]
    rw [add_comm j, ← add_assoc (steps A - i)]
    rw [Nat.sub_add_cancel (Nat.le_of_lt_add_one ilt)]
    exact Nat.add_lt_add_iff_left.mpr hlt
  have sAsjlt : steps A - j < (2 * N + 1) ^ 2 :=
    lt_trans hlt' sAsilt
  rw [focused_cells_getElem _ _ _ _ ilt, focused_cells_getElem _ _ _ _ jlt] at h
  -- Let's introduce some helpful abbreviations
  let sjAi := subjourney A (steps A - i) (lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_add_one _))
  let sjAj := subjourney A (steps A - j) (lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_add_one _))
  change (focused_cells D N sjAi)[0]'(_) = (focused_cells D N sjAj)[0]'(_) at h
  -- The 'i' subjourney has non-zero steps
  -- However, this *isn't* true for the 'j' subjourney
  have snzi : steps sjAi ≠ 0 := by
    rw [subjourney_steps]
    apply Nat.sub_ne_zero_of_lt
    exact lt_of_lt_of_le hlt (Nat.le_of_lt_add_one jlt)
  have ssjAilt : steps sjAi < (2 * N + 1) ^ 2 := by rwa [subjourney_steps]
  -- We've already proven that for a "normal" journey, the head of the
  -- focused cells list is focused. Use that here.
  have hfocused := focused_cells_getElem_zero_is_focused_of_normal_journey D N sjAi snzi ssjAilt
  apply uneaten_of_focused D N sjAi snzi hfocused
  apply List.mem_iff_getElem.mpr
  -- We'll need this a few places below, so prove it now:
  have : steps A - i - 1 - (j - i - 1) = steps A - j := by
    rw [← Nat.sub_add_eq _ i 1, ← Nat.sub_add_eq _ i 1, Nat.sub_right_comm, Nat.sub_sub]
    rw [Nat.sub_add_cancel (Nat.add_one_le_of_lt hlt)]
  have ilt' : i < steps A := lt_of_lt_of_le hlt (Nat.le_of_lt_add_one jlt)
  -- We know exactly where the conflicting cell is located in the list, so use that
  use j - i - 1
  use (by
    rw [focused_cells_length, subjourney_drop_last_steps, subjourney_steps]
    rw [← Nat.sub_add_eq, ← Nat.sub_add_eq]
    apply Nat.add_lt_add_iff_right.mp
    rw [Nat.sub_add_cancel (Nat.add_one_le_of_lt hlt), Nat.add_right_comm]
    rwa [Nat.sub_add_cancel (Nat.add_one_le_of_lt ilt')]
  )
  rw [focused_cells_getElem, h]
  apply getElem_congr_coll
  apply congrArg
  rw [subjourney_drop_last_subjourney, subjourney_subjourney]
  apply subjourney_congr_idx
  rwa [subjourney_drop_last_steps, subjourney_steps]
  -- Prove pending bounds checks
  · rw [subjourney_drop_last_steps, subjourney_steps, this]
    exact lt_trans hlt' (Nat.lt_add_one _)
  · rwa [subjourney_drop_last_steps, subjourney_steps, this]
  · rw [subjourney_drop_last_steps, subjourney_steps]
    rw [Nat.sub_one_add_one (Nat.ne_zero_of_lt hlt'), Nat.sub_right_comm]
    apply (@Nat.add_lt_add_iff_right (i + 1) _ _).mp
    have jpos := lt_of_le_of_lt (Nat.zero_le _) hlt
    rw [← add_assoc, Nat.sub_add_cancel ((Nat.le_sub_one_iff_lt jpos).mpr hlt), ← add_assoc (steps A - i)]
    rw [Nat.sub_add_cancel (Nat.le_of_lt_add_one ilt)]
    rwa [Nat.sub_add_cancel (Nat.add_one_le_of_lt jpos)]

/- Given a devil, make a new devil that behaves in the same way, unless
   the original devil would make an "unfocused" response. In that case,
   choose any focused response instead. That is, respond with any cell
   within distance 'N' of the origin that has not already been eaten. -/
def make_focused (D : Devil) (N : Nat) : Devil :=
  fun Ap ↦ (focused_cells D N Ap.A)[0]'(by
    rw [focused_cells_length]
    exact Nat.succ_pos _
  )

-- The devil created by 'make_focused' is in-fact focused.
lemma make_focused_is_focused (D : Devil) (N : Nat) : focused (make_focused D N) N := by
  unfold focused make_focused
  intro p A
  constructor
  · -- For part #1 of this proof, we'll use 'focused_cells_nodupes' to show that
    -- the 'make_focused' devil never gives a duplicate response. Most of the proof
    -- demonstrating the necessary bounds checks.
    intro i j ilt jlt inej
    rw [response, response]; dsimp
    by_contra! h
    have sAsilt : steps A - i < steps A + 1 :=
      lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_add_one _)
    have sAsjlt : steps A - j < steps A + 1 :=
      lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_add_one _)
    have sAsinesAsj : steps A - i ≠ steps A - j := by
      contrapose! inej
      apply Nat.add_right_inj.mp
      rw [Nat.sub_add_cancel (Nat.le_of_lt_add_one ilt), inej]
      rw [Nat.sub_add_cancel (Nat.le_of_lt_add_one jlt)]
    -- Here we actually apply the 'nodupes' theorem.
    apply focused_cells_nodupes D N A (steps A - i) (steps A - j) sAsilt sAsjlt sAsinesAsj
    rw [focused_cells_getElem D N A _ sAsilt, focused_cells_getElem D N A _ sAsjlt]
    -- Now the goal looks like 'h', but with the indices written differently.
    -- Use 'convert' to make new goals from those differences.
    convert h
    · rw [Nat.sub_sub_right, add_comm, Nat.add_sub_assoc, Nat.sub_self, add_zero]
      -- Pending bounds checks
      · exact le_refl _
      · exact Nat.le_of_lt_add_one ilt
    · rw [Nat.sub_sub_right, add_comm, Nat.add_sub_assoc, Nat.sub_self, add_zero]
      -- Pending bounds checks
      · exact le_refl _
      · exact Nat.le_of_lt_add_one jlt
  · -- For part #2 of this proof we need to show that the 'make_focused' devil only
    -- responds with cells close to the origin for the first (2N+1)² responses
    intro n ⟨nlt', nlt⟩
    unfold response; dsimp
    let sjA := subjourney A n nlt
    -- First we need to take care of some special cases (and sub-cases)
    -- starting with n = 0
    by_cases nz : n = 0
    · subst nz
      have sz : steps sjA = 0 := by rw [subjourney_steps]
      by_cases hclose : close N (0, 0) (response D sjA)
      · rwa [focused_cells_getElem_zero_of_steps_zero_of_close_response D N sjA hclose sz]
      · rw [focused_cells_getElem_zero_of_steps_zero_of_far_response D N sjA hclose sz]
        unfold close dist; simp
    rename' nz => nnz; push_neg at nnz
    have snz : steps sjA ≠ 0 := by
      rwa [subjourney_steps]
    apply close_of_focused D N sjA snz
    apply focused_cells_getElem_zero_is_focused_of_normal_journey D N sjA snz
    rwa [subjourney_steps]

--#check Equiv.symm
--#check Finite.injective_iff_surjective_of_equiv (square_equiv.symm)



/- For any focused devil and angel journey over a certain length, every cell
   within a distance of 'N' from the origin will have been eaten -/
lemma focused_eats_all_close (D : Devil) (p : Nat) (N : Nat) :
  focused D N → ∀ (A : Journey p), (less : (2*N+1)^2 ≤ steps A + 1) →
  ∀ u, close N (0, 0) u → ∃ i, ¬((ilt : i < (2*N+1)^2) →
  ¬response D (subjourney A i (lt_of_lt_of_le ilt less)) = u) := by
  intro hfocused A lts u hclose
  -- Define a function that corresponds to the devil's responses
  -- for the first (2N+1)²-1 steps.
  let f : Fin ((2 * N + 1) ^ 2) → B N :=
    fun i ↦ ⟨response D (subjourney A i.val (lt_of_lt_of_le i.2 lts)),
      (hfocused p A).right i.1 ⟨i.2, lt_of_lt_of_le i.2 lts⟩
    ⟩
  -- Prove 'f' is injective
  have hinj : Function.Injective f := by
    intro a b hab
    contrapose! hab
    have := (hfocused p A).left a.1 b.1 (lt_of_lt_of_le a.2 lts) (lt_of_lt_of_le b.2 lts) (Fin.val_ne_iff.mpr hab)
    unfold f
    intro h
    replace h := SetCoe.ext_iff.mpr h; dsimp at h
    exact this h
  -- Since we've already shown an equivalence between Fin (2N+1)² and B(N)
  -- we can conclude that 'f' must also be surjective.
  have hsurj := (Finite.injective_iff_surjective_of_equiv (square_equiv N).symm).mp hinj
  unfold Function.Surjective at hsurj
  -- Use the surjectivity of 'f' to complete the proof
  rcases hsurj ⟨u, hclose⟩ with ⟨i, iprop⟩
  use i; push_neg
  use i.2
  exact SetCoe.ext_iff.mpr iprop

/- If a devil 'D' would eat a particular cell after step 'i' in response
   to a particular angel, and if that cell is "close" to the origin, then
   the "focused" version of D would eat that same cell on or before that
   same step in response to that same angel.
-/
lemma focused_is_dominant (D : Devil) (N : Nat) :
  ∀ (p : Nat) (A : Journey p) j (jlt : j < steps A + 1),
  close N (0, 0) (response D (subjourney A j jlt)) → ∃ i, ¬((ile : i ≤ j) →
  response (make_focused D N) (subjourney A i (lt_of_le_of_lt ile jlt)) ≠ response D (subjourney A j jlt)) := by
  intro p A j jlt hclose
  let sjA := subjourney A j jlt
  -- If the focused devil responds the same way as the
  -- original then the goal is trivial
  by_cases hresponse : response (make_focused D N) sjA = response D sjA
  · use j; push_neg
    use le_refl _
  contrapose! hresponse
  rw [response, make_focused]; dsimp
  -- Now we just need to deal with each of the subcases in the 'focused_cells' definition:
  by_cases jz : j = 0
  · have sz : steps sjA = 0 := by rwa [subjourney_steps]
    exact focused_cells_getElem_zero_of_steps_zero_of_close_response D N sjA hclose sz
  rename' jz => jnz; push_neg at jnz
  have snz : steps sjA ≠ 0 := by rwa [subjourney_steps]
  by_cases lej : (2 * N + 1) ^ 2 ≤ j
  · -- If 'j' is "large", the 'make_focused' devil will choose a cell outside
    -- the escape square, but will have eaten every cell in the escape square
    -- at some point in the past.
    have less : (2 * N + 1) ^ 2 ≤ steps sjA + 1 := by
      rw [subjourney_steps]
      exact le_of_lt (lt_of_le_of_lt lej (Nat.lt_add_one _))
    have := focused_eats_all_close (make_focused D N) p N (make_focused_is_focused D N) sjA less _ hclose
    push_neg at this
    rcases this with ⟨i, ilt, iprop⟩
    rw [subjourney_subjourney A (lt_trans ilt (Nat.lt_add_one_of_le lej))] at iprop
    exact False.elim ((hresponse i (Nat.le_of_lt (Nat.lt_of_lt_of_le ilt lej))) iprop)
  rename' lej => jlt'; push_neg at jlt'
  by_cases hfocused : cell_is_focused D N sjA snz (response D sjA)
  · -- If the response from the original devil is "focused" then it will
    -- match the response of the 'make_focused' devil and the goal is trivial
    apply focused_cells_getElem_zero_of_normal_journey_of_focused_response D N sjA snz
    · rwa [subjourney_steps]
    · assumption
  exfalso
  unfold cell_is_focused close_and_uneaten at hfocused
  push_neg at hfocused
  -- Let 'i' be the previous step on which (response D sjA) was eaten
  rcases List.getElem_of_mem (hfocused hclose) with ⟨i, ilt, iprop⟩
  rw [focused_cells_length, subjourney_drop_last_steps, Nat.sub_one_add_one snz, subjourney_steps] at ilt
  apply hresponse (j - (i + 1)) (Nat.sub_le _ _)
  have ilt' : i < steps (subjourney_drop_last sjA snz) + 1 := by
    rwa [subjourney_drop_last_steps, subjourney_steps, Nat.sub_one_add_one jnz]
  rw [← iprop, focused_cells_getElem D N _ i ilt']
  unfold make_focused response; dsimp
  apply getElem_congr_coll
  apply congrArg
  rw [subjourney_drop_last_subjourney, subjourney_subjourney]
  apply subjourney_congr_idx
  rw [subjourney_drop_last_steps, subjourney_steps, add_comm, Nat.sub_add_eq]
  -- Prove pending bounds checks
  · rw [subjourney_drop_last_steps, subjourney_steps, ← Nat.sub_add_eq]
    exact lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_add_one _)
  · rw [subjourney_drop_last_steps, subjourney_steps, ← Nat.sub_add_eq]
    apply Nat.sub_lt_of_pos_le
    · linarith
    · rw [add_comm]
      exact Nat.add_one_le_of_lt ilt
