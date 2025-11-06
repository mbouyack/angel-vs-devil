import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import AngelDevil.Reduced
import AngelDevil.Focused
import AngelDevil.Runner
import AngelDevil.Dupes
import AngelDevil.Perimeter
import AngelDevil.Blocked

set_option linter.style.longLine false

/-
  This file contains the most significant results from Máthé's paper,
  including the final result: that the Angel of power 2 wins.
-/

/- Indicates that devil 'D' traps any angel of power 'p' within a square of
   size (2N+1) centered on the origin. I will occasionally refer to this as
   the "escape square", since in order to win an angel will need to succeed
   in escaping that square -/
def traps_in_square (D : Devil) (p N : Nat) : Prop :=
  ∀ (A : Journey p), N < dist (0, 0) (last A) → ¬allowed D A

/- An alternative definition of the devil's victory criterion based on the
   idea of trapping an angel of power 'p' in a square centered on the origin.
   We will prove that our two definitions are equivalent. -/
def devil_wins' (D : Devil) (p : Nat) : Prop := ∃ N, traps_in_square D p N

abbrev outside_fun {p : Nat} (A : Journey p) (N : Nat) : Fin (steps A + 1) → Prop :=
  fun i ↦ N < dist (0, 0) (cell A i.1 i.2)

/- If a devil wins by the alternate definition, then any angel of power 'p'
   that ends its journey outside the "escape square" must be caught somewhere
   inside the "extended perimeter": the square of size 2(N+p) + 1 centered
   at the origin. -/
-- TODO: Consider switching back to 'Fin' for antecedents in some cases to avoid
-- having to express conjuntions as implications
lemma extended_perimeter (D : Devil) (p : Nat) (N : Nat) (htraps : traps_in_square D p N) (A : Journey p) :
  N < dist (0, 0) (last A) →
  ∃ i j, ¬((ilt : i < j) → (jlt : j < steps A + 1) →
  (dist (0, 0) (cell A j jlt) ≤ N + p → response D (subjourney A i (lt_trans ilt jlt)) ≠ cell A j jlt)) := by
  intro Nlt
  unfold traps_in_square allowed at htraps
  -- Prove that steps A ≠ 0
  have snz : steps A ≠ 0 := by
    intro h
    rw [last, cell_congr_idx A h (Nat.lt_add_one _), journey_start, dist_self] at Nlt
    exact not_lt_zero' Nlt
  -- Get the index of the first cell outside the escape square (call it 'k')
  let k := (find_first (outside_fun A N) (Nat.add_one_ne_zero _))
  -- The kth cell is in-fact outside the escape square
  have ksat : N < dist (0, 0) (last (subjourney A k.val k.2)) := by
    rw [subjourney_last_cell]
    exact find_first_is_sat (outside_fun A N) ⟨⟨steps A, Nat.lt_add_one _⟩, Nlt⟩
  -- The kth cell is the *first* step outside the escape square
  have kfirst : ∀ i (ilt : i < steps A + 1),
    N < dist (0, 0) (cell A i ilt) → k.val ≤ i := by
    intro i ilt houtside
    exact Fin.le_iff_val_le_val.mp (find_first_is_first (outside_fun A N) ⟨i, ilt⟩ houtside)
  -- Handle the case where the first step outside the escape square
  -- is not the last step of the journey.
  by_cases knl : k.val ≠ steps A
  · -- We can solve the goal by recursion because k < steps A
    rcases extended_perimeter D p N htraps (subjourney A k.1 k.2) ksat with ⟨i, j, h⟩
    push_neg at h
    rcases h with ⟨ilt, jlt, hinside, hcaught⟩
    rw [subjourney_steps] at jlt
    rw [subjourney_cell] at hinside; swap
    · exact Nat.le_of_lt_add_one jlt
    rw [subjourney_subjourney _ (lt_trans ilt jlt), subjourney_cell] at hcaught; swap
    · exact Nat.le_of_lt_add_one jlt
    use i, j; push_neg
    use ilt, lt_trans jlt
      (Nat.add_one_lt_add_one_iff.mpr (Nat.lt_of_le_of_ne (Nat.le_of_lt_add_one k.2) knl))
  rename' knl => hkl; push_neg at hkl
  -- Use 'htraps' to reduce the goal to proving that step 'j'
  -- is inside the extended perimeter.
  have h := htraps A Nlt
  push_neg at h
  rcases h with ⟨i, j, ilt, jlt, hcaught⟩
  use i, j; push_neg
  use ilt, jlt
  apply And.intro _ hcaught
  -- Handle the case where step 'j' is inside the escape square
  -- In that case it is trivial to show step 'j' is also inside
  -- the extended perimeter.
  by_cases hinside : dist (0, 0) (cell A j jlt) ≤ N
  · exact le_trans hinside (Nat.le_add_right N p)
  rename' hinside => houtside; push_neg at houtside
  -- If j ≠ steps A, we reach a contradiction, since 'k' should be the first
  -- step outside the square
  by_cases jnl : j ≠ steps A
  · have jlt' : j < k :=
      Nat.lt_of_lt_of_eq (Nat.lt_of_le_of_ne (Nat.le_of_lt_add_one jlt) jnl) hkl.symm
    exact False.elim ((not_lt_of_ge (kfirst j jlt houtside)) jlt')
  rename' jnl => hjl; push_neg at hjl
  rw [cell_congr_idx A hjl jlt]
  -- Show that the second-to-last step of the journey is still inside the
  -- escape square
  have spltss := Nat.lt_of_le_of_lt (Nat.sub_le (steps A) 1) (Nat.lt_add_one _)
  have hinside : dist (0, 0) (cell A (steps A - 1) spltss) ≤ N := by
    by_contra! h
    apply Nat.lt_irrefl (steps A)
    have := Nat.lt_add_one_of_le (kfirst (steps A - 1) spltss h)
    rwa [hkl, Nat.sub_one_add_one snz] at this
  -- Use 'journey_steps_close' and 'dist_tri' to show that the first step outside
  -- the escape square is still inside the extended perimeter
  calc
    dist (0, 0) (last A) ≤ dist (0, 0) (cell A (steps A - 1) spltss) +
                                 dist (cell A (steps A - 1) spltss) (last A) := dist_tri _ _ _
    _ ≤ N + dist (cell A (steps A - 1) spltss) (last A) := Nat.add_le_add_right hinside _
    _ ≤ N + p := by
      apply Nat.add_le_add_left
      convert journey_steps_close A (steps A - 1) (Nat.sub_one_lt snz)
      rw [last]; congr
      exact (Nat.sub_one_add_one snz).symm
termination_by (steps A)
decreasing_by
  rw [subjourney_steps]
  exact Nat.lt_of_le_of_ne (Nat.le_of_lt_add_one ((find_first (outside_fun A N) (Nat.add_one_ne_zero _)).2)) knl

-- Prove that our two definitions of devil victory are equivalent
lemma devil_wins_equiv (p : Nat) :
  (∃ D : Devil, devil_wins D p) ↔ (∃ D : Devil, devil_wins' D p) := by
  constructor
  · -- The forward direction is a simple application of the lower bound
    -- on steps, proven in 'journey_lb'.
    rintro ⟨D, N, htraps⟩
    exact ⟨D, p * N, fun A distlb ↦ htraps A (journey_lb A N distlb)⟩
  · -- The reverse direction is more complicating and involves showing
    -- that a "focused" devil can both trap the angel in a region around the
    -- origin and eventually eat every available cell.
    rintro ⟨D, N, htraps⟩
    let N' := (2*(N+p) + 1)^2
    let D' := make_focused D (N+p)
    use D', N'
    intro A N'lt
    unfold allowed; push_neg
    -- Did the angel end its journey within the "escape square", or outside?
    by_cases houtside : N < dist (0, 0) (last A)
    · -- If outside, it must have been caught somewhere within the "extended perimeter"
      rcases extended_perimeter D p N htraps A houtside with ⟨i, j, h⟩; push_neg at h
      rcases h with ⟨ilt, jlt, hinsidex, hcaught⟩
      -- Show that the angel would fare no better against the focused variant of D
      -- (would be caught at the same cell on or before the same turn)
      rcases (hcaught ▸ (focused_is_dominant D (N+p) p A i (lt_trans ilt jlt))) hinsidex with ⟨i', h⟩; push_neg at h
      rcases h with ⟨i'le, hcaught'⟩
      exact ⟨i', j, Nat.lt_of_le_of_lt i'le ilt, jlt, hcaught'⟩
    · rename' houtside => hinside; push_neg at hinside
      -- If the angel doesn't leave the escape square, it will eventually be caught
      -- as every available cell is eaten.
      have hclose := close_of_le_of_close N (N+p) (0, 0) (last A) (Nat.le_add_right N p) hinside
      have hfocused := make_focused_is_focused D (N+p)
      -- The angel will definitely be caught on its last turn
      -- (though it may also be caught before then)
      have N'lt' : N' ≤ steps A + 1 := Nat.le_of_lt (lt_trans N'lt (Nat.lt_add_one _))
      rcases focused_eats_all_close D' p (N+p) hfocused A N'lt' (last A) hclose with ⟨i, h⟩; push_neg at h
      rcases h with ⟨ilt, hcaught⟩
      exact ⟨i, steps A, lt_trans ilt N'lt, Nat.lt_add_one _ , hcaught⟩

/- Theorem 8.1 (Conway)
   "It does no damage to the Angel’s prospects if we require him after each move to
    eat away every square that he could have landed on at that move, but didn’t."

   We formalize this as follows: If the devil doesn't win, then for every devil
   'D' and natural number 'N', there exists an efficient, allowed journey
   longer than N.

   The idea for proving this theorem is to show that if there is a devil
   who can catch any efficient angel, we can construct a devil which can catch
   every angel of that power.
-/
theorem efficient_angel_wins_of_angel_wins (p : Nat) :
  ¬(∃ D : Devil, devil_wins D p) → ∀ D : Devil, ∀ N : Nat, ∃ A : Journey p,
  N < steps A ∧ efficient A ∧ allowed D A := by
  intro h
  contrapose! h
  -- Proof by contradiction:
  -- Suppose there is a devil, D, that beats any "efficient" angel of power 'p'
  rcases h with ⟨D, N, Dprop⟩
  -- Contruct a devil, D', that responds in the same way
  -- to the full journey that D would to the reduced journey
  let D' : Devil := fun Ap ↦ response D (reduced Ap.A)
  have D'prop : ∀ p (A : Journey p), response D' A = response D (reduced A) := fun p A ↦ rfl
  -- Switch to the alternate definition of devil victory and set the
  -- 'escape square' to be large enough that we get the necessary lower
  -- bound on the length of the reduced journey.
  rw [devil_wins_equiv]
  use D', p * N
  unfold allowed at Dprop
  push_neg at *
  intro A distlb
  have steps_lb := journey_lb (reduced A) N ((reduced_last A) ▸ distlb)
  -- Since devil D should catch the angel "reduced A", suppose it happens
  -- at the 'j₀'th step of the journey, on a cell previously eaten on step 'i₀'
  rcases Dprop (reduced A) steps_lb (reduced_efficient A) with ⟨i₀, j₀, i₀lt, j₀lt, hcaught⟩
  -- Map i₀ and j₀ to the original journey (as i₁ and j₁ respectively)
  let i₁ := reduced_map A i₀ (lt_trans i₀lt j₀lt)
  let j₁ := reduced_map A j₀ j₀lt
  unfold allowed; push_neg
  use i₁, j₁, redmap_mono A i₀lt j₀lt, redmap_lt A j₀ j₀lt
  -- Conclude that devil D' would catch angel A on cell j₁
  -- which has previously been eaten on step i₁
  rw [D'prop, ← redmap_redsub_comm A i₀, hcaught]
  exact (redmap_cell A j₀ j₀lt).symm

/-
  Proof notes:
  ψ - Nice Devil
  φ - Devil

  (v[0], ..., v[n]) - journey played against ψ (Nice Devil)
  (u[0], ..., u[k]) - reduced journey, played against φ (Devil)
  The devil catches the angel: φ (u[0], ..., u[s]) = u[t], where 0 ≤ s < t ≤ k
  s' - smallest index such that v[s'] = u[s]
  t' - smallest index such that v[t'] = u[t]
       Note that in both cases this corresponds to the inverse of the "natural"
       mapping from the reduced journey to the original journey. That is
       (u[0], ..., u[s]) is the reduced journey of (v[0], ..., v[s'])

  If after step s' the Nice Devil follows the recommendation of the Devil,
  then on step t' the angel will step on a previously eaten cell. So assume
  the Nice Devil did nothing on step s' because eating v[t'] would not have
  been nice.

  l - step of the nice devil's journey which makes v[t'] not nice
      That is, 0 ≤ l < s' such that d(v[t'], v[l]) ≤ p

  Becuase v[l] is close to v[t'] and l < s', in constructing the reduced journey
  some cell with index less than s' should have been chosen.

  This is a contradiction, so the Nice Devil catches the Angel on the same
  cell as the standard Devil
-/

/- Theorem 2.7 (Máthé)
  "If the Devil can catch the Angel of power p, then there is an N such that the
   Nice Devil can entrap the Angel of power p in the domain B(N)."

   Note that B(N) refers to the "escape square" of size 2N+1 in our formalization.
-/
theorem nice_devil_wins_of_devil_wins (p : Nat) : (∃ D : Devil, devil_wins D p) →
  (∃ (D : Devil), nice D p ∧ devil_wins' D p) := by
  rw [devil_wins_equiv]
  rintro ⟨d₀, N, h⟩
  -- Construct a devil, d₁, which responds in the same was as d₀ would to
  -- the "reduced" journey, but nice.
  let d₁ : Devil := make_nice (fun Ap ↦ response d₀ (reduced Ap.A))
  -- The claim is that the Nice Devil d₁ will trap the angel
  -- We select the box size to force 2 < steps (reduced A)
  use d₁, make_nice_is_nice _ p, (p + 1) + N
  intro A houtside
  rw [← reduced_last] at houtside
  replace h := h (reduced A) (lt_trans (Nat.lt_add_of_pos_left (Nat.add_one_pos _)) houtside)
  unfold allowed at *
  push_neg at *
  rcases h with ⟨i₀, j₀, i₀ltj₀, j₀lt, hcaught⟩
  have i₀lt := lt_trans i₀ltj₀ j₀lt
  let i₁ := reduced_map A i₀ i₀lt
  let j₁ := reduced_map A j₀ j₀lt
  have i₁lt := redmap_lt A i₀ i₀lt
  have j₁lt := redmap_lt A j₀ j₀lt
  use i₁, j₁, redmap_mono A i₀ltj₀ j₀lt, j₁lt
  let sjAi₁ := subjourney A i₁ i₁lt
  by_cases hnc : is_nice_cell sjAi₁ (response d₀ (reduced sjAi₁))
  · -- If the cell eaten by d₀ is "nice", d₁ will copy it and
    -- catch the angel in the same place
    unfold d₁ make_nice response; dsimp
    unfold sjAi₁ response at *
    rw [if_pos hnc, ← redmap_redsub_comm A i₀, hcaught]
    exact (redmap_cell A j₀ j₀lt).symm
  · -- Otherwise we will show one of two contradictions depending the reason
    -- why the chosen cell was not "nice".
    absurd hnc; clear hnc
    rw [is_nice_cell_iff]
    unfold mean_cell mean_fun
    push_neg
    rw [← redmap_redsub_comm A i₀, hcaught]
    constructor
    · -- We show that the angel could not have been caught on the origin.
      -- Use the size of the escape square (given by 'houtside') to prove
      -- 1 < steps (reduced A). Then conclude that 'reduced A' has no duplicate
      -- cells. In particular (0, 0) cannot repeat.
      apply reduced_start_no_repeat A _ j₀ j₀lt (Nat.ne_zero_of_lt i₀ltj₀)
      apply journey_lb (reduced A) 1
      apply lt_trans _ houtside
      rw [mul_one]
      exact lt_of_lt_of_le (Nat.lt_add_one _) (Nat.le_add_right _ _)
    · -- Finally, we show that if the cell chosen by d₀ was not "nice" there must be
      -- some close cell at index 'l' which would have been chosen for the reduced
      -- journey rather instead of A[i₁]. This is a contradiction.
      --
      -- Note that this portion of the proof is written in a somewhat unusal style.
      -- I was having trouble with strange errors with unhelpful descriptions and
      -- I thought it might be related to my "deferred bounds check" approach.
      -- To avoid this, I rewrote everything to prove the bounds checks in advance.
      intro l hlnl
      -- Much of the rest of the proof is just proving various inequalities
      have llei₁ : l.val ≤ i₁ := by
        apply Nat.le_of_lt_add_one
        apply lt_of_lt_of_eq l.2
        rw [subjourney_steps]
      rw [subjourney_cell A i₁ l.val i₁lt llei₁, ← redmap_cell A j₀ j₀lt]
      rcases Nat.exists_eq_add_one_of_ne_zero (Nat.ne_zero_of_lt i₀ltj₀) with ⟨j₀pred, j₀prop⟩
      have j₀plt : j₀pred < steps (reduced A) + 1 :=
        lt_trans (lt_of_lt_of_eq (Nat.lt_add_one _) j₀prop.symm) j₀lt
      have i₁le : i₁ ≤ reduced_map A j₀pred j₀plt := by
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_add_one (lt_of_lt_of_eq i₀ltj₀ j₀prop)) with lhs | rhs
        · exact Nat.le_of_lt (redmap_mono A lhs j₀plt)
        · apply Nat.le_of_eq
          unfold i₁; subst rhs; rfl
      subst j₀prop
      by_contra hclose
      have hlle : l.val ≤ reduced_map A (j₀pred + 1) j₀lt :=
        le_trans (le_of_le_of_eq (Nat.le_of_lt_add_one l.2) (subjourney_steps A i₁ i₁lt))
          (le_trans i₁le (le_of_lt (redmap_mono A (Nat.lt_add_one j₀pred) j₀lt)))
      -- Build the contradiction we will eventually show
      have hcontra : ¬reduced_map A j₀pred (lt_trans (Nat.lt_add_one _) j₀lt) ≤ l.val :=
        Nat.not_le.mpr (lt_of_lt_of_le (lt_of_le_of_ne (Nat.le_of_lt_add_one l.2) hlnl) i₁le)
      let sjAj₁ := subjourney A (reduced_map A (j₀pred + 1) j₀lt) j₁lt
      have hllt : ↑l < steps sjAj₁ + 1 := by
        nth_rw 2 [subjourney_steps]
        exact Nat.lt_add_one_of_le hlle
      -- Here's where the actually logic happens!
      have : close p (cell sjAj₁ (↑l) hllt) (last sjAj₁) := by
        rw [subjourney_last_cell A j₁ j₁lt]
        rw [subjourney_cell A j₁ l.val j₁lt hlle]
        exact (close_comm p _ _).mp hclose
      rw [← redmap_consecutive A j₀pred j₀lt] at hcontra
      exact hcontra (first_close_to_last_is_first sjAj₁ l.val hllt this)

-- If the nice devil wins, then it traps the runner within the escape square.
-- Note that this result applies to the entire 'RunPath', not just the runner's journey.
lemma run_path_trapped_of_nice_devil_wins
  (D : Devil) (p : Nat) (hnice : nice D p) (hdwins : devil_wins' D p) :
  ∃ N, ∀ n, ∀ rs ∈ RunPath D p n, close N (0, 0) (loc rs) := by
  let ⟨N, htraps⟩ := hdwins
  use N
  intro n rs rsmem
  -- First handle the case where n = 0
  by_cases nz : n = 0
  · subst nz
    rw [run_path_of_length_zero D p] at rsmem
    rw [List.mem_singleton.mp rsmem]
    exact close_self N (0, 0)
  rename' nz => nnz; push_neg at nnz
  have npos : 0 < n := Nat.pos_of_ne_zero nnz
  -- Next, find the sprint that produced 'rs'
  rcases List.getElem_of_mem rsmem with ⟨k, klt, hrpk⟩
  rcases make_run_sprints_getElem_exists_of_run_path_mem D p n npos rs rsmem with ⟨i, ilt, j, jlt, hij⟩
  have ilt' : i < n := by rwa [make_run_sprints_length] at ilt
  have rsmem' : rs ∈ (make_run D p n).sprints[i] := List.mem_of_getElem hij
  -- Prove the closeness result required for the append operation below
  have hclose : close p (last (make_run D p i).A) (loc rs) := by
    rw [close_comm]
    convert make_run_sprint_mem_journey_cell_close D p n i ilt' rs rsmem'
    rw [← make_run_subjourney D p i n (lt_trans ilt' (Nat.lt_add_one _))]
    rw [last, subjourney_cell]
    apply cell_congr_idx
    · rw [subjourney_steps]
    · rw [subjourney_steps]
  -- Construct a journey which follows the runner for the first 'i' steps
  -- and then jumps to 'rs' for the last step.
  let A := append_journey (make_run D p i).A (loc rs) hclose
  have hlast : last A = loc rs := by
    rw [append_last]
  rw [← hlast]
  unfold close
  by_contra! hfar
  -- Use 'htraps' to show that the goal follows from 'allowed D A'
  apply htraps A hfar
  -- Now we just need to prove that A is allowed
  intro a b alt blt₀
  have blt₁ : b < i + 1 + 1 := by
    rwa [append_steps, make_run_journey_steps] at blt₀
  -- If b < i + 1, then we can use the fact that the runner's journey
  -- is always allowed if the devil is nice
  by_cases blt₂ : b < i + 1
  · unfold A
    have blt₃ : b < steps (make_run D p i).A + 1 := by
      rwa [make_run_journey_steps]
    rw [append_subjourney]; swap
    · rw [make_run_journey_steps]
      exact lt_trans alt blt₂
    rw [append_cell_ne_last _ _ _ _ blt₃]
    exact make_run_journey_allowed_of_nice D p i hnice a b alt blt₃
  rename' blt₂ => isle; push_neg at isle
  have bis : b = i + 1 := le_antisymm (Nat.le_of_lt_add_one blt₁) isle
  subst bis
  have alt' : a < n + 1 :=
    lt_trans alt (Nat.add_one_lt_add_one_iff.mpr ilt')
  have hsteps : steps A = i + 1 := by
    rw [append_steps, make_run_journey_steps]
  -- We've already proven that cells in the RunPath are never eaten
  -- Rewrite the goal so we can apply that theorem.
  rw [append_subjourney]; swap
  · rwa [make_run_journey_steps]
  rw [make_run_subjourney]; swap
  · assumption
  rw [← make_run_eaten D p n a alt']
  rw [← cell_congr_idx A hsteps (Nat.lt_add_one _), ← last, append_last]
  intro h
  exact run_path_not_eaten_of_nice D p n hnice rs rsmem (List.mem_of_getElem h)

-- Let RS be the run states "close" to the origin
def RS (N : Nat) : Set RunState :=
  {rs : RunState | close N (0, 0) (loc rs)}

-- Demonstrate an equivalence between the RunStates in the escape square
-- and the cartesian product of several Finsets whose cardinalities are known.
def runstate_equiv (N : Nat) :
  RS N ≃ Finset.range (2 * N + 1) ×ˢ Finset.range (2 * N + 1) ×ˢ uvec_finset where
  toFun := fun ⟨rs, rsmem⟩ ↦ ⟨⟨Int.toNat (rs.x + N), Int.toNat (rs.y + N), rs.u⟩, by
    apply Finset.mem_product.mpr; dsimp
    constructor
    · apply Finset.mem_range.mpr
      have hlexN : 0 ≤ rs.x + N := by
        apply Int.le_add_of_sub_left_le
        rw [Int.zero_sub]
        exact close_origin_negxle N (loc rs) rsmem
      have hxNle : rs.x + N ≤ 2 * N := by
        rw [two_mul]
        apply add_le_add_right
        exact close_origin_xle N (loc rs) rsmem
      rw [Int.toNat_lt hlexN, Int.natCast_add, Int.natCast_one]
      exact Int.lt_add_one_of_le hxNle
    apply Finset.mem_product.mpr; dsimp
    constructor
    · apply Finset.mem_range.mpr
      have hleyN : 0 ≤ rs.y + N := by
        apply Int.le_add_of_sub_left_le
        rw [Int.zero_sub]
        exact close_origin_negyle N (loc rs) rsmem
      have hyNle : rs.y + N ≤ 2 * N := by
        rw [two_mul]
        apply add_le_add_right
        exact close_origin_yle N (loc rs) rsmem
      rw [Int.toNat_lt hleyN, Int.natCast_add, Int.natCast_one]
      exact Int.lt_add_one_of_le hyNle
    · exact uvec_finset_mem _
  ⟩
  invFun := fun ⟨⟨a, b, u⟩, hmem⟩ ↦ ⟨⟨a - N, b - N, u⟩, by
    rcases Finset.mem_product.mp hmem with ⟨amem, hmem⟩
    rcases Finset.mem_product.mp hmem with ⟨bmem, umem⟩
    have alt := Finset.mem_range.mp amem; dsimp at alt
    have blt := Finset.mem_range.mp bmem; dsimp at blt
    apply close_origin_of_bounds
    unfold loc; dsimp
    constructor
    · simp
    constructor
    · apply Int.sub_left_le_of_le_add (Int.le_of_lt_add_one _)
      rw [← two_mul]
      exact Int.ofNat_lt.mpr alt
    constructor
    · simp
    · apply Int.sub_left_le_of_le_add (Int.le_of_lt_add_one _)
      rw [← two_mul]
      exact Int.ofNat_lt.mpr blt
  ⟩
  left_inv := by
    intro ⟨rs, rsmem⟩; dsimp; congr
    · rw [Int.natCast_toNat_eq_self.mpr, Int.add_sub_cancel]
      apply Int.le_add_of_sub_left_le
      rw [zero_sub]
      exact close_origin_negxle N (loc rs) rsmem
    · rw [Int.natCast_toNat_eq_self.mpr, Int.add_sub_cancel]
      apply Int.le_add_of_sub_left_le
      rw [zero_sub]
      exact close_origin_negyle N (loc rs) rsmem
  right_inv := by
    intro ⟨⟨a, b, u⟩, hmem⟩; dsimp; congr
    · rw [Int.sub_add_cancel]; rfl
    · rw [Int.sub_add_cancel]; rfl

-- Use the run states equivalence to show that 'RS N' is a Fintype
instance (N : Nat) : Fintype (RS N) := by
  let F := (Finset.range (2 * N + 1) ×ˢ Finset.range (2 * N + 1) ×ˢ uvec_finset)
  exact Fintype.ofEquiv F (runstate_equiv N).symm

-- Use the run states equivalence to prove the cardinality of RS
-- NOTE: It was very satisfying to prove this, but we don't actually need it!
-- We only needed to prove that 'RS N' was a Fintype so we can use its cardinality.
lemma runstate_card (N : Nat) : (RS N).toFinset.card = (2 * N + 1) * (2 * N + 1) * 4 := by
  rw [Set.toFinset_card]
  rw [← Finset.card_eq_of_equiv_fintype (runstate_equiv N).symm]
  rw [Finset.card_product, Finset.card_product]
  rw [Finset.card_range, uvec_finset_card, mul_assoc]

-- If the nice devil wins, then a long enough RunPath must eventually loop
lemma run_path_loops_of_nice_devil_wins
  (D : Devil) (p : Nat) (hnice : nice D p) (hdwins : devil_wins' D p) :
  ∃ N, ∀ n, N < (RunPath D p n).length → list_has_dupes (RunPath D p n) := by
  -- First get the size of the escape square
  rcases run_path_trapped_of_nice_devil_wins D p hnice hdwins with ⟨N, hclose⟩
  -- Use the cardinality of 'RS N' as the lower bound for the length of the RunPath
  use (RS N).toFinset.card
  intro n cardlt
  let L := (RunPath D p n).length
  -- Define 'F' as the Finset of all 'Fin L'
  let F := @Finset.univ (Fin L) _
  change (RS N).toFinset.card < L at cardlt
  rw [← Eq.trans Finset.card_univ (Fintype.card_fin L)] at cardlt
  -- Define a function from F to 'RS N'
  let f : Fin L → RunState := fun i ↦ (RunPath D p n)[i]
  -- Show that the image of 'f' is in 'RS N'
  have hmapsto : Set.MapsTo f F (RS N).toFinset := by
    intro i _; simp
    exact hclose n (RunPath D p n)[i] (List.get_mem _ _)
  -- Use the pigeonhole principle to conclude that the RunPath contains a duplicate state
  rcases Finset.exists_ne_map_eq_of_card_lt_of_maps_to cardlt hmapsto with ⟨i, _, j, _, inej, hij⟩
  unfold list_has_dupes
  by_cases ilt : i.val < j.val
  · use i.val, j.val, ilt, j.2
    exact hij
  rename' ilt => jle; push_neg at jle
  use j.val, i.val, lt_of_le_of_ne jle (Fin.val_ne_iff.mpr inej).symm, i.2
  exact hij.symm

-- If the devil wins, then some "nice" devil can force the runner to
-- return to the x-axis. We'll bundle all the objects which describe
-- this arrangement into a structure called an 'Endgame'. The final
-- argument of the proof will be to show that an "Endgame 2" cannot
-- exist.
structure Endgame (p : Nat) where
  D : Devil
  n : Nat
  i : Nat
  T : List RunState
  hlt : i < (RunPath D p n).length
  hlb : (RunPath D p (n - 1)).length ≤ i
  hnice : nice D p
  hpath : T = List.take (i + 1) (RunPath D p n)
  hnodupe : list_nodupes T
  hynonneg : ∀ rs ∈ T, 0 ≤ rs.y
  hwest : ∀ rs ∈ T,
    rs.y = 0 → rs.u ≠ uvec_left
  hsouth : south_facing_yz_xnn (T.getLast (by
    apply List.ne_nil_of_length_pos
    rw [hpath, List.length_take_of_le (Nat.add_one_le_of_lt hlt)]
    exact Nat.add_one_pos _
  ))

-- Prove that for some 'n' the run path of n sprints intersects the x-axis, facing south
lemma xaxis_sprint_exists_of_nice_devil_wins
  (D : Devil) (p : Nat) (ppos : 0 < p) (hnice : nice D p) (hwins : devil_wins' D p) :
  ∃ n, ∃ rs ∈ (RunPath D p n), south_facing_yz_xnn rs := by
  rcases run_path_loops_of_nice_devil_wins D p hnice hwins with ⟨N, h⟩
  rcases run_path_exist_of_length_of_ppos D p ppos N with ⟨n, Nlt⟩
  exact ⟨n, run_path_sfyzxnn_of_path_loops D p n hnice (h n Nlt)⟩

-- Find the first sprint in which the runner intersects the x-axis, facing south
def find_xaxis_sprint_of_nice_devil_wins
  (D : Devil) (p : Nat) (ppos : 0 < p) (hnice : nice D p) (hwins : devil_wins' D p) : Nat :=
  Nat.find (xaxis_sprint_exists_of_nice_devil_wins D p ppos hnice hwins)

-- The run path found by 'find_xaxis_sprint_of_nice_devil_wins' does in-fact
-- intersect the x-axis, facing south
lemma find_xaxis_sprint_intersects_xaxis
  (D : Devil) (p : Nat) (ppos : 0 < p) (hnice : nice D p) (hwins : devil_wins' D p) :
  ∃ rs ∈ (RunPath D p (find_xaxis_sprint_of_nice_devil_wins D p ppos hnice hwins)),
  south_facing_yz_xnn rs :=
  Nat.find_spec (xaxis_sprint_exists_of_nice_devil_wins D p ppos hnice hwins)

lemma xaxis_step_exists_of_nice_devil_wins
  (D : Devil) (p : Nat) (ppos : 0 < p) (hnice : nice D p) (hwins : devil_wins' D p) :
  ∃ i, (fun RP ↦ ∃ (ilt : i < RP.length), south_facing_yz_xnn RP[i])
  (RunPath D p (find_xaxis_sprint_of_nice_devil_wins D p ppos hnice hwins)) := by
  rcases find_xaxis_sprint_intersects_xaxis D p ppos hnice hwins with ⟨rs, rsmem, hrs⟩
  rcases List.getElem_of_mem rsmem with ⟨i, ilt, hi⟩
  use i, ilt
  rwa [hi]

-- Find the first step on which the runner intersects the x-axis, facing south
def find_xaxis_step_of_nice_devil_wins
  (D : Devil) (p : Nat) (ppos : 0 < p) (hnice : nice D p) (hwins : devil_wins' D p) : Nat :=
  Nat.find (xaxis_step_exists_of_nice_devil_wins D p ppos hnice hwins)

-- The step found by 'find_xaxis_step_of_nice_devil_wins' is in-fact on the x-axis, facing south
lemma find_xaxis_step_is_xaxis
  (D : Devil) (p : Nat) (ppos : 0 < p) (hnice : nice D p) (hwins : devil_wins' D p) :
  (fun i ↦ ((fun RP : List RunState ↦ ∃ (ilt : i < RP.length), south_facing_yz_xnn RP[i])
   (RunPath D p (find_xaxis_sprint_of_nice_devil_wins D p ppos hnice hwins))))
  (find_xaxis_step_of_nice_devil_wins D p ppos hnice hwins) :=
  Nat.find_spec (xaxis_step_exists_of_nice_devil_wins D p ppos hnice hwins)

-- The first step in the run path on the x-axis facing south appears before the
-- end of the first sprint in which this occurs.
-- Note that this corresponds to 'hlt' in the specification of an Endgame
lemma find_xaxis_step_of_nice_devil_wins_lt
  (D : Devil) (p : Nat) (ppos : 0 < p) (hnice : nice D p) (hwins : devil_wins' D p) :
  find_xaxis_step_of_nice_devil_wins D p ppos hnice hwins <
  (RunPath D p (find_xaxis_sprint_of_nice_devil_wins D p ppos hnice hwins)).length := by
  let n := find_xaxis_sprint_of_nice_devil_wins D p ppos hnice hwins
  let i := find_xaxis_step_of_nice_devil_wins D p ppos hnice hwins
  change i < (RunPath D p n).length
  rcases xaxis_step_exists_of_nice_devil_wins D p ppos hnice hwins with ⟨j, jlt, hj⟩
  apply lt_of_le_of_lt _ jlt
  -- Since step j is an x-axis step and i is the first such step, i ≤ j
  apply Nat.find_min' (xaxis_step_exists_of_nice_devil_wins D p ppos hnice hwins)
  use jlt

-- Construct an endgame, given a nice devil that wins
def endgame_of_nice_devil_wins
  (D : Devil) (p : Nat) (ppos : 0 < p) (hnice : nice D p) (hwins : devil_wins' D p) : Endgame p where
  D := D
  n := find_xaxis_sprint_of_nice_devil_wins D p ppos hnice hwins
  i := find_xaxis_step_of_nice_devil_wins D p ppos hnice hwins
  T := List.take ((find_xaxis_step_of_nice_devil_wins D p ppos hnice hwins) + 1)
       (RunPath D p (find_xaxis_sprint_of_nice_devil_wins D p ppos hnice hwins))
  hlt := find_xaxis_step_of_nice_devil_wins_lt D p ppos hnice hwins
  hlb := by
    let n := find_xaxis_sprint_of_nice_devil_wins D p ppos hnice hwins
    let i := find_xaxis_step_of_nice_devil_wins D p ppos hnice hwins
    change (RunPath D p (n - 1)).length ≤ i
    have inz : i ≠ 0 := by
      intro iz
      rcases Nat.find_spec (xaxis_step_exists_of_nice_devil_wins D p ppos hnice hwins) with ⟨_, _, _, hsouth⟩
      absurd hsouth; push_neg
      change (RunPath D p n)[i].u ≠ uvec_down
      rw [getElem_congr_idx iz, run_path_getElem_zero]
      unfold run_start uvec_down uvec_up; simp
    have ipos : 0 < i := Nat.pos_of_ne_zero inz
    by_cases nz : n = 0
    · rw [nz, Nat.zero_sub, run_path_of_length_zero, List.length_singleton]
      exact Nat.one_le_of_lt ipos
    rename' nz => nnz; push_neg at nnz
    have npos : 0 < n := Nat.pos_of_ne_zero nnz
    by_contra! ilt
    absurd Nat.sub_one_lt nnz; push_neg
    -- Show that if i < (RunPath D p (n - 1)).length, the nth sprint is
    -- not the first sprint that intersects the x-axis, which is a contradiction
    apply Nat.find_min' (xaxis_sprint_exists_of_nice_devil_wins D p ppos hnice hwins)
    let rs := (RunPath D p n)[i]'(find_xaxis_step_of_nice_devil_wins_lt D p ppos hnice hwins)
    -- Show that rs is also a member of the run path with n-1 sprints
    have rsmem : rs ∈ (RunPath D p (n - 1)) := by
      unfold rs
      rw [getElem_congr_coll (run_path_recurrence D p n npos)]
      rw [List.getElem_append_left ilt]
      exact List.getElem_mem ilt
    use rs, rsmem
    rcases Nat.find_spec (xaxis_step_exists_of_nice_devil_wins D p ppos hnice hwins) with ⟨_, _⟩
    assumption
  hnice := hnice
  hpath := rfl
  hnodupe := by
    let n := find_xaxis_sprint_of_nice_devil_wins D p ppos hnice hwins
    let i := find_xaxis_step_of_nice_devil_wins D p ppos hnice hwins
    let L := (RunPath D p n).length
    have hiex := xaxis_step_exists_of_nice_devil_wins D p ppos hnice hwins
    rcases Nat.find_spec hiex with ⟨ilt, hi⟩
    change i < L at ilt
    change south_facing_yz_xnn (RunPath D p n)[i] at hi
    --have ilt : i < L :=
    --  find_xaxis_step_of_nice_devil_wins_lt D p ppos hnice hwins
    change list_nodupes (List.take (i + 1) (RunPath D p n))
    -- Show that the goal follows trivially if the run path has no duplicates
    -- then we can assume for the remainder of the proof that it does.
    by_cases hdupe : list_nodupes (RunPath D p n)
    · contrapose! hdupe
      rw [list_not_nodupes] at *
      rcases hdupe with ⟨a, b, alt, blt, hab⟩
      have blt' : b < L := by
        rw [List.length_take_of_le (Nat.add_one_le_of_lt ilt)] at blt
        exact lt_of_le_of_lt (Nat.le_of_lt_add_one blt) ilt
      rw [List.getElem_take, List.getElem_take] at hab
      exact ⟨a, b, alt, blt', hab⟩
    rw [list_not_nodupes] at hdupe
    -- Reduce the goal to proving that the first 'sfyzxnn' step
    -- appears before the first duplicate
    rw [first_dupe_gt_iff_no_dupes_take _ hdupe _ (Nat.add_one_le_of_lt ilt)]
    apply Nat.add_one_le_of_lt
    -- Now use proof by contradiction:
    -- If the first duplicate appears before the first 'sfyzxnn' step
    -- there must be some even earlier 'sfyzxnn' step prior to that,
    -- which is a contradiction.
    by_contra! h
    let b := (find_first_dupe (RunPath D p n) (list_ne_nil_of_has_dupes _ hdupe)).1
    have blt : b < L := Fin.prop _
    rcases first_dupe_is_dupe _ hdupe with ⟨_, hlt, _⟩
    have bnz : b ≠ 0 := Nat.ne_zero_of_lt hlt
    have hb : (RunPath D p n)[b] = run_start :=
      run_path_first_dupe_is_run_start D p n hnice hdupe
    rcases run_path_start_repeats_has_earlier_sfyzxnn D p n hnice b blt bnz hb with ⟨j, jlt, hj⟩
    have jlt' : j < L := lt_trans jlt blt
    -- Since 'i' is the location of the first sfyzxnn step,
    -- it must be at least as early as 'j'
    have ilej : i ≤ j := Nat.find_min' hiex ⟨jlt', hj⟩
    -- Now combine all the inequalities to reach a contradiction
    exact (lt_self_iff_false _).mp (lt_of_le_of_lt ilej (lt_of_lt_of_le jlt h))
  hynonneg := by
    intro rs rsmem
    by_contra! rsyneg
    let n := find_xaxis_sprint_of_nice_devil_wins D p ppos hnice hwins
    let i := find_xaxis_step_of_nice_devil_wins D p ppos hnice hwins
    let L := (RunPath D p n).length
    have hiex := xaxis_step_exists_of_nice_devil_wins D p ppos hnice hwins
    rcases Nat.find_spec hiex with ⟨ilt, hi⟩
    change i < L at ilt
    change south_facing_yz_xnn (RunPath D p n)[i] at hi
    change rs ∈ List.take (i + 1) (RunPath D p n) at rsmem
    rcases List.mem_take_iff_getElem.mp rsmem with ⟨j, jlt, hj⟩
    rw [min_eq_left (Nat.add_one_le_of_lt ilt)] at jlt
    have jlt' : j < L := lt_of_le_of_lt (Nat.le_of_lt_add_one jlt) ilt
    -- Let 'k' be the point prior to 'j' where the path crossed the x-axis
    rcases run_path_has_earlier_sfyzxnn_of_south D p n hnice j jlt' (hj ▸ rsyneg) with ⟨k, klt, hk⟩
    have klt' : k < L := lt_trans klt jlt'
    -- Since 'i' is the first point at which the path crossed the x-axis
    -- 'i' must be no later than 'k'. This leads to a contradiction.
    have ilek : i ≤ k := Nat.find_min' hiex ⟨klt', hk⟩
    exact not_lt_of_ge (le_trans (Nat.le_of_lt_add_one jlt) ilek) klt
  hwest := by
    intro rs rsmem hyz
    rcases List.getElem_of_mem rsmem with ⟨j, jlt, rfl⟩
    let n := find_xaxis_sprint_of_nice_devil_wins D p ppos hnice hwins
    let i := find_xaxis_step_of_nice_devil_wins D p ppos hnice hwins
    let L := (RunPath D p n).length
    have hiex := xaxis_step_exists_of_nice_devil_wins D p ppos hnice hwins
    rcases Nat.find_spec hiex with ⟨ilt, hi⟩
    change i < L at ilt
    change j < (List.take (i + 1) (RunPath D p n)).length at jlt
    change (List.take (i + 1) (RunPath D p n))[j].y = 0 at hyz
    change (List.take (i + 1) (RunPath D p n))[j].u ≠ uvec_left
    have jlt' : j < i + 1 := by
      rwa [List.length_take_of_le (Nat.add_one_le_of_lt ilt)] at jlt
    have jlt'' : j < L := lt_of_le_of_lt (Nat.le_of_lt_add_one jlt') ilt
    have hjxnn : 0 ≤ (RunPath D p n)[j].x :=
      run_path_x_nonneg D p n (RunPath D p n)[j] (List.getElem_mem jlt'')
    -- If the path is ever on the x-axis facing west,
    -- there must have been an earlier step facing south.
    -- This will lead to a contradiction.
    rw [List.getElem_take] at *
    by_contra! hwest
    have := run_path_xaxis_west_has_earlier_xaxis_south D p n hnice j jlt'' ⟨hjxnn, hyz, hwest⟩
    rcases this with ⟨k, klt, hk⟩
    have klt' : k < L := lt_trans klt jlt''
    -- Since 'i' is the first point at which the path crossed the x-axis
    -- 'i' must be no later than 'k'. This leads to a contradiction.
    have ilek : i ≤ k := Nat.find_min' hiex ⟨klt', hk⟩
    exact not_lt_of_ge (le_trans (Nat.le_of_lt_add_one jlt') ilek) klt
  hsouth := by
    rw [List.getLast_eq_getElem, List.getElem_take]
    let n := find_xaxis_sprint_of_nice_devil_wins D p ppos hnice hwins
    let i := find_xaxis_step_of_nice_devil_wins D p ppos hnice hwins
    let L := (RunPath D p n).length
    have hiex := xaxis_step_exists_of_nice_devil_wins D p ppos hnice hwins
    rcases Nat.find_spec hiex with ⟨ilt, hi⟩
    convert hi
    change i < L at ilt
    rw [List.length_take_of_le (Nat.add_one_le_of_lt ilt)]
    rw [Nat.add_one_sub_one]
    rfl

-- Produce the final 'blocked' list by taking the last blocked list
-- used in the endgame trace and removing any cells eaten by the devil
-- outside of the first quadrant or higher than the west wall.
abbrev endgame_blocked {p : Nat} (E : Endgame p) : List (Int × Int) :=
  blocked_trim_quad1 (E.i + 1) run_start (make_block_list E.D p (E.n + 1)) (E.n * p + 1)

-- Prove that run_start is "valid" under the endgame blocked list
lemma endgame_run_start_valid {p : Nat} (E : Endgame p) :
  run_start_valid (endgame_blocked E) run_start := by
  unfold run_start_valid
  let ⟨rsnmem, lormem⟩ := run_start_valid_of_nice E.D p E.hnice (E.n + 1)
  let BL := make_block_list E.D p (E.n + 1)
  let T := trace (E.i + 1) run_start BL
  have tlpos : 0 < T.length := by
    rw [trace_length]
    exact Nat.add_one_pos _
  have hnnil : T ≠ [] := List.ne_nil_of_length_pos tlpos
  constructor
  · apply trace_trim_quad1_notmem_of_notmem
    exact rsnmem
  · apply trace_trim_quad1_mem _ _ _ _ _ lormem
    unfold run_start left_of_runner uvec_up; simp
    use (by rw [← Int.natCast_mul]; linarith), run_start
    constructor
    · apply List.mem_of_getElem
      · convert trace_getElem_zero_of_nonnil _ _ _ hnnil
      · exact tlpos
    · unfold run_start loc; simp

lemma endgame_trace_ne_nil {p : Nat} (E : Endgame p) : E.T ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [E.hpath]
  have isle : E.i + 1 ≤ (RunPath E.D p E.n).length :=
    Nat.add_one_le_of_lt E.hlt
  rw [List.length_take_of_le isle]
  exact Nat.add_one_pos _

-- The endgame trace is equal to the trace of length 'E.i + 1',
-- starting at 'run_start' and using the endgame blocked list
lemma endgame_trace_eq {p : Nat} (E : Endgame p) :
  E.T = trace (E.i + 1) run_start (endgame_blocked E) := by
  let BL := make_block_list E.D p (E.n + 1)
  let RP := RunPath E.D p E.n
  rw [E.hpath]
  have Eislt := Nat.add_one_le_of_lt E.hlt
  have htrace := run_path_eq_trace_of_nice E.D p E.n (E.n + 1) (by simp) E.hnice
  have htake := trace_take RP.length run_start BL (E.i + 1) Eislt
  rw [htrace, ← htake]
  apply trace_trim_quad1_unchanged (E.i + 1) run_start BL (E.n * p + 1)
  intro rs rsmem
  have rsmem' : rs ∈ RP := by
    unfold RP
    rw [htrace]
    apply List.mem_of_mem_take
    rwa [← htake]
  rcases List.getElem_of_mem rsmem with ⟨i, ilt, hi⟩
  have rsmem'' : rs ∈ E.T := by
    rw [← hi, E.hpath, htrace, ← htake]
    exact List.getElem_mem _
  constructor
  · exact run_path_x_nonneg E.D p E.n rs rsmem'
  constructor
  · exact E.hynonneg rs rsmem''
  constructor
  · apply Int.lt_add_one_of_le
    rw [← Int.natCast_mul]
    exact run_path_y_le E.D p E.n _ rsmem'
  · exact E.hwest _ rsmem''

def endgame_perimeter_length {p : Nat} (E : Endgame p) : Nat :=
  perimeter_length run_start (endgame_blocked E) (endgame_run_start_valid E)

-- Give a name to the trace which circumnavigates the endgame blocked list
def endgame_perimeter {p : Nat} (E : Endgame p) : List RunState :=
  trace (endgame_perimeter_length E) run_start (endgame_blocked E)

lemma endgame_perimeter_length_pos {p : Nat} (E : Endgame p) :
  0 < endgame_perimeter_length E := by
  apply perimeter_length_pos

-- Prove that the endpoint of the endgame trace falls within the endgame perimeter
lemma endgame_endpoint_lt {p : Nat} (E : Endgame p) :
  E.i < (endgame_perimeter E).length := by
  unfold endgame_perimeter
  rw [trace_length, endgame_perimeter_length]
  by_contra! lei
  let BL := endgame_blocked E
  let T := trace (E.i + 1) run_start BL
  have hvalid := endgame_run_start_valid E
  have hnnil : T ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [trace_length]
    exact Nat.add_one_pos _
  let P := perimeter_length run_start BL hvalid
  have Ppos : 0 < P :=
    perimeter_length_pos run_start BL hvalid
  -- Show that if E.i is not less than that perimeter length,
  -- there must be a duplicate (which is a contradiction)
  have Psle : P + 1 ≤ T.length := by
    rw [trace_length]
    exact Nat.add_one_le_add_one_iff.mpr lei
  absurd E.hnodupe
  rw [list_not_nodupes]
  use 0, P, (perimeter_length_pos _ _ hvalid), (by
    rw [E.hpath]
    rw [List.length_take_of_le (Nat.add_one_le_of_lt E.hlt)]
    exact Nat.lt_add_one_of_le lei
  )
  repeat rw [getElem_congr_coll (endgame_trace_eq E)]
  rw [trace_getElem_zero_of_nonnil (E.i + 1) run_start BL hnnil]; symm
  have hrepeat := trace_start_repeats_idx run_start BL hvalid
  rw [List.getElem_take' _ (Nat.lt_add_one P)]
  rw [← getElem_congr_idx (Nat.add_one_sub_one P)]; swap
  · rw [List.length_take_of_le Psle]; simp
  rw [List.getLast_eq_getElem] at hrepeat
  convert hrepeat
  · rw [← trace_take]
    exact Nat.add_one_le_add_one_iff.mpr lei
  · rw [trace_length]

-- Prove a lower bound on length of the endgame trace
lemma endgame_endpoint_lb {p : Nat} (E : Endgame p) : (E.n - 1) * p + 1 ≤ E.i := by
  apply le_trans _ E.hlb
  rw [add_comm, mul_comm]
  exact run_path_length_lb E.D p (E.n - 1)

def endgame_endpoint {p : Nat} (E : Endgame p) : RunState :=
  (endgame_perimeter E)[E.i]'(endgame_endpoint_lt E)

lemma endgame_endpoint_eq {p : Nat} (E : Endgame p) :
  endgame_endpoint E = E.T.getLast (endgame_trace_ne_nil E) := by
  let BL := (endgame_blocked E)
  let P := endgame_perimeter_length E
  have isle : E.i + 1 ≤ (trace P run_start BL).length :=
    Nat.add_one_le_of_lt (endgame_endpoint_lt E)
  have isle' : E.i + 1 ≤ P := by
    unfold endgame_perimeter at isle
    rwa [trace_length] at isle
  rw [List.getLast_congr _ _ (endgame_trace_eq E)]; swap
  · apply List.ne_nil_of_length_pos
    rw [trace_length]
    exact Nat.add_one_pos _
  have htake := trace_take P run_start BL _ isle'
  rw [List.getLast_congr _ _ htake]; swap
  · apply List.ne_nil_of_length_pos
    rw [List.length_take_of_le isle]
    exact Nat.add_one_pos _
  rw [List.getLast_eq_getElem, List.getElem_take]
  unfold endgame_endpoint; congr
  rw [List.length_take_of_le isle]; simp

lemma endgame_endpoint_yz {p : Nat} (E : Endgame p) :
  (endgame_endpoint E).y = 0 := by
  convert E.hsouth.2.1
  exact endgame_endpoint_eq E

lemma endgame_endpoint_lex {p : Nat} (E : Endgame p) :
  0 ≤ (endgame_endpoint E).x := by
  convert E.hsouth.1
  exact endgame_endpoint_eq E

-- Prove that the last point in the perimeter has coordinates (-1, -1)
lemma endgame_southwest_point_eq {p : Nat} (E : Endgame p) :
  loc ((endgame_perimeter E)[endgame_perimeter_length E - 1]'(by
    unfold endgame_perimeter
    rw [trace_length]
    apply Nat.sub_one_lt (Nat.ne_zero_of_lt (endgame_perimeter_length_pos E))
  )) = (-1, -1) := by
  let P := endgame_perimeter_length E
  let BL := endgame_blocked E
  have Ppos : 0 < P := by
    apply perimeter_length_pos
  have hvalid := endgame_run_start_valid E
  have hrepeat := trace_start_repeats_idx run_start BL hvalid
  change (trace (P + 1) run_start BL).getLast _ = _ at hrepeat
  rw [List.getLast_eq_getElem] at hrepeat
  have rw₀ : (trace (P + 1) run_start BL).length - 1 = P := by
    rw [trace_length]; simp
  rw [getElem_congr_idx rw₀] at hrepeat
  rw [trace_getElem_recurrence' (P + 1) run_start BL P Ppos (Nat.lt_add_one _)] at hrepeat
  apply congrArg (undo_next_step BL) at hrepeat
  rw [next_step_undo_cancel] at hrepeat
  -- In order to use 'undo_next_step' we need to prove
  -- that the last cell in the perimeter is "valid"
  pick_goal 2; pick_goal 3
  · exact trace_wall_blocked_of_valid (P + 1) run_start BL hvalid _ (List.getElem_mem _)
  · exact trace_avoids_blocked (P + 1) run_start BL hvalid.1 _ (List.getElem_mem _)
  unfold endgame_perimeter
  rw [getElem_congr_coll (trace_take (P + 1) run_start BL P (by norm_num))]
  rw [List.getElem_take, hrepeat]
  unfold undo_next_step; simp
  have huleft : loc (undo_turn_left run_start) ∉ BL := by
    apply trace_trim_quad1_notmem_of_yneg
    unfold undo_turn_left run_start loc uvec_up; simp
  rw [if_neg huleft]
  unfold undo_turn_left run_start loc uvec_up; simp

-- Prove the bounds check for the southwest point
-- (which comes immediately after the "endpoint")
lemma endgame_southeast_point_lt {p : Nat} (E : Endgame p) :
  E.i + 1 < (endgame_perimeter E).length := by
  apply lt_of_le_of_ne (Nat.add_one_le_of_lt (endgame_endpoint_lt E))
  unfold endgame_perimeter
  rw [trace_length]
  by_contra! iseq
  -- If E.i + 1 = P, the endpoint is equal to the southwest point
  -- But this is impossible because the former has x = 0 and the
  -- latter has x = -1
  absurd endgame_endpoint_yz E
  unfold endgame_endpoint
  rw [getElem_congr_idx (Nat.eq_sub_of_add_eq iseq)]
  have rw₀ := (Prod.ext_iff.mp (endgame_southwest_point_eq E)).2
  unfold loc at rw₀; simp at rw₀
  rw [rw₀]
  norm_num

-- Prove that the southeast point has y = -1 and x-coordinate
-- one greater than the endgame endpoint.
lemma endgame_southeast_point_eq {p : Nat} (E : Endgame p) :
  loc ((endgame_perimeter E)[E.i + 1]'(endgame_southeast_point_lt E)) =
  ((endgame_endpoint E).x + 1, -1) := by
  let P := endgame_perimeter_length E
  let BL := endgame_blocked E
  let T := endgame_perimeter E
  unfold endgame_perimeter
  have ilt : E.i < T.length := by
    exact endgame_endpoint_lt E
  have islt : E.i + 1 < endgame_perimeter_length E := by
    convert endgame_southeast_point_lt E
    unfold endgame_perimeter
    rw [trace_length]
  rw [trace_getElem_recurrence _ _ _ _ islt]
  unfold next_step
  have : loc (turn_left T[E.i]) = ((endgame_endpoint E).x + 1, -1) := by
    have rw₀ := endgame_endpoint_eq E
    unfold endgame_endpoint at rw₀; unfold T loc; simp
    rw [endgame_endpoint_eq E, rw₀]
    unfold turn_left; simp
    rw [E.hsouth.2.1, E.hsouth.2.2]
    unfold uvec_down; simp
  have hleft : loc (turn_left T[E.i]) ∉ endgame_blocked E := by
    apply trace_trim_quad1_notmem_of_yneg
    rw [this]; simp
  unfold T endgame_perimeter at hleft
  rw [if_pos hleft]
  exact this
