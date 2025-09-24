import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import AngelDevil.Reduced
import AngelDevil.Focused
import AngelDevil.Runner

set_option linter.style.longLine false
set_option linter.style.multiGoal false

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
  let k := (_find_first (outside_fun A N))
  -- The kth cell is in-fact outside the escape square
  have ksat : N < dist (0, 0) (last (subjourney A k.val k.2)) := by
    rw [subjourney_last_cell]
    exact _find_first_is_sat (outside_fun A N) ⟨⟨steps A, Nat.lt_add_one _⟩, Nlt⟩
  -- The kth cell is the *first* step outside the escape square
  have kfirst : ∀ i (ilt : i < steps A + 1),
    N < dist (0, 0) (cell A i ilt) → k.val ≤ i := by
    intro i ilt houtside
    exact Fin.le_iff_val_le_val.mp (_find_first_is_first (outside_fun A N) ⟨i, ilt⟩ houtside)
  -- Handle the case where the first step outside the escape square
  -- is not the last step of the journey.
  by_cases knl : k.val ≠ steps A
  · -- We can solve the goal by recursion because k < steps A
    rcases extended_perimeter D p N htraps (subjourney A k.1 k.2) ksat with ⟨i, j, h⟩
    push_neg at h
    rcases h with ⟨ilt, jlt, hinside, hcaught⟩
    rw [subjourney_steps] at jlt
    rw [subjourney_cell] at hinside
    rw [subjourney_subjourney, subjourney_cell] at hcaught
    use i, j; push_neg
    use ilt, lt_trans jlt
      (Nat.add_one_lt_add_one_iff.mpr (Nat.lt_of_le_of_ne (Nat.le_of_lt_add_one k.2) knl))
    -- Prove pending bounds checks
    · exact Nat.le_of_lt_add_one jlt
    · exact lt_trans ilt jlt
    · exact Nat.le_of_lt_add_one jlt
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
  exact Nat.lt_of_le_of_ne (Nat.le_of_lt_add_one ((_find_first (outside_fun A N)).2)) knl

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
theorem JC8_1 (p : Nat) : ¬(∃ D : Devil, devil_wins D p) → ∀ D : Devil, ∀ N : Nat, ∃ A : Journey p,
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
theorem AM2_7 (p : Nat) : (∃ D : Devil, devil_wins D p) →
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
  (D : Devil) (p : Nat) (ppos : 0 < p) (hnice : nice D p) (hdwins : devil_wins' D p) :
  ∃ N, ∀ n, allowed D (make_run D p n ppos).A →
  ∀ rs ∈ RunPath D p n ppos, close N (0, 0) (loc rs) := by
  let ⟨N, htraps⟩ := hdwins
  use N
  intro n hallowed rs rsmem
  -- First handle the case where n = 0
  by_cases nz : n = 0
  · subst nz
    rw [run_path_of_length_zero D p ppos] at rsmem
    rw [List.mem_singleton.mp rsmem]
    exact close_self N (0, 0)
  rename' nz => nnz; push_neg at nnz
  have npos : 0 < n := Nat.pos_of_ne_zero nnz
  -- Next, find the sprint that produced 'rs'
  rcases List.getElem_of_mem rsmem with ⟨k, klt, hrpk⟩
  rcases make_run_sprints_getElem_exists_of_run_path_mem D p n ppos npos rs rsmem with ⟨i, ilt, j, jlt, hij⟩
  have ilt' : i < n := by rwa [make_run_sprints_length] at ilt
  have rsmem' : rs ∈ (make_run D p n ppos).sprints[i] := List.mem_of_getElem hij
  -- Prove the closeness result required for the append operation below
  have hclose : close p (last (make_run D p i ppos).A) (loc rs) := by
    rw [close_comm]
    convert make_run_sprint_mem_journey_cell_close D p n ppos i ilt' rs rsmem'
    rw [← make_run_subjourney D p i n ppos (lt_trans ilt' (Nat.lt_add_one _))]
    rw [last, subjourney_cell]
    apply cell_congr_idx
    · rw [subjourney_steps]
    · rw [subjourney_steps]
  -- Construct a journey which follows the runner for the first 'i' steps
  -- and then jumps to 'rs' for the last step.
  let A := append_journey (make_run D p i ppos).A (loc rs) hclose
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
    have blt₃ : b < steps (make_run D p i ppos).A + 1 := by
      rwa [make_run_journey_steps]
    rw [append_subjourney]; swap
    · rw [make_run_journey_steps]
      exact lt_trans alt blt₂
    rw [append_cell_ne_last _ _ _ _ blt₃]
    exact make_run_journey_allowed_of_nice D p i ppos hnice a b alt blt₃
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
  rw [← make_run_eaten D p n ppos a alt']
  rw [← cell_congr_idx A hsteps (Nat.lt_add_one _), ← last, append_last]
  intro h
  exact run_path_not_eaten_of_nice D p n ppos hnice rs rsmem (List.mem_of_getElem h)
