import AngelDevil.Runner

/- This file defines a mechanism for creating a "trimmed" blocked list
   and proves the conditions under which a trace is unaffected by this
   trimming.
-/

-- Removing elements from the blocked list has no effect on the trace
-- as long as none are "close" to cells in the original trace
lemma trace_unchanged_of_close_blocked_unchanged
  (n : Nat) (start : RunState) (blocked₀ blocked₁ : List (Int × Int)) (hss : blocked₁ ⊆ blocked₀)
  (hclose : ∀ x ∈ blocked₀, (∃ rs ∈ trace n start blocked₀, close 1 x (loc rs)) → x ∈ blocked₁) :
  trace n start blocked₀ = trace n start blocked₁ := by
  apply List.ext_getElem
  · rw [trace_length, trace_length]
  intro i ilt₀ ilt₁
  have ilt : i < n := by rwa [trace_length] at ilt₀
  have hnnil₀ : trace n start blocked₀ ≠ [] := by
    apply List.ne_nil_of_length_pos
    exact Nat.zero_lt_of_lt ilt₀
  have hnnil₁ : trace n start blocked₁ ≠ [] := by
    apply List.ne_nil_of_length_pos
    exact Nat.zero_lt_of_lt ilt₁
  -- Handle the case where i = 0
  by_cases iz : i = 0
  · subst iz
    rw [trace_getElem_zero_of_nonnil _ _ _ hnnil₀]
    rw [trace_getElem_zero_of_nonnil _ _ _ hnnil₁]
  rename' iz => inz; push_neg at inz
  have ipos : 0 < i := Nat.pos_of_ne_zero inz
  -- Apply the trace recurrence
  rw [trace_getElem_recurrence' n start blocked₀ i ipos ilt]
  rw [trace_getElem_recurrence' n start blocked₁ i ipos ilt]
  have iplt : i - 1 < n - 1 :=
    Nat.sub_lt_sub_right (Nat.one_le_of_lt ipos) ilt
  -- Recurse
  have hrecurse :
    (trace (n - 1) start blocked₀)[i - 1]'(by rwa [trace_length]) =
    (trace (n - 1) start blocked₁)[i - 1]'(by rwa [trace_length]) := by
    congr 1
    apply trace_unchanged_of_close_blocked_unchanged (n - 1) start blocked₀ blocked₁ hss
    intro x xmem h
    rcases h with ⟨rs, rsmem, hclose'⟩
    apply hclose x xmem ⟨rs, _, hclose'⟩
    rcases List.getElem_of_mem rsmem with ⟨j, jlt, rfl⟩
    rw [getElem_congr_coll (trace_take n start blocked₀ (n - 1) (Nat.sub_le _ _))]
    rw [List.getElem_take]
    apply List.getElem_mem
  -- Rewrite the recursion for the trace of length 'n'
  rw [getElem_congr_coll (trace_take n start blocked₀ (n - 1) (Nat.sub_le _ _))] at hrecurse
  rw [getElem_congr_coll (trace_take n start blocked₁ (n - 1) (Nat.sub_le _ _))] at hrecurse
  rw [List.getElem_take, List.getElem_take] at hrecurse
  rw [← hrecurse]
  -- Re-state the goal for clarity
  let rs := (trace n start blocked₀)[i - 1]
  have rsmem : rs ∈ trace n start blocked₀ := List.getElem_mem _
  change next_step blocked₀ rs = next_step blocked₁ rs
  -- Unfold just the left-hand side to limit the scope of 'split_ifs'
  nth_rw 1 [next_step]
  -- Show that in each of the three cases the relevant blocked cells
  -- must either be in both blocked₀ and blocked₁, or neither
  split_ifs with hleft₀ hforward₀ <;> unfold next_step
  · have hleft₁ : loc (turn_left rs) ∈ blocked₁ := by
      apply hclose _ hleft₀ ⟨rs, rsmem, _⟩
      rw [close_comm]
      exact turn_left_dist_le_one rs
    have hforward₁ : loc (move_forward rs) ∈ blocked₁ := by
      apply hclose _ hforward₀ ⟨rs, rsmem, _⟩
      rw [close_comm]
      exact move_forward_dist_le_one rs
    simp; rw [if_pos hleft₁, if_pos hforward₁]
  · have hleft₁ : loc (turn_left rs) ∈ blocked₁ := by
      apply hclose _ hleft₀ ⟨rs, rsmem, _⟩
      rw [close_comm]
      exact turn_left_dist_le_one rs
    have hforward₁ : loc (move_forward rs) ∉ blocked₁ := by
      contrapose! hforward₀
      exact hss hforward₀
    simp; rw [if_pos hleft₁, if_neg hforward₁]
  · have hleft₁ : loc (turn_left rs) ∉ blocked₁ := by
      contrapose! hleft₀
      exact hss hleft₀
    rw [if_pos hleft₁]

-- Define a blocked list filter that removes all cells outside a given rectangle
def blocked_trim_rect (top bottom left right : Int) (blocked : List (Int × Int)) :=
  List.filter (fun (a : Int × Int) ↦
    a.2 ≤ top ∧ bottom ≤ a.2 ∧ left ≤ a.1 ∧ a.1 ≤ right) blocked

-- Prove that using 'blocked_trim_rect' to trim the blocked list has no effect
-- on the trace if all steps in the trace are properly inside the given rectangle.
lemma trace_trim_rect_unchanged (n : Nat) (start : RunState) (blocked : List (Int × Int))
  (top bottom left right : Int) :
  (∀ i (ilt : i < n),
  (fun a ↦ a.2 < top ∧ bottom < a.2 ∧ left < a.1 ∧ a.1 < right)
  ((trace n start blocked)[i]'(by rwa [trace_length]))) →
  trace n start blocked = trace n start (blocked_trim_rect top bottom left right blocked) := by
  intro hbounds
  let blocked' := blocked_trim_rect top bottom left right blocked
  change _ = trace n start blocked'
  have hss : blocked' ⊆ blocked := by
    intro a amem
    exact (List.mem_filter.mp amem).1
  apply trace_unchanged_of_close_blocked_unchanged n start _ _ hss
  intro a amem h
  rcases h with ⟨rs, rsmem, hclose⟩
  rcases List.getElem_of_mem rsmem with ⟨i, ilt, hi⟩
  have ilt' : i < n := by rwa [trace_length] at ilt
  have hbounds' := (hi ▸ hbounds i ilt'); simp at hbounds'
  unfold blocked' blocked_trim_rect
  apply List.mem_filter.mpr ⟨amem, _⟩; simp
  -- Close the goal by showing that if any of the bounds were violated
  -- it would lead to a contradition with hbounds' and hclose
  constructor
  · by_contra! toplt
    have lesub :  2 ≤ a.2 - (loc rs).2 := by
      apply Int.le_sub_left_of_add_le
      rw [← one_add_one_eq_two, ← add_assoc]
      exact Int.add_one_le_of_lt (lt_of_le_of_lt (Int.add_one_le_of_lt hbounds'.1) toplt)
    have := Int.ofNat_le.mpr (le_of_max_le_right hclose)
    rw [Int.natAbs_of_nonneg (le_trans (by norm_num) lesub), Int.natCast_one] at this
    absurd le_trans lesub this; push_neg; exact one_lt_two
  constructor
  · by_contra! ltbottom
    have lesub :  2 ≤ (loc rs).2 - a.2 := by
      apply Int.le_sub_left_of_add_le
      rw [← one_add_one_eq_two, ← add_assoc]
      exact Int.add_one_le_of_lt (lt_of_le_of_lt (Int.add_one_le_of_lt ltbottom) (hbounds'.2.1))
    have := Int.ofNat_le.mpr (le_of_max_le_right hclose)
    rw [← Int.natAbs_neg, Int.neg_sub] at this
    rw [Int.natAbs_of_nonneg (le_trans (by norm_num) lesub), Int.natCast_one] at this
    absurd le_trans lesub this; push_neg; exact one_lt_two
  constructor
  · by_contra! ltleft
    have lesub :  2 ≤ (loc rs).1 - a.1 := by
      apply Int.le_sub_left_of_add_le
      rw [← one_add_one_eq_two, ← add_assoc]
      exact Int.add_one_le_of_lt (lt_of_le_of_lt (Int.add_one_le_of_lt ltleft) (hbounds'.2.2.1))
    have := Int.ofNat_le.mpr (le_of_max_le_left hclose)
    rw [← Int.natAbs_neg, Int.neg_sub] at this
    rw [Int.natAbs_of_nonneg (le_trans (by norm_num) lesub), Int.natCast_one] at this
    absurd le_trans lesub this; push_neg; exact one_lt_two
  · by_contra! rightlt
    have lesub :  2 ≤ a.1 - (loc rs).1 := by
      apply Int.le_sub_left_of_add_le
      rw [← one_add_one_eq_two, ← add_assoc]
      exact Int.add_one_le_of_lt (lt_of_le_of_lt (Int.add_one_le_of_lt hbounds'.2.2.2) rightlt)
    have := Int.ofNat_le.mpr (le_of_max_le_left hclose)
    rw [Int.natAbs_of_nonneg (le_trans (by norm_num) lesub), Int.natCast_one] at this
    absurd le_trans lesub this; push_neg; exact one_lt_two
