import AngelDevil.Trace

/- This file defines a mechanism for creating a "trimmed" blocked list
   and proves the conditions under which a trace is unaffected by this
   trimming.
-/

-- Removing elements from the blocked list has no effect on 'next_step'
-- as long as none are "close" to the current cell
lemma next_step_unchanged_of_close_blocked_unchanged
  (rs : RunState) (blocked₀ blocked₁ : List (Int × Int))
  (hss : blocked₁ ⊆ blocked₀) (hclose : ∀ a ∈ blocked₀, close 1 a (loc rs) → a ∈ blocked₁) :
  next_step blocked₀ rs = next_step blocked₁ rs := by
  -- Unfold just the left-hand side to limit the scope of 'split_ifs'
  nth_rw 1 [next_step]
  -- Show that in each of the three cases the relevant blocked cells
  -- must either be in both blocked₀ and blocked₁, or neither
  split_ifs with hleft₀ hforward₀ <;> unfold next_step
  · have hleft₁ : loc (turn_left rs) ∈ blocked₁ := by
      apply hclose _ hleft₀
      rw [close_comm]
      exact turn_left_dist_le_one rs
    have hforward₁ : loc (move_forward rs) ∈ blocked₁ := by
      apply hclose _ hforward₀
      rw [close_comm]
      exact move_forward_dist_le_one rs
    simp; rw [if_pos hleft₁, if_pos hforward₁]
  · have hleft₁ : loc (turn_left rs) ∈ blocked₁ := by
      apply hclose _ hleft₀
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
  apply next_step_unchanged_of_close_blocked_unchanged rs _ _ hss
  exact fun a amem h ↦ hclose a amem ⟨rs, rsmem, h⟩

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

-- Define a blocked list filter that removes all cells with y = -1
def blocked_trim_neg_one (blocked : List (Int × Int)) :=
  List.filter (fun (a : Int × Int) ↦ a.2 ≠ -1) blocked

-- Prove that using 'blocked_trim_neg_one' to trim the blocked list has no effect
-- on the trace if all steps in the trace have non-negative y-coordinate and
-- never face west when the y-coordinate is zero
lemma trace_trim_neg_one_unchanged (n : Nat) (start : RunState) (blocked : List (Int × Int)) :
  (∀ i (ilt : i < n),
  (fun a ↦ 0 ≤ a.y ∧ (a.y = 0 → a.u ≠ uvec_left))
  ((trace n start blocked)[i]'(by rwa [trace_length]))) →
  trace n start blocked = trace n start (blocked_trim_neg_one blocked) := by
  intro h
  let blocked' := blocked_trim_neg_one blocked
  change _ = trace n start blocked'
  have hss : blocked' ⊆ blocked :=
    fun a amem ↦ (List.mem_filter.mp amem).1
  have hss' : ∀ a ∈ blocked, 0 ≤ a.2 → a ∈ blocked' := by
    intro a amem ynn
    apply List.mem_filter.mpr ⟨amem, _⟩; simp; push_neg
    linarith
  apply List.ext_getElem
  · rw [trace_length, trace_length]
  intro i ilt ilt'
  have ilt'' : i < n := by rwa [trace_length] at ilt
  have hnnil₀ : trace n start blocked ≠ [] := by
    apply List.ne_nil_of_length_pos
    exact Nat.zero_lt_of_lt ilt
  have hnnil₁ : trace n start blocked' ≠ [] := by
    apply List.ne_nil_of_length_pos
    exact Nat.zero_lt_of_lt ilt'
  -- Handle the case where i = 0
  by_cases iz : i = 0
  · subst iz
    rw [trace_getElem_zero_of_nonnil _ _ _ hnnil₀]
    rw [trace_getElem_zero_of_nonnil _ _ _ hnnil₁]
  rename' iz => inz; push_neg at inz
  have ipos : 0 < i := Nat.pos_of_ne_zero inz
  -- Apply the trace recurrence
  rw [trace_getElem_recurrence' n start blocked i ipos ilt'']
  rw [trace_getElem_recurrence' n start blocked' i ipos ilt'']
  have iplt : i - 1 < n - 1 :=
    Nat.sub_lt_sub_right (Nat.one_le_of_lt ipos) ilt''
  -- Recurse
  have hrecurse :
    (trace (n - 1) start blocked)[i - 1]'(by rwa [trace_length]) =
    (trace (n - 1) start blocked')[i - 1]'(by rwa [trace_length]) := by
    congr 1
    apply trace_trim_neg_one_unchanged (n - 1) start blocked
    intro j jlt
    rw [getElem_congr_coll (trace_take n start blocked (n - 1) (Nat.sub_le _ _))]
    rw [List.getElem_take]
    exact h j (lt_of_lt_of_le jlt (Nat.sub_le _ _))
  -- Rewrite the recursion for the trace of length 'n'
  rw [getElem_congr_coll (trace_take n start blocked (n - 1) (Nat.sub_le _ _))] at hrecurse
  rw [getElem_congr_coll (trace_take n start blocked' (n - 1) (Nat.sub_le _ _))] at hrecurse
  rw [List.getElem_take, List.getElem_take] at hrecurse
  rw [← hrecurse]
  -- Re-state the goal for clarity
  let rs := (trace n start blocked)[i - 1]
  change next_step blocked rs = next_step blocked' rs
  -- Handle the case where the y-coordinate of 'rs' is positive
  by_cases ypos : 0 < rs.y
  · apply next_step_unchanged_of_close_blocked_unchanged rs blocked blocked' hss
    intro a amem hclose
    apply List.mem_filter.mpr ⟨amem, _⟩; simp; push_neg
    by_contra! hay
    have := Int.ofNat_le.mpr (le_of_max_le_right hclose)
    rw [← Int.natAbs_neg, Int.neg_sub, hay, Int.sub_neg] at this;
    have ysnn : 0 ≤ (loc rs).2 + 1 :=
      le_of_lt (lt_trans ypos ((lt_add_iff_pos_right _).mpr (one_pos)))
    rw [Int.natAbs_of_nonneg ysnn, Int.natCast_one] at this
    absurd Int.le_sub_right_of_add_le this; simp
    exact ypos
  rename' ypos => ynpos; push_neg at ynpos
  -- If rs.y is non-positive, it must be zero
  have yz := le_antisymm ynpos (h (i - 1) (lt_of_le_of_lt (Nat.sub_le _ _) ilt'')).1
  have hnleft : rs.u ≠ uvec_left := (h (i - 1) (lt_of_le_of_lt (Nat.sub_le _ _) ilt'')).2 yz
  have htrace : (trace n start blocked)[i] = next_step blocked rs :=
    trace_getElem_recurrence' n start blocked i ipos ilt''
  unfold next_step at htrace
  -- Finish the proof for each of the possible directions and possible steps
  -- That's 9 different cases, but I don't have any better ideas!
  split_ifs at htrace with hleft hforward
  · -- First, consider the case where the runner tries to turn right
    rcases Finset.mem_insert.mp (uvec_finset_mem rs.u) with hup | hrest
    · -- If the runner begins facing up, the 'left' and 'forward' cells
      -- both have y = 1, and so will be in both blocked lists, or neither
      unfold next_step; simp
      have hleft' : loc (turn_left rs) ∈ blocked' := by
        apply hss' _ hleft
        unfold turn_left loc; simp
        rw [hup, yz, uvec_up]; simp
      have hforward' : loc (move_forward rs) ∈ blocked' := by
        apply hss' _ hforward
        unfold move_forward loc; simp
        rw [hup, yz, uvec_up]; simp
      rw [if_pos hleft, if_pos hforward, if_pos hleft', if_pos hforward']
    rcases Finset.mem_insert.mp hrest with hdown | hrest
    · -- Show that if the runner begins facing down and
      -- turns right, it produces a prohibited state
      absurd (htrace ▸ (h i ilt'')).2; simp
      unfold turn_right uvec_left; simp
      rw [hdown]
      exact ⟨yz, rfl, rfl⟩
    have hright := Finset.mem_singleton.mp (Finset.mem_of_mem_insert_of_ne hrest hnleft)
    · -- If the runner begins facing right, the 'left' and 'forward' cells
      -- both have y ≥ 0, and so will be in both blocked lists, or neither
      unfold next_step; simp
      have hleft' : loc (turn_left rs) ∈ blocked' := by
        apply hss' _ hleft
        unfold turn_left loc; simp
        rw [hright, yz, uvec_right]; simp
      have hforward' : loc (move_forward rs) ∈ blocked' := by
        apply hss' _ hforward
        unfold move_forward loc; simp
        rw [hright, yz, uvec_right]; simp
      rw [if_pos hleft, if_pos hforward, if_pos hleft', if_pos hforward']
  · -- Next, consider the case where the runner tries to move forward
    rcases Finset.mem_insert.mp (uvec_finset_mem rs.u) with hup | hrest
    · -- If the runner begins facing up, the 'left' and 'forward' cells
      -- both have y = 1, and so will be in both blocked lists, or neither
      unfold next_step; simp
      have hleft' : loc (turn_left rs) ∈ blocked' := by
        apply hss' _ hleft
        unfold turn_left loc; simp
        rw [hup, yz, uvec_up]; simp
      have hforward' : loc (move_forward rs) ∉ blocked' :=
        fun h ↦ False.elim (hforward (hss h))
      rw [if_pos hleft, if_neg hforward, if_pos hleft', if_neg hforward']
    rcases Finset.mem_insert.mp hrest with hdown | hrest
    · -- Show that if the runner begins facing down and
      -- moves forward, it produces a prohibited state
      absurd (htrace ▸ (h i ilt'')).1; simp
      unfold move_forward
      rw [hdown, yz, uvec_down]; simp
    have hright := Finset.mem_singleton.mp (Finset.mem_of_mem_insert_of_ne hrest hnleft)
    · -- If the runner begins facing right, the 'left' and 'forward' cells
      -- both have y ≥ 0, and so will be in both blocked lists, or neither
      unfold next_step; simp
      have hleft' : loc (turn_left rs) ∈ blocked' := by
        apply hss' _ hleft
        unfold turn_left loc; simp
        rw [hright, yz, uvec_right]; simp
      have hforward' : loc (move_forward rs) ∉ blocked' :=
        fun h ↦ False.elim (hforward (hss h))
      rw [if_pos hleft, if_neg hforward, if_pos hleft', if_neg hforward']
  · -- Last, consider the case where the runner tries to turn left
    rcases Finset.mem_insert.mp (uvec_finset_mem rs.u) with hup | hrest
    · -- If the runner begins facing up, the 'left' and 'forward' cells
      -- both have y = 1, and so will be in both blocked lists, or neither
      unfold next_step; simp
      have hleft' : loc (turn_left rs) ∉ blocked' :=
        fun h ↦ False.elim (hleft (hss h))
      rw [if_neg hleft, if_neg hleft']
    rcases Finset.mem_insert.mp hrest with hdown | hrest
    · -- Show that if the runner begins facing down and
      -- turns left, it produces a prohibited state
      absurd (htrace ▸ (h i ilt'')).1; simp
      unfold turn_left; simp
      rw [hdown, yz, uvec_down]; simp
    have hright := Finset.mem_singleton.mp (Finset.mem_of_mem_insert_of_ne hrest hnleft)
    · -- If the runner begins facing right, the 'left' and 'forward' cells
      -- both have y ≥ 0, and so will be in both blocked lists, or neither
      unfold next_step; simp
      have hleft' : loc (turn_left rs) ∉ blocked' :=
        fun h ↦ False.elim (hleft (hss h))
      rw [if_neg hleft, if_neg hleft']

-- I tried getting List.max? to work, but it was more effort than just writing
-- out the 18 lines of code below
def list_int_max (L : List Int) : Int :=
  match L with
  | []      => 0
  | x :: xs => max x (list_int_max xs)

lemma list_int_max_cons (a : Int) (L : List Int) :
  list_int_max (a :: L) = max a (list_int_max L) := rfl

lemma list_int_le_max (L : List Int) :
  ∀ a ∈ L, a ≤ list_int_max L :=
  match L with
  | []      => fun _ amem ↦ False.elim (List.not_mem_nil amem)
  | x :: xs => by
    intro a amem
    rw [list_int_max_cons]
    rcases List.mem_cons.mp amem with rfl | rhs
    · exact Int.le_max_left _ _
    · exact le_max_of_le_right (list_int_le_max xs a rhs)

-- Blocked list filter that only keeps cells with -1 ≤ x, 0 ≤ y, y ≤ top, and
-- x-coordinate less than or equal to one more than the maximum x coordinate in the trace
-- To construct the final blocked list, this filter will be used with 'top' chosen
-- to match the height of the west wall.
def blocked_trim_quad1
  (n : Nat) (start : RunState) (blocked : List (Int × Int)) (top : Int) : List (Int × Int) :=
  blocked_trim_neg_one (blocked_trim_rect top (-1) (-1)
    (list_int_max (List.map (fun a ↦ a.x) (trace n start blocked)) + 1) blocked)

-- Prove the conditions under which the trace is unchanged by 'blocked_trim_quad1'
lemma trace_trim_quad1_unchanged
  (n : Nat) (start : RunState) (blocked : List (Int × Int)) (top : Int) :
  (∀ rs ∈ trace n start blocked,
  0 ≤ rs.x ∧ 0 ≤ rs.y ∧ rs.y < top ∧ (rs.y = 0 → rs.u ≠ uvec_left)) →
  trace n start blocked = trace n start (blocked_trim_quad1 n start blocked top) := by
  intro h
  -- Prove that the bounds for the rectangular filter follow from the givens
  have hbounds : ∀ (i : ℕ) (ilt : i < n),
    (fun a ↦ a.y < top ∧ -1 < a.y ∧ -1 < a.x ∧
     a.x < list_int_max (List.map (fun a ↦ a.x) (trace n start blocked)) + 1)
    ((trace n start blocked)[i]'(by rwa [trace_length])) := by
    intro i ilt
    constructor
    · exact (h _ (List.getElem_mem _)).2.2.1
    constructor
    · apply Int.lt_of_sub_pos; simp
      apply Int.lt_add_one_of_le
      exact (h _ (List.getElem_mem _)).2.1
    constructor
    · apply Int.lt_of_sub_pos; simp
      apply Int.lt_add_one_of_le
      exact (h _ (List.getElem_mem _)).1
    · apply Int.lt_add_one_of_le
      apply list_int_le_max
      apply List.mem_map.mpr
      exact ⟨_, List.getElem_mem _, rfl⟩
  unfold blocked_trim_quad1
  rw [← trace_trim_neg_one_unchanged]
  · rwa [← trace_trim_rect_unchanged]
  intro i ilt
  -- Reorder / repackage the bounds for the y = -1 filter
  have h' : ∀ rs ∈ trace n start blocked, 0 ≤ rs.y ∧ (rs.y = 0 → rs.u ≠ uvec_left) :=
    fun rs rsmem ↦ ⟨(h rs rsmem).2.1, (h rs rsmem).2.2.2⟩
  apply h'
  convert List.getElem_mem _ using 2; swap
  · rwa [trace_length]
  rwa [← trace_trim_rect_unchanged]

-- Applying the "quad1" filter to a blocked list can only shorten it
lemma trace_trim_quad1_length_le
  (n : Nat) (start : RunState) (blocked : List (Int × Int)) (top : Int) :
  (blocked_trim_quad1 n start blocked top).length ≤ blocked.length :=
  le_trans (List.length_filter_le _ _) (List.length_filter_le _ _)

-- Prove the conditions under which an element of 'blocked' is still
-- in the list after the "quad1" filter is applied
lemma trace_trim_quad1_mem
  (n : Nat) (start : RunState) (blocked : List (Int × Int)) (top : Int) :
  ∀ a ∈ blocked, 0 ≤ a.2 ∧ a.2 ≤ top ∧ -1 ≤ a.1 ∧
  (∃ rs ∈ trace n start blocked, a.1 ≤ (loc rs).1 + 1) →
  a ∈ blocked_trim_quad1 n start blocked top := by
  intro a amem ⟨ley, yle, lex, exle⟩
  apply List.mem_filter.mpr ⟨_, (by simp; linarith)⟩
  apply List.mem_filter.mpr ⟨amem, _⟩; simp
  use yle, le_trans (by norm_num) ley, lex
  rcases exle with ⟨rs, rsmem, hrs⟩
  apply Int.le_add_of_sub_right_le (le_trans (Int.sub_right_le_of_le_add hrs) _)
  apply list_int_le_max
  rw [List.mem_map]
  use rs, rsmem; rfl

-- If a cell was not in the original blocked list, it also will not
-- be in the list that results from applying the "quad1" filter.
lemma trace_trim_quad1_notmem_of_notmem
  (n : Nat) (start : RunState) (blocked : List (Int × Int)) (top : Int) :
  ∀ a, a ∉ blocked → a ∉ blocked_trim_quad1 n start blocked top := by
  intro a amem
  contrapose! amem
  exact (List.mem_filter.mp (List.mem_filter.mp amem).1).1

-- If a cell has y-coordinate less than zero, it will not be in
-- the blocked list that results from applying the "quad1" filter.
lemma trace_trim_quad1_notmem_of_yneg
  (n : Nat) (start : RunState) (blocked : List (Int × Int)) (top : Int) :
  ∀ a, a.2 < 0 → a ∉ blocked_trim_quad1 n start blocked top := by
  intro a aylt amem
  have ayne : a.2 ≠ -1 := by
    have := (List.mem_filter.mp amem).2
    simp at this; push_neg at this
    assumption
  have aylt' : a.2 < -1 := by
    apply lt_of_le_of_ne _ ayne
    linarith
  absurd aylt'; push_neg
  have := (List.mem_filter.mp (List.mem_filter.mp amem).1).2
  simp at this
  exact this.2.1

lemma trace_trim_quad1_notmem_of_xlt
  (n : Nat) (start : RunState) (blocked : List (Int × Int)) (top : Int) :
  ∀ a, a.1 < -1 → a ∉ blocked_trim_quad1 n start blocked top := by
  intro a aylt amem
  absurd aylt; push_neg
  have := (List.mem_filter.mp (List.mem_filter.mp amem).1).2; simp at this
  exact this.2.2.1
