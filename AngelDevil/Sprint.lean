import Mathlib.Tactic.NormNum.Core
import Mathlib.Tactic.Contrapose
import AngelDevil.Basic
import AngelDevil.Util
import AngelDevil.Trace

set_option linter.style.longLine false

-- A useful equivalence for the following definitions / lemmas
lemma sprint_fin_prop (p : Nat) (start : RunState) (blocked : List (Int × Int)) (ppos : 0 < p) :
  ∀ i, i < (trace (2 * p) start blocked).length ↔ i < 2 * p - 1 + 1 := by
  intro i
  constructor
  · intro h
    rw [Nat.sub_one_add_one]; swap
    · apply Nat.ne_zero_of_lt
      exact (Nat.mul_lt_mul_left (two_pos)).mpr ppos
    rwa [trace_length] at h
  · intro h
    rw [trace_length]
    rwa [Nat.sub_one_add_one] at h
    apply Nat.ne_zero_iff_zero_lt.mpr
    exact Nat.mul_pos two_pos ppos

abbrev sprint_end_fun (p : Nat) (start : RunState) (blocked : List (Int × Int)) (ppos : 0 < p) :
  Fin (2 * p - 1 + 1) → Prop := fun i ↦ ¬close p (loc start) (loc ((trace (2 * p) start blocked)[i]'(by
    rw [sprint_fin_prop]
    · exact i.2
    · assumption
  )))

-- Define a "sprint" as the trace with length no greater than '2p' for which every
-- cell in the trace is "close" to the start.
def sprint (p : Nat) (start : RunState) (blocked : List (Int × Int)) : List RunState :=
  trace (if h : (∃ rs : RunState, rs ∈ trace (2 * p) start blocked ∧ ¬close p (loc start) (loc rs)) then
  (_find_first (sprint_end_fun p start blocked (by
    rcases h with ⟨rs, h₀, h₁⟩
    have ppos := List.length_pos_of_mem h₀
    rw [trace_length] at ppos
    exact Nat.pos_of_mul_pos_left ppos
  ))) else (2 * p)) start blocked

lemma sprint_getElem_zero_of_nonnil (p : Nat) (start : RunState) (blocked : List (Int × Int)) :
  (hnnil : sprint p start blocked ≠ []) →
  (sprint p start blocked)[0]'(List.length_pos_iff.mpr hnnil) = start := by
  intro hnnil
  unfold sprint
  apply trace_getElem_zero_of_nonnil
  exact hnnil

-- If 'p' is positive, the sprint will not be empty
lemma sprint_nonnil_of_ppos (p : Nat) (start : RunState) (blocked : List (Int × Int)) :
  0 < p → sprint p start blocked ≠ [] := by
  intro ppos
  apply List.ne_nil_of_length_pos
  rw [sprint, trace_length]
  split_ifs with h
  · rcases h with ⟨rs, h₀, h₁⟩
    apply Nat.pos_of_ne_zero
    intro hfind
    have : sprint_end_fun p start blocked ppos 0 := by
      rw [← Fin.val_eq_zero_iff.mp hfind]
      apply _find_first_is_sat
      rcases List.getElem_of_mem h₀ with ⟨i, ilt, hirs⟩
      let i' : Fin (2 * p - 1 + 1) := ⟨i, (sprint_fin_prop p start blocked ppos i).mp ilt⟩
      use i'
      unfold sprint_end_fun
      rw [← hirs] at h₁
      exact h₁
    apply this
    convert close_self p (loc start)
    apply trace_getElem_zero_of_nonnil
    apply List.ne_nil_of_length_pos
    rw [trace_length]
    exact Nat.mul_pos two_pos ppos
  exact Nat.mul_pos (by norm_num) ppos

lemma sprint_getElem_zero_of_ppos (p : Nat) (start : RunState) (blocked : List (Int × Int)) :
  (ppos : 0 < p) → (sprint p start blocked)[0]'(by
    apply List.length_pos_of_ne_nil
    exact sprint_nonnil_of_ppos p start blocked ppos
  ) = start :=
  fun ppos ↦
  sprint_getElem_zero_of_nonnil p start blocked (sprint_nonnil_of_ppos p start blocked ppos)

-- The maximum sprint length is 2 * p
lemma sprint_length_le (p : Nat) (start : RunState) (blocked : List (Int × Int)) :
  (sprint p start blocked).length ≤ 2 * p := by
  unfold sprint
  rw [trace_length]
  split_ifs with h; swap
  · rfl
  rcases h with ⟨rs, hmem, hnclose⟩
  rcases List.getElem_of_mem hmem with ⟨i, ilt, hirs⟩
  apply le_of_lt (lt_of_lt_of_le (Fin.prop _) _)
  rw [Nat.sub_one_add_one]
  rw [trace_length] at ilt
  apply Nat.ne_zero_of_lt ilt

-- The minimum sprint length is p+1
lemma sprint_length_lb (p : Nat) (start : RunState) (blocked : List (Int × Int)) (ppos : 0 < p) :
  p < (sprint p start blocked).length := by
  unfold sprint
  -- This hypothesis is easier to work with than the final goal
  have : ∀ (i : Fin (2 * p - 1 + 1)), i.val ≤ p →
    ¬sprint_end_fun p start blocked ppos i := by
    intro i ile
    unfold sprint_end_fun; push_neg
    rw [Fin.getElem_fin, trace_getElem_getLast]
    exact le_trans (trace_getLast_close (i.val + 1) (Nat.add_one_pos _) start blocked) ile
  split_ifs with h <;> rw [trace_length]
  · by_contra! ltp
    apply this _ ltp
    -- '_find_first_is_sat' completes the goal, but we still need to show
    -- that there exists at least one cell in the trace which is not close
    apply _find_first_is_sat
    rcases h with ⟨rs, rsmem, h⟩
    rcases List.getElem_of_mem rsmem with ⟨i, ilt, hirs⟩
    have ilt' : i < 2 * p - 1 + 1 := by
      rw [trace_length] at ilt
      rwa [Nat.sub_one_add_one]
      apply Nat.mul_ne_zero (by norm_num)
      exact Nat.ne_zero_of_lt ppos
    let i' : Fin (2 * p - 1 + 1) := ⟨i, ilt'⟩
    use i'
    convert h
  · linarith

-- Each run state in a sprint is equal to the corresponding element of the corresponding trace
lemma sprint_getElem_eq_trace_getElem (p : Nat) (start : RunState) (blocked : List (Int × Int)) :
  ∀ i (ilt : i < (sprint p start blocked).length),
  (sprint p start blocked)[i] = (trace (2 * p) start blocked)[i]'(by
    rw [trace_length]
    exact lt_of_lt_of_le ilt (sprint_length_le p start blocked)
  ) := by
  intro i ilt
  have twoppos : 0 < (2 * p) := by
    apply lt_of_le_of_lt (Nat.zero_le _)
    exact (lt_of_lt_of_le ilt (sprint_length_le p start blocked))
  unfold sprint
  split_ifs with h
  · rw [getElem_congr_coll (trace_take (2 * p) start blocked _ _)]; swap
    · apply le_of_lt
      nth_rw 14 [← Nat.sub_one_add_one (Nat.ne_zero_of_lt twoppos)]
      exact Fin.prop _
    apply List.getElem_take
  rfl

-- All run states in a sprint are close to the start of that sprint
lemma sprint_close_mem_head (p : Nat) (ppos : 0 < p) (start : RunState) (blocked : List (Int × Int)) :
  ∀ x ∈ (sprint p start blocked), close p (loc x)
  (loc ((sprint p start blocked).head (sprint_nonnil_of_ppos p start blocked ppos))) := by
  intro x hmem
  rw [← List.getElem_zero_eq_head]; swap
  · exact List.length_pos_of_mem hmem
  rw [sprint_getElem_zero_of_nonnil, close_comm]; swap
  · exact List.ne_nil_of_mem hmem
  rcases List.getElem_of_mem hmem with ⟨i, ilt, rfl⟩
  rw [sprint_getElem_eq_trace_getElem p start blocked i ilt]
  by_contra! h
  have ilt' := lt_of_lt_of_le ilt (sprint_length_le p start blocked)
  have ppos : 0 < p := by
    apply (Nat.mul_lt_mul_left (two_pos)).mp
    rw [mul_zero]
    exact lt_of_le_of_lt (Nat.zero_le _) ilt'
  let i' : Fin (2 * p - 1 + 1) := ⟨i, lt_of_lt_of_eq ilt' (Nat.sub_one_add_one (Nat.ne_zero_of_lt ilt')).symm⟩
  unfold sprint at ilt
  have hthen : ∃ rs ∈ trace (2 * p) start blocked, ¬close p (loc start) (loc rs) := by
    use (trace (2 * p) start blocked)[i]'(by rwa [trace_length])
    use List.getElem_mem (by rwa [trace_length])
  rw [dif_pos hthen, trace_length] at ilt
  have := _find_first_is_first (sprint_end_fun p start blocked ppos) i' h
  exact Nat.not_lt.mpr this ilt

-- Prove that the first and last cells in a sprint are "close"
lemma sprint_close_first_last (p : Nat) (hpos : 0 < p) (start : RunState) (blocked : List (Int × Int)) :
  close p
  (loc ((sprint p start blocked).head (sprint_nonnil_of_ppos p start blocked hpos)))
  (loc ((sprint p start blocked).getLast (sprint_nonnil_of_ppos p start blocked hpos))) := by
  have hnnil := sprint_nonnil_of_ppos p start blocked hpos
  rw [close_comm]
  exact sprint_close_mem_head p hpos start blocked _ (List.getLast_mem hnnil)

-- The runner never visits an eaten cell
-- (as long as they don't start on an eaten cell)
lemma sprint_avoids_blocked (p : Nat) (start : RunState)
  (blocked : List (Int × Int)) (hsafe : loc start ∉ blocked) :
  ∀ x, x ∈ (sprint p start blocked) → loc x ∉ blocked := by
  intro x hmem₀ hmem₁
  unfold sprint at hmem₀
  split_ifs at hmem₀ with h
  repeat exact trace_avoids_blocked _ start blocked hsafe x hmem₀ hmem₁
