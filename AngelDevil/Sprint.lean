import Mathlib.Tactic.NormNum.Core
import Mathlib.Tactic.Contrapose
import AngelDevil.Basic
import AngelDevil.Util
import AngelDevil.Trace

set_option linter.style.longLine false

abbrev sprint_end_fun (p : Nat) (start : RunState) (blocked : List (Int × Int)) :
  Fin (2 * p + 1) → Prop := fun i ↦ ¬close p (loc start) (loc ((trace (2 * p + 1) start blocked)[i]'(by
    rw [trace_length]
    exact i.2
  )))

-- Define a "sprint" as the trace with length no greater than '2p+1' for which every
-- cell in the trace is "close" to the start.
-- Note that the paper describes what I have formalized as a "sprint" as having cells
-- v[0], v[1], v[2], ..., v[n], where n ≤ 2p. That means each sprint can have a maximum
-- length of 2p + 1 (not just '2p', as I had mistakenly stated previously).
def sprint (p : Nat) (start : RunState) (blocked : List (Int × Int)) : List RunState :=
  trace (if (∃ rs : RunState, rs ∈ trace (2 * p + 1) start blocked ∧ ¬close p (loc start) (loc rs)) then
  (_find_first (sprint_end_fun p start blocked)) else (2 * p + 1)) start blocked

lemma sprint_getElem_zero_of_nonnil (p : Nat) (start : RunState) (blocked : List (Int × Int)) :
  (hnnil : sprint p start blocked ≠ []) →
  (sprint p start blocked)[0]'(List.length_pos_iff.mpr hnnil) = start := by
  intro hnnil
  unfold sprint
  apply trace_getElem_zero_of_nonnil
  exact hnnil

lemma sprint_nonnil (p : Nat) (start : RunState) (blocked : List (Int × Int)) :
  sprint p start blocked ≠ [] := by
  apply List.ne_nil_of_length_pos (Nat.pos_of_ne_zero _)
  rw [sprint, trace_length]
  split_ifs with h
  · rcases h with ⟨rs, rsmem, hfar⟩
    intro hfind
    have : sprint_end_fun p start blocked 0 := by
      rw [← Fin.val_eq_zero_iff.mp hfind]
      apply _find_first_is_sat
      rcases List.getElem_of_mem rsmem with ⟨i, ilt, hirs⟩
      let i' : Fin (2 * p + 1) := ⟨i, by rwa [trace_length] at ilt⟩
      use i'
      unfold sprint_end_fun
      rw [← hirs] at hfar
      exact hfar
    apply this
    convert close_self _ _
    apply trace_getElem_zero_of_nonnil
    apply List.ne_nil_of_length_pos
    rw [trace_length]
    exact Nat.add_one_pos _
  · exact Nat.add_one_ne_zero _

lemma sprint_getElem_zero (p : Nat) (start : RunState) (blocked : List (Int × Int)) :
  (sprint p start blocked)[0]'(by
    apply List.length_pos_of_ne_nil
    exact sprint_nonnil p start blocked
  ) = start :=
  sprint_getElem_zero_of_nonnil p start blocked (sprint_nonnil p start blocked)

-- The maximum sprint length is 2 * p + 1
lemma sprint_length_le (p : Nat) (start : RunState) (blocked : List (Int × Int)) :
  (sprint p start blocked).length ≤ 2 * p + 1 := by
  unfold sprint
  rw [trace_length]
  split_ifs with h; swap
  · exact le_refl _
  rcases h with ⟨rs, hmem, hnclose⟩
  rcases List.getElem_of_mem hmem with ⟨i, ilt, hirs⟩
  apply le_of_lt (lt_of_lt_of_le (Fin.prop _) _)
  exact le_refl _

-- The minimum sprint length is p+1
lemma sprint_length_lb (p : Nat) (start : RunState) (blocked : List (Int × Int)) :
  p < (sprint p start blocked).length := by
  unfold sprint
  -- This hypothesis is easier to work with than the final goal
  have : ∀ (i : Fin (2 * p + 1)), i.val ≤ p →
    ¬sprint_end_fun p start blocked i := by
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
    have ilt' : i < 2 * p + 1 := by
      rwa [trace_length] at ilt
    let i' : Fin (2 * p + 1) := ⟨i, ilt'⟩
    use i'
    convert h
  · linarith

-- Each run state in a sprint is equal to the corresponding element of the corresponding trace
lemma sprint_getElem_eq_trace_getElem (p : Nat) (start : RunState) (blocked : List (Int × Int)) :
  ∀ i (ilt : i < (sprint p start blocked).length),
  (sprint p start blocked)[i] = (trace (2 * p + 1) start blocked)[i]'(by
    rw [trace_length]
    exact lt_of_lt_of_le ilt (sprint_length_le p start blocked)
  ) := by
  intro i ilt
  have twoppos : 0 < (2 * p + 1) := by
    apply lt_of_le_of_lt (Nat.zero_le _)
    exact (lt_of_lt_of_le ilt (sprint_length_le p start blocked))
  unfold sprint
  split_ifs with h
  · rw [getElem_congr_coll (trace_take (2 * p + 1) start blocked _ _)]; swap
    · exact le_of_lt (Fin.prop _)
    apply List.getElem_take
  rfl

-- All run states in a sprint are close to the start of that sprint
lemma sprint_close_mem_head (p : Nat) (start : RunState) (blocked : List (Int × Int)) :
  ∀ x ∈ (sprint p start blocked), close p (loc x)
  (loc ((sprint p start blocked).head (sprint_nonnil p start blocked))) := by
  intro x hmem
  rw [← List.getElem_zero_eq_head]; swap
  · exact List.length_pos_of_mem hmem
  rw [sprint_getElem_zero_of_nonnil, close_comm]; swap
  · exact List.ne_nil_of_mem hmem
  rcases List.getElem_of_mem hmem with ⟨i, ilt, rfl⟩
  rw [sprint_getElem_eq_trace_getElem p start blocked i ilt]
  by_contra! h
  have ilt' := lt_of_lt_of_le ilt (sprint_length_le p start blocked)
  let i' : Fin (2 * p + 1) := ⟨i, lt_of_lt_of_eq ilt' (Nat.sub_one_add_one (Nat.ne_zero_of_lt ilt')).symm⟩
  unfold sprint at ilt
  have hthen : ∃ rs ∈ trace (2 * p + 1) start blocked, ¬close p (loc start) (loc rs) := by
    use (trace (2 * p + 1) start blocked)[i]'(by rwa [trace_length])
    use List.getElem_mem (by rwa [trace_length])
  rw [if_pos hthen, trace_length] at ilt
  have := _find_first_is_first (sprint_end_fun p start blocked) i' h
  exact Nat.not_lt.mpr this ilt

-- Prove that the first and last cells in a sprint are "close"
lemma sprint_close_first_last (p : Nat) (start : RunState) (blocked : List (Int × Int)) :
  close p
  (loc ((sprint p start blocked).head (sprint_nonnil p start blocked)))
  (loc ((sprint p start blocked).getLast (sprint_nonnil p start blocked))) := by
  have hnnil := sprint_nonnil p start blocked
  rw [close_comm]
  exact sprint_close_mem_head p start blocked _ (List.getLast_mem hnnil)

-- The runner never visits an eaten cell
-- (as long as they don't start on an eaten cell)
lemma sprint_avoids_blocked (p : Nat) (start : RunState)
  (blocked : List (Int × Int)) (hsafe : loc start ∉ blocked) :
  ∀ x, x ∈ (sprint p start blocked) → loc x ∉ blocked := by
  intro x hmem₀ hmem₁
  unfold sprint at hmem₀
  split_ifs at hmem₀ with h
  repeat exact trace_avoids_blocked _ start blocked hsafe x hmem₀ hmem₁

-- If two different block lists produce the same trace for
-- every distance, then the corresponding sprints are equal.
lemma sprints_match_of_traces_match
  (p : Nat) (start : RunState) (blocked₀ blocked₁ : List (Int × Int)) :
  (∀ n, trace n start blocked₀ = trace n start blocked₁) →
  sprint p start blocked₀ = sprint p start blocked₁ := by
  intro htraces
  have htrace := htraces (2 * p + 1)
  unfold sprint
  by_cases h₀ : ∃ rs ∈ trace (2 * p + 1) start blocked₀, ¬close p (loc start) (loc rs)
  · rw [if_pos h₀]
    let h₀tmp := h₀
    rcases h₀tmp with ⟨rs, rsmem, hfar⟩
    have h₁ : ∃ rs ∈ trace (2 * p + 1) start blocked₁, ¬close p (loc start) (loc rs) :=
      ⟨rs, htrace ▸ rsmem, hfar⟩
    rw [if_pos h₁]
    convert htraces _ using 2
    apply (Fin.val_eq_val _ _).mpr
    congr; ext i
    unfold sprint_end_fun
    constructor
    repeat
    · rw [getElem_congr_coll htrace]
      exact id
  · rw [if_neg h₀]
    have h₁ : ¬∃ rs ∈ trace (2 * p + 1) start blocked₁, ¬close p (loc start) (loc rs) := by
      push_neg at *
      intro rs rsmem
      rw [← htrace] at rsmem
      exact h₀ rs rsmem
    rw [if_neg h₁]
    exact htrace
