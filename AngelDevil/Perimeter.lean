import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import AngelDevil.Trace
import AngelDevil.Region

set_option linter.style.longLine false

-- An edge will be defined as a pair of cells, one which
-- appears inside a region, and the other which appears outside.
-- Note that this constraint is not bundled in the structure but
-- will hold for any edge found by 'get_edges' (see below).
@[ext] structure Edge where
  _in : (Int × Int)
  _out : (Int × Int)
  hadj : adjacent _in _out

-- Prove that we can determine whether two edges are equal
instance : DecidableEq Edge := fun a b ↦
  if h : a._in = b._in ∧ a._out = b._out then
    isTrue (Edge.ext_iff.mpr h)
  else
    isFalse (fun h' ↦ h (Edge.ext_iff.mp h'))

-- Make an edge with 'c' and the cell to its left
def mk_edge_left (c : Int × Int) : Edge where
  _in := c
  _out := left c
  hadj := (adjacent_comm _ _).mp (left_adjacent c)

-- Make an edge with 'c' and the cell to its right
def mk_edge_right (c : Int × Int) : Edge where
  _in := c
  _out := right c
  hadj := (adjacent_comm _ _).mp (right_adjacent c)

-- Make an edge with 'c' and the cell above it
def mk_edge_up (c : Int × Int) : Edge where
  _in := c
  _out := up c
  hadj := (adjacent_comm _ _).mp (up_adjacent c)

-- Make an edge with 'c' and the cell below it
def mk_edge_down (c : Int × Int) : Edge where
  _in := c
  _out := down c
  hadj := (adjacent_comm _ _).mp (down_adjacent c)

lemma edge_up_eq (c : Int × Int) :
  mk_edge_up c = ⟨c, up c, (mk_edge_up c).hadj⟩ := rfl

lemma edge_down_eq (c : Int × Int) :
  mk_edge_down c = ⟨c, down c, (mk_edge_down c).hadj⟩ := rfl

lemma edge_right_eq (c : Int × Int) :
  mk_edge_right c = ⟨c, right c, (mk_edge_right c).hadj⟩ := rfl

lemma edge_left_eq (c : Int × Int) :
  mk_edge_left c = ⟨c, left c, (mk_edge_left c).hadj⟩ := rfl

lemma edge_up_ne_edge_down (c : Int × Int) :
  mk_edge_up c ≠ mk_edge_down c :=
  fun h ↦ up_ne_down c (Edge.ext_iff.mp h).2

lemma edge_up_ne_edge_left (c : Int × Int) :
  mk_edge_up c ≠ mk_edge_left c :=
  fun h ↦ up_ne_left c (Edge.ext_iff.mp h).2

lemma edge_up_ne_edge_right (c : Int × Int) :
  mk_edge_up c ≠ mk_edge_right c :=
  fun h ↦ up_ne_right c (Edge.ext_iff.mp h).2

lemma edge_down_ne_edge_left (c : Int × Int) :
  mk_edge_down c ≠ mk_edge_left c :=
  fun h ↦ down_ne_left c (Edge.ext_iff.mp h).2

lemma edge_down_ne_edge_right (c : Int × Int) :
  mk_edge_down c ≠ mk_edge_right c :=
  fun h ↦ down_ne_right c (Edge.ext_iff.mp h).2

lemma edge_left_ne_edge_right (c : Int × Int) :
  mk_edge_left c ≠ mk_edge_right c :=
  fun h ↦ left_ne_right c (Edge.ext_iff.mp h).2

-- Swap the cell considered 'in' and the cell considered 'out
-- Typically this will be used to indicate that a pair of cells
-- is *not* an edge.
def edge_flip (e : Edge) : Edge where
  _in := e._out
  _out := e._in
  hadj := (adjacent_comm _ _).mp e.hadj

def get_cell_edges (c : Int × Int) : Finset Edge :=
  {(mk_edge_up c), (mk_edge_down c), (mk_edge_left c), (mk_edge_right c)}

def get_cell_antiedges (c : Int × Int) : Finset Edge :=
  Finset.image edge_flip (get_cell_edges c)

-- Find all edges such that _in ∈ L and _out ∉ L
def get_edges (S : Finset (Int × Int)) : Finset Edge :=
  (S.biUnion get_cell_edges) \ (S.biUnion get_cell_antiedges)

lemma edge_flip_in (e : Edge) : (edge_flip e)._in = e._out := rfl

lemma edge_flip_out (e : Edge) : (edge_flip e)._out = e._in := rfl

lemma edge_flip_flip (e : Edge) : edge_flip (edge_flip e) = e := rfl

-- An edge is on a particular cell, if-and-only-if it is one of four possible edges
lemma cell_edges_mem_iff (c : Int × Int) (e : Edge) :
  e ∈ get_cell_edges c ↔
  e = mk_edge_up c ∨ e = mk_edge_down c ∨ e = mk_edge_left c ∨ e = mk_edge_right c := by
  constructor
  · intro emem
    repeat apply Or.elim (Finset.mem_insert.mp emem) (fun h ↦ Or.inl h); intro emem; right
    exact Finset.mem_singleton.mp emem
  · intro h
    repeat apply Finset.mem_insert.mpr (Or.elim h (fun h ↦ Or.inl h) _); intro h; right
    exact Finset.mem_singleton.mpr h

-- An edge is an edge of 'c' if-and-only-if c is its "in" cell
lemma cell_edges_mem_iff' (c : Int × Int) :
  ∀ e, e ∈ get_cell_edges c ↔ e._in = c := by
  intro e
  constructor
  · intro h
    repeat apply Or.elim (Finset.mem_insert.mp h) (fun hec ↦ by rw [hec]; rfl); intro h
    rw [Finset.mem_singleton.mp h]; rfl
  · intro h
    have he : e = ⟨c, e._out, h ▸ e.hadj⟩ := by
      apply Edge.ext <;> dsimp
      assumption
    rw [he]
    apply (cell_edges_mem_iff _ _).mpr
    rcases h ▸ e.hadj with h₀ | h₁ | h₂ | h₃
    · rw [edge_up_eq]; left; symm; congr
    · rw [edge_down_eq]; right; left; symm; congr
    · rw [edge_left_eq]; right; right; left; symm; congr
    · rw [edge_right_eq]; right; right; right; symm; congr

-- If a flipped edge is an edge of 'c', the the original edge is an anti-edge of 'c'
lemma cell_antiedges_mem_iff (c : Int × Int) :
  ∀ e, e ∈ get_cell_antiedges c ↔ edge_flip e ∈ get_cell_edges c := by
  intro e
  constructor
  · intro emem
    unfold get_cell_antiedges at emem
    rcases Finset.mem_image.mp emem with ⟨e', e'mem, rfl⟩
    rwa [edge_flip_flip]
  · intro emem
    apply Finset.mem_image.mpr
    use edge_flip e, emem
    rw [edge_flip_flip]

-- The sets of edges and antiedges are disjoint
lemma cell_edges_antiedges_disjoint (c : Int × Int) :
  Disjoint (get_cell_edges c) (get_cell_antiedges c) := by
  apply Finset.disjoint_iff_inter_eq_empty.mpr
  ext e; constructor
  · intro h
    rcases Finset.mem_inter.mp h with ⟨emem₀, emem₁⟩
    rw [cell_edges_mem_iff'] at emem₀
    rw [cell_antiedges_mem_iff, cell_edges_mem_iff', edge_flip_in] at emem₁
    exact False.elim ((adjacent_ne _ _ e.hadj) (emem₁ ▸ emem₀))
  · exact fun h ↦ False.elim (Finset.notMem_empty _ h)

lemma cell_edges_antiedges_sdiff (c : Int × Int) :
  (get_cell_edges c) \ (get_cell_antiedges c) = get_cell_edges c :=
  Finset.sdiff_eq_self_of_disjoint (cell_edges_antiedges_disjoint c)

-- Prove that the edges returned by 'get_edges' actually match our expectations
lemma get_edges_mem_iff (S : Finset (Int × Int)) :
  ∀ (e : Edge), e ∈ (get_edges S) ↔ e._in ∈ S ∧ e._out ∉ S := by
  intro e
  unfold get_edges
  constructor
  · intro emem
    rcases Finset.mem_sdiff.mp emem with ⟨emem, enmem⟩
    rcases Finset.mem_biUnion.mp emem with ⟨c, cmem, hec⟩
    rw [(cell_edges_mem_iff' _ _).mp hec]; use cmem
    contrapose! enmem; rename' enmem => outmem
    apply Finset.mem_biUnion.mpr
    use e._out, outmem
    rw [cell_antiedges_mem_iff, ← edge_flip_in, cell_edges_mem_iff']
  · intro ⟨emem, enmem⟩
    apply Finset.mem_sdiff.mpr
    · constructor
      · apply Finset.mem_biUnion.mpr
        use e._in, emem
        rw [cell_edges_mem_iff']
      · contrapose! enmem; rename' enmem => emem'
        rcases Finset.mem_biUnion.mp emem' with ⟨c, cmem, emem''⟩
        rw [cell_antiedges_mem_iff, cell_edges_mem_iff', edge_flip_in] at emem''
        rwa [emem'']

lemma get_edges_singleton (c : Int × Int) :
  get_edges {c} = get_cell_edges c := by
  unfold get_edges
  rw [Finset.singleton_biUnion, Finset.singleton_biUnion]
  apply Finset.sdiff_eq_self_of_disjoint
  exact cell_edges_antiedges_disjoint _

-- To show that the set of edges of a single cell has four elements
-- we need to show that each pair of elements is non-equal.
lemma get_edges_singleton_card (c : Int × Int) :
  (get_edges {c}).card = 4 := by
  rw [get_edges_singleton]
  unfold get_cell_edges
  rw [Finset.card_insert_of_notMem]; swap
  · intro h
    apply Or.elim (Finset.mem_insert.mp h) (fun h' ↦ edge_up_ne_edge_down _ h'); intro h
    apply Or.elim (Finset.mem_insert.mp h) (fun h' ↦ edge_up_ne_edge_left _ h'); intro h
    exact edge_up_ne_edge_right _ (Finset.mem_singleton.mp h)
  rw [Finset.card_insert_of_notMem]; swap
  · intro h
    apply Or.elim (Finset.mem_insert.mp h) (fun h' ↦ edge_down_ne_edge_left _ h'); intro h
    exact edge_down_ne_edge_right _ (Finset.mem_singleton.mp h)
  rw [Finset.card_insert_of_notMem]; swap
  · intro h
    exact edge_left_ne_edge_right _ (Finset.mem_singleton.mp h)
  rw [Finset.card_singleton]

-- Useful rewrite for the proof below
lemma edge_flip_biUnion_edges (S : Finset (Int × Int)) :
  Finset.image edge_flip (S.biUnion get_cell_edges) = S.biUnion get_cell_antiedges := by
  rw [Finset.biUnion_image]; rfl

-- Useful rewrite for the proof below
lemma edge_flip_biUnion_antiedges (S : Finset (Int × Int)) :
  Finset.image edge_flip (S.biUnion get_cell_antiedges) = S.biUnion get_cell_edges := by
  unfold get_cell_antiedges
  rw [Finset.biUnion_image]; congr; ext c e
  constructor
  · intro emem; convert emem
    rw [Finset.image_image]; symm
    -- Explicit arguments are required to get Lean to find 'DecidableEq Edge'
    convert @Finset.image_id Edge (get_cell_edges c) _
  · intro emem; convert emem
    rw [Finset.image_image]
    -- Explicit arguments are required to get Lean to find 'DecidableEq Edge'
    convert @Finset.image_id Edge (get_cell_edges c) _

-- Prove some useful theorems for working with set difference.
lemma finset_sdiff_union (S T U : Finset Edge) : S \ (T ∪ U) = (S \ T) \ U := by
  ext x
  repeat rw [Finset.mem_sdiff]
  rw [and_assoc, Finset.mem_union]; push_neg
  rfl

lemma finset_sdiff_sdiff_sdiff_cancel (S T : Finset Edge) :
  (S \ T) \ (T \ S) = S \ T := by
  ext x
  repeat rw [Finset.mem_sdiff]
  push_neg
  rw [and_assoc, imp_iff_not_or, and_or_left, and_self, and_or_left]
  nth_rw 3 [and_comm]
  rw [← and_assoc, and_self, or_self]

lemma finset_sdiff_sdiff_disjoint_right (S T U : Finset Edge) (hdisj : Disjoint S U) :
  S \ (T \ U) = S \ T := by
  ext x
  repeat rw [Finset.mem_sdiff]
  push_neg
  rw [imp_iff_not_or]
  have h : ¬(x ∈ S ∧ x ∈ U) := by
    rw [← Finset.mem_inter]
    intro h
    apply Finset.notMem_empty x
    exact (Finset.ext_iff.mp (Finset.disjoint_iff_inter_eq_empty.mp hdisj) x).mp h
  rw [and_or_left, or_comm, or_iff_not_imp_left]
  exact ⟨fun h' ↦ h' h, fun h' _ ↦ h'⟩

lemma get_edges_insert (c : Int × Int) (S : Finset (Int × Int)) (cnmem : c ∉ S) :
  get_edges (insert c S) = ((get_edges S) ∪ (get_edges {c})) \
  (Finset.image edge_flip ((get_edges S) ∪ (get_edges {c}))) := by
  rw [get_edges_singleton]
  unfold get_edges
  rw [Finset.biUnion_insert, Finset.biUnion_insert]
  rw [Finset.image_union, Finset.image_sdiff]; swap
  · -- Prove that 'edge_flip' is injective
    unfold edge_flip
    intro a b hab; dsimp at hab
    exact Edge.ext_iff.mpr (Edge.ext_iff.mp hab).symm
  rw [edge_flip_biUnion_edges, edge_flip_biUnion_antiedges]
  change _ = _ \ (_ ∪ get_cell_antiedges c)
  rw [Finset.union_sdiff_distrib, finset_sdiff_union, cell_edges_antiedges_sdiff]
  nth_rw 2 [Finset.union_comm]
  rw [finset_sdiff_union]
  change _ ∪ (get_edges S) \ get_cell_antiedges c = _
  rw [Finset.union_sdiff_distrib, finset_sdiff_union]
  rw [finset_sdiff_sdiff_sdiff_cancel]
  change _ = (get_edges S) \ _ ∪ _
  nth_rw 3 [Finset.union_comm]
  rw [finset_sdiff_union, cell_edges_antiedges_sdiff]
  -- We cannot complete the proof purely through set identities.
  -- We need to take advantage of the fact that these two sets are disjoint.
  have hdisjoint : Disjoint (get_cell_edges c) (S.biUnion get_cell_edges) := by
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    ext x; constructor
    · intro h
      rcases Finset.mem_inter.mp h with ⟨xmem₀, xmem₁⟩
      rcases Finset.mem_biUnion.mp xmem₁ with ⟨d, dmem, xmem₂⟩
      have hc : x._in = c :=
        (cell_edges_mem_iff' _ _).mp xmem₀
      have hd : x._in = d :=
        (cell_edges_mem_iff' _ _).mp xmem₂
      absurd cnmem
      rwa [← hc, hd]
    · exact fun h ↦ False.elim (Finset.notMem_empty _ h)
  rw [finset_sdiff_sdiff_disjoint_right _ _ _ hdisjoint]
  rw [Finset.union_comm]

-- The number of edges of a region is less than or equal to twice the number
-- of cells considered for the region, plus two.
lemma region_edges_le (L : List (Int × Int)) (start : (Int × Int)) (smem : start ∈ L) :
  (get_edges (Region L start)).card ≤ 2 * L.length + 2 := by
  -- First handle the case where the region has only a single cell
  by_cases hrl1 : (Region L start).card = 1
  · rcases Finset.card_eq_one.mp hrl1 with ⟨a, ha⟩
    rw [ha, get_edges_singleton]
    have llpos : 1 ≤ L.length := Nat.add_one_le_of_lt (List.length_pos_of_mem smem)
    apply le_trans _ (Nat.add_le_add_right (Nat.mul_le_mul_left 2 llpos) 2)
    rw [mul_one, two_add_two_eq_four]
    repeat apply le_trans (Finset.card_insert_le _ _) (Nat.add_one_le_add_one_iff.mpr _)
    rw [Finset.card_singleton]
  rename' hrl1 => hrlne1; push_neg at hrlne1
  have rlpos : 0 < (Region L start).card :=
    Finset.card_pos.mpr (Finset.nonempty_of_ne_empty (region_ne_empty L start))
  have rllb : 1 < (Region L start).card :=
    Nat.lt_of_le_of_ne (Nat.add_one_le_of_lt rlpos) hrlne1.symm
  -- Use the region recurrence to remove a cell, 'a'
  rcases region_recurrence_exists L start smem rllb with ⟨a, anes, ha⟩
  -- Define 'R' as being the region constructed from 'L' with 'a' removed
  let R := Region ((list_rm_dupes L).erase a) start
  have amem : a ∈ Region L start :=
    ha ▸ (Finset.mem_insert_self _ _)
  have amemL : a ∈ L :=
    region_subset_list L start smem a amem
  have smem' : start ∈ (list_rm_dupes L).erase a :=
    (List.mem_erase_of_ne anes.symm).mpr ((list_rm_dupes_mem_iff _ _).mpr smem)
  let anmem : a ∉ R := by
    intro amem'
    absurd region_subset_list ((list_rm_dupes L).erase a) start smem' a amem'
    exact list_nodupes_not_mem_erase_of_nodupes _ (list_rm_dupes_nodupes _) _
  rw [ha, get_edges_insert a R anmem]
  -- Rewrite the cardinality of the set difference
  apply Nat.add_le_add_iff_right.mp
  rw [Finset.card_sdiff_add_card_inter]
  -- Introduce 'b' as the cell which connects 'a' to the rest of the region
  rcases region_adjacent_exists_of_mem L start smem rllb a amem with ⟨b, bmem, hadj⟩
  have aneb : a ≠ b := fun hmem ↦ adjacent_ne _ _ hadj hmem
  have bmem' : b ∈ R :=
    Finset.mem_of_mem_insert_of_ne (ha ▸ bmem) aneb.symm
  -- Define the edges that connect 'a' and 'b' and prove some results about them
  let e : Edge := ⟨a, b, hadj⟩
  let e' : Edge := ⟨b, a, (adjacent_comm _ _).mp hadj⟩
  have enee' : e ≠ e' := fun h ↦ False.elim (aneb (Edge.ext_iff.mp h).1)
  have emem : e ∈ get_edges {a} := by
    apply (get_edges_mem_iff _ _).mpr (And.intro (List.mem_singleton_self _) _)
    exact fun hmem ↦ aneb.symm (List.mem_singleton.mp hmem)
  have e'mem : e' ∈ get_edges R := by
    exact (get_edges_mem_iff _ _).mpr (And.intro bmem' anmem)
  have hflip : e = edge_flip e' := rfl
  have hflip' : e' = edge_flip e := rfl
  -- Prove that at least two edges will be removed as part of the sdiff
  have hss : ({e, e'} : Finset Edge) ⊆
    (get_edges R ∪ get_edges {a}) ∩ (Finset.image edge_flip (get_edges R ∪ get_edges {a})) := by
    intro x xmem
    apply Finset.mem_inter.mpr
    constructor
    · rcases Finset.mem_insert.mp xmem with lhs | rhs
      · subst lhs
        exact Finset.mem_union.mpr (Or.inr emem)
      · convert Finset.mem_union.mpr (Or.inl e'mem)
        exact Finset.mem_singleton.mp rhs
    · apply Finset.mem_image.mpr
      rcases Finset.mem_insert.mp xmem with lhs | rhs
      · subst lhs
        exact ⟨e', Finset.mem_union.mpr (Or.inl e'mem), hflip.symm⟩
      · use e, Finset.mem_union.mpr (Or.inr emem)
        exact (Eq.trans (Finset.mem_singleton.mp rhs) hflip').symm
  apply le_trans _ (Nat.add_le_add_left (Finset.card_le_card hss) (2 * L.length + 2))
  rw [Finset.card_insert_of_notMem]; swap
  · exact fun h ↦ False.elim (enee' (Finset.mem_singleton.mp h))
  -- Prove that the two sets of edges are disjoint
  have hdisj : Disjoint (get_edges R) (get_edges {a}) := by
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    ext x; constructor
    · intro h
      rcases Finset.mem_inter.mp h with ⟨xmem₀, xmem₁⟩
      have xina : x._in = a := Finset.mem_singleton.mp ((get_edges_mem_iff _ _).mp xmem₁).1
      exact False.elim (anmem (xina ▸ ((get_edges_mem_iff _ _).mp xmem₀).1))
    · exact fun h ↦ False.elim (Finset.notMem_empty _ h)
  rw [Finset.card_singleton, Finset.card_union_of_disjoint hdisj]
  rw [get_edges_singleton_card, add_assoc, one_add_one_eq_two]
  rw [two_add_two_eq_four]
  apply Nat.add_le_add_right
  -- Finally, apply the result recursively to leave a simple inequality as the goal
  apply le_trans (region_edges_le _ _ smem')
  have amemL' : a ∈ (list_rm_dupes L) :=
    (list_rm_dupes_mem_iff _ _).mpr amemL
  rw [List.length_erase_of_mem amemL', Nat.mul_sub, mul_one]
  rw [Nat.sub_add_cancel]; swap
  · nth_rw 1 [← Nat.mul_one 2]
    apply Nat.mul_le_mul_left _ (Nat.add_one_le_of_lt _)
    exact List.length_pos_of_mem ((list_rm_dupes_mem_iff _ _).mpr smem)
  exact Nat.mul_le_mul_left _ (list_rm_dupes_length_le _)
termination_by (Region L start).card
decreasing_by
  rw [ha, Finset.card_insert_of_notMem anmem]
  exact Nat.lt_add_one _
