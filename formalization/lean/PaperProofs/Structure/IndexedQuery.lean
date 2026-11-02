module

public import PaperProofs.Structure.IndexedDescent
public import PaperProofs.Structure.IndexedTable
public import PaperProofs.Structure.LaminarRankExtraction
public import PaperProofs.Structure.Rank

/-!
Budget tests and tree descent on the materialized capacity rows. The tests
consume the already computed counts and cached ancestor pointers. No tool
rank is evaluated by the runtime query. Its specification remains the
independent Safe/game rank. Full finite-word RAM costs are separate.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.IndexedQuery

open IndexedEntry IndexedDescent

def accepts {q : Nat} (cache : IndexedNodeCache (Fin q)) (counts : IndexedCapacity cache) :
    FixedEntry cache → Bool
  | .void => false
  | .vector capacity => (List.finRange cache.nodes.size).all (fun node => decide (counts.get node ≤ capacity.get node))

def ancestorSlackTest {q : Nat} (cache : IndexedNodeCache (Fin q))
    (counts capacity : IndexedCapacity cache) (node : cache.NodeId) : Bool :=
  (IndexedAncestors.ancestorChain cache node).all (fun ancestor => decide (counts.get ancestor < capacity.get ancestor))

def extensionTest {q : Nat} (cache : IndexedNodeCache (Fin q)) (counts : IndexedCapacity cache)
    (node : Option cache.NodeId) : FixedEntry cache → Bool
  | .void => false
  | .vector capacity => match node with
      | none => false
      | some start => accepts cache counts (.vector capacity) && ancestorSlackTest cache counts capacity start

theorem accepts_iff_denote {q : Nat} (cache : IndexedNodeCache (Fin q))
    (used : Finset (Fin q)) (entry : FixedEntry cache) :
    accepts cache (usedCounts cache used) entry = true ↔ used ∈ entry.denote cache := by
  cases entry with
  | void => simp [accepts, CapacityBits.Entry.denote, CapacityBits.Entry.toCapacityEntry, CapacityEntry.denote]
  | vector capacity =>
    change (List.finRange cache.nodes.size).all _ = true ↔
      ∀ node ∈ (Finset.univ : Finset cache.NodeId), (used ∩ cache.decode node).card ≤ capacity.get node
    simp only [List.all_eq_true, List.mem_finRange, forall_const, usedCounts_get, decide_eq_true_eq, Finset.mem_univ]

theorem prepared_ancestorSlackTest_iff (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q))
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (node : (prepareNormalization q full).indexed.NodeId) :
    ancestorSlackTest (prepareNormalization q full).indexed (usedCounts (prepareNormalization q full).indexed used) capacity node = true ↔
      AncestorSlack full ((prepareNormalization q full).indexed.unindexCapacity capacity) used
        ((prepareNormalization q full).indexed.decode node) := by
  rw [ancestorSlackTest, List.all_eq_true]
  constructor
  · intro h ancestor hancestor
    obtain ⟨hactive, hsub⟩ := (mem_ancestors full _ _).mp hancestor
    obtain ⟨index, hdecode⟩ := prepared_indexed_node_exists q full ancestor hactive
    have hm : index ∈ IndexedAncestors.ancestorChain (prepareNormalization q full).indexed node :=
      (IndexedAncestors.prepared_ancestorChain_mem_iff q full hq hlaminar node index).mpr (hdecode ▸ hsub)
    have hh := h index hm
    simp only [decide_eq_true_eq, usedCounts_get] at hh
    rw [← hdecode, unindexCapacity_at _ (prepared_indexed_nodes_nodup q full)]
    exact hh
  · intro h ancestor hm
    have hs := (IndexedAncestors.prepared_ancestorChain_mem_iff q full hq hlaminar node ancestor).mp hm
    have hh := h _ ((mem_ancestors full _ _).mpr ⟨prepared_indexed_node_mem q full ancestor, hs⟩)
    rw [unindexCapacity_at _ (prepared_indexed_nodes_nodup q full)] at hh
    simpa only [decide_eq_true_eq, usedCounts_get] using hh

theorem prepared_reify_unindex (q : Nat) (full : List (Finset (Fin q)))
    (capacity : IndexedCapacity (prepareNormalization q full).indexed) :
    reifyCapacity (prepareNormalization q full).indexed
      ((prepareNormalization q full).indexed.unindexCapacity capacity) = capacity := by
  apply Vector.ext
  intro i hi
  change (reifyCapacity (prepareNormalization q full).indexed
    ((prepareNormalization q full).indexed.unindexCapacity capacity)).get ⟨i, hi⟩ = capacity.get ⟨i, hi⟩
  rw [reifyCapacity_get, unindexCapacity_at _ (prepared_indexed_nodes_nodup q full)]

theorem prepared_extensionTest_iff (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q))
    (node : (prepareNormalization q full).indexed.NodeId)
    (entry : FixedEntry (prepareNormalization q full).indexed)
    (hnormalized : IsNormalized (prepareNormalization q full).indexed entry) :
    extensionTest (prepareNormalization q full).indexed (usedCounts (prepareNormalization q full).indexed used)
      (some node) entry = true ↔
      ∃ tool ∈ (prepareNormalization q full).indexed.decode node, tool ∉ used ∧ insert tool used ∈ entry.denote (prepareNormalization q full).indexed := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  cases entry with
  | void => simp [extensionTest, CapacityBits.Entry.denote, CapacityBits.Entry.toCapacityEntry, CapacityEntry.denote]
  | vector capacity =>
    rw [extensionTest, Bool.and_eq_true, accepts_iff_denote,
      prepared_ancestorSlackTest_iff q full hq hlaminar,
      prepared_toSupport_denote q full (.vector capacity)]
    change (used ∈ capacityFamily (layout full) ((prepareNormalization q full).indexed.unindexCapacity capacity) ∧ _) ↔
      ∃ tool ∈ _, tool ∉ used ∧ insert tool used ∈ capacityFamily (layout full) ((prepareNormalization q full).indexed.unindexCapacity capacity)
    constructor
    · rintro ⟨hused, hancestors⟩
      exact (extension_iff_ancestorSlack full hlaminar _
        (prepared_indexed_normalized_to_original q full hq hlaminar capacity hnormalized) used _ hused
        (prepared_indexed_node_mem q full node)
        (nodeFamily_nonempty_nodes full _ (prepared_indexed_node_mem q full node))).mpr hancestors
    · rintro ⟨tool, htool, hunused, hinsert⟩
      exact ⟨capacityFamily_downward_closed _ _ (Finset.subset_insert _ _) hinsert,
        extension_necessity full _ used _ ⟨tool, htool, hunused, hinsert⟩⟩

def selectEntry {q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts : IndexedCapacity cache)
    (node : Option cache.NodeId) : FixedEntry cache → Option (Fin q)
  | .void => none
  | .vector capacity => node.bind (selectAt cache leaves counts capacity)

theorem prepared_selectEntry_exists (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q))
    (node : (prepareNormalization q full).indexed.NodeId)
    (entry : FixedEntry (prepareNormalization q full).indexed)
    (hnormalized : IsNormalized (prepareNormalization q full).indexed entry)
    (htest : extensionTest (prepareNormalization q full).indexed (usedCounts (prepareNormalization q full).indexed used) (some node) entry = true) :
    ∃ tool, selectEntry (prepareNormalization q full).indexed (leafTools (prepareNormalization q full).indexed)
      (usedCounts (prepareNormalization q full).indexed used) (some node) entry = some tool ∧
      tool ∈ (prepareNormalization q full).indexed.decode node ∧ tool ∉ used ∧
      insert tool used ∈ entry.denote (prepareNormalization q full).indexed := by
  cases entry with
  | void => cases htest
  | vector capacity =>
    rw [extensionTest, Bool.and_eq_true] at htest
    have hused := (accepts_iff_denote _ used (.vector capacity)).mp htest.1
    rw [prepared_toSupport_denote q full (.vector capacity)] at hused
    have ha := (prepared_ancestorSlackTest_iff q full hq hlaminar used capacity node).mp htest.2
    obtain ⟨tool, hr, ht, hu, hi⟩ := prepared_selectAt_exists q full hq hlaminar _
      (prepared_indexed_normalized_to_original q full hq hlaminar capacity hnormalized) used hused node ha
    rw [prepared_reify_unindex] at hr
    refine ⟨tool, hr, ht, hu, ?_⟩
    rw [prepared_toSupport_denote q full (.vector capacity)]
    exact hi

def entryAt {q : Nat} {cache : IndexedNodeCache (Fin q)} (row : IndexedTable.Row cache (q + 1))
    (budget : Nat) : FixedEntry cache :=
  if h : budget < q + 2 then row.get ⟨budget, h⟩ else .void

theorem entryAt_get {q : Nat} {cache : IndexedNodeCache (Fin q)} (row : IndexedTable.Row cache (q + 1))
    (budget : Nat) (hb : budget < q + 2) : entryAt row budget = row.get ⟨budget, hb⟩ := by
  simp only [entryAt, hb, ↓reduceDIte]

def budgetExtensionTest {q : Nat} (cache : IndexedNodeCache (Fin q))
    (counts : IndexedCapacity cache) (row : IndexedTable.Row cache (q + 1))
    (node : Option cache.NodeId) (budget : Nat) : Bool :=
  extensionTest cache counts node (entryAt row budget)

def firstFalse (q : Nat) (test : Nat → Bool) : Option Nat :=
  (List.range' 0 (q + 2)).find? (fun budget => !(test budget))

def rankFromTests (q : Nat) (test : Nat → Bool) : ℕ∞ :=
  match firstFalse q test with
  | none => ⊤
  | some budget => budget

def selectedBudget (q : Nat) (test : Nat → Bool) : Option Nat :=
  match firstFalse q test with
  | none => some (q + 1)
  | some 0 => none
  | some (budget + 1) => some budget

def maximizingTool {q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts : IndexedCapacity cache)
    (row : IndexedTable.Row cache (q + 1)) (node : Option cache.NodeId) : Option (Fin q) :=
  (selectedBudget q (budgetExtensionTest cache counts row node)).bind
    (fun budget => selectEntry cache leaves counts node (entryAt row budget))

theorem firstFalse_eq_some_of_spectrum (q : Nat) (test : Nat → Bool) (rank : ℕ∞)
    (hspectrum : ∀ k, k < q + 2 → (test k = true ↔ (k : ℕ∞) < rank))
    (b : Nat) (hb : b ≤ q + 1) (hrank : rank = (b : ℕ∞)) : firstFalse q test = some b := by
  apply find_range'_first _ 0 (q + 2) b (Nat.zero_le _) (by omega)
  · have hf : test b = false := Bool.eq_false_iff.mpr (by
      intro ht
      have hh := (hspectrum b (by omega)).mp ht
      rw [hrank] at hh
      exact (lt_irrefl _) hh)
    simp only [hf, Bool.not_false]
  · intro k _ hk
    have ht : test k = true := (hspectrum k (by omega)).mpr (by
      rw [hrank]
      exact ENat.natCast_lt_natCast.mpr hk)
    simp only [ht, Bool.not_true]

theorem firstFalse_eq_none_of_spectrum (q : Nat) (test : Nat → Bool) (rank : ℕ∞)
    (hspectrum : ∀ k, k < q + 2 → (test k = true ↔ (k : ℕ∞) < rank))
    (hrank : rank = ⊤) : firstFalse q test = none := by
  unfold firstFalse
  apply List.find?_eq_none.mpr
  intro k hk
  have hb : k < q + 2 := by
    obtain ⟨i, hi, hki⟩ := List.mem_range'.mp hk
    omega
  have hlt : (k : ℕ∞) < rank := by
    rw [hrank]
    exact ENat.natCast_lt_top k
  have ht : test k = true := (hspectrum k hb).mpr hlt
  rw [ht]
  exact Bool.false_ne_true

theorem rankFromTests_eq_of_spectrum (q : Nat) (test : Nat → Bool) (rank : ℕ∞)
    (hspectrum : ∀ k, k < q + 2 → (test k = true ↔ (k : ℕ∞) < rank))
    (hbound : rank ≠ ⊤ → rank ≤ ((q + 1 : Nat) : ℕ∞)) : rankFromTests q test = rank := by
  by_cases ht : rank = ⊤
  · simp only [rankFromTests, firstFalse_eq_none_of_spectrum q test rank hspectrum ht, ht]
  · obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp ht
    have hbn : b ≤ q + 1 := ENat.natCast_le_natCast.mp (hb.symm ▸ hbound ht)
    rw [rankFromTests, firstFalse_eq_some_of_spectrum q test rank hspectrum b hbn hb.symm]
    exact hb

theorem badChildRank_finite_le_q_add_one (q : Nat) (eligible : Finset (Fin q))
    (later : List (Finset (Fin q))) (remaining : Finset (Fin q))
    (hfinite : badChildRank eligible later remaining ≠ ⊤) :
    badChildRank eligible later remaining ≤ ((q + 1 : Nat) : ℕ∞) := by
  apply Finset.sup_le
  intro tool ht
  have hcf : errorRank later (remaining.erase tool) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite (childRank_le_badChildRank eligible later remaining ht)
  have hbound := errorRank_finite_le_card_add_one later (remaining.erase tool) hcf
  apply hbound.trans
  apply ENat.natCast_le_natCast.mpr
  have hc := Finset.card_le_univ (remaining.erase tool)
  simp only [Fintype.card_fin] at hc
  omega

theorem prepared_budgetExtensionTest_iff (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q))
    (later : List (Finset (Fin q)))
    (row : IndexedTable.Row (prepareNormalization q full).indexed (q + 1))
    (hrow : IndexedTable.RowCorrect (prepareNormalization q full).indexed later row)
    (node : (prepareNormalization q full).indexed.NodeId) (k : Nat) (hk : k < q + 2) :
    budgetExtensionTest (prepareNormalization q full).indexed (usedCounts (prepareNormalization q full).indexed used)
      row (some node) k = true ↔
      (k : ℕ∞) < badChildRank ((prepareNormalization q full).indexed.decode node) later (Finset.univ \ used) := by
  rw [budgetExtensionTest, entryAt_get row k hk,
    prepared_extensionTest_iff q full hq hlaminar used node _ (hrow ⟨k, hk⟩).1,
    (hrow ⟨k, hk⟩).2.2, lt_badChildRank_iff]
  simp only [safeUsedFamily, Set.mem_ofPred_eq, remaining_after_used_insert, Finset.mem_inter,
    Finset.mem_sdiff, Finset.mem_univ, true_and, and_assoc]

def goodRank {q : Nat} (cache : IndexedNodeCache (Fin q)) (counts : IndexedCapacity cache)
    (row : IndexedTable.Row cache (q + 1)) : ℕ∞ :=
  rankFromTests q (fun k => accepts cache counts (entryAt row k))

def badRank {q : Nat} (cache : IndexedNodeCache (Fin q)) (counts : IndexedCapacity cache)
    (row : IndexedTable.Row cache (q + 1)) (node : Option cache.NodeId) : ℕ∞ :=
  rankFromTests q (budgetExtensionTest cache counts row node)

def currentRank {q : Nat} (cache : IndexedNodeCache (Fin q)) (counts : IndexedCapacity cache)
    (row : IndexedTable.Row cache (q + 1)) (node : Option cache.NodeId) : ℕ∞ :=
  min (goodRank cache counts row) (1 + badRank cache counts row node)

theorem errorRank_finite_le_q_add_one (q : Nat) (later : List (Finset (Fin q))) (remaining : Finset (Fin q))
    (hfinite : errorRank later remaining ≠ ⊤) : errorRank later remaining ≤ ((q + 1 : Nat) : ℕ∞) := by
  apply (errorRank_finite_le_card_add_one later remaining hfinite).trans
  apply ENat.natCast_le_natCast.mpr
  have hc := Finset.card_le_univ remaining
  simp only [Fintype.card_fin] at hc
  omega

theorem prepared_goodRank_eq (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (later : List (Finset (Fin q)))
    (row : IndexedTable.Row (prepareNormalization q full).indexed (q + 1))
    (hrow : IndexedTable.RowCorrect (prepareNormalization q full).indexed later row) :
    goodRank (prepareNormalization q full).indexed (usedCounts (prepareNormalization q full).indexed used) row =
      errorRank later (Finset.univ \ used) := by
  apply rankFromTests_eq_of_spectrum
  · intro k hk
    rw [entryAt_get row k hk, accepts_iff_denote, (hrow ⟨k, hk⟩).2.2]
    exact safeUsed_rank_membership later used k
  · exact errorRank_finite_le_q_add_one q later (Finset.univ \ used)

theorem prepared_badRank_eq (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (later : List (Finset (Fin q)))
    (row : IndexedTable.Row (prepareNormalization q full).indexed (q + 1))
    (hrow : IndexedTable.RowCorrect (prepareNormalization q full).indexed later row)
    (node : (prepareNormalization q full).indexed.NodeId) :
    badRank (prepareNormalization q full).indexed (usedCounts (prepareNormalization q full).indexed used) row (some node) =
      badChildRank ((prepareNormalization q full).indexed.decode node) later (Finset.univ \ used) := by
  apply rankFromTests_eq_of_spectrum
  · exact prepared_budgetExtensionTest_iff q full hq hlaminar used later row hrow node
  · exact badChildRank_finite_le_q_add_one q _ later (Finset.univ \ used)

theorem prepared_currentRank_eq (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (later : List (Finset (Fin q)))
    (row : IndexedTable.Row (prepareNormalization q full).indexed (q + 1))
    (hrow : IndexedTable.RowCorrect (prepareNormalization q full).indexed later row)
    (node : (prepareNormalization q full).indexed.NodeId) :
    currentRank (prepareNormalization q full).indexed (usedCounts (prepareNormalization q full).indexed used) row (some node) =
      errorRank (((prepareNormalization q full).indexed.decode node) :: later) (Finset.univ \ used) := by
  rw [currentRank, prepared_goodRank_eq q full used later row hrow,
    prepared_badRank_eq q full hq hlaminar used later row hrow, errorRank_cons]

theorem selectedBudget_of_firstFalse (q : Nat) (test : Nat → Bool) (b : Nat)
    (hfirst : firstFalse q test = some b) (hb : 0 < b) : selectedBudget q test = some (b - 1) := by
  rw [selectedBudget, hfirst]
  cases b with
  | zero => omega
  | succ b => rfl

theorem prepared_budget_tool (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (later : List (Finset (Fin q)))
    (row : IndexedTable.Row (prepareNormalization q full).indexed (q + 1))
    (hrow : IndexedTable.RowCorrect (prepareNormalization q full).indexed later row)
    (node : (prepareNormalization q full).indexed.NodeId) (k : Nat) (hk : k < q + 2)
    (htest : budgetExtensionTest (prepareNormalization q full).indexed
      (usedCounts (prepareNormalization q full).indexed used) row (some node) k = true) :
    ∃ tool, selectEntry (prepareNormalization q full).indexed (leafTools (prepareNormalization q full).indexed)
      (usedCounts (prepareNormalization q full).indexed used) (some node) (entryAt row k) = some tool ∧
      tool ∈ (prepareNormalization q full).indexed.decode node ∧ tool ∉ used ∧
      (k : ℕ∞) < errorRank later ((Finset.univ \ used).erase tool) := by
  have hn : IsNormalized (prepareNormalization q full).indexed (entryAt row k) := by
    rw [entryAt_get row k hk]
    exact (hrow ⟨k, hk⟩).1
  obtain ⟨tool, hr, ht, hu, hi⟩ := prepared_selectEntry_exists q full hq hlaminar used node (entryAt row k) hn htest
  rw [entryAt_get row k hk, (hrow ⟨k, hk⟩).2.2] at hi
  have hs : Safe later ((Finset.univ \ used).erase tool) k := by
    simpa only [safeUsedFamily, Set.mem_ofPred_eq, remaining_after_used_insert] using hi
  exact ⟨tool, hr, ht, hu, (safe_iff_lt_errorRank _ _ _).mp hs⟩

/-- The actual budget scan followed by one slack descent returns a tool
attaining the independently defined maximum successor rank, including top.
No per-tool rank, optimum or strategy is passed to the implementation. -/
theorem prepared_maximizingTool_exists (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (later : List (Finset (Fin q)))
    (row : IndexedTable.Row (prepareNormalization q full).indexed (q + 1))
    (hrow : IndexedTable.RowCorrect (prepareNormalization q full).indexed later row)
    (node : (prepareNormalization q full).indexed.NodeId)
    (havailable : (((prepareNormalization q full).indexed.decode node) ∩ (Finset.univ \ used)).Nonempty) :
    ∃ tool, maximizingTool (prepareNormalization q full).indexed (leafTools (prepareNormalization q full).indexed)
      (usedCounts (prepareNormalization q full).indexed used) row (some node) = some tool ∧
      tool ∈ (prepareNormalization q full).indexed.decode node ∧ tool ∉ used ∧
      errorRank later ((Finset.univ \ used).erase tool) =
        badChildRank ((prepareNormalization q full).indexed.decode node) later (Finset.univ \ used) := by
  let test := budgetExtensionTest (prepareNormalization q full).indexed
    (usedCounts (prepareNormalization q full).indexed used) row (some node)
  let rank := badChildRank ((prepareNormalization q full).indexed.decode node) later (Finset.univ \ used)
  have hspectrum : ∀ k, k < q + 2 → (test k = true ↔ (k : ℕ∞) < rank) :=
    prepared_budgetExtensionTest_iff q full hq hlaminar used later row hrow node
  have hnonzero : rank ≠ 0 := by
    intro hz
    exact (Finset.nonempty_iff_ne_empty.mp havailable) ((badChildRank_eq_zero_iff _ _ _).mp hz)
  by_cases htop : rank = ⊤
  · have hfirst := firstFalse_eq_none_of_spectrum q test rank hspectrum htop
    have htt : test (q + 1) = true := (hspectrum _ (by omega)).mpr (by rw [htop]; exact ENat.natCast_lt_top _)
    obtain ⟨tool, hr, ht, hu, hlt⟩ := prepared_budget_tool q full hq hlaminar used later row hrow node (q + 1) (by omega) htt
    have hc : errorRank later ((Finset.univ \ used).erase tool) = ⊤ := by
      by_contra hcf
      exact (not_lt_of_ge (errorRank_finite_le_q_add_one q later _ hcf)) hlt
    refine ⟨tool, ?_, ht, hu, hc.trans htop.symm⟩
    rw [maximizingTool, selectedBudget, hfirst]
    exact hr
  · obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp htop
    have hbn : b ≤ q + 1 := ENat.natCast_le_natCast.mp (hb.symm ▸ badChildRank_finite_le_q_add_one q _ later _ htop)
    have hbpos : 0 < b := by
      by_contra hn
      have hz : b = 0 := by omega
      apply hnonzero
      rw [← hb, hz]
      rfl
    have hfirst := firstFalse_eq_some_of_spectrum q test rank hspectrum b hbn hb.symm
    have hk : b - 1 < q + 2 := by omega
    have htt : test (b - 1) = true := (hspectrum _ hk).mpr (by rw [← hb]; exact ENat.natCast_lt_natCast.mpr (by omega))
    obtain ⟨tool, hr, ht, hu, hlt⟩ := prepared_budget_tool q full hq hlaminar used later row hrow node (b - 1) hk htt
    have hm := Finset.mem_inter.mpr ⟨ht, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu⟩⟩
    have hle := childRank_le_badChildRank _ later (Finset.univ \ used) hm
    have hcf : errorRank later ((Finset.univ \ used).erase tool) ≠ ⊤ := ne_top_of_le_ne_top htop hle
    obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hcf
    rw [← hc] at hlt
    rw [← hc] at hle
    change (c : ℕ∞) ≤ rank at hle
    rw [← hb] at hle
    have hcn := ENat.natCast_lt_natCast.mp hlt
    have hcb := ENat.natCast_le_natCast.mp hle
    have heq : c = b := by omega
    refine ⟨tool, ?_, ht, hu, ?_⟩
    · rw [maximizingTool, selectedBudget_of_firstFalse q test b hfirst hbpos]
      exact hr
    · change errorRank later ((Finset.univ \ used).erase tool) = rank
      rw [← hc, ← hb, heq]

theorem prepared_maximizingTool_eq_none_iff (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (later : List (Finset (Fin q)))
    (row : IndexedTable.Row (prepareNormalization q full).indexed (q + 1))
    (hrow : IndexedTable.RowCorrect (prepareNormalization q full).indexed later row)
    (node : (prepareNormalization q full).indexed.NodeId) :
    maximizingTool (prepareNormalization q full).indexed (leafTools (prepareNormalization q full).indexed)
      (usedCounts (prepareNormalization q full).indexed used) row (some node) = none ↔
      ((prepareNormalization q full).indexed.decode node) ∩ (Finset.univ \ used) = ∅ := by
  constructor
  · intro hn
    by_contra he
    obtain ⟨tool, hr, _⟩ := prepared_maximizingTool_exists q full hq hlaminar used later row hrow node
      (Finset.nonempty_iff_ne_empty.mpr he)
    rw [hn] at hr
    cases hr
  · intro he
    have hz := (badChildRank_eq_zero_iff ((prepareNormalization q full).indexed.decode node) later (Finset.univ \ used)).mpr he
    have hfirst := firstFalse_eq_some_of_spectrum q
      (budgetExtensionTest (prepareNormalization q full).indexed (usedCounts (prepareNormalization q full).indexed used) row (some node))
      _ (prepared_budgetExtensionTest_iff q full hq hlaminar used later row hrow node) 0 (by omega) hz
    rw [maximizingTool, selectedBudget, hfirst]
    rfl

theorem prepared_maximizingTool_spec (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (later : List (Finset (Fin q)))
    (row : IndexedTable.Row (prepareNormalization q full).indexed (q + 1))
    (hrow : IndexedTable.RowCorrect (prepareNormalization q full).indexed later row)
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (hpick : maximizingTool (prepareNormalization q full).indexed (leafTools (prepareNormalization q full).indexed)
      (usedCounts (prepareNormalization q full).indexed used) row (some node) = some tool) :
    tool ∈ (prepareNormalization q full).indexed.decode node ∧ tool ∉ used ∧
      errorRank later ((Finset.univ \ used).erase tool) =
        badChildRank ((prepareNormalization q full).indexed.decode node) later (Finset.univ \ used) := by
  have he : ((prepareNormalization q full).indexed.decode node) ∩ (Finset.univ \ used) ≠ ∅ := by
    intro hempty
    have hn := (prepared_maximizingTool_eq_none_iff q full hq hlaminar used later row hrow node).mpr hempty
    rw [hn] at hpick
    cases hpick
  obtain ⟨chosen, hc, ht, hu, hr⟩ := prepared_maximizingTool_exists q full hq hlaminar used later row hrow node
    (Finset.nonempty_iff_ne_empty.mpr he)
  have heq : chosen = tool := Option.some.inj (hc.symm.trans hpick)
  exact heq ▸ ⟨ht, hu, hr⟩

theorem goodRank_eq_of_rowCorrect {q : Nat} (cache : IndexedNodeCache (Fin q))
    (used : Finset (Fin q)) (later : List (Finset (Fin q))) (row : IndexedTable.Row cache (q + 1))
    (hrow : IndexedTable.RowCorrect cache later row) :
    goodRank cache (usedCounts cache used) row = errorRank later (Finset.univ \ used) := by
  apply rankFromTests_eq_of_spectrum
  · intro k hk
    rw [entryAt_get row k hk, accepts_iff_denote, (hrow ⟨k, hk⟩).2.2]
    exact safeUsed_rank_membership later used k
  · exact errorRank_finite_le_q_add_one q later (Finset.univ \ used)

theorem extensionTest_none {q : Nat} (cache : IndexedNodeCache (Fin q)) (counts : IndexedCapacity cache)
    (entry : FixedEntry cache) : extensionTest cache counts none entry = false := by cases entry <;> rfl

theorem firstFalse_noneNode {q : Nat} (cache : IndexedNodeCache (Fin q)) (counts : IndexedCapacity cache)
    (row : IndexedTable.Row cache (q + 1)) : firstFalse q (budgetExtensionTest cache counts row none) = some 0 := by
  apply find_range'_first _ 0 (q + 2) 0 (Nat.zero_le _) (by omega)
  · rw [budgetExtensionTest, extensionTest_none]
    rfl
  · intro k _ hk
    omega

theorem badRank_none {q : Nat} (cache : IndexedNodeCache (Fin q)) (counts : IndexedCapacity cache)
    (row : IndexedTable.Row cache (q + 1)) : badRank cache counts row none = 0 := by
  rw [badRank, rankFromTests, firstFalse_noneNode]
  rfl

theorem maximizingTool_noneNode {q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts : IndexedCapacity cache)
    (row : IndexedTable.Row cache (q + 1)) : maximizingTool cache leaves counts row none = none := by
  rw [maximizingTool, selectedBudget, firstFalse_noneNode]
  rfl

structure Reply (q : Nat) where
  rank : ℕ∞
  good : ℕ∞
  bad : ℕ∞
  tool : Option (Fin q)

/-- This runtime interface consumes one STORED successor row and the
precomputed stage/count/leaf data. No preprocessing is performed here. -/
def query {q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts : IndexedCapacity cache)
    (row : IndexedTable.Row cache (q + 1)) (node : Option cache.NodeId) : Reply q :=
  let good := goodRank cache counts row
  let bad := badRank cache counts row node
  ⟨min good (1 + bad), good, bad, maximizingTool cache leaves counts row node⟩

def terminalReply (q : Nat) : Reply q := ⟨⊤, ⊤, 0, none⟩

/-- Array lookup in the actual already-built positive-q table. -/
def storedPositiveRow (q : Nat) (full : List (Finset (Fin q))) (next : Fin (full.length + 1)) :
    IndexedTable.Row (prepareNormalization q full).indexed (q + 1) :=
  (IndexedTable.buildPositive q full (q + 1)).rows[next.val]'(by
    rw [IndexedTable.buildPositive_size]
    exact next.isLt)

theorem storedPositiveRow_correct (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (next : Fin (full.length + 1)) :
    IndexedTable.RowCorrect (prepareNormalization q full).indexed (full.drop next.val) (storedPositiveRow q full next) := by
  have hrows := (IndexedTable.prepared_rows_correct q full hq hlaminar (q + 1) full (fun _ hm => hm)).2
  have hl : next.val < full.tails.length := by simpa only [List.length_tails] using next.isLt
  have hr : next.val < (IndexedTable.rowsList (prepareNormalization q full).indexed (q + 1) full).length := by
    simpa only [IndexedTable.rowsList_length] using next.isLt
  have hrow := hrows.get hl hr
  rw [List.get_tails] at hrow
  simpa only [storedPositiveRow, IndexedTable.buildPositive, List.get_eq_getElem, List.getElem_toArray] using hrow

/-- The original stage node is also an existing preprocessing cache entry. -/
def storedStageNode (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (stage : Fin full.length) :
    Option (prepareNormalization q full).indexed.NodeId :=
  (IndexedStaticMetadata.buildPositive q full hq).stageNodes.get stage

theorem stored_query_good (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (stage : Fin full.length) :
    let next : Fin (full.length + 1) := ⟨stage.val + 1, by omega⟩
    (query (prepareNormalization q full).indexed (leafTools (prepareNormalization q full).indexed)
      (usedCounts (prepareNormalization q full).indexed used) (storedPositiveRow q full next)
      (storedStageNode q full hq stage)).good = errorRank (full.drop (stage.val + 1)) (Finset.univ \ used) := by
  dsimp only
  exact prepared_goodRank_eq q full used _ _ (storedPositiveRow_correct q full hq hlaminar _)

theorem stored_query_bad (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (stage : Fin full.length) :
    let next : Fin (full.length + 1) := ⟨stage.val + 1, by omega⟩
    (query (prepareNormalization q full).indexed (leafTools (prepareNormalization q full).indexed)
      (usedCounts (prepareNormalization q full).indexed used) (storedPositiveRow q full next)
      (storedStageNode q full hq stage)).bad = badChildRank full[stage.val] (full.drop (stage.val + 1)) (Finset.univ \ used) := by
  dsimp only
  cases hn : storedStageNode q full hq stage with
  | none =>
    have he := (IndexedStaticMetadata.buildPositive_stage_none_iff q full hq stage).mp hn
    rw [he]
    exact (badRank_none _ _ _).trans (by simp [badChildRank])
  | some node =>
    have hd := ((IndexedStaticMetadata.buildPositive_stage_some_iff q full hq stage node).mp hn).2
    let next : Fin (full.length + 1) := ⟨stage.val + 1, by omega⟩
    have hb := prepared_badRank_eq q full hq hlaminar used (full.drop next.val) (storedPositiveRow q full next)
      (storedPositiveRow_correct q full hq hlaminar next) node
    rw [hd] at hb
    exact hb

theorem stored_query_rank (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (stage : Fin full.length) :
    let next : Fin (full.length + 1) := ⟨stage.val + 1, by omega⟩
    (query (prepareNormalization q full).indexed (leafTools (prepareNormalization q full).indexed)
      (usedCounts (prepareNormalization q full).indexed used) (storedPositiveRow q full next)
      (storedStageNode q full hq stage)).rank = errorRank (full.drop stage.val) (Finset.univ \ used) := by
  dsimp only
  rw [List.drop_eq_getElem_cons stage.isLt, errorRank_cons]
  exact congrArg₂ min (stored_query_good q full hq hlaminar used stage)
    (congrArg (fun r : ℕ∞ => 1 + r) (stored_query_bad q full hq hlaminar used stage))

theorem stored_query_tool_none_iff (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (stage : Fin full.length) :
    let next : Fin (full.length + 1) := ⟨stage.val + 1, by omega⟩
    (query (prepareNormalization q full).indexed (leafTools (prepareNormalization q full).indexed)
      (usedCounts (prepareNormalization q full).indexed used) (storedPositiveRow q full next)
      (storedStageNode q full hq stage)).tool = none ↔ full[stage.val] ∩ (Finset.univ \ used) = ∅ := by
  dsimp only
  cases hn : storedStageNode q full hq stage with
  | none =>
    have he := (IndexedStaticMetadata.buildPositive_stage_none_iff q full hq stage).mp hn
    constructor
    · intro _
      rw [he, Finset.empty_inter]
    · intro _
      exact maximizingTool_noneNode _ _ _ _
  | some node =>
    have hd := ((IndexedStaticMetadata.buildPositive_stage_some_iff q full hq stage node).mp hn).2
    let next : Fin (full.length + 1) := ⟨stage.val + 1, by omega⟩
    have hh := prepared_maximizingTool_eq_none_iff q full hq hlaminar used (full.drop next.val)
      (storedPositiveRow q full next) (storedPositiveRow_correct q full hq hlaminar next) node
    rw [hd] at hh
    exact hh

theorem stored_query_tool_spec (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (stage : Fin full.length) (tool : Fin q)
    (hpick : let next : Fin (full.length + 1) := ⟨stage.val + 1, by omega⟩
      (query (prepareNormalization q full).indexed (leafTools (prepareNormalization q full).indexed)
        (usedCounts (prepareNormalization q full).indexed used) (storedPositiveRow q full next)
        (storedStageNode q full hq stage)).tool = some tool) :
    tool ∈ full[stage.val] ∧ tool ∉ used ∧
      errorRank (full.drop (stage.val + 1)) ((Finset.univ \ used).erase tool) =
        badChildRank full[stage.val] (full.drop (stage.val + 1)) (Finset.univ \ used) := by
  dsimp only at hpick
  cases hn : storedStageNode q full hq stage with
  | none =>
    change maximizingTool _ _ _ _ (storedStageNode q full hq stage) = some tool at hpick
    rw [hn, maximizingTool_noneNode] at hpick
    cases hpick
  | some node =>
    change maximizingTool _ _ _ _ (storedStageNode q full hq stage) = some tool at hpick
    rw [hn] at hpick
    have hd := ((IndexedStaticMetadata.buildPositive_stage_some_iff q full hq stage node).mp hn).2
    let next : Fin (full.length + 1) := ⟨stage.val + 1, by omega⟩
    have hh := prepared_maximizingTool_spec q full hq hlaminar used (full.drop next.val)
      (storedPositiveRow q full next) (storedPositiveRow_correct q full hq hlaminar next) node tool hpick
    rw [hd] at hh
    exact hh

/-- The q=0 path uses the pre-existing EMPTY cache and zero-tool direct
table. In particular this constructor never prepares an inclusion tree. -/
def storedZeroRow (full : List (Finset (Fin 0))) (next : Fin (full.length + 1)) :
    IndexedTable.Row (IndexedTable.emptyCache (Fin 0)) 1 :=
  (IndexedTable.buildZero full 1).rows[next.val]'(by
    change next.val < (IndexedTable.build 0 full 1).rows.size
    rw [IndexedTable.build_size]
    exact next.isLt)

theorem storedZeroRow_correct (full : List (Finset (Fin 0))) (hlaminar : LaminarSchedule full)
    (next : Fin (full.length + 1)) :
    IndexedTable.RowCorrect (IndexedTable.emptyCache (Fin 0)) (full.drop next.val) (storedZeroRow full next) := by
  intro budget
  exact IndexedTable.build_entry_correct 0 full hlaminar 1 next budget

theorem zeroTool_query (full : List (Finset (Fin 0))) (hlaminar : LaminarSchedule full)
    (used : Finset (Fin 0)) (stage : Fin full.length) :
    let cache := IndexedTable.emptyCache (Fin 0)
    let next : Fin (full.length + 1) := ⟨stage.val + 1, by omega⟩
    let answer := query cache (leafTools cache) (usedCounts cache used) (storedZeroRow full next) none
    answer.rank = 1 ∧ answer.bad = 0 ∧ answer.tool = none ∧
      answer.good = errorRank (full.drop (stage.val + 1)) (Finset.univ \ used) := by
  let cache := IndexedTable.emptyCache (Fin 0)
  let next : Fin (full.length + 1) := ⟨stage.val + 1, by omega⟩
  have hg := goodRank_eq_of_rowCorrect cache used (full.drop next.val) (storedZeroRow full next)
    (storedZeroRow_correct full hlaminar next)
  have hb := badRank_none cache (usedCounts cache used) (storedZeroRow full next)
  have ht := maximizingTool_noneNode cache (leafTools cache) (usedCounts cache used) (storedZeroRow full next)
  have hrem : (Finset.univ \ used : Finset (Fin 0)) = ∅ :=
    Finset.eq_empty_of_forall_notMem (fun tool _ => Fin.elim0 tool)
  have hr : min (errorRank (full.drop next.val) (Finset.univ \ used)) (1 + (0 : ℕ∞)) = 1 := by
    rw [hrem]
    have hh := errorRank_cons (∅ : Finset (Fin 0)) (full.drop next.val) ∅
    rw [errorRank_no_tools] at hh
    simpa only [badChildRank, Finset.empty_inter, Finset.sup_empty, bot_eq_zero] using hh.symm
  exact ⟨(congrArg₂ min hg (congrArg (fun r : ℕ∞ => 1 + r) hb)).trans hr, hb, ht, hg⟩

theorem terminalReply_rank (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) :
    (terminalReply q).rank = errorRank (full.drop full.length) (Finset.univ \ used) := by
  rw [List.drop_length, errorRank_terminal]
  rfl

/-- The paper's e_k equivalence on the actual stored successor row and
the actual cached stage node, including an EMPTY compatibility set. -/
theorem stored_budgetExtensionTest_iff (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (stage : Fin full.length)
    (k : Nat) (hk : k < q + 2) :
    let next : Fin (full.length + 1) := ⟨stage.val + 1, by omega⟩
    budgetExtensionTest (prepareNormalization q full).indexed (usedCounts (prepareNormalization q full).indexed used)
      (storedPositiveRow q full next) (storedStageNode q full hq stage) k = true ↔
      ∃ tool ∈ full[stage.val] ∩ (Finset.univ \ used),
        (k : ℕ∞) < errorRank (full.drop (stage.val + 1)) ((Finset.univ \ used).erase tool) := by
  dsimp only
  simp_rw [← safe_iff_lt_errorRank]
  rw [← lt_badChildRank_iff]
  cases hn : storedStageNode q full hq stage with
  | none =>
    have he := (IndexedStaticMetadata.buildPositive_stage_none_iff q full hq stage).mp hn
    rw [budgetExtensionTest, extensionTest_none, he]
    simp [badChildRank]
  | some node =>
    let next : Fin (full.length + 1) := ⟨stage.val + 1, by omega⟩
    have hd := ((IndexedStaticMetadata.buildPositive_stage_some_iff q full hq stage node).mp hn).2
    have hh := prepared_budgetExtensionTest_iff q full hq hlaminar used (full.drop next.val)
      (storedPositiveRow q full next) (storedPositiveRow_correct q full hq hlaminar next) node k hk
    rw [hd] at hh
    exact hh

theorem stored_budgetExtensionTest_antitone (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (stage : Fin full.length)
    (j k : Nat) (hjk : j ≤ k) (hk : k < q + 2) :
    let next : Fin (full.length + 1) := ⟨stage.val + 1, by omega⟩
    budgetExtensionTest (prepareNormalization q full).indexed (usedCounts (prepareNormalization q full).indexed used)
      (storedPositiveRow q full next) (storedStageNode q full hq stage) k = true →
    budgetExtensionTest (prepareNormalization q full).indexed (usedCounts (prepareNormalization q full).indexed used)
      (storedPositiveRow q full next) (storedStageNode q full hq stage) j = true := by
  dsimp only
  intro ht
  obtain ⟨tool, htool, hrank⟩ := (stored_budgetExtensionTest_iff q full hq hlaminar used stage k hk).mp ht
  apply (stored_budgetExtensionTest_iff q full hq hlaminar used stage j (by omega)).mpr
  exact ⟨tool, htool, lt_of_le_of_lt (ENat.natCast_le_natCast.mpr hjk) hrank⟩

end PaperProofs.Structure.LaminarTree.IndexedQuery
