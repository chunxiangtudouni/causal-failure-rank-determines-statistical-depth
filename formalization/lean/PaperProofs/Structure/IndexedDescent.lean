module

public import PaperProofs.Structure.IndexedStaticMetadata
public import PaperProofs.Structure.LaminarExtension

/-!
Executable slack-child descent on the already prepared inclusion tree.
The query reads a cached singleton-tool vector, child arrays, used counts
and capacities. It never ranks or enumerates candidate tools. All semantic
preconditions are external theorem hypotheses, not cache fields. The real
tree's t-1 edges bound node visits plus child probes by 2t. A finite-word RAM
execution bound and the cost of building used counts remain separate.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.IndexedDescent

def singletonTool {q : Nat} (support : Finset (Fin q)) : Option (Fin q) :=
  if h : support.Nonempty ∧ support.card ≤ 1 then some (support.min' h.1) else none

theorem singletonTool_singleton {q : Nat} (tool : Fin q) :
    singletonTool {tool} = some tool := by simp [singletonTool]

theorem singletonTool_spec {q : Nat} (support : Finset (Fin q)) (tool : Fin q)
    (h : singletonTool support = some tool) : support = {tool} := by
  unfold singletonTool at h
  split at h
  next hs =>
    have heq : support.min' hs.1 = tool := Option.some.inj h
    have hmem : tool ∈ support := heq ▸ Finset.min'_mem support hs.1
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hmem, ?_⟩
    intro other hother
    exact (Finset.card_le_one.mp hs.2) other hother tool hmem
  next hs => cases h

def leafTools {q : Nat} (cache : IndexedNodeCache (Fin q)) : Vector (Option (Fin q)) cache.nodes.size :=
  Vector.ofFn (fun node => singletonTool (cache.decode node))

def usedCounts {q : Nat} (cache : IndexedNodeCache (Fin q)) (used : Finset (Fin q)) : IndexedCapacity cache :=
  Vector.ofFn (fun node => (used ∩ cache.decode node).card)

theorem leafTools_get {q : Nat} (cache : IndexedNodeCache (Fin q)) (node : cache.NodeId) :
    (leafTools cache).get node = singletonTool (cache.decode node) := cache_get_ofFn _ _

theorem usedCounts_get {q : Nat} (cache : IndexedNodeCache (Fin q)) (used : Finset (Fin q)) (node : cache.NodeId) :
    (usedCounts cache used).get node = (used ∩ cache.decode node).card := cache_get_ofFn _ _

def firstSlackChild {q : Nat} (cache : IndexedNodeCache (Fin q))
    (counts capacity : IndexedCapacity cache) (node : cache.NodeId) : Option cache.NodeId :=
  (cache.children.get node).toList.find? (fun child => decide (counts.get child < capacity.get child))

theorem firstSlackChild_spec {q : Nat} (cache : IndexedNodeCache (Fin q))
    (counts capacity : IndexedCapacity cache) (node child : cache.NodeId)
    (h : firstSlackChild cache counts capacity node = some child) :
    child ∈ (cache.children.get node).toList ∧ counts.get child < capacity.get child := by
  unfold firstSlackChild at h
  have htest := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, by simpa only [decide_eq_true_eq] using htest⟩

def descend {q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts capacity : IndexedCapacity cache) :
    Nat → cache.NodeId → Option (Fin q)
  | 0, _ => none
  | fuel + 1, node => match leaves.get node with
      | some tool => some tool
      | none => match firstSlackChild cache counts capacity node with
          | none => none
          | some child => descend cache leaves counts capacity fuel child

/-- A cached adjacency edge is a genuine inclusion-tree child. -/
theorem prepared_child_support (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full)
    (parent child : (prepareNormalization q full).indexed.NodeId)
    (hchild : child ∈ ((prepareNormalization q full).indexed.children.get parent).toList) :
    (prepareNormalization q full).indexed.decode child ∈
      children (nodeFamily full) ((prepareNormalization q full).indexed.decode parent) := by
  rw [← prepared_indexed_children_decode q full hq hlaminar parent]
  exact Finset.mem_image.mpr ⟨child, List.mem_toFinset.mpr hchild, rfl⟩

theorem prepared_child_index_lt (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full)
    (parent child : (prepareNormalization q full).indexed.NodeId)
    (hchild : child ∈ ((prepareNormalization q full).indexed.children.get parent).toList) :
    child.val < parent.val := by
  apply IndexedAncestors.prepared_parent_index_lt q full hq hlaminar child parent
  exact (indexNodes_child_mem _ _ child parent).mp (Array.mem_toList_iff.mp hchild)

theorem prepared_slackChild_exists (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (capacity : Finset (Fin q) → Nat)
    (hnormalized : Normalized full capacity) (used : Finset (Fin q))
    (node : (prepareNormalization q full).indexed.NodeId)
    (hinternal : 1 < ((prepareNormalization q full).indexed.decode node).card)
    (hslack : (used ∩ (prepareNormalization q full).indexed.decode node).card <
      capacity ((prepareNormalization q full).indexed.decode node)) :
    ∃ child, firstSlackChild (prepareNormalization q full).indexed
      (usedCounts (prepareNormalization q full).indexed used)
      (IndexedEntry.reifyCapacity (prepareNormalization q full).indexed capacity) node = some child := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  obtain ⟨support, hsupport, hsupportSlack⟩ := slack_child_exists full hlaminar capacity hnormalized used
    (prepared_indexed_node_mem q full node) hinternal hslack
  rw [← prepared_indexed_children_decode q full hq hlaminar node] at hsupport
  obtain ⟨child, hchild, hdecode⟩ := Finset.mem_image.mp hsupport
  have hmem : child ∈ ((prepareNormalization q full).indexed.children.get node).toList := List.mem_toFinset.mp hchild
  have hlt : (usedCounts (prepareNormalization q full).indexed used).get child <
      (IndexedEntry.reifyCapacity (prepareNormalization q full).indexed capacity).get child := by
    rw [usedCounts_get, IndexedEntry.reifyCapacity_get, hdecode]
    exact hsupportSlack
  cases hfind : firstSlackChild (prepareNormalization q full).indexed
      (usedCounts (prepareNormalization q full).indexed used)
      (IndexedEntry.reifyCapacity (prepareNormalization q full).indexed capacity) node with
  | some found => exact ⟨found, rfl⟩
  | none =>
    have hnone := List.find?_eq_none.mp hfind
    exact False.elim (hnone child hmem (by simpa only [decide_eq_true_eq] using hlt))

theorem prepared_descend_exists (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (capacity : Finset (Fin q) → Nat)
    (hnormalized : Normalized full capacity) (used : Finset (Fin q))
    (hused : used ∈ capacityFamily (layout full) capacity) (fuel : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (hindex : node.val < fuel)
    (hancestors : AncestorSlack full capacity used ((prepareNormalization q full).indexed.decode node)) :
    ∃ tool, descend (prepareNormalization q full).indexed
      (leafTools (prepareNormalization q full).indexed)
      (usedCounts (prepareNormalization q full).indexed used)
      (IndexedEntry.reifyCapacity (prepareNormalization q full).indexed capacity) fuel node = some tool ∧
      tool ∈ (prepareNormalization q full).indexed.decode node ∧ tool ∉ used ∧
        insert tool used ∈ capacityFamily (layout full) capacity := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  induction fuel generalizing node with
  | zero => omega
  | succ fuel ih =>
    have hnode := prepared_indexed_node_mem q full node
    have hslack : (used ∩ (prepareNormalization q full).indexed.decode node).card <
        capacity ((prepareNormalization q full).indexed.decode node) :=
      hancestors _ ((mem_ancestors full _ _).mpr ⟨hnode, Finset.Subset.refl _⟩)
    cases hleaf : (leafTools (prepareNormalization q full).indexed).get node with
    | some tool =>
      have hsingle : (prepareNormalization q full).indexed.decode node = {tool} :=
        singletonTool_spec _ tool (by simpa only [leafTools_get] using hleaf)
      have hunused : tool ∉ used := by
        intro ht
        have hcount : (used ∩ (prepareNormalization q full).indexed.decode node).card = 1 := by
          simp [hsingle, ht]
        have hcapacity := hnormalized.1 tool
        rw [hcount, hsingle] at hslack
        omega
      refine ⟨tool, by simp only [descend, hleaf], ?_, hunused, ?_⟩
      · rw [hsingle]
        exact Finset.mem_singleton_self _
      · apply insert_mem_capacityFamily_of_slack full capacity used hused hunused
        intro ancestor hancestor htool
        apply hancestors ancestor
        apply (mem_ancestors full _ _).mpr
        refine ⟨hancestor, ?_⟩
        rw [hsingle]
        exact Finset.singleton_subset_iff.mpr htool
    | none =>
      have hnonempty := nodeFamily_nonempty_nodes full _ hnode
      have hinternal : 1 < ((prepareNormalization q full).indexed.decode node).card := by
        by_contra hn
        have hone : ((prepareNormalization q full).indexed.decode node).card = 1 := by
          have hp := Finset.card_pos.mpr hnonempty
          omega
        obtain ⟨tool, hsingle⟩ := Finset.card_eq_one.mp hone
        have hsome : (leafTools (prepareNormalization q full).indexed).get node = some tool := by
          rw [leafTools_get, hsingle]
          exact singletonTool_singleton tool
        rw [hleaf] at hsome
        cases hsome
      obtain ⟨child, hchild⟩ := prepared_slackChild_exists q full hq hlaminar capacity hnormalized used node hinternal hslack
      have hspec := firstSlackChild_spec (prepareNormalization q full).indexed
        (usedCounts (prepareNormalization q full).indexed used)
        (IndexedEntry.reifyCapacity (prepareNormalization q full).indexed capacity) node child hchild
      have hsupport := prepared_child_support q full hq hlaminar node child hspec.1
      have hchildSlack : (used ∩ (prepareNormalization q full).indexed.decode child).card <
          capacity ((prepareNormalization q full).indexed.decode child) := by
        simpa only [usedCounts_get, IndexedEntry.reifyCapacity_get] using hspec.2
      have hchildAncestors := ancestorSlack_child full hlaminar capacity used hancestors hsupport hchildSlack
      have hchildIndex := prepared_child_index_lt q full hq hlaminar node child hspec.1
      obtain ⟨tool, hresult, htool, hunused, hinsert⟩ := ih child (by omega) hchildAncestors
      refine ⟨tool, ?_, ?_, hunused, hinsert⟩
      · simp only [descend, hleaf, hchild]
        exact hresult
      · exact ((mem_children_iff (nodeFamily_laminar full hlaminar)
          (nodeFamily_nonempty_nodes full) _ _).mp hsupport).2.2.1.subset htool

/-- One lookup-only descent with fuel t, on the existing prepared cache. -/
def selectAt {q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts capacity : IndexedCapacity cache)
    (node : cache.NodeId) : Option (Fin q) := descend cache leaves counts capacity cache.nodes.size node

theorem prepared_selectAt_exists (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (capacity : Finset (Fin q) → Nat)
    (hnormalized : Normalized full capacity) (used : Finset (Fin q))
    (hused : used ∈ capacityFamily (layout full) capacity)
    (node : (prepareNormalization q full).indexed.NodeId)
    (hancestors : AncestorSlack full capacity used ((prepareNormalization q full).indexed.decode node)) :
    ∃ tool, selectAt (prepareNormalization q full).indexed
      (leafTools (prepareNormalization q full).indexed)
      (usedCounts (prepareNormalization q full).indexed used)
      (IndexedEntry.reifyCapacity (prepareNormalization q full).indexed capacity) node = some tool ∧
      tool ∈ (prepareNormalization q full).indexed.decode node ∧ tool ∉ used ∧
        insert tool used ∈ capacityFamily (layout full) capacity :=
  prepared_descend_exists q full hq hlaminar capacity hnormalized used hused _ node node.isLt hancestors

/-- The query consumes the existing cached stage node. It performs no
support-set search, node reconstruction or candidate-tool enumeration. -/
def selectStage {q stageCount : Nat} (cache : IndexedNodeCache (Fin q))
    (stages : Vector (Option cache.NodeId) stageCount)
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts capacity : IndexedCapacity cache)
    (stage : Fin stageCount) : Option (Fin q) :=
  (stages.get stage).bind (selectAt cache leaves counts capacity)

theorem prepared_selectStage_exists (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (capacity : Finset (Fin q) → Nat)
    (hnormalized : Normalized full capacity) (used : Finset (Fin q))
    (hused : used ∈ capacityFamily (layout full) capacity) (stage : Fin full.length)
    (hnonempty : full[stage.val] ≠ ∅) (hancestors : AncestorSlack full capacity used full[stage.val]) :
    ∃ tool, selectStage (prepareNormalization q full).indexed
      (IndexedStaticMetadata.buildPositive q full hq).stageNodes
      (leafTools (prepareNormalization q full).indexed)
      (usedCounts (prepareNormalization q full).indexed used)
      (IndexedEntry.reifyCapacity (prepareNormalization q full).indexed capacity) stage = some tool ∧
      tool ∈ full[stage.val] ∧ tool ∉ used ∧ insert tool used ∈ capacityFamily (layout full) capacity := by
  obtain ⟨node, hnode, hdecode⟩ := IndexedStaticMetadata.buildPositive_stage_nonempty q full hq stage hnonempty
  have ha : AncestorSlack full capacity used ((prepareNormalization q full).indexed.decode node) := by
    rw [hdecode]
    exact hancestors
  obtain ⟨tool, hresult, htool, hunused, hinsert⟩ :=
    prepared_selectAt_exists q full hq hlaminar capacity hnormalized used hused node ha
  refine ⟨tool, ?_, ?_, hunused, hinsert⟩
  · simp only [selectStage, hnode, Option.bind_some]
    exact hresult
  · rw [← hdecode]
    exact htool

/-- The visited-node trace follows exactly the query's branching. Its
length counts recursive node visits, not child-array reads or RAM steps. -/
def descentTrace {q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts capacity : IndexedCapacity cache) :
    Nat → cache.NodeId → List cache.NodeId
  | 0, _ => []
  | fuel + 1, node => node :: match leaves.get node with
      | some _ => []
      | none => match firstSlackChild cache counts capacity node with
          | none => []
          | some child => descentTrace cache leaves counts capacity fuel child

theorem descentTrace_length_le {q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts capacity : IndexedCapacity cache)
    (fuel : Nat) (node : cache.NodeId) :
    (descentTrace cache leaves counts capacity fuel node).length ≤ fuel := by
  induction fuel generalizing node with
  | zero => exact Nat.le_refl 0
  | succ fuel ih =>
    cases hl : leaves.get node with
    | some tool => simp only [descentTrace, hl, List.length_singleton]; omega
    | none =>
      cases hc : firstSlackChild cache counts capacity node with
      | none => simp only [descentTrace, hl, hc, List.length_singleton]; omega
      | some child =>
        simpa only [descentTrace, hl, hc, List.length_cons] using Nat.succ_le_succ (ih child)

/-- Exact number of child entries examined by the existing first-hit scan. -/
def childProbeCount {q : Nat} {cache : IndexedNodeCache (Fin q)}
    (counts capacity : IndexedCapacity cache) : List cache.NodeId → Nat
  | [] => 0
  | child :: later => if counts.get child < capacity.get child then 1 else
      1 + childProbeCount counts capacity later

theorem childProbeCount_le_length {q : Nat} {cache : IndexedNodeCache (Fin q)}
    (counts capacity : IndexedCapacity cache) (children : List cache.NodeId) :
    childProbeCount counts capacity children ≤ children.length := by
  induction children with
  | nil => exact Nat.le_refl 0
  | cons child later ih =>
    simp only [childProbeCount, List.length_cons]
    split <;> omega

/-- Query work in the exact units claimed in A:69: visited nodes and
tested child entries. This is not a Lean-host or finite-word RAM model. -/
def descentWork {q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts capacity : IndexedCapacity cache) :
    Nat → cache.NodeId → Nat
  | 0, _ => 0
  | fuel + 1, node => 1 + match leaves.get node with
      | some _ => 0
      | none => childProbeCount counts capacity (cache.children.get node).toList +
          match firstSlackChild cache counts capacity node with
          | none => 0
          | some child => descentWork cache leaves counts capacity fuel child

theorem descentWork_le_trace {q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts capacity : IndexedCapacity cache)
    (fuel : Nat) (node : cache.NodeId) :
    descentWork cache leaves counts capacity fuel node ≤
      (descentTrace cache leaves counts capacity fuel node).length +
        ((descentTrace cache leaves counts capacity fuel node).map
          (fun parent => (cache.children.get parent).size)).sum := by
  induction fuel generalizing node with
  | zero => exact Nat.le_refl 0
  | succ fuel ih =>
    have hp := childProbeCount_le_length counts capacity (cache.children.get node).toList
    rw [Array.length_toList] at hp
    cases hl : leaves.get node with
    | some tool =>
      simp only [descentWork, descentTrace, hl, List.length_singleton, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      exact Nat.le_add_right _ _
    | none =>
      cases hc : firstSlackChild cache counts capacity node with
      | none =>
        simp only [descentWork, descentTrace, hl, hc, List.length_singleton, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        exact Nat.add_le_add_left hp 1
      | some child =>
        have ht := ih child
        simp only [descentWork, descentTrace, hl, hc, List.length_cons, List.map_cons, List.sum_cons]
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          Nat.add_le_add_left (Nat.add_le_add hp ht) 1

theorem descentTrace_index_le {q : Nat} (cache : IndexedNodeCache (Fin q))
    (hdown : ∀ parent child, child ∈ (cache.children.get parent).toList → child.val < parent.val)
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts capacity : IndexedCapacity cache)
    (fuel : Nat) (node target : cache.NodeId)
    (hmem : target ∈ descentTrace cache leaves counts capacity fuel node) : target.val ≤ node.val := by
  induction fuel generalizing node with
  | zero => cases hmem
  | succ fuel ih =>
    simp only [descentTrace, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact Nat.le_refl _
    · cases hl : leaves.get node with
      | some tool => simp only [hl, List.not_mem_nil] at hmem
      | none =>
        cases hc : firstSlackChild cache counts capacity node with
        | none => simp only [hl, hc, List.not_mem_nil] at hmem
        | some child =>
          have ht : target ∈ descentTrace cache leaves counts capacity fuel child := by simpa only [hl, hc] using hmem
          exact (ih child ht).trans (hdown node child (firstSlackChild_spec cache counts capacity node child hc).1).le

theorem descentTrace_nodup {q : Nat} (cache : IndexedNodeCache (Fin q))
    (hdown : ∀ parent child, child ∈ (cache.children.get parent).toList → child.val < parent.val)
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts capacity : IndexedCapacity cache)
    (fuel : Nat) (node : cache.NodeId) : (descentTrace cache leaves counts capacity fuel node).Nodup := by
  induction fuel generalizing node with
  | zero => exact List.nodup_nil
  | succ fuel ih =>
    cases hl : leaves.get node with
    | some tool => simp only [descentTrace, hl, List.nodup_singleton]
    | none =>
      cases hc : firstSlackChild cache counts capacity node with
      | none => simp only [descentTrace, hl, hc, List.nodup_singleton]
      | some child =>
        simp only [descentTrace, hl, hc, List.nodup_cons]
        refine ⟨?_, ih child⟩
        intro hmem
        have hle := descentTrace_index_le cache hdown leaves counts capacity fuel child node hmem
        exact (not_le_of_gt (hdown node child (firstSlackChild_spec cache counts capacity node child hc).1)) hle

/-- The real tree's t-1 edges amortize child-array scans across the entire
descent. Thus node visits PLUS child entries examined are at most 2t.
The cost of constructing counts and metadata is not included in this query. -/
theorem prepared_descentWork_le_twice_nodes (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full)
    (leaves : Vector (Option (Fin q)) (prepareNormalization q full).indexed.nodes.size)
    (counts capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (node : (prepareNormalization q full).indexed.NodeId) :
    descentWork (prepareNormalization q full).indexed leaves counts capacity
      (prepareNormalization q full).indexed.nodes.size node ≤
        2 * (prepareNormalization q full).indexed.nodes.size := by
  let cache := (prepareNormalization q full).indexed
  let trace := descentTrace cache leaves counts capacity cache.nodes.size node
  have hnd : trace.Nodup := descentTrace_nodup cache
    (fun parent child hc => prepared_child_index_lt q full hq hlaminar parent child hc) leaves counts capacity _ node
  have hsum : (trace.map (fun parent => (cache.children.get parent).size)).sum ≤
      ∑ parent : cache.NodeId, (cache.children.get parent).size := by
    rw [← List.sum_toFinset _ hnd]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; exact Nat.zero_le _)
  have hedge := prepared_indexed_edge_count q full hq hlaminar
  have hlength := descentTrace_length_le cache leaves counts capacity cache.nodes.size node
  have hwork := descentWork_le_trace cache leaves counts capacity cache.nodes.size node
  change (trace.map (fun parent => (cache.children.get parent).size)).sum ≤ _ at hsum
  change (∑ parent : cache.NodeId, (cache.children.get parent).size) = cache.nodes.size - 1 at hedge
  change trace.length ≤ cache.nodes.size at hlength
  change descentWork cache leaves counts capacity cache.nodes.size node ≤
    trace.length + (trace.map (fun parent => (cache.children.get parent).size)).sum at hwork
  change descentWork cache leaves counts capacity cache.nodes.size node ≤ 2 * cache.nodes.size
  omega

end PaperProofs.Structure.LaminarTree.IndexedDescent
