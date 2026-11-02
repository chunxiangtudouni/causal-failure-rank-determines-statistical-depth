module

public import PaperProofs.Structure.LaminarNormalize
public import Mathlib.Data.List.Nodup
public import Init.Data.List.FinRange

/-!
Indexed, materialized parent and child adjacency for one prepared node order.
All fields are actual finite data. Their agreement with the original inclusion
tree is proved separately below, rather than required as structure fields.
No operation-count, word-access or bit-storage bound is assumed or asserted.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree

structure IndexedNodeCache (Tool : Type*) where
  nodes : Array (Finset Tool)
  parents : Vector (Option (Fin nodes.size)) nodes.size
  children : Vector (Array (Fin nodes.size)) nodes.size

abbrev IndexedNodeCache.NodeId {Tool : Type*} (cache : IndexedNodeCache Tool) := Fin cache.nodes.size

def IndexedNodeCache.decode {Tool : Type*} (cache : IndexedNodeCache Tool)
    (node : cache.NodeId) : Finset Tool := cache.nodes[node.val]

theorem cache_get_ofFn {α : Type*} {size : Nat} (f : Fin size → α) (index : Fin size) :
    (Vector.ofFn f).get index = f index := by
  change (Vector.ofFn f)[index.val] = f index
  simp

variable {Tool : Type*} [DecidableEq Tool]

/-- A finite preprocessing lookup, with no choice of a node index. -/
def findNodeId (nodes : Array (Finset Tool)) (support : Finset Tool) : Option (Fin nodes.size) :=
  (List.finRange nodes.size).find? (fun index => decide (nodes[index.val] = support))

theorem findNodeId_decode (nodes : Array (Finset Tool)) (support : Finset Tool)
    (index : Fin nodes.size) (hfind : findNodeId nodes support = some index) :
    nodes[index.val] = support := by
  have h := List.find?_some hfind
  simpa only [decide_eq_true_eq] using h

theorem findNodeId_exists (nodes : Array (Finset Tool)) (support : Finset Tool)
    (hmem : support ∈ nodes.toList) : ∃ index, findNodeId nodes support = some index := by
  obtain ⟨position, hposition, hsupport⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hmem)
  cases hfind : findNodeId nodes support with
  | some index => exact ⟨index, rfl⟩
  | none =>
    have hnone := List.find?_eq_none.mp hfind
    have h := hnone ⟨position, hposition⟩ (List.mem_finRange _)
    exact False.elim (h (by simp only [hsupport, decide_true]))

omit [DecidableEq Tool] in
theorem nodeArray_decode_injective (nodes : Array (Finset Tool)) (hnodup : nodes.toList.Nodup) :
    Function.Injective (fun index : Fin nodes.size => nodes[index.val]) := by
  intro left right heq
  have hleft : left.val < nodes.toList.length := by simpa only [Array.length_toList] using left.isLt
  have hright : right.val < nodes.toList.length := by simpa only [Array.length_toList] using right.isLt
  have hlist : nodes.toList[left.val]'hleft = nodes.toList[right.val]'hright := by
    simpa only [Array.getElem_toList] using heq
  exact Fin.ext (hnodup.getElem_inj.mp hlist)

theorem findNodeId_eq_some_iff (nodes : Array (Finset Tool)) (hnodup : nodes.toList.Nodup)
    (support : Finset Tool) (index : Fin nodes.size) :
    findNodeId nodes support = some index ↔ nodes[index.val] = support := by
  constructor
  · exact findNodeId_decode nodes support index
  · intro heq
    have hmem : support ∈ nodes.toList := heq ▸ Array.getElem_mem_toList index.isLt
    obtain ⟨found, hfound⟩ := findNodeId_exists nodes support hmem
    have hsame : found = index := nodeArray_decode_injective nodes hnodup
      ((findNodeId_decode nodes support found hfound).trans heq.symm)
    exact hsame ▸ hfound

/-- Preserve the actual prepared parent table; only translate supports to IDs. -/
def NormalizationData.parentSupport (data : NormalizationData Tool) (node : Finset Tool) :
    Option (Finset Tool) := (data.parentTable.lookup node).join

def indexNodes (nodes : Array (Finset Tool)) (sourceParent : Finset Tool → Option (Finset Tool)) :
    IndexedNodeCache Tool :=
  let parents := Vector.ofFn (fun child : Fin nodes.size =>
    (sourceParent nodes[child.val]).bind (findNodeId nodes))
  { nodes := nodes
    parents := parents
    children := Vector.ofFn (fun parent =>
      ((List.finRange nodes.size).filter (fun child => decide (parents.get child = some parent))).toArray) }

def NormalizationData.indexed (data : NormalizationData Tool) : IndexedNodeCache Tool :=
  indexNodes data.order.toArray data.parentSupport

theorem indexNodes_parent_get (nodes : Array (Finset Tool))
    (sourceParent : Finset Tool → Option (Finset Tool)) (child : Fin nodes.size) :
    (indexNodes nodes sourceParent).parents.get child =
      (sourceParent nodes[child.val]).bind (findNodeId nodes) := cache_get_ofFn _ _

theorem indexNodes_parent_iff (nodes : Array (Finset Tool)) (hnodup : nodes.toList.Nodup)
    (sourceParent : Finset Tool → Option (Finset Tool)) (child parent : Fin nodes.size) :
    (indexNodes nodes sourceParent).parents.get child = some parent ↔
      sourceParent nodes[child.val] = some nodes[parent.val] := by
  rw [indexNodes_parent_get]
  cases hsource : sourceParent nodes[child.val] with
  | none => simp
  | some support =>
    simp only [Option.bind_some, Option.some.injEq]
    exact (findNodeId_eq_some_iff nodes hnodup support parent).trans eq_comm

theorem indexNodes_child_mem (nodes : Array (Finset Tool))
    (sourceParent : Finset Tool → Option (Finset Tool)) (child parent : Fin nodes.size) :
    child ∈ (indexNodes nodes sourceParent).children.get parent ↔
      (indexNodes nodes sourceParent).parents.get child = some parent := by
  let parents : Vector (Option (Fin nodes.size)) nodes.size := Vector.ofFn
    (fun child : Fin nodes.size => (sourceParent nodes[child.val]).bind (findNodeId nodes))
  change child ∈ (Vector.ofFn (fun parent : Fin nodes.size =>
    ((List.finRange nodes.size).filter (fun child => decide (parents.get child = some parent))).toArray)).get
      parent ↔ parents.get child = some parent
  rw [cache_get_ofFn, List.mem_toArray, List.mem_filter]
  simp only [List.mem_finRange, true_and, decide_eq_true_eq]

theorem prepared_order_nodup (q : Nat) (full : List (Finset (Fin q))) :
    (prepareNormalization q full).order.Nodup := by
  change ((explicitNodeList q full).mergeSort _).Nodup
  exact (explicitNodeList_nodup q full).mergeSort

theorem prepared_parentSupport (q : Nat) (full : List (Finset (Fin q)))
    (node : Finset (Fin q)) (hnode : node ∈ nodeFamily full) :
    (prepareNormalization q full).parentSupport node = explicitParent q full node := by
  have hlist : node ∈ explicitNodeList q full := by
    apply List.mem_toFinset.mp
    rw [explicitNodeList_toFinset]
    exact hnode
  simp only [NormalizationData.parentSupport, prepareNormalization,
    List.lookup_graph (fun child => parentFromList (explicitNodeList q full) child) hlist,
    Option.join_some, explicitParent]

theorem prepared_indexed_node_mem (q : Nat) (full : List (Finset (Fin q)))
    (index : (prepareNormalization q full).indexed.NodeId) :
    (prepareNormalization q full).indexed.decode index ∈ nodeFamily full := by
  apply (mem_preparedOrder q full _).mp
  exact Array.getElem_mem_toList index.isLt

theorem prepared_indexed_size_le (q : Nat) (full : List (Finset (Fin q))) :
    (prepareNormalization q full).indexed.nodes.size ≤ full.length + q + 1 := by
  exact prepared_order_length_le q full

theorem prepared_indexed_decode_injective (q : Nat) (full : List (Finset (Fin q))) :
    Function.Injective (prepareNormalization q full).indexed.decode := by
  unfold IndexedNodeCache.decode
  apply nodeArray_decode_injective
  change (prepareNormalization q full).order.toArray.toList.Nodup
  simpa only [List.toList_toArray] using prepared_order_nodup q full

theorem prepared_indexed_node_exists (q : Nat) (full : List (Finset (Fin q)))
    (node : Finset (Fin q)) (hnode : node ∈ nodeFamily full) :
    ∃ index : (prepareNormalization q full).indexed.NodeId,
      (prepareNormalization q full).indexed.decode index = node := by
  have hmem : node ∈ (prepareNormalization q full).order.toArray.toList := by
    simpa only [List.toList_toArray] using (mem_preparedOrder q full node).mpr hnode
  obtain ⟨index, hfind⟩ := findNodeId_exists _ node hmem
  exact ⟨index, findNodeId_decode _ node index hfind⟩

theorem prepared_indexed_parent_iff (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (child parent : (prepareNormalization q full).indexed.NodeId) :
    (prepareNormalization q full).indexed.parents.get child = some parent ↔
      IsParent (nodeFamily full) ((prepareNormalization q full).indexed.decode child)
        ((prepareNormalization q full).indexed.decode parent) := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have hnodup : (prepareNormalization q full).order.toArray.toList.Nodup := by
    simpa only [List.toList_toArray] using prepared_order_nodup q full
  have hcache : (prepareNormalization q full).indexed.parents.get child = some parent ↔
      (prepareNormalization q full).parentSupport ((prepareNormalization q full).indexed.decode child) =
        some ((prepareNormalization q full).indexed.decode parent) :=
    indexNodes_parent_iff _ hnodup _ child parent
  rw [hcache]
  rw [prepared_parentSupport q full _ (prepared_indexed_node_mem q full child),
    explicitParent_agrees q full hq hlaminar (prepared_indexed_node_mem q full child)]
  exact parent?_eq_some_iff (nodeFamily_laminar full hlaminar)
    (nodeFamily_nonempty_nodes full _ (prepared_indexed_node_mem q full child))

/-- Every cached child ID decodes to precisely a genuine child of the same
original tree, and every genuine child has an ID in that cached adjacency. -/
theorem prepared_indexed_children_decode (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (parent : (prepareNormalization q full).indexed.NodeId) :
    (((prepareNormalization q full).indexed.children.get parent).toList.toFinset.image
      (prepareNormalization q full).indexed.decode) =
        children (nodeFamily full) ((prepareNormalization q full).indexed.decode parent) := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  ext node
  rw [Finset.mem_image]
  constructor
  · rintro ⟨child, hchild, rfl⟩
    apply (mem_children_iff (nodeFamily_laminar full hlaminar) (nodeFamily_nonempty_nodes full) _ _).mpr
    refine ⟨prepared_indexed_node_mem q full child, ?_⟩
    apply (prepared_indexed_parent_iff q full hq hlaminar child parent).mp
    exact (indexNodes_child_mem _ _ child parent).mp
      (Array.mem_toList_iff.mp (List.mem_toFinset.mp hchild))
  · intro hchild
    obtain ⟨hactive, hparent⟩ := (mem_children_iff (nodeFamily_laminar full hlaminar)
      (nodeFamily_nonempty_nodes full) _ _).mp hchild
    obtain ⟨child, hdecode⟩ := prepared_indexed_node_exists q full node hactive
    refine ⟨child, List.mem_toFinset.mpr (Array.mem_toList_iff.mpr ?_), hdecode⟩
    apply (indexNodes_child_mem _ _ child parent).mpr
    apply (prepared_indexed_parent_iff q full hq hlaminar child parent).mpr
    simpa only [hdecode] using hparent

end PaperProofs.Structure.LaminarTree
