module

public import PaperProofs.Structure.IndexedAncestors
import Lean.Elab.Tactic.Omega

/-!
Static stage and singleton lookup data for the positive-tool tree branch.
The constructor performs the existing finite support searches once. A cell
then accepts an optional NodeId, so it does not search for its stage support.
These are concrete vectors, with external correctness theorems. No runtime,
host Vector-access, packed-access, or word-RAM cost claim is made here. The
original zero-tool direct branch continues to require no tree.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.IndexedStaticMetadata

variable {Tool : Type*}

structure Data {q : Nat} (cache : IndexedNodeCache (Fin q)) (stageCount : Nat) where
  stageNodes : Vector (Option cache.NodeId) stageCount
  toolNodes : Vector cache.NodeId q

/-- Finite lookup extraction from a supplied cache. The proof is erased and
the runtime operation is the existing finite find followed by Option.get. -/
def singletonNodeIn {q : Nat} (cache : IndexedNodeCache (Fin q))
    (hfound : ∀ tool : Fin q, (findNodeId cache.nodes {tool}).isSome) (tool : Fin q) : cache.NodeId :=
  (findNodeId cache.nodes {tool}).get (hfound tool)

def buildFromCache {q : Nat} (cache : IndexedNodeCache (Fin q)) (full : List (Finset (Fin q)))
    (hfound : ∀ tool : Fin q, (findNodeId cache.nodes {tool}).isSome) : Data cache full.length where
  stageNodes := Vector.ofFn (fun stage => if full[stage.val] = ∅ then none else findNodeId cache.nodes full[stage.val])
  toolNodes := Vector.ofFn (singletonNodeIn cache hfound)

theorem singletonLookup_isSome (q : Nat) (full : List (Finset (Fin q))) (tool : Fin q) :
    (findNodeId (prepareNormalization q full).indexed.nodes {tool}).isSome := by
  obtain ⟨node, hdecode⟩ := prepared_indexed_node_exists q full {tool} (singleton_mem full tool)
  have hfind := (findNodeId_eq_some_iff _ (prepared_indexed_nodes_nodup q full) {tool} node).mpr hdecode
  rw [hfind]
  rfl

/-- Computable lookup extraction: no choice and no separately supplied node. -/
def singletonNode (q : Nat) (full : List (Finset (Fin q))) (tool : Fin q) :
    (prepareNormalization q full).indexed.NodeId :=
  singletonNodeIn (prepareNormalization q full).indexed (singletonLookup_isSome q full) tool

theorem singletonNode_lookup (q : Nat) (full : List (Finset (Fin q))) (tool : Fin q) :
    findNodeId (prepareNormalization q full).indexed.nodes {tool} = some (singletonNode q full tool) :=
  (Option.some_get (singletonLookup_isSome q full tool)).symm

theorem singletonNode_decode (q : Nat) (full : List (Finset (Fin q))) (tool : Fin q) :
    (prepareNormalization q full).indexed.decode (singletonNode q full tool) = {tool} :=
  findNodeId_decode _ _ _ (singletonNode_lookup q full tool)

/-- Only the positive-q path constructs a tree. All fields are actual data. -/
def buildPositive (q : Nat) (full : List (Finset (Fin q))) (_hq : 0 < q) :
    Data (prepareNormalization q full).indexed full.length :=
  let cache := (prepareNormalization q full).indexed
  buildFromCache cache full (singletonLookup_isSome q full)

theorem buildPositive_stage_get (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (stage : Fin full.length) :
    ((buildPositive q full hq).stageNodes).get stage =
      if full[stage.val] = ∅ then none else findNodeId (prepareNormalization q full).indexed.nodes full[stage.val] :=
  cache_get_ofFn _ _

theorem buildPositive_tool_get (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (tool : Fin q) :
    ((buildPositive q full hq).toolNodes).get tool = singletonNode q full tool :=
  cache_get_ofFn _ _

theorem buildPositive_stage_some_iff (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (stage : Fin full.length) (node : (prepareNormalization q full).indexed.NodeId) :
    ((buildPositive q full hq).stageNodes).get stage = some node ↔
      full[stage.val] ≠ ∅ ∧ (prepareNormalization q full).indexed.decode node = full[stage.val] := by
  rw [buildPositive_stage_get]
  by_cases hempty : full[stage.val] = ∅
  · simp [hempty]
  · rw [ite_eq_right hempty]
    constructor
    · intro hfind
      exact ⟨hempty, (findNodeId_eq_some_iff _ (prepared_indexed_nodes_nodup q full) full[stage.val] node).mp hfind⟩
    · intro hfields
      exact (findNodeId_eq_some_iff _ (prepared_indexed_nodes_nodup q full) full[stage.val] node).mpr hfields.2

theorem buildPositive_stage_none_iff (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (stage : Fin full.length) :
    ((buildPositive q full hq).stageNodes).get stage = none ↔ full[stage.val] = ∅ := by
  rw [buildPositive_stage_get]
  by_cases hempty : full[stage.val] = ∅
  · simp only [hempty, ↓reduceIte]
  · rw [ite_eq_right hempty]
    obtain ⟨node, hdecode⟩ := prepared_indexed_node_exists q full full[stage.val]
      (nonempty_stage_mem full (List.getElem_mem stage.isLt) (Finset.nonempty_iff_ne_empty.mpr hempty))
    have hfind := (findNodeId_eq_some_iff _ (prepared_indexed_nodes_nodup q full) full[stage.val] node).mpr hdecode
    simp only [hfind, Option.some_ne_none, hempty]

theorem buildPositive_stage_nonempty (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (stage : Fin full.length) (hnonempty : full[stage.val] ≠ ∅) :
    ∃ node, ((buildPositive q full hq).stageNodes).get stage = some node ∧
      (prepareNormalization q full).indexed.decode node = full[stage.val] := by
  cases hstage : ((buildPositive q full hq).stageNodes).get stage with
  | none => exact False.elim (hnonempty ((buildPositive_stage_none_iff q full hq stage).mp hstage))
  | some node => exact ⟨node, rfl, ((buildPositive_stage_some_iff q full hq stage node).mp hstage).2⟩

theorem buildPositive_tool_decode (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (tool : Fin q) :
    (prepareNormalization q full).indexed.decode (((buildPositive q full hq).toolNodes).get tool) = {tool} := by
  rw [buildPositive_tool_get]
  exact singletonNode_decode q full tool

theorem buildPositive_tool_injective (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    Function.Injective (fun tool => ((buildPositive q full hq).toolNodes).get tool) := by
  intro left right heq
  change ((buildPositive q full hq).toolNodes).get left = ((buildPositive q full hq).toolNodes).get right at heq
  have hsingle : ({left} : Finset (Fin q)) = {right} := by
    rw [← buildPositive_tool_decode q full hq left, heq, buildPositive_tool_decode q full hq right]
  exact Finset.singleton_inj.mp hsingle

theorem buildPositive_stage_size (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    (buildPositive q full hq).stageNodes.toArray.size = full.length := Vector.size_toArray _

theorem buildPositive_tool_size (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    (buildPositive q full hq).toolNodes.toArray.size = q := Vector.size_toArray _

theorem buildPositive_lookup_entries (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    (buildPositive q full hq).stageNodes.toArray.size +
      (buildPositive q full hq).toolNodes.toArray.size = full.length + q := by
  rw [buildPositive_stage_size, buildPositive_tool_size]

theorem buildPositive_cache_size_le (q : Nat) (full : List (Finset (Fin q))) :
    (prepareNormalization q full).indexed.nodes.size ≤ full.length + q + 1 :=
  prepared_indexed_size_le q full

/-- A cell consumes the already cached NodeId, not a support set. -/
def extendAt (cache : IndexedNodeCache Tool) (node : Option cache.NodeId) :
    IndexedEntry.FixedEntry cache → IndexedEntry.FixedEntry cache
  | .void => .void
  | .vector capacity => match node with
      | none => .void
      | some start => if IndexedAncestors.chainZero cache capacity start then .void
          else .vector (IndexedAncestors.chainDecrement cache capacity start)

theorem extendAt_none (cache : IndexedNodeCache Tool) (entry : IndexedEntry.FixedEntry cache) :
    extendAt cache none entry = .void := by cases entry <;> rfl

theorem extendAt_find_eq [DecidableEq Tool] (cache : IndexedNodeCache Tool) (eligible : Finset Tool)
    (entry : IndexedEntry.FixedEntry cache) :
    extendAt cache (if eligible = ∅ then none else findNodeId cache.nodes eligible) entry =
      IndexedAncestors.chainExtend cache eligible entry := by
  cases entry with
  | void => rfl
  | vector capacity =>
    by_cases hempty : eligible = ∅
    · simp only [extendAt, IndexedAncestors.chainExtend, hempty, ↓reduceIte]
    · simp only [extendAt, IndexedAncestors.chainExtend, hempty, ↓reduceIte]
      cases findNodeId cache.nodes eligible <;> rfl

def cellAt (cache : IndexedNodeCache Tool) (node : Option cache.NodeId)
    (good bad : IndexedEntry.FixedEntry cache) : IndexedEntry.FixedEntry cache :=
  IndexedEntry.intersect cache good (extendAt cache node bad)

def budgetCellAt (cache : IndexedNodeCache Tool) (node : Option cache.NodeId) (budget : Nat)
    (good bad : IndexedEntry.FixedEntry cache) : IndexedEntry.FixedEntry cache :=
  if budget = 0 then IndexedEntry.free cache else cellAt cache node good bad

theorem buildPositive_extendAt_eq_chain (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (stage : Fin full.length) (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) :
    extendAt (prepareNormalization q full).indexed (((buildPositive q full hq).stageNodes).get stage) entry =
      IndexedAncestors.chainExtend (prepareNormalization q full).indexed full[stage.val] entry := by
  rw [buildPositive_stage_get]
  exact extendAt_find_eq _ _ _

theorem buildPositive_extendAt_eq_indexed (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (stage : Fin full.length)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) :
    extendAt (prepareNormalization q full).indexed (((buildPositive q full hq).stageNodes).get stage) entry =
      IndexedEntry.extend (prepareNormalization q full).indexed full[stage.val] entry := by
  rw [buildPositive_extendAt_eq_chain]
  apply IndexedAncestors.prepared_chainExtend_eq q full hq hlaminar
  by_cases hempty : full[stage.val] = ∅
  · exact Or.inl hempty
  · exact Or.inr (nonempty_stage_mem full (List.getElem_mem stage.isLt) (Finset.nonempty_iff_ne_empty.mpr hempty))

theorem buildPositive_cellAt_eq_indexed (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (stage : Fin full.length)
    (good bad : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) :
    cellAt (prepareNormalization q full).indexed (((buildPositive q full hq).stageNodes).get stage) good bad =
      IndexedEntry.cell (prepareNormalization q full).indexed full[stage.val] good bad := by
  rw [cellAt, buildPositive_extendAt_eq_indexed q full hq hlaminar]
  rfl

theorem buildPositive_budgetCellAt_eq_indexed (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (stage : Fin full.length) (budget : Nat)
    (good bad : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) :
    budgetCellAt (prepareNormalization q full).indexed (((buildPositive q full hq).stageNodes).get stage)
      budget good bad = IndexedEntry.budgetCell (prepareNormalization q full).indexed full[stage.val] budget good bad := by
  simp only [budgetCellAt, IndexedEntry.budgetCell, buildPositive_cellAt_eq_indexed q full hq hlaminar]

theorem budgetCellAt_zero (cache : IndexedNodeCache Tool) (node : Option cache.NodeId)
    (good bad : IndexedEntry.FixedEntry cache) : budgetCellAt cache node 0 good bad = IndexedEntry.free cache := rfl

end PaperProofs.Structure.LaminarTree.IndexedStaticMetadata
