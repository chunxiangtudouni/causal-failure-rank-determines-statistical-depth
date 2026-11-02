module

public import PaperProofs.Structure.LaminarNormalize
public import PaperProofs.Structure.UsedGame
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.Infix
public import Init.Data.Vector.OfFn
import Lean.Elab.Tactic.Omega

/-!
A13: a bottom-up capacity table on one fixed full-input tree.
The independent target is `safeUsedFamily`, already defined from causal plays.
Rows are actual finite Vectors; active capacity coordinates are materialized
between layers to avoid retaining a recursively evaluated capacity-expression
DAG. Lookup and normalization cost certificates are separate obligations.
The public constructor includes an actual zero-tool branch, which prepares no
tree and uses the already proved operational no-tools boundary.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree

variable {Tool : Type*} [DecidableEq Tool]

/-- Eager finite coordinate bindings. Only active nodes are semantically used. -/
def NormalizationData.materializeCapacity (data : NormalizationData Tool)
    (capacity : Finset Tool → Nat) : Finset Tool → Nat :=
  let bindings := data.order.map (fun node => (node, capacity node))
  fun node => (bindings.lookup node).getD 0

theorem materializeCapacity_at (data : NormalizationData Tool)
    (capacity : Finset Tool → Nat) (node : Finset Tool) (hnode : node ∈ data.order) :
    data.materializeCapacity capacity node = capacity node := by
  simp only [NormalizationData.materializeCapacity, List.lookup_graph capacity hnode,
    Option.getD_some]

def NormalizationData.materializeEntry (data : NormalizationData Tool) :
    CapacityEntry (Finset Tool) → CapacityEntry (Finset Tool)
  | .void => .void
  | .vector capacity => .vector (data.materializeCapacity capacity)

theorem prepared_materializeEntry_sound (q : Nat) (full : List (Finset (Fin q)))
    (entry : CapacityEntry (Finset (Fin q))) :
    ((prepareNormalization q full).materializeEntry entry).denote (layout full) =
      entry.denote (layout full) := by
  cases entry with
  | void => rfl
  | vector capacity =>
    ext used
    constructor
    · intro hused node hnode
      have heq := materializeCapacity_at (prepareNormalization q full) capacity node
        ((mem_preparedOrder q full node).mpr hnode)
      exact heq ▸ hused node hnode
    · intro hused node hnode
      have heq := materializeCapacity_at (prepareNormalization q full) capacity node
        ((mem_preparedOrder q full node).mpr hnode)
      exact heq.symm ▸ hused node hnode

theorem prepared_materializeCapacity_normalized (q : Nat) (full : List (Finset (Fin q)))
    (capacity : Finset (Fin q) → Nat) (hnormalized : Normalized full capacity) :
    Normalized full ((prepareNormalization q full).materializeCapacity capacity) := by
  have heq (node : Finset (Fin q)) (hnode : node ∈ nodeFamily full) :
      (prepareNormalization q full).materializeCapacity capacity node = capacity node :=
    materializeCapacity_at _ _ _ ((mem_preparedOrder q full node).mpr hnode)
  refine ⟨fun tool => ?_, ?_⟩
  · rw [heq {tool} (singleton_mem full tool)]
    exact hnormalized.1 tool
  · intro node hnode hinternal
    rw [heq node hnode]
    have hsum :
        (∑ child ∈ children (nodeFamily full) node,
          (prepareNormalization q full).materializeCapacity capacity child) =
        ∑ child ∈ children (nodeFamily full) node, capacity child :=
      Finset.sum_congr rfl
        (fun child hchild => heq child (children_subset (nodeFamily full) node hchild))
    rw [hsum]
    exact hnormalized.2 node hnode hinternal

theorem prepared_materializeEntry_normalized (q : Nat) (full : List (Finset (Fin q)))
    (entry : CapacityEntry (Finset (Fin q))) (hnormalized : EntryNormalized full entry) :
    EntryNormalized full ((prepareNormalization q full).materializeEntry entry) := by
  cases entry with
  | void => trivial
  | vector capacity => exact prepared_materializeCapacity_normalized q full capacity hnormalized

def freeEntry : CapacityEntry (Finset Tool) := .vector (fun node => node.card)

variable [Fintype Tool]

theorem freeEntry_denote (full : List (Finset Tool)) :
    (freeEntry : CapacityEntry (Finset Tool)).denote (layout full) = Set.univ :=
  capacityFamily_free (layout full)

theorem freeEntry_normalized (full : List (Finset Tool)) (hlaminar : LaminarSchedule full) :
    EntryNormalized full (freeEntry : CapacityEntry (Finset Tool)) := free_normalized full hlaminar

end PaperProofs.Structure.LaminarTree

namespace PaperProofs.Structure.LaminarTree

variable {Tool : Type*} [DecidableEq Tool]

abbrev BudgetLayer (Tool : Type*) (maxBudget : Nat) :=
  Vector (CapacityEntry (Finset Tool)) (maxBudget + 1)

def previousBudget {maxBudget : Nat} (budget : Fin (maxBudget + 1)) : Fin (maxBudget + 1) :=
  ⟨budget.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) budget.isLt⟩

omit [DecidableEq Tool] in
theorem get_ofFn_layer {maxBudget : Nat}
    (entries : Fin (maxBudget + 1) → CapacityEntry (Finset Tool))
    (budget : Fin (maxBudget + 1)) : (Vector.ofFn entries).get budget = entries budget := by
  change (Vector.ofFn entries)[budget.val] = entries budget
  simp

def terminalLayer (Tool : Type*) (maxBudget : Nat) : BudgetLayer Tool maxBudget :=
  Vector.ofFn (fun _ => freeEntry)

variable [Fintype Tool]

/-- Both continuations read the already materialized previous suffix row. -/
def capacityLayerStep (data : NormalizationData Tool) (full : List (Finset Tool))
    (maxBudget : Nat) (eligible : Finset Tool) (previous : BudgetLayer Tool maxBudget) :
    BudgetLayer Tool maxBudget :=
  Vector.ofFn (fun budget =>
    if budget.val = 0 then freeEntry else
      data.materializeEntry (data.intersectEntries (previous.get budget)
        (extendEntry full eligible (previous.get (previousBudget budget)))))

theorem capacityLayerStep_get (data : NormalizationData Tool) (full : List (Finset Tool))
    (maxBudget : Nat) (eligible : Finset Tool) (previous : BudgetLayer Tool maxBudget)
    (budget : Fin (maxBudget + 1)) :
    (capacityLayerStep data full maxBudget eligible previous).get budget =
      if budget.val = 0 then freeEntry else
        data.materializeEntry (data.intersectEntries (previous.get budget)
          (extendEntry full eligible (previous.get (previousBudget budget)))) :=
  get_ofFn_layer _ _

/-- A representation invariant, not the definition of game safety. -/
def LayerCorrect (full suffix : List (Finset Tool)) {maxBudget : Nat}
    (layer : BudgetLayer Tool maxBudget) : Prop :=
  ∀ budget : Fin (maxBudget + 1), EntryNormalized full (layer.get budget) ∧
    (layer.get budget).denote (layout full) = safeUsedFamily suffix budget.val

theorem terminalLayer_correct (full : List (Finset Tool)) (hlaminar : LaminarSchedule full)
    (maxBudget : Nat) : LayerCorrect full [] (terminalLayer Tool maxBudget) := by
  intro budget
  have heq : (terminalLayer Tool maxBudget).get budget = freeEntry := get_ofFn_layer _ _
  rw [heq]
  exact ⟨freeEntry_normalized full hlaminar,
    (freeEntry_denote full).trans (safeUsed_terminal budget.val).symm⟩

theorem capacityLayerStep_correct (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (maxBudget : Nat)
    (eligible : Finset (Fin q)) (hstage : eligible ∈ full) (later : List (Finset (Fin q)))
    (previous : BudgetLayer (Fin q) maxBudget) (hprevious : LayerCorrect full later previous) :
    LayerCorrect full (eligible :: later)
      (capacityLayerStep (prepareNormalization q full) full maxBudget eligible previous) := by
  have heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full := by
    by_cases hempty : eligible = ∅
    · exact Or.inl hempty
    · exact Or.inr (nonempty_stage_mem full hstage (Finset.nonempty_iff_ne_empty.mpr hempty))
  intro budget
  rw [capacityLayerStep_get]
  by_cases hzero : budget.val = 0
  · simp only [hzero, ↓reduceIte]
    exact ⟨freeEntry_normalized full hlaminar,
      (freeEntry_denote full).trans (safeUsed_zero (eligible :: later)).symm⟩
  · simp only [hzero, ↓reduceIte]
    have hgood := hprevious budget
    have hbad := hprevious (previousBudget budget)
    have hextended := extendEntry_normalized full hlaminar eligible heligible _ hbad.1
    have hintersection := prepared_intersectEntries_normalized q full hq hlaminar _ _ hgood.1 hextended
    refine ⟨prepared_materializeEntry_normalized q full _ hintersection, ?_⟩
    rw [prepared_materializeEntry_sound, prepared_intersectEntries_sound q full hq hlaminar,
      extendEntry_sound full hlaminar eligible heligible _ hbad.1, hgood.2, hbad.2]
    obtain ⟨smaller, hsucc⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    have hpred : (previousBudget budget).val = smaller := by
      change budget.val - 1 = smaller
      omega
    rw [hpred, hsucc]
    exact (safeUsed_budget_recurrence eligible later smaller).symm

/-- Each recursive call builds the previous suffix only once. A row is a
stored finite Vector, not a budget-indexed recomputation of that suffix. -/
def capacityRows (data : NormalizationData Tool) (full : List (Finset Tool)) (maxBudget : Nat) :
    List (Finset Tool) → BudgetLayer Tool maxBudget × List (BudgetLayer Tool maxBudget)
  | [] => (terminalLayer Tool maxBudget, [])
  | eligible :: later =>
      let previous := capacityRows data full maxBudget later
      (capacityLayerStep data full maxBudget eligible previous.1, previous.1 :: previous.2)

def capacityRowsList (data : NormalizationData Tool) (full : List (Finset Tool))
    (maxBudget : Nat) (suffix : List (Finset Tool)) : List (BudgetLayer Tool maxBudget) :=
  let rows := capacityRows data full maxBudget suffix
  rows.1 :: rows.2

theorem capacityRows_rest_length (data : NormalizationData Tool) (full : List (Finset Tool))
    (maxBudget : Nat) (suffix : List (Finset Tool)) :
    (capacityRows data full maxBudget suffix).2.length = suffix.length := by
  induction suffix with
  | nil => rfl
  | cons eligible later ih => simpa only [capacityRows, List.length_cons] using congrArg Nat.succ ih

theorem capacityRowsList_length (data : NormalizationData Tool) (full : List (Finset Tool))
    (maxBudget : Nat) (suffix : List (Finset Tool)) :
    (capacityRowsList data full maxBudget suffix).length = suffix.length + 1 := by
  simp only [capacityRowsList, List.length_cons, capacityRows_rest_length]

theorem capacityRows_correct (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (maxBudget : Nat) (suffix : List (Finset (Fin q)))
    (hsub : ∀ eligible ∈ suffix, eligible ∈ full) :
    LayerCorrect full suffix (capacityRows (prepareNormalization q full) full maxBudget suffix).1 ∧
      List.Forall₂ (fun later layer => LayerCorrect full later layer) suffix.tails
        (capacityRowsList (prepareNormalization q full) full maxBudget suffix) := by
  revert hsub
  induction suffix with
  | nil =>
    intro _
    have hterminal := terminalLayer_correct full hlaminar maxBudget
    exact ⟨hterminal, List.Forall₂.cons hterminal List.Forall₂.nil⟩
  | cons eligible later ih =>
    intro hsub
    have htail := ih (fun next hnext => hsub next (List.mem_cons_of_mem _ hnext))
    have hcurrent := capacityLayerStep_correct q full hq hlaminar maxBudget eligible
      (hsub eligible List.mem_cons_self) later _ htail.1
    exact ⟨hcurrent, List.Forall₂.cons hcurrent htail.2⟩

/-- The table retains the same preprocessing object for rank/action clients. -/
structure CapacityTable (Tool : Type*) (maxBudget : Nat) where
  tree : NormalizationData Tool
  rows : Array (BudgetLayer Tool maxBudget)

def buildPositiveCapacityTable (q : Nat) (full : List (Finset (Fin q))) (maxBudget : Nat) :
    CapacityTable (Fin q) maxBudget :=
  let tree := prepareNormalization q full
  {
    tree := tree
    rows := (capacityRowsList tree full maxBudget full).toArray
  }

theorem buildPositiveCapacityTable_size (q : Nat) (full : List (Finset (Fin q)))
    (maxBudget : Nat) :
    (buildPositiveCapacityTable q full maxBudget).rows.size = full.length + 1 := by
  simp only [buildPositiveCapacityTable, List.size_toArray, capacityRowsList_length]

/-- The zero-tool branch uses operational first-failure semantics directly. -/
theorem safeUsed_zero_tools_live (eligible : Finset (Fin 0))
    (later : List (Finset (Fin 0))) (budget : Nat) :
    safeUsedFamily (eligible :: later) (budget + 1) = ∅ := by
  ext used
  have hremaining : (Finset.univ \ used : Finset (Fin 0)) = ∅ :=
    Finset.eq_empty_of_forall_notMem (fun tool => Fin.elim0 tool)
  change Safe (eligible :: later) (Finset.univ \ used) (budget + 1) ↔ False
  rw [hremaining]
  exact iff_false_intro (not_safe_no_tools eligible later budget)

def zeroToolLayer (maxBudget : Nat) (suffix : List (Finset (Fin 0))) :
    BudgetLayer (Fin 0) maxBudget :=
  Vector.ofFn (fun budget => if suffix = [] ∨ budget.val = 0 then freeEntry else .void)

theorem zeroToolLayer_correct (full : List (Finset (Fin 0)))
    (hlaminar : LaminarSchedule full) (maxBudget : Nat) (suffix : List (Finset (Fin 0))) :
    LayerCorrect full suffix (zeroToolLayer maxBudget suffix) := by
  intro budget
  have heq : (zeroToolLayer maxBudget suffix).get budget =
      if suffix = [] ∨ budget.val = 0 then freeEntry else .void := get_ofFn_layer _ _
  rw [heq]
  cases suffix with
  | nil =>
    simp only [true_or, ↓reduceIte]
    exact ⟨freeEntry_normalized full hlaminar,
      (freeEntry_denote full).trans (safeUsed_terminal budget.val).symm⟩
  | cons eligible later =>
    by_cases hzero : budget.val = 0
    · simp only [hzero, or_true, ↓reduceIte]
      exact ⟨freeEntry_normalized full hlaminar,
        (freeEntry_denote full).trans (safeUsed_zero (eligible :: later)).symm⟩
    · simp only [List.cons_ne_nil, hzero, or_self, ↓reduceIte]
      obtain ⟨smaller, hsucc⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      refine ⟨True.intro, ?_⟩
      rw [hsucc, safeUsed_zero_tools_live]
      rfl

/-- No tree preprocessing is run when there are no tools. -/
def buildZeroCapacityTable (full : List (Finset (Fin 0))) (maxBudget : Nat) :
    CapacityTable (Fin 0) maxBudget :=
  { tree := ⟨[], []⟩
    rows := (full.tails.map (zeroToolLayer maxBudget)).toArray }

/-- One full-input tree is prepared once; all suffix/budget rows share it.
The original zero-tool model has a separate direct branch. -/
def buildCapacityTable : (q : Nat) → (full : List (Finset (Fin q))) → (maxBudget : Nat) →
    CapacityTable (Fin q) maxBudget
  | 0, full, maxBudget => buildZeroCapacityTable full maxBudget
  | q + 1, full, maxBudget => buildPositiveCapacityTable (q + 1) full maxBudget

theorem buildCapacityTable_size (q : Nat) (full : List (Finset (Fin q))) (maxBudget : Nat) :
    (buildCapacityTable q full maxBudget).rows.size = full.length + 1 := by
  cases q with
  | zero => simp only [buildCapacityTable, buildZeroCapacityTable, List.size_toArray,
      List.length_map, List.length_tails]
  | succ q => exact buildPositiveCapacityTable_size (q + 1) full maxBudget

/-- All stored rows denote the independent causal game on the corresponding
suffix, with no positive-tool-count restriction. -/
theorem buildCapacityTable_rows_correct (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (maxBudget : Nat) :
    List.Forall₂ (fun suffix layer => LayerCorrect full suffix layer) full.tails
      (buildCapacityTable q full maxBudget).rows.toList := by
  cases q with
  | zero =>
    change List.Forall₂ _ full.tails (full.tails.map (zeroToolLayer maxBudget)).toArray.toList
    rw [List.toList_toArray]
    generalize full.tails = suffixes
    induction suffixes with
    | nil => exact List.Forall₂.nil
    | cons suffix suffixes ih =>
      exact List.Forall₂.cons (zeroToolLayer_correct full hlaminar maxBudget suffix) ih
  | succ q =>
    change List.Forall₂ _ full.tails
      (capacityRowsList (prepareNormalization (q + 1) full) full maxBudget full).toArray.toList
    rw [List.toList_toArray]
    exact (capacityRows_correct (q + 1) full (Nat.zero_lt_succ q) hlaminar maxBudget full
      (fun _ hmem => hmem)).2

/-- A total, bounded lookup in the array of suffix rows. -/
def CapacityTable.entry {maxBudget : Nat} (table : CapacityTable Tool maxBudget)
    (next : Fin table.rows.size) (budget : Fin (maxBudget + 1)) :
    CapacityEntry (Finset Tool) := (table.rows[next.val]).get budget

theorem buildCapacityTable_entry_correct (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (maxBudget : Nat)
    (next : Fin (full.length + 1)) (budget : Fin (maxBudget + 1)) :
    let table := buildCapacityTable q full maxBudget
    let row : Fin table.rows.size :=
      ⟨next.val, (buildCapacityTable_size q full maxBudget).symm ▸ next.isLt⟩
    EntryNormalized full (table.entry row budget) ∧
      (table.entry row budget).denote (layout full) =
        safeUsedFamily (full.drop next.val) budget.val := by
  have hrows := buildCapacityTable_rows_correct q full hlaminar maxBudget
  have hleft : next.val < full.tails.length := by simpa only [List.length_tails] using next.isLt
  have hright : next.val < (buildCapacityTable q full maxBudget).rows.toList.length := by
    simpa only [Array.length_toList, buildCapacityTable_size] using next.isLt
  have hrow := hrows.get hleft hright
  rw [List.get_tails] at hrow
  exact hrow budget

end PaperProofs.Structure.LaminarTree
