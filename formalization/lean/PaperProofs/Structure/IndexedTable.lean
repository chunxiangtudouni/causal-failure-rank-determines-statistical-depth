module

public import PaperProofs.Structure.IndexedEntry
public import PaperProofs.Structure.LaminarTable
import Lean.Elab.Tactic.Omega

/-!
Materialized fixed-coordinate suffix/budget rows on one full-input
cache. The runtime recurrence uses IndexedEntry.budgetCell. Its correctness
target is the independent causal SafeUsed family, not a recursively defined
capacity/game value. The constructor has a separate zero-tool branch that
does not prepare a tree. Counting stored cells is separate from proving any
cost for the ancestor/min operations, one complete cell, or the whole table.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.IndexedTable

open IndexedEntry

variable {Tool : Type*}

abbrev Row (cache : IndexedNodeCache Tool) (maxBudget : Nat) :=
  Vector (FixedEntry cache) (maxBudget + 1)

def terminalRow (cache : IndexedNodeCache Tool) (maxBudget : Nat) : Row cache maxBudget :=
  Vector.ofFn (fun _ => free cache)

def rowStep [DecidableEq Tool] (cache : IndexedNodeCache Tool) (maxBudget : Nat)
    (eligible : Finset Tool) (previous : Row cache maxBudget) : Row cache maxBudget :=
  Vector.ofFn (fun budget => budgetCell cache eligible budget.val
    (previous.get budget) (previous.get (previousBudget budget)))

theorem terminalRow_get (cache : IndexedNodeCache Tool) (maxBudget : Nat)
    (budget : Fin (maxBudget + 1)) : (terminalRow cache maxBudget).get budget = free cache :=
  cache_get_ofFn _ _

theorem rowStep_get [DecidableEq Tool] (cache : IndexedNodeCache Tool) (maxBudget : Nat)
    (eligible : Finset Tool) (previous : Row cache maxBudget) (budget : Fin (maxBudget + 1)) :
    (rowStep cache maxBudget eligible previous).get budget = budgetCell cache eligible budget.val
      (previous.get budget) (previous.get (previousBudget budget)) := cache_get_ofFn _ _

/-- A proved external representation invariant, with no oracle in the data. -/
def RowCorrect {q : Nat} (cache : IndexedNodeCache (Fin q)) (suffix : List (Finset (Fin q)))
    {maxBudget : Nat} (row : Row cache maxBudget) : Prop :=
  ∀ budget : Fin (maxBudget + 1), IsNormalized cache (row.get budget) ∧
    (row.get budget).Bounded q ∧
      (row.get budget).denote cache = safeUsedFamily suffix budget.val

theorem prepared_free_normalized (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    IsNormalized (prepareNormalization q full).indexed (free (prepareNormalization q full).indexed) :=
  prepared_reify_normalized q full hq hlaminar freeEntry (freeEntry_normalized full hlaminar)

theorem prepared_terminalRow_correct (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (maxBudget : Nat) :
    RowCorrect (prepareNormalization q full).indexed []
      (terminalRow (prepareNormalization q full).indexed maxBudget) := by
  intro budget
  rw [terminalRow_get]
  exact ⟨prepared_free_normalized q full hq hlaminar, free_bounded q _,
    (free_denote _).trans (safeUsed_terminal budget.val).symm⟩

theorem prepared_rowStep_correct (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (maxBudget : Nat)
    (eligible : Finset (Fin q)) (hstage : eligible ∈ full) (later : List (Finset (Fin q)))
    (previous : Row (prepareNormalization q full).indexed maxBudget)
    (hprevious : RowCorrect (prepareNormalization q full).indexed later previous) :
    RowCorrect (prepareNormalization q full).indexed (eligible :: later)
      (rowStep (prepareNormalization q full).indexed maxBudget eligible previous) := by
  have heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full := by
    by_cases hempty : eligible = ∅
    · exact Or.inl hempty
    · exact Or.inr (nonempty_stage_mem full hstage (Finset.nonempty_iff_ne_empty.mpr hempty))
  intro budget
  rw [rowStep_get]
  by_cases hzero : budget.val = 0
  · simp only [budgetCell, hzero, ↓reduceIte]
    exact ⟨prepared_free_normalized q full hq hlaminar, free_bounded q _,
      (free_denote _).trans (safeUsed_zero (eligible :: later)).symm⟩
  · simp only [budgetCell, hzero, ↓reduceIte]
    have hgood := hprevious budget
    have hbad := hprevious (previousBudget budget)
    have hnormalized := prepared_cell_normalized_bounded q full hq hlaminar eligible
      (previous.get budget) (previous.get (previousBudget budget)) hgood.1
    refine ⟨hnormalized.1, hnormalized.2, ?_⟩
    rw [prepared_cell_denote q full hq hlaminar eligible heligible _ _ hbad.1, hgood.2.2, hbad.2.2]
    obtain ⟨smaller, hsucc⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    have hpred : (previousBudget budget).val = smaller := by
      change budget.val - 1 = smaller
      omega
    rw [hpred, hsucc]
    exact (safeUsed_budget_recurrence eligible later smaller).symm

/-- The previous suffix is built once, then stored and read by all budgets. -/
def rows [DecidableEq Tool] (cache : IndexedNodeCache Tool) (maxBudget : Nat) :
    List (Finset Tool) → Row cache maxBudget × List (Row cache maxBudget)
  | [] => (terminalRow cache maxBudget, [])
  | eligible :: later =>
      let previous := rows cache maxBudget later
      (rowStep cache maxBudget eligible previous.1, previous.1 :: previous.2)

def rowsList [DecidableEq Tool] (cache : IndexedNodeCache Tool) (maxBudget : Nat)
    (suffix : List (Finset Tool)) : List (Row cache maxBudget) :=
  let result := rows cache maxBudget suffix
  result.1 :: result.2

theorem rows_rest_length [DecidableEq Tool] (cache : IndexedNodeCache Tool)
    (maxBudget : Nat) (suffix : List (Finset Tool)) :
    (rows cache maxBudget suffix).2.length = suffix.length := by
  induction suffix with
  | nil => rfl
  | cons eligible later ih => simpa only [rows, List.length_cons] using congrArg Nat.succ ih

theorem rowsList_length [DecidableEq Tool] (cache : IndexedNodeCache Tool)
    (maxBudget : Nat) (suffix : List (Finset Tool)) :
    (rowsList cache maxBudget suffix).length = suffix.length + 1 := by
  simp only [rowsList, List.length_cons, rows_rest_length]

theorem prepared_rows_correct (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (maxBudget : Nat)
    (suffix : List (Finset (Fin q))) (hsub : ∀ eligible ∈ suffix, eligible ∈ full) :
    RowCorrect (prepareNormalization q full).indexed suffix
      (rows (prepareNormalization q full).indexed maxBudget suffix).1 ∧
      List.Forall₂ (fun later row => RowCorrect (prepareNormalization q full).indexed later row)
        suffix.tails (rowsList (prepareNormalization q full).indexed maxBudget suffix) := by
  revert hsub
  induction suffix with
  | nil =>
    intro _
    have hterminal := prepared_terminalRow_correct q full hq hlaminar maxBudget
    exact ⟨hterminal, List.Forall₂.cons hterminal List.Forall₂.nil⟩
  | cons eligible later ih =>
    intro hsub
    have htail := ih (fun next hnext => hsub next (List.mem_cons_of_mem _ hnext))
    have hcurrent := prepared_rowStep_correct q full hq hlaminar maxBudget eligible
      (hsub eligible List.mem_cons_self) later _ htail.1
    exact ⟨hcurrent, List.Forall₂.cons hcurrent htail.2⟩

/-- Only actual cache/row data is stored. Correctness is proved below. -/
structure Table (Tool : Type*) (maxBudget : Nat) where
  cache : IndexedNodeCache Tool
  rows : Array (Row cache maxBudget)

def buildPositive (q : Nat) (full : List (Finset (Fin q))) (maxBudget : Nat) : Table (Fin q) maxBudget :=
  let cache := (prepareNormalization q full).indexed
  { cache := cache, rows := (rowsList cache maxBudget full).toArray }

theorem buildPositive_size (q : Nat) (full : List (Finset (Fin q))) (maxBudget : Nat) :
    (buildPositive q full maxBudget).rows.size = full.length + 1 := by
  simp only [buildPositive, List.size_toArray, rowsList_length]

def emptyCache (Tool : Type*) : IndexedNodeCache Tool :=
  { nodes := #[]
    parents := Vector.ofFn (fun node : Fin 0 => (Fin.elim0 node : Option (Fin 0)))
    children := Vector.ofFn (fun node : Fin 0 => (Fin.elim0 node : Array (Fin 0))) }

theorem emptyCache_entry_normalized (Tool : Type*) (entry : FixedEntry (emptyCache Tool)) :
    IsNormalized (emptyCache Tool) entry := by
  cases entry with
  | void => trivial
  | vector capacity => exact ⟨fun node => Fin.elim0 node, fun node => Fin.elim0 node⟩

/-- A zero-tool row uses the original terminal/zero-budget/live-failure split. -/
def zeroRow (maxBudget : Nat) (suffix : List (Finset (Fin 0))) : Row (emptyCache (Fin 0)) maxBudget :=
  Vector.ofFn (fun budget => if suffix = [] ∨ budget.val = 0 then free (emptyCache (Fin 0)) else .void)

theorem zeroRow_get (maxBudget : Nat) (suffix : List (Finset (Fin 0))) (budget : Fin (maxBudget + 1)) :
    (zeroRow maxBudget suffix).get budget =
      if suffix = [] ∨ budget.val = 0 then free (emptyCache (Fin 0)) else .void := cache_get_ofFn _ _

theorem zeroRow_correct (maxBudget : Nat) (suffix : List (Finset (Fin 0))) :
    RowCorrect (emptyCache (Fin 0)) suffix (zeroRow maxBudget suffix) := by
  intro budget
  rw [zeroRow_get]
  cases suffix with
  | nil =>
    simp only [true_or, ↓reduceIte]
    exact ⟨emptyCache_entry_normalized _ _, free_bounded 0 _,
      (free_denote _).trans (safeUsed_terminal budget.val).symm⟩
  | cons eligible later =>
    by_cases hzero : budget.val = 0
    · simp only [hzero, or_true, ↓reduceIte]
      exact ⟨emptyCache_entry_normalized _ _, free_bounded 0 _,
        (free_denote _).trans (safeUsed_zero (eligible :: later)).symm⟩
    · simp only [List.cons_ne_nil, hzero, or_self, ↓reduceIte]
      obtain ⟨smaller, hsucc⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      refine ⟨True.intro, True.intro, ?_⟩
      rw [hsucc, safeUsed_zero_tools_live]
      rfl

def buildZero (full : List (Finset (Fin 0))) (maxBudget : Nat) : Table (Fin 0) maxBudget :=
  { cache := emptyCache (Fin 0), rows := (full.tails.map (zeroRow maxBudget)).toArray }

/-- Positive q prepares one full-input cache; zero q prepares no tree. -/
def build : (q : Nat) → (full : List (Finset (Fin q))) → (maxBudget : Nat) → Table (Fin q) maxBudget
  | 0, full, maxBudget => buildZero full maxBudget
  | q + 1, full, maxBudget => buildPositive (q + 1) full maxBudget

theorem build_size (q : Nat) (full : List (Finset (Fin q))) (maxBudget : Nat) :
    (build q full maxBudget).rows.size = full.length + 1 := by
  cases q with
  | zero => simp only [build, buildZero, List.size_toArray, List.length_map, List.length_tails]
  | succ q => exact buildPositive_size (q + 1) full maxBudget

theorem build_rows_correct (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (maxBudget : Nat) :
    List.Forall₂ (fun suffix row => RowCorrect (build q full maxBudget).cache suffix row)
      full.tails (build q full maxBudget).rows.toList := by
  cases q with
  | zero =>
    change List.Forall₂ _ full.tails (full.tails.map (zeroRow maxBudget)).toArray.toList
    rw [List.toList_toArray]
    generalize full.tails = suffixes
    induction suffixes with
    | nil => exact List.Forall₂.nil
    | cons suffix suffixes ih => exact List.Forall₂.cons (zeroRow_correct maxBudget suffix) ih
  | succ q =>
    change List.Forall₂ _ full.tails
      (rowsList (prepareNormalization (q + 1) full).indexed maxBudget full).toArray.toList
    rw [List.toList_toArray]
    exact (prepared_rows_correct (q + 1) full (Nat.zero_lt_succ q) hlaminar maxBudget full
      (fun _ hmem => hmem)).2

def Table.entry {maxBudget : Nat} (table : Table Tool maxBudget)
    (next : Fin table.rows.size) (budget : Fin (maxBudget + 1)) : FixedEntry table.cache :=
  (table.rows[next.val]).get budget

theorem build_entry_correct (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (maxBudget : Nat)
    (next : Fin (full.length + 1)) (budget : Fin (maxBudget + 1)) :
    let table := build q full maxBudget
    let row : Fin table.rows.size := ⟨next.val, (build_size q full maxBudget).symm ▸ next.isLt⟩
    IsNormalized table.cache (table.entry row budget) ∧ (table.entry row budget).Bounded q ∧
      (table.entry row budget).denote table.cache = safeUsedFamily (full.drop next.val) budget.val := by
  have hrows := build_rows_correct q full hlaminar maxBudget
  have hleft : next.val < full.tails.length := by simpa only [List.length_tails] using next.isLt
  have hright : next.val < (build q full maxBudget).rows.toList.length := by
    simpa only [Array.length_toList, build_size] using next.isLt
  have hrow := hrows.get hleft hright
  rw [List.get_tails] at hrow
  exact hrow budget

theorem build_entry_refines_old (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (maxBudget : Nat)
    (next : Fin (full.length + 1)) (budget : Fin (maxBudget + 1)) :
    let indexed := build q full maxBudget
    let old := buildCapacityTable q full maxBudget
    let indexedRow : Fin indexed.rows.size := ⟨next.val, (build_size q full maxBudget).symm ▸ next.isLt⟩
    let oldRow : Fin old.rows.size := ⟨next.val, (buildCapacityTable_size q full maxBudget).symm ▸ next.isLt⟩
    (indexed.entry indexedRow budget).denote indexed.cache = (old.entry oldRow budget).denote (layout full) := by
  exact (build_entry_correct q full hlaminar maxBudget next budget).2.2.trans
    (buildCapacityTable_entry_correct q full hlaminar maxBudget next budget).2.symm

/-- Actual row-major entries read from the stored array, for serialization. -/
def Table.cells {maxBudget : Nat} (table : Table Tool maxBudget) : List (FixedEntry table.cache) :=
  (List.finRange table.rows.size).flatMap (fun next =>
    (List.finRange (maxBudget + 1)).map (fun budget => table.entry next budget))

theorem Table.cells_length {maxBudget : Nat} (table : Table Tool maxBudget) :
    table.cells.length = table.rows.size * (maxBudget + 1) := by
  simp only [Table.cells, List.length_flatMap, List.length_map, List.length_finRange,
    List.map_const', List.sum_replicate, Nat.nsmul_eq_mul]

theorem Table.mem_cells_iff {maxBudget : Nat} (table : Table Tool maxBudget) (entry : FixedEntry table.cache) :
    entry ∈ table.cells ↔ ∃ next budget, table.entry next budget = entry := by
  simp only [Table.cells, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]

theorem build_cells_length (q : Nat) (full : List (Finset (Fin q))) (maxBudget : Nat) :
    (build q full maxBudget).cells.length = (full.length + 1) * (maxBudget + 1) := by
  rw [Table.cells_length, build_size]

theorem build_rankTable_cells_length (q : Nat) (full : List (Finset (Fin q))) :
    (build q full (q + 1)).cells.length = (full.length + 1) * (q + 2) :=
  build_cells_length q full (q + 1)

theorem build_cells_bounded (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (maxBudget : Nat) :
    ∀ entry ∈ (build q full maxBudget).cells, entry.Bounded q := by
  intro entry hentry
  obtain ⟨row, budget, rfl⟩ := (Table.mem_cells_iff _ entry).mp hentry
  let next : Fin (full.length + 1) := ⟨row.val, by simpa only [build_size] using row.isLt⟩
  exact (build_entry_correct q full hlaminar maxBudget next budget).2.1

theorem build_cache_size_le (q : Nat) (full : List (Finset (Fin q))) (maxBudget : Nat) :
    (build q full maxBudget).cache.nodes.size ≤ full.length + q + 1 := by
  cases q with
  | zero => exact Nat.zero_le _
  | succ q => exact prepared_indexed_size_le (q + 1) full

theorem build_encode_length_le (q : Nat) (full : List (Finset (Fin q))) (maxBudget : Nat) :
    (CapacityBits.encodeEntries q (build q full maxBudget).cells).length ≤
      (full.length + 1) * (maxBudget + 1) *
        (1 + (build q full maxBudget).cache.nodes.size * CapacityBits.width q) := by
  have hlength := CapacityBits.encodeEntries_length_le q (build q full maxBudget).cells
  rw [build_cells_length] at hlength
  exact hlength

theorem build_encode_length_le_input (q : Nat) (full : List (Finset (Fin q))) (maxBudget : Nat) :
    (CapacityBits.encodeEntries q (build q full maxBudget).cells).length ≤
      (full.length + 1) * (maxBudget + 1) *
        (1 + (full.length + q + 1) * CapacityBits.width q) := by
  exact (build_encode_length_le q full maxBudget).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (build_cache_size_le q full maxBudget)) _))

theorem build_codec_roundtrip_prefix (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (maxBudget : Nat) (remaining : List Bool) :
    CapacityBits.decodeEntriesPrefix q (build q full maxBudget).cache.nodes.size
      ((full.length + 1) * (maxBudget + 1))
      (CapacityBits.encodeEntries q (build q full maxBudget).cells ++ remaining) =
        some ((build q full maxBudget).cells, remaining) := by
  have hroundtrip := CapacityBits.decodeEntriesPrefix_encode_append q (build q full maxBudget).cells
    (build_cells_bounded q full hlaminar maxBudget) remaining
  rw [build_cells_length] at hroundtrip
  exact hroundtrip

theorem build_packed_codec_roundtrip (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (maxBudget : Nat) :
    CapacityBits.decodeEntriesPrefix q (build q full maxBudget).cache.nodes.size
      ((full.length + 1) * (maxBudget + 1))
      (CapacityBits.unpackStream (CapacityBits.packStream
        (CapacityBits.encodeEntries q (build q full maxBudget).cells))) =
          some ((build q full maxBudget).cells, []) := by
  have hroundtrip := CapacityBits.decodePackedEntries_encodeEntries q (build q full maxBudget).cells
    (build_cells_bounded q full hlaminar maxBudget)
  rw [build_cells_length] at hroundtrip
  exact hroundtrip

theorem build_entry_codec_refines_game (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (maxBudget : Nat)
    (next : Fin (full.length + 1)) (budget : Fin (maxBudget + 1)) :
    let table := build q full maxBudget
    let row : Fin table.rows.size := ⟨next.val, (build_size q full maxBudget).symm ▸ next.isLt⟩
    (CapacityBits.decodeEntry q table.cache.nodes.size (CapacityBits.encodeEntry q (table.entry row budget))).map
      (CapacityBits.Entry.denote table.cache) = some (safeUsedFamily (full.drop next.val) budget.val) := by
  dsimp only
  have hcorrect := build_entry_correct q full hlaminar maxBudget next budget
  rw [CapacityBits.decoded_entry_denote _ _ _ hcorrect.2.1, hcorrect.2.2]

end PaperProofs.Structure.LaminarTree.IndexedTable
