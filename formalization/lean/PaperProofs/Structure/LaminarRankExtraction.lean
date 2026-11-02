module

public import PaperProofs.Structure.LaminarTable
public import Mathlib.Data.List.Range
public import Mathlib.Data.List.Find
import Lean.Elab.Tactic.Omega

/-!
A14 rank extraction from the stored full-input capacity table. The executable
checker reads finitely many active capacity coordinates. It never decides the
operational `Safe` proposition. Searching the budgets 1,...,q+1 computes the
independently defined `errorRank`, including zero tools and terminal suffixes.
No running-time or data-access cost certificate is claimed here.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree

variable {Tool : Type*} [DecidableEq Tool]

/-- An actual finite coordinate test, with VOID distinct from every vector. -/
def entryAccepts (nodes : List (Finset Tool)) (used : Finset Tool) :
    CapacityEntry (Finset Tool) → Bool
  | .void => false
  | .vector capacity => nodes.all (fun node => decide ((used ∩ node).card ≤ capacity node))

variable [Fintype Tool]

theorem entryAccepts_iff_denote (full : List (Finset Tool)) (nodes : List (Finset Tool))
    (hnodes : ∀ node, node ∈ nodes ↔ node ∈ nodeFamily full)
    (used : Finset Tool) (entry : CapacityEntry (Finset Tool)) :
    entryAccepts nodes used entry = true ↔ used ∈ entry.denote (layout full) := by
  cases entry with
  | void => simp [entryAccepts, CapacityEntry.denote]
  | vector capacity =>
    change nodes.all (fun node => decide ((used ∩ node).card ≤ capacity node)) = true ↔
      ∀ node ∈ nodeFamily full, (used ∩ node).card ≤ capacity node
    rw [List.all_eq_true]
    simp only [decide_eq_true_eq]
    exact ⟨fun h node hnode => h node ((hnodes node).mpr hnode),
      fun h node hnode => h node ((hnodes node).mp hnode)⟩

theorem zero_entryAccepts_iff_denote (full : List (Finset (Fin 0)))
    (used : Finset (Fin 0)) (entry : CapacityEntry (Finset (Fin 0))) :
    entryAccepts [] used entry = true ↔ used ∈ entry.denote (layout full) := by
  cases entry with
  | void => simp [entryAccepts, CapacityEntry.denote]
  | vector capacity =>
    have hempty (s : Finset (Fin 0)) : s = ∅ :=
      Finset.eq_empty_of_forall_notMem (fun tool => Fin.elim0 tool)
    change true = true ↔ ∀ node ∈ nodeFamily full, (used ∩ node).card ≤ capacity node
    simp only [true_iff]
    intro node _
    rw [hempty (used ∩ node), Finset.card_empty]
    exact Nat.zero_le _

theorem built_entryAccepts_iff_denote (q : Nat) (full : List (Finset (Fin q)))
    (maxBudget : Nat) (used : Finset (Fin q)) (entry : CapacityEntry (Finset (Fin q))) :
    entryAccepts (buildCapacityTable q full maxBudget).tree.order used entry = true ↔
      used ∈ entry.denote (layout full) := by
  cases q with
  | zero => exact zero_entryAccepts_iff_denote full used entry
  | succ q => exact entryAccepts_iff_denote full _ (mem_preparedOrder (q + 1) full) used entry

/-- Bounded table lookup followed by the finite active-coordinate checker. -/
def CapacityTable.acceptsBudget {maxBudget : Nat} (table : CapacityTable Tool maxBudget)
    (next : Fin table.rows.size) (used : Finset Tool) (budget : Nat) : Bool :=
  if hbudget : budget < maxBudget + 1 then
    entryAccepts table.tree.order used (table.entry next ⟨budget, hbudget⟩)
  else false

def builtTableRow (q : Nat) (full : List (Finset (Fin q))) (maxBudget : Nat)
    (next : Fin (full.length + 1)) : Fin (buildCapacityTable q full maxBudget).rows.size :=
  ⟨next.val, (buildCapacityTable_size q full maxBudget).symm ▸ next.isLt⟩

theorem built_acceptsBudget_iff (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (maxBudget : Nat) (next : Fin (full.length + 1))
    (used : Finset (Fin q)) (budget : Nat) (hbudget : budget < maxBudget + 1) :
    (buildCapacityTable q full maxBudget).acceptsBudget
      (builtTableRow q full maxBudget next) used budget = true ↔
        Safe (full.drop next.val) (Finset.univ \ used) budget := by
  simp only [CapacityTable.acceptsBudget, hbudget, ↓reduceDIte]
  rw [built_entryAccepts_iff_denote]
  have hentry :
      ((buildCapacityTable q full maxBudget).entry (builtTableRow q full maxBudget next)
        ⟨budget, hbudget⟩).denote (layout full) = safeUsedFamily (full.drop next.val) budget :=
    (buildCapacityTable_entry_correct q full hlaminar maxBudget next ⟨budget, hbudget⟩).2
  change used ∈ _ ↔ _
  rw [hentry]
  rfl

/-- A first-hit scan in increasing order, on an already built table. -/
def CapacityTable.firstUnsafeBudget (q : Nat) (table : CapacityTable Tool (q + 1))
    (next : Fin table.rows.size) (used : Finset Tool) : Option Nat :=
  (List.range' 1 (q + 1)).find? (fun budget => !(table.acceptsBudget next used budget))

def CapacityTable.extractedRank (q : Nat) (table : CapacityTable Tool (q + 1))
    (next : Fin table.rows.size) (used : Finset Tool) : ℕ∞ :=
  match table.firstUnsafeBudget q next used with
  | none => ⊤
  | some budget => budget

/-- The ordered search returns a prescribed first failing coordinate. -/
theorem find_range'_first (predicate : Nat → Bool) (start length target : Nat)
    (hlower : start ≤ target) (hupper : target < start + length)
    (htarget : predicate target = true)
    (hbefore : ∀ budget, start ≤ budget → budget < target → predicate budget = false) :
    (List.range' start length).find? predicate = some target := by
  induction length generalizing start with
  | zero => omega
  | succ length ih =>
    by_cases heq : start = target
    · subst start
      simp only [List.range'_succ, htarget, List.find?_cons_of_pos]
    · have hlt : start < target := by omega
      have hfalse := hbefore start (Nat.le_refl _) hlt
      rw [List.range'_succ, List.find?_cons_of_neg (by simp [hfalse])]
      apply ih (start + 1) (by omega) (by omega)
      intro budget hbudget hless
      exact hbefore budget (by omega) hless

theorem built_extractedRank_eq_errorRank (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (next : Fin (full.length + 1)) (used : Finset (Fin q)) :
    (buildCapacityTable q full (q + 1)).extractedRank q
      (builtTableRow q full (q + 1) next) used =
        errorRank (full.drop next.val) (Finset.univ \ used) := by
  let table := buildCapacityTable q full (q + 1)
  let row := builtTableRow q full (q + 1) next
  let rank := errorRank (full.drop next.val) (Finset.univ \ used)
  have hcheck (budget : Nat) (hbudget : budget < q + 1 + 1) :
      table.acceptsBudget row used budget = true ↔ (budget : ℕ∞) < rank :=
    (built_acceptsBudget_iff q full hlaminar (q + 1) next used budget hbudget).trans
      (safe_iff_lt_errorRank _ _ _)
  by_cases htop : rank = ⊤
  · have hnone : table.firstUnsafeBudget q row used = none := by
      apply List.find?_eq_none.mpr
      intro budget hmem
      obtain ⟨offset, hoffset, rfl⟩ := List.mem_range'.mp hmem
      have hbudget : 1 + 1 * offset < q + 1 + 1 := by omega
      have hsafe := (hcheck _ hbudget).mpr (by rw [htop]; exact ENat.natCast_lt_top _)
      simp only [one_mul] at hsafe
      simp [hsafe]
    change table.extractedRank q row used = rank
    simp only [CapacityTable.extractedRank, hnone]
    exact htop.symm
  · obtain ⟨finiteRank, hfiniteRank⟩ := ENat.ne_top_iff_exists.mp htop
    have hpositive : 0 < finiteRank := by
      have hpos := errorRank_pos (full.drop next.val) (Finset.univ \ used)
      change 0 < rank at hpos
      rw [← hfiniteRank] at hpos
      exact ENat.natCast_lt_natCast.mp hpos
    have hcard : (Finset.univ \ used : Finset (Fin q)).card ≤ q := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ (Finset.univ \ used : Finset (Fin q))
    have hbounded : finiteRank ≤ q + 1 := by
      have hbound := errorRank_finite_le_card_add_one
        (full.drop next.val) (Finset.univ \ used) htop
      change rank ≤ _ at hbound
      rw [← hfiniteRank] at hbound
      have hnat := ENat.natCast_le_natCast.mp hbound
      omega
    have hfail : table.acceptsBudget row used finiteRank = false := by
      apply Bool.eq_false_iff.mpr
      intro hsafe
      have hlt := (hcheck finiteRank (by omega)).mp hsafe
      rw [← hfiniteRank] at hlt
      exact (lt_irrefl _ hlt)
    have hsome : table.firstUnsafeBudget q row used = some finiteRank := by
      apply find_range'_first _ 1 (q + 1) finiteRank (by omega) (by omega) (by simp [hfail])
      intro budget _ hless
      have hsafe := (hcheck budget (by omega)).mpr (by
        rw [← hfiniteRank]
        exact ENat.natCast_lt_natCast.mpr hless)
      simp [hsafe]
    change table.extractedRank q row used = rank
    simp only [CapacityTable.extractedRank, hsome]
    exact hfiniteRank

end PaperProofs.Structure.LaminarTree
