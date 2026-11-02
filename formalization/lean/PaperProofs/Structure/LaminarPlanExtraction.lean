module

public import PaperProofs.Structure.LaminarToolExtraction
import Lean.Elab.Tactic.Omega

/-!
A concrete finite causal plan extracted using one shared full-input table.
Its runtime choices inspect only the stored table, used set and known stage
sequence. Safety is proved against the independent adversarial Play semantics.
The Plan tree can expand exponentially; this module supplies no efficient
controller, running-time certificate or storage bound.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree

variable {Tool : Type*} [DecidableEq Tool]

theorem safePlan_choose_of {eligible : Finset Tool} {later : List (Finset Tool)}
    (good bad : Plan Tool later) (remaining : Finset Tool) (budget : Nat) (tool : Tool)
    (hgood : SafePlan good remaining (budget + 1))
    (hlegal : tool ∈ eligible ∩ remaining)
    (hbad : SafePlan bad (remaining.erase tool) budget) :
    SafePlan (.choose (eligible := eligible) good tool bad) remaining (budget + 1) := by
  intro errors herr play
  cases play with
  | correct_choose continuation => exact hgood errors herr continuation
  | unavailable _ _ _ _ hillegal => exact hillegal hlegal
  | repaired _ continuation => exact hbad _ (Nat.le_of_succ_le_succ herr) continuation

/-- Total structural recursion, with explicit decline for a missing row or
missing eligible tool. The table is passed unchanged to every recursive call. -/
def planFromTable (q : Nat) (table : CapacityTable (Fin q) (q + 1)) :
    (suffix : List (Finset (Fin q))) → Nat → Finset (Fin q) → Plan (Fin q) suffix
  | [], _, _ => .done
  | eligible :: later, offset, used =>
      let good := planFromTable q table later (offset + 1) used
      if hrow : offset + 1 < table.rows.size then
        match pickMaxRankTool q table ⟨offset + 1, hrow⟩ eligible used with
        | none => .decline good
        | some tool => .choose good tool
            (planFromTable q table later (offset + 1) (insert tool used))
      else .decline good

theorem planFromBuiltTable_safe (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (suffix : List (Finset (Fin q)))
    (offset : Nat) (hdrop : suffix = full.drop offset) (used : Finset (Fin q)) (budget : Nat)
    (hsafe : Safe suffix (Finset.univ \ used) budget) :
    SafePlan (planFromTable q (buildCapacityTable q full (q + 1)) suffix offset used)
      (Finset.univ \ used) budget := by
  induction suffix generalizing offset used budget with
  | nil =>
    intro errors herr play
    cases play
  | cons eligible later ih =>
    cases budget with
    | zero => exact safePlan_zero _ _
    | succ budget =>
      have htail : later = full.drop (offset + 1) := by
        have h := congrArg List.tail hdrop
        simpa only [List.tail_cons, List.tail_drop] using h
      have hoffset : offset < full.length := by
        apply Nat.lt_of_not_ge
        intro hle
        have hempty := List.drop_eq_nil_of_le hle
        rw [← hdrop] at hempty
        exact List.cons_ne_nil _ _ hempty
      have hrow : offset + 1 < (buildCapacityTable q full (q + 1)).rows.size := by
        rw [buildCapacityTable_size]
        omega
      let next : Fin (full.length + 1) := ⟨offset + 1, by omega⟩
      have hsafeNext : Safe (eligible :: full.drop next.val) (Finset.univ \ used) (budget + 1) := by
        simpa only [next, ← htail] using hsafe
      obtain ⟨tool, hpick, heligible, hunused, hbad⟩ :=
        built_pickMaxRankTool_safe_exists q full hlaminar next eligible used budget hsafeNext
      have hrowEq : (⟨offset + 1, hrow⟩ : Fin (buildCapacityTable q full (q + 1)).rows.size) =
          builtTableRow q full (q + 1) next := by
        apply Fin.ext
        rfl
      have hpickActual : pickMaxRankTool q (buildCapacityTable q full (q + 1))
          ⟨offset + 1, hrow⟩ eligible used = some tool := by
        rw [hrowEq]
        exact hpick
      have hgood := ((safe_cons_succ_iff eligible later (Finset.univ \ used) budget).mp hsafe).1
      have hgoodPlan := ih (offset + 1) htail used (budget + 1) hgood
      have hbadLater : Safe later (Finset.univ \ insert tool used) budget := by
        simpa only [next, ← htail, remaining_after_used_insert] using hbad
      have hbadPlan := ih (offset + 1) htail (insert tool used) budget hbadLater
      simp only [planFromTable, hrow, ↓reduceDIte, hpickActual]
      apply safePlan_choose_of _ _ _ budget tool hgoodPlan
      · exact Finset.mem_inter.mpr ⟨heligible, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hunused⟩⟩
      · simpa only [remaining_after_used_insert] using hbadPlan

/-- One table construction is shared by the complete finite causal Plan. -/
def extractedSuffixPlan (q : Nat) (full : List (Finset (Fin q)))
    (next : Fin (full.length + 1)) (used : Finset (Fin q)) : Plan (Fin q) (full.drop next.val) :=
  let table := buildCapacityTable q full (q + 1)
  planFromTable q table (full.drop next.val) next.val used

theorem extractedSuffixPlan_safe_iff (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (next : Fin (full.length + 1))
    (used : Finset (Fin q)) (budget : Nat) :
    SafePlan (extractedSuffixPlan q full next used) (Finset.univ \ used) budget ↔
      Safe (full.drop next.val) (Finset.univ \ used) budget := by
  constructor
  · intro hplan
    exact ⟨extractedSuffixPlan q full next used, hplan⟩
  · exact planFromBuiltTable_safe q full hlaminar (full.drop next.val) next.val rfl used budget

theorem extractedSuffixPlan_safe_iff_lt_rank (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (next : Fin (full.length + 1))
    (used : Finset (Fin q)) (budget : Nat) :
    SafePlan (extractedSuffixPlan q full next used) (Finset.univ \ used) budget ↔
      (budget : ℕ∞) < errorRank (full.drop next.val) (Finset.univ \ used) :=
  (extractedSuffixPlan_safe_iff q full hlaminar next used budget).trans (safe_iff_lt_errorRank _ _ _)

theorem extractedSuffixPlan_safe_all_of_rank_top (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (next : Fin (full.length + 1)) (used : Finset (Fin q))
    (htop : errorRank (full.drop next.val) (Finset.univ \ used) = ⊤) :
    ∀ budget, SafePlan (extractedSuffixPlan q full next used) (Finset.univ \ used) budget := by
  intro budget
  apply (extractedSuffixPlan_safe_iff_lt_rank q full hlaminar next used budget).mpr
  rw [htop]
  exact ENat.natCast_lt_top budget

end PaperProofs.Structure.LaminarTree
