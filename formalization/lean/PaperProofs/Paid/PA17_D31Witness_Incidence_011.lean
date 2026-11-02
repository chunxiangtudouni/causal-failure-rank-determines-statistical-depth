module

public import PaperProofs.Paid.PA17_D31Witness_001
public import PaperProofs.Common.NativeHorizon

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Paid.PA17D31WitnessIncidence011

open Common Common.Native MeasureTheory PA17D31Witness001

variable {I : Instance}

def committedStages (L : Ledger I) : Finset I.Stage :=
  (L.commitments.map (fun a => a.handle.stage)).toFinset

def executedStages (L : Ledger I) : Finset I.Stage :=
  (L.executions.map (fun e => e.handle.stage)).toFinset

def errorStages (truth : I.Stage → Bool) : Finset I.Stage :=
  Finset.univ.filter (fun stage => truth stage = true)

theorem committedStages_card (L : Ledger I) (hwf : LedgerWellFormed L) :
    (committedStages L).card = L.commitments.length := by
  rw [committedStages, List.toFinset_card_of_nodup hwf.commitment_stages, List.length_map]

theorem executedStages_card (L : Ledger I) (hwf : LedgerWellFormed L) :
    (executedStages L).card = L.executions.length := by
  rw [executedStages, List.toFinset_card_of_nodup hwf.execution_stages, List.length_map]

theorem executedStages_subset_committed (L : Ledger I) (hwf : LedgerWellFormed L) :
    executedStages L ⊆ committedStages L := by
  intro stage hs
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
  obtain ⟨a, ha, hh, _, _⟩ := hwf.backed e he
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ha, congrArg MismatchHandle.stage hh⟩)

theorem committedStages_subset_errors (C : Contract I) (s : State I) (hinv : Invariant C s)
    (hfalse : ∀ stage bit, s.ledger.written stage = some bit → bit = false) :
    committedStages s.ledger ⊆ errorStages s.ledger.truth := by
  intro stage hs
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
  have hb := hfalse a.handle.stage _ (hinv.commitment_genuine a ha).1
  simp only [errorStages, Finset.mem_filter, Finset.mem_univ, true_and]
  cases ht : s.ledger.truth a.handle.stage
  · simp only [ht, Bool.not_false] at hb
    cases hb
  · rfl

theorem executedStages_subset_errors (C : Contract I) (s : State I) (hinv : Invariant C s)
    (hfalse : ∀ stage bit, s.ledger.written stage = some bit → bit = false) :
    executedStages s.ledger ⊆ errorStages s.ledger.truth :=
  (executedStages_subset_committed s.ledger hinv.wellFormed).trans
    (committedStages_subset_errors C s hinv hfalse)

/-- Once the first K errors have real commitments, coverage of a task with
at most K errors is complete. No tools or payments are virtualized here. -/
theorem committedStages_eq_errors_of_coverage (C : Contract I) (s : State I)
    (hinv : Invariant C s)
    (hfalse : ∀ stage bit, s.ledger.written stage = some bit → bit = false)
    (hcount : (errorStages s.ledger.truth).card ≤ I.toolCount)
    (hcover : ∀ stage ∈ errorStages s.ledger.truth,
      stage ∈ committedStages s.ledger ∨ I.toolCount ≤ s.ledger.commitments.length) :
    committedStages s.ledger = errorStages s.ledger.truth := by
  have hsub := committedStages_subset_errors C s hinv hfalse
  apply Finset.Subset.antisymm hsub
  intro stage hs
  rcases hcover stage hs with hc | hfull
  · exact hc
  · have heq := Finset.eq_of_subset_of_card_le hsub
      (hcount.trans (hfull.trans_eq (committedStages_card s.ledger hinv.wellFormed).symm))
    exact heq.symm ▸ hs

theorem menuUnusedTool_none_all_used (P : Parameters)
    (history : List (VisibleEvent P.sharedInstance))
    (hnone : blindUnusedTool P history = none) :
    historyUsed history = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro tool
  by_contra hnot
  unfold blindUnusedTool Parameters.menuUnusedTool at hnone
  let used : Finset (Fin P.tools) := historyUsed history
  have hnone' : (List.finRange P.tools).find? (fun selected =>
      decide (selected ∉ used)) = none := hnone
  let selected : Fin P.tools := tool
  have hnot' : selected ∉ used := hnot
  have h := List.find?_eq_none.mp hnone' selected (List.mem_finRange selected)
  exact h (decide_eq_true_iff.mpr hnot')

end PaperProofs.Paid.PA17D31WitnessIncidence011
