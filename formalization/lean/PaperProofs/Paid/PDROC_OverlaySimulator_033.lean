module

public import PaperProofs.Paid.PDROC_OverlaySimulator_031

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

/-- Lift stage/tool inclusion to commitment witnesses without asserting
serial equality or equality of correction lists. -/
theorem overlay_commitment_witness_of_pairs {actual virtual : List (VisibleEvent I)}
    (hs : ∀ pair, pair ∈ reservedPairs actual → pair ∈ reservedPairs virtual)
    (pair : MismatchHandle I × I.Tool) (hp : pair ∈ historyCommitments actual) :
    ∃ other ∈ historyCommitments virtual, other.1.stage = pair.1.stage ∧ other.2 = pair.2 := by
  have hm : (pair.1.stage, pair.2) ∈ reservedPairs actual :=
    List.mem_map.mpr ⟨pair, hp, rfl⟩
  obtain ⟨other, ho, he⟩ := List.mem_map.mp (hs _ hm)
  exact ⟨other, ho, congrArg (fun x : I.Stage × I.Tool => x.1) he, congrArg (fun x : I.Stage × I.Tool => x.2) he⟩

theorem overlay_execution_witness_of_pairs {actual virtual : List (VisibleEvent I)}
    (hs : ∀ pair, pair ∈ executedPairs actual → pair ∈ executedPairs virtual)
    (pair : MismatchHandle I × I.Tool) (hp : pair ∈ historyExecutions actual) :
    ∃ other ∈ historyExecutions virtual, other.1.stage = pair.1.stage ∧ other.2 = pair.2 := by
  have hm : (pair.1.stage, pair.2) ∈ executedPairs actual :=
    List.mem_map.mpr ⟨pair, hp, rfl⟩
  obtain ⟨other, ho, he⟩ := List.mem_map.mp (hs _ hm)
  exact ⟨other, ho, congrArg (fun x : I.Stage × I.Tool => x.1) he, congrArg (fun x : I.Stage × I.Tool => x.2) he⟩

/-- One-way physical inventories suffice for allocation and freshness.
Execution additionally uses only a reverse witness for its own commitment,
not global equality between the physical and virtual ledgers. -/
theorem overlay_historyAllowsAction_transport
    (actual virtual : List (VisibleEvent I)) (action : Action I)
    (hcursor : historyCursor actual = historyCursor virtual)
    (hnone : ∀ stage, historyWritten actual stage = none ↔ historyWritten virtual stage = none)
    (hvalid : ∀ handle, historyCursor virtual = handle.stage.val → historyValidHandle virtual handle →
      historyValidHandle actual (reserialHandle actual handle))
    (hused : ∀ tool, tool ∈ historyUsed actual → tool ∈ historyUsed virtual)
    (hreserve : ∀ pair ∈ historyCommitments actual,
      ∃ other ∈ historyCommitments virtual, other.1.stage = pair.1.stage ∧ other.2 = pair.2)
    (hexec : ∀ pair ∈ historyExecutions actual,
      ∃ other ∈ historyExecutions virtual, other.1.stage = pair.1.stage ∧ other.2 = pair.2)
    (hreverse : ∀ handle tool, historyCursor virtual = handle.stage.val → historyValidHandle virtual handle →
      (handle, tool) ∈ historyCommitments virtual →
        (reserialHandle actual handle, tool) ∈ historyCommitments actual)
    (hallow : historyAllowsAction virtual action) :
    historyAllowsAction actual (reserialAction actual (fun _ bit => bit) action) := by
  cases action with
  | review stage => exact ⟨hcursor.trans hallow.1, (hnone stage).mpr hallow.2⟩
  | write stage bit => exact ⟨hcursor.trans hallow.1, (hnone stage).mpr hallow.2⟩
  | advance stage => exact ⟨hcursor.trans hallow.1, fun hn => hallow.2 ((hnone stage).mp hn)⟩
  | allocate handle tool =>
    rcases hallow with ⟨hc, hv, he, hu, hr⟩
    refine ⟨hcursor.trans hc, hvalid handle hc hv, he, fun hm => hu (hused _ hm), ?_⟩
    intro pair hp
    obtain ⟨other, ho, hs, _ht⟩ := hreserve pair hp
    change pair.1.stage ≠ handle.stage
    rw [← hs]
    exact hr other ho
  | execute handle tool =>
    rcases hallow with ⟨hc, hv, he, hr, hu, hx⟩
    refine ⟨hcursor.trans hc, hvalid handle hc hv, he, hreverse handle tool hc hv hr, ?_, ?_⟩
    · intro pair hp
      obtain ⟨other, ho, _hs, ht⟩ := hexec pair hp
      rw [← ht]
      exact hu other ho
    · intro pair hp
      obtain ⟨other, ho, hs, _ht⟩ := hexec pair hp
      change pair.1.stage ≠ handle.stage
      rw [← hs]
      exact hx other ho
  | stop | abandon => trivial

end PDROC
