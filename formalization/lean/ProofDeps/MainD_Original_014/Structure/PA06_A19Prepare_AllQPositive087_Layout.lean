module

public import Structure.PA06_A19Prepare_AfterParents085_Layout
public import Structure.PA06_A19Prepare_EarlyGate079_CodeAgreement

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED selected-program compact slices. Only the first ten
instructions were replaced. The original retention, ordering and parent
semantics therefore run at their unchanged absolute offsets in this ONE
program; their output data are not assumed by the raw caller. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQPositive087

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawIncidenceLaminarRAM RawTreePreprocessingClaims CompactControllerClaims
open PA06A19PrepareAllQCode082 (program oldP)

abbrev bits := PA06A19PreparePreBuild044.bits
abbrev allocation := PA06A19PreparePreBuild044.allocation
abbrev capacity := PA06A19PreparePreBuild044.capacity

def compactTail : List PackingOp :=
  PA06A19PrepareRawHeader039Entry.headerSuffix
    PA06A19PrepareAfterParents085.headerRight

theorem oldP_compact :
    oldP = PA06A19PrepareCompactCandidates007.program compactTail := rfl

theorem slot_after_gate (index : Nat) (lo : 10 ≤ index) (hi : index < oldP.length)
    (fallback : PackingOp) : program.getD index fallback = oldP.getD index fallback := by
  have patchedBound : index < program.length := by
    simpa only [PA06A19PrepareAllQCode082.program_length,
      PA06A19PrepareAllQCode082.oldP_length] using hi
  rw [List.getD_eq_getElem _ _ patchedBound, List.getD_eq_getElem _ _ hi]
  exact PA06A19PrepareEarlyGate079.slot_after_ten
    (5 * PA06A19PrepareAllQCode082.handlerStart) oldP index lo hi

theorem old_retention : PA06A19PrepareAfterGate081.RetentionAt oldP := by
  rw [oldP_compact]
  exact PA06A19PrepareCompactOrdering034Entry.retention_slice
    (RawCandidateParentRAM.programAt PA06A19PrepareCompactCandidates007.parentStart ++ compactTail)

theorem old_ordering : PA06A19PrepareAfterGate081.OrderingAt oldP := by
  rw [oldP_compact]
  exact PA06A19PrepareCompactOrdering034Entry.ordering_slice
    (RawCandidateParentRAM.programAt PA06A19PrepareCompactCandidates007.parentStart ++ compactTail)

theorem old_parents : PA06A19PrepareAfterGate081.ParentsAt oldP := by
  rw [oldP_compact]
  exact PA06A19PrepareCompactCandidates007.parent_slice compactTail

theorem retention : PA06A19PrepareAfterGate081.RetentionAt program := by
  refine ⟨?_, ?_⟩
  · simpa only [PA06A19PrepareAllQCode082.program_length,
      PA06A19PrepareAllQCode082.oldP_length] using old_retention.1
  · intro position hp
    have hi : PA06A19PrepareAfterGate081.retentionStart + position < oldP.length := by
      have room := old_retention.1
      omega
    rw [slot_after_gate _ (by change 10 ≤ 144 + position; omega) hi]
    exact old_retention.2 position hp

theorem ordering : PA06A19PrepareAfterGate081.OrderingAt program := by
  refine ⟨?_, ?_⟩
  · simpa only [PA06A19PrepareAllQCode082.program_length,
      PA06A19PrepareAllQCode082.oldP_length] using old_ordering.1
  · intro position hp
    have hi : PA06A19PrepareAfterGate081.orderingStart + position < oldP.length := by
      have room := old_ordering.1
      omega
    rw [slot_after_gate _ (by change 10 ≤ 542 + position; omega) hi]
    exact old_ordering.2 position hp

theorem parents : PA06A19PrepareAfterGate081.ParentsAt program := by
  refine ⟨?_, ?_⟩
  · simpa only [PA06A19PrepareAllQCode082.program_length,
      PA06A19PrepareAllQCode082.oldP_length] using old_parents.1
  · intro position hp
    have hi : PA06A19PrepareAfterGate081.parentStart + position < oldP.length := by
      have room := old_parents.1
      omega
    rw [slot_after_gate _ (by change 10 ≤ 845 + position; omega) hi]
    exact old_parents.2 position hp

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQPositive087
