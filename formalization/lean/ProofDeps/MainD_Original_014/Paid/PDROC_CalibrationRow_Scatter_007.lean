module

public import Paid.PDROC_CalibrationRow_Scatter_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Canonical provenance follows the original labelled blocks from the
actual caller. It records real source-clock/cursor/read-row/partial-row
entry facts and the executed literal prefix, including the first of two
coincident absorbing bumps. No phase-closure premise is supplied. -/
inductive ScatterProvenance (P : Parameters) (origin base level clock read write : ℕ)
    (input : List Cell) (caller : State) : State→Prop where
  | initial : ScatterProvenance P origin base level clock read write input caller caller
  | block (cursor : ℕ) (label : Label) (before middle after state : State)
      (previous : ScatterProvenance P origin base level clock read write input caller before)
      (entry : ScatterEntry P base level clock cursor read write before label)
      (position : before.pc=labelAddress origin label)
      (body : linearExecute input (basicBlock label).body before=some middle)
      (control : (controlInstruction origin (basicBlock label).control).execute input middle=some after)
      (prefixRun : (∃ count≤(basicBlock label).body.length,
        linearExecute input ((basicBlock label).body.take count) before=some state) ∨ state=after) :
      ScatterProvenance P origin base level clock read write input caller state

theorem scatterProvenance_closed (P : Parameters) (origin base level clock read write : ℕ)
    (input : List Cell) (caller : State) :
    ScatterClosed P origin base level clock read write input
      (ScatterProvenance P origin base level clock read write input caller) := by
  intro cursor label before middle after entry previous position body control state prefixRun
  exact ScatterProvenance.block cursor label before middle after state previous entry position body control prefixRun

/-- Same original scatter semantics and cost as numeric038, now on one
actual trace with full prefix frames/live/caller-carry and canonical
phase provenance. This covers only scatterGate through stepNext. -/
theorem scatter_complete_provenance (input : List Cell) (P : Parameters)
    (origin base level clock read write : ℕ) (before : State)
    (data : ScatterData P base level clock 0 read write before)
    (position : before.pc=labelAddress origin .scatterGate) (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,SafeSegment origin base (region base P.certificate.M) input
      (ScatterProvenance P origin base level clock read write input before) before after (3000*(level+1)) ∧
      ScatterData P base level clock (2*level+1) read write after ∧ after.pc=labelAddress origin .stepNext ∧
      RowAt after write (P.walkRow level true (clock+1)) ∧
      MemoryFrame (region base P.certificate.M) before after ∧ after.output=before.output ∧
      after.register .fresh=before.register .fresh :=
  scatter_complete_safe input P origin base level clock read write before data
    (ScatterProvenance P origin base level clock read write input before)
    (scatterProvenance_closed P origin base level clock read write input before)
    .initial position levelBound

end PDROC.CalibrationRow
