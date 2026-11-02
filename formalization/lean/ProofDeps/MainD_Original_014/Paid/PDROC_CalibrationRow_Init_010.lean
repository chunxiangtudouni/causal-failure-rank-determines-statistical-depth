module

public import Paid.PDROC_CalibrationRow_Init_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Concrete caller-carry provenance for every initialization state.
The initial scratch registers/header6 may be arbitrary Cells. Each new
node records a real labelled block with its actual InitData and exact
literal-prefix/control execution, rather than a P-only input bound. -/
inductive InitProvenance (P : Parameters) (origin base level : ℕ) (input : List Cell)
    (caller : State) : State→Prop where
  | initial : InitProvenance P origin base level input caller caller
  | block (cursor : ℕ) (label : Label) (before middle after state : State)
      (previous : InitProvenance P origin base level input caller before)
      (data : InitData P base level cursor before) (bound : cursor≤2*level+1)
      (entry : InitLabelEntry level cursor label before)
      (position : before.pc=labelAddress origin label)
      (body : linearExecute input (basicBlock label).body before=some middle)
      (control : (controlInstruction origin (basicBlock label).control).execute input middle=some after)
      (prefixRun : (∃ count≤(basicBlock label).body.length,
        linearExecute input ((basicBlock label).body.take count) before=some state) ∨ state=after) :
      InitProvenance P origin base level input caller state

theorem initProvenance_closed (P : Parameters) (origin base level : ℕ) (input : List Cell) (caller : State) :
    InitClosed P origin base level input (InitProvenance P origin base level input caller) := by
  intro cursor label before middle after data bound entry previous position body control state prefixRun
  exact InitProvenance.block cursor label before middle after state previous data bound entry position body control prefixRun

/-- Full original initialization component with NO extra phase-closure
or operand-size premise: the canonical concrete provenance closes by
construction. This remains only the initialization part of original D27. -/
theorem init_complete_provenance (P : Parameters) (origin base level : ℕ) (input : List Cell) (before : State)
    (header : Header P base level before) (position : before.pc=labelAddress origin .initGate)
    (cursor : before.heap (base+7)=.natural 0)
    (width : before.heap (base+8)=.natural (2*level+1))
    (read : before.heap (base+9)=.natural (firstRow base))
    (write : before.heap (base+10)=.natural (secondRow base P.certificate.M))
    (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,SafeSegment origin base (region base P.certificate.M) input
      (InitProvenance P origin base level input before) before after (1600*(level+1)) ∧
      after.pc=labelAddress origin .stepStart ∧ Header P base level after ∧
      after.heap (base+7)=.natural (2*level+1) ∧ after.heap (base+8)=.natural (2*level+1) ∧
      after.heap (base+9)=.natural (firstRow base) ∧
      after.heap (base+10)=.natural (secondRow base P.certificate.M) ∧
      RowAt after (firstRow base) (P.walkRow level true 0) :=
  init_complete_safe P origin base level input (InitProvenance P origin base level input before)
    (initProvenance_closed P origin base level input before) before header .initial position cursor width read write levelBound

end PDROC.CalibrationRow
