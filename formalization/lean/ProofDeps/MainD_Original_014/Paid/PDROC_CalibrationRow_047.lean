module

public import Paid.PDROC_CalibrationRow_046
public import Paid.PDROC_CalibrationRow_028
public import Paid.PDROC_CalibrationRow_038

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Initialization has really finished, but heap6 is still the caller's
arbitrary Cell until the following stepStart instruction sequence. -/
structure DeltaReady (P : Parameters) (base level : ℕ) (state : State) : Prop where
  header : Header P base level state
  cursor : state.heap (base+7)=.natural (2*level+1)
  width : state.heap (base+8)=.natural (2*level+1)
  readValue : state.heap (base+9)=.natural (firstRow base)
  writeValue : state.heap (base+10)=.natural (secondRow base P.certificate.M)
  readRow : RowAt state (firstRow base) (P.walkRow level true 0)

/-- Typed entries of the Q scaffold only. The separate zero/scatter
components supply their own actual loop entries and literal prefixes.
The clock/pointers are stable at these block ENTRIES, not throughout a
partial stepNext; its actual prefix carries the transient header state. -/
inductive QScaffoldEntry (P : Parameters) (base level : ℕ) : Label→State→Prop where
  | start (before : State) (data : DeltaReady P base level before) :
      QScaffoldEntry P base level .stepStart before
  | gate (clock : ℕ) (before : State) (bound : clock≤P.certificate.Q)
      (data : StepData P base level clock before) :
      QScaffoldEntry P base level .stepGate before
  | zeroStart (clock : ℕ) (before : State) (bound : clock<P.certificate.Q)
      (data : StepData P base level clock before) :
      QScaffoldEntry P base level .zeroStart before
  | scatterStart (clock : ℕ) (before : State) (bound : clock<P.certificate.Q)
      (data : ZeroData P base level clock (2*level+1)
        (rowPointers base P.certificate.M clock).1 (rowPointers base P.certificate.M clock).2
        (P.walkRow level true clock) before)
      (writeRow : RowAt before (rowPointers base P.certificate.M clock).2
        (Array.replicate (2*level+1) (0 : ℚ))) :
      QScaffoldEntry P base level .scatterStart before
  | next (clock : ℕ) (before : State) (bound : clock<P.certificate.Q)
      (data : ScatterData P base level clock (2*level+1)
        (rowPointers base P.certificate.M clock).1 (rowPointers base P.certificate.M clock).2 before)
      (newRow : RowAt before (rowPointers base P.certificate.M clock).2 (P.walkRow level true (clock+1))) :
      QScaffoldEntry P base level .stepNext before

theorem QScaffoldEntry.header (P : Parameters) (base level : ℕ) (label : Label) (before : State)
    (entry : QScaffoldEntry P base level label before) : Header P base level before := by
  cases entry with
  | start _ data => exact data.header
  | gate _ _ _ data => exact data.control.header
  | zeroStart _ _ _ data => exact data.control.header
  | scatterStart _ _ _ data _ => exact data.header
  | next _ _ _ data _ => exact data.control.header

/-- A local closure interface used only when assembling actual blocks.
The final canonical provenance instantiates it by constructors, so the
original row theorem will not acquire a supplied closure or size bound. -/
def QScaffoldClosed (P : Parameters) (origin base level : ℕ) (input : List Cell)
    (Good : State→Prop) : Prop :=
  ∀ label before middle after,QScaffoldEntry P base level label before → Good before →
    before.pc=labelAddress origin label →
    linearExecute input (basicBlock label).body before=some middle →
    (controlInstruction origin (basicBlock label).control).execute input middle=some after →
    ∀ state,BlockPrefix input label before after state→Good state

end PDROC.CalibrationRow
