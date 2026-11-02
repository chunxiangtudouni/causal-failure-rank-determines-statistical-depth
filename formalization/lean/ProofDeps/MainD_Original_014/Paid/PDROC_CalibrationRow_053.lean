module

public import Paid.PDROC_CalibrationRow_052
public import Paid.PDROC_CalibrationRow_044
public import Paid.PDROC_CalibrationRow_048
public import Paid.PDROC_CalibrationRow_054

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Whole original levelInit→sumStart callee, on ONE actual fetched
trace. Every state has its frame/output/fresh/16-live certificate and
canonical clock/cursor/read-row/partial-row/literal-prefix provenance.
The only entrance facts are the original Header, entry PC and L≤M+1;
there is no preinitialized row, clock type, external closure, or bound
on arbitrary caller scratch. Numeric bit bounds can consume these
sources together with the real outer caller's initial bounds. -/
theorem row_complete_provenance (input : List Cell) (P : Parameters) (origin base level : ℕ) (before : State)
    (header : Header P base level before) (position : before.pc=labelAddress origin .levelInit)
    (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,SafeSegment origin base (region base P.certificate.M) input
      (RowProvenance P origin base level input before) before after (10000*(P.certificate.Q+1)*(level+1)) ∧
      after.pc=labelAddress origin .sumStart ∧ StepData P base level P.certificate.Q after ∧
      after.heap (base+6)=.natural P.certificate.Q ∧ after.heap (base+7)=.natural (2*level+1) ∧
      after.heap (base+8)=.natural (2*level+1) ∧
      after.heap (base+9)=.natural (rowPointers base P.certificate.M P.certificate.Q).1 ∧
      after.heap (base+10)=.natural (rowPointers base P.certificate.M P.certificate.Q).2 ∧
      RowAt after (rowPointers base P.certificate.M P.certificate.Q).1 (P.walkRow level true P.certificate.Q) := by
  let Good := RowProvenance P origin base level input before
  let entry : State := {levelInitResult before base level P.certificate.M with pc:=labelAddress origin .initGate}
  have entryRun : SafeSegment origin base (region base P.certificate.M) input Good before entry 480 :=
    levelInit_safe input P origin base level before header position Good
      (fun state prefixRun => RowProvenance.levelInit state header position prefixRun)
  have entryFrame : MemoryFrame (region base P.certificate.M) before entry := levelInit_frame before base level P.certificate.M
  have entryHeader := Header.transport P base level before entry header entryFrame
    (levelInit_live before base level P.certificate.M) (levelInit_fields before base level P.certificate.M).2.2.1
  have slots := levelInit_slots before base level P.certificate.M
  obtain ⟨initialized,initRaw,initPosition,initHeader,initCursor,initWidth,initRead,initWrite,deltaRow⟩ :=
    init_complete_provenance P origin base level input entry entryHeader rfl
      slots.1 slots.2.1 slots.2.2.1 slots.2.2.2 levelBound
  have initRun : SafeSegment origin base (region base P.certificate.M) input Good entry initialized (1600*(level+1)) :=
    initRaw.weaken (fun state phase => RowProvenance.init entry state entryRun.final.2.2.2.2 entryHeader rfl
      slots.1 slots.2.1 slots.2.2.1 slots.2.2.2 phase)
  have ready : DeltaReady P base level initialized :=
    ⟨initHeader,initCursor,initWidth,initRead,initWrite,deltaRow⟩
  let started := constantSlotResult initialized base 6 (.natural 0)
  let start : State := {started with pc:=labelAddress origin .stepGate}
  have startBody : linearExecute input (basicBlock .stepStart).body initialized=some started :=
    constantSlot_execute input initialized base 6 (.natural 0) initHeader.fresh
  have startControl : (controlInstruction origin (basicBlock .stepStart).control).execute input started=some start := rfl
  have startRun : SafeSegment origin base (region base P.certificate.M) input Good initialized start 90 :=
    constantRow_safe input P origin base level 6 .stepStart .stepGate initialized initHeader rfl initPosition rfl rfl
      (by decide) (by decide) Good
      (fun state prefixRun => RowProvenance.scaffold .stepStart initialized started start state initRun.final.2.2.2.2
        (.start initialized ready) initPosition startBody startControl prefixRun)
  have startDataMiddle := StepData.start P base level initialized initHeader initCursor initWidth initRead initWrite deltaRow
  have startData := StepData.sameMemory P base level 0 started start startDataMiddle rfl rfl rfl
  obtain ⟨after,qRaw,done,finish⟩ :=
    qLoop_provenance input P origin base level 0 start startData rfl (Nat.zero_le _) levelBound
  have qRun : SafeSegment origin base (region base P.certificate.M) input Good start after
      (5000*(P.certificate.Q-0)*(level+1)+135) :=
    qRaw.weaken (fun state phase => RowProvenance.q start state startRun.final.2.2.2.2 startData rfl phase)
  have combined := ((entryRun.trans initRun).trans startRun).trans qRun
  exact ⟨after,combined.mono (rowCost_bound P.certificate.Q level),finish,done,
    done.control.clockValue,done.control.cursorValue,done.control.width,done.control.read,done.control.write,done.readRow⟩

end PDROC.CalibrationRow
