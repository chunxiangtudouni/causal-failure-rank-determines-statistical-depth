module

public import Paid.PDROC_CalibrationRow_051
public import Paid.PDROC_CalibrationRow_Init_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Provenance for the ORIGINAL weak-Header callee. Every component is
tied to its real caller, so a carried arbitrary Cell is never converted
into an assumed P-only bit bound. In particular the init component keeps
old heap6, and the scaffold's stepStart really establishes Nat0. -/
inductive RowProvenance (P : Parameters) (origin base level : ℕ) (input : List Cell)
    (caller : State) : State→Prop where
  | initial : RowProvenance P origin base level input caller caller
  | levelInit (state : State) (header : Header P base level caller)
      (position : caller.pc=labelAddress origin .levelInit)
      (prefixRun : BlockPrefix input .levelInit caller
        {levelInitResult caller base level P.certificate.M with pc:=labelAddress origin .initGate} state) :
      RowProvenance P origin base level input caller state
  | init (before state : State)
      (previous : RowProvenance P origin base level input caller before)
      (header : Header P base level before) (position : before.pc=labelAddress origin .initGate)
      (cursor : before.heap (base+7)=.natural 0) (width : before.heap (base+8)=.natural (2*level+1))
      (readValue : before.heap (base+9)=.natural (firstRow base))
      (writeValue : before.heap (base+10)=.natural (secondRow base P.certificate.M))
      (phase : InitProvenance P origin base level input before state) :
      RowProvenance P origin base level input caller state
  | scaffold (label : Label) (before middle after state : State)
      (previous : RowProvenance P origin base level input caller before)
      (entry : QScaffoldEntry P base level label before)
      (position : before.pc=labelAddress origin label)
      (body : linearExecute input (basicBlock label).body before=some middle)
      (control : (controlInstruction origin (basicBlock label).control).execute input middle=some after)
      (prefixRun : BlockPrefix input label before after state) :
      RowProvenance P origin base level input caller state
  | q (before state : State)
      (previous : RowProvenance P origin base level input caller before)
      (data : StepData P base level 0 before) (position : before.pc=labelAddress origin .stepGate)
      (phase : QProvenance P origin base level input before state) :
      RowProvenance P origin base level input caller state

end PDROC.CalibrationRow
