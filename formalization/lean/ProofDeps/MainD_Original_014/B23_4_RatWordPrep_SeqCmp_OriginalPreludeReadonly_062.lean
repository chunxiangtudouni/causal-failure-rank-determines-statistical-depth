module

public import B23_4_RatWordPrep_SeqCmp_OriginalPreludeSyntax_061

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.OriginalPrelude

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM

variable {C : Type*}

def callerContext (memory : Store C) : C := OriginalFee.context (feeMemory memory)

theorem program_readonly (point : Label) : RawGetter.Readonly (callerContext (C := C)) (program .halt point) := by
  cases point
  all_goals repeat' first
    | (rename_i point; fin_cases point)
    | (rename_i point; cases point)
  all_goals
    dsimp [RawGetter.Readonly,program,callerContext,feeMemory,copyIso,feeIso,
      WholeCopy.program,WholeCopy.capture,WholeCopy.present,WholeCopy.bit,
      HeaderNat.program,HeaderNat.fieldIso,Header.program,Header.source,NatField.program,Rewind.program,Rewind.clearSlot,
      OriginalFee.program,OriginalFee.context,OriginalFee.rawIso,
      RatInput.Complement.program,RatInput.Complement.storeMap,RatInput.Original.program,RatInput.Original.storeMap,
      PSTRSymbolicRatExport.Joined.combinedProgram,PSTRSymbolicRatExport.Joined.parserProgram,
      PSTRSymbolicRatExport.Joined.exchange,PSTRSymbolicWordPriorStack.program,PSTRSymbolicWordPriorStack.source,
      RatInput.Encoder.program,RatInput.Encoder.exchange,RatInput.Encoder.finishBody,RatInput.Encoder.putPrefix,
      RatInput.program,RatInput.fieldBody,RatInput.restoreBody,
      RatOutput.Link.program,RatOutput.Link.exchange,IsolatedRat.program,IsolatedRat.body,RatOutput.program,
      WordNatIO.callerProgram,WordNatIO.program,WordNatIO.jump,
      RawGetter.program,RawGetter.bootMemory,RawGetter.parserIso,RawGetter.parserProgram,RawGetter.parserSource,
      PSTRSymbolicRatExport.ratProgram,PSTRSymbolicRatExport.fieldBody,PSTRSymbolicNaturalExport.program,
      LabelMap.statement,StoreIso.statement,StoreIso.machine,StoreIso.exchange,StackIso.statement,
      VirtualReturn.program,VirtualReturn.statement,VirtualReturn.core,VirtualBool.source,BoolOnStacks.program,ContextLift.statement]
    repeat' constructor
    all_goals (intros; rfl)

theorem step_context (before after : State C) (edge : TM2.step (program .halt) before=some after) :
    callerContext after.var=callerContext before.var := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact RawGetter.nodes_readonly callerContext _ (program_readonly point) memory contents _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_context (trace : List (State C)) (before : State C) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program .halt) a=some b)) :
    ∀ current∈trace,callerContext current.var=callerContext before.var := by
  induction trace generalizing before with
  | nil => simp
  | cons start rest ih =>
    have same : start=before := Option.some.inj first
    subst start
    cases rest with
    | nil =>
      intro current member
      have same := List.mem_singleton.mp member
      subst current
      rfl
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      intro current member
      rcases List.mem_cons.mp member with rfl | later
      · rfl
      · exact (ih next rfl tailChain current later).trans (step_context before next edge)

end B23_4_RatWordPrep.OriginalPrelude
