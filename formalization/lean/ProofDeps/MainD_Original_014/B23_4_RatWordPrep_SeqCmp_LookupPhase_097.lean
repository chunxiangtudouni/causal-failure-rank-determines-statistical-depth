module

public import B23_4_RatWordPrep_SeqCmp_LookupSkip_095

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Lookup

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

def phaseBuild (stageN : Bool) (point : RootB234.RuntimeCounter.Builder.Label) : Label :=
  if stageN then buildNLabel point else buildJLabel point
def phaseRoles (stageN : Bool) : RatInput.Stack ≃ RatInput.Stack :=
  if stageN then sourceNRoles else sourceJRoles

theorem phaseBuild_body (truth stageN : Bool) (caller : Statement C)
    (point : RootB234.RuntimeCounter.Builder.Label) (n5 : point≠5) :
    program truth caller (phaseBuild stageN point)=LabelMap.statement (phaseBuild stageN)
      (StoreIso.statement (WordFields.packetIso C) (RootB234.RuntimeCounter.Builder.atProgram (phaseRoles stageN) false point)) := by
  cases stageN <;> simp [phaseBuild,phaseRoles,buildNLabel,buildJLabel,n5,program] <;> rfl

/-- The actual prefix count is obtained from the physical query0 or N1
packet. The same trace then runs all real counter/packet-transfer rounds. -/
theorem actual_phase (truth stageN : Bool) (caller : Statement C) (values : List Rat)
    (before : State C) (sourceTail tableTail : List Bool)
    (active : before.l=some (phaseBuild stageN 0)) (scratch : before.stk 4=[])
    (source : before.stk (if stageN then 1 else 0)=NatField.packet values.length sourceTail)
    (table : before.stk 2=PacketLists.rats values tableTail) :
    ∃ (final : State C) (_run : Segment truth caller before final) (finalDigits : List Bool),
      final.l=some (skipRound stageN 7) ∧ final.var.2.2=before.var.2.2 ∧
      final.stk 2=tableTail ∧ final.stk 15=PacketLists.rats values.reverse (before.stk 15) ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet finalDigits ∧
      PSTRTMIncrement009.valueDigits finalDigits=0 ∧
      finalDigits.length=(PSTRTMNatValue017.rawPayload values.length).length ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      ∀ slot,SkipFrame slot→final.stk slot=before.stk slot := by
  have sourceActual : before.stk (phaseRoles stageN 8)=NatField.packet values.length sourceTail := by
    cases stageN <;> exact source
  have scratchActual : before.stk (phaseRoles stageN 4)=[] := by cases stageN <;> exact scratch
  obtain ⟨middle,builderRun,port,builderContext,contents,_time⟩ := actual_builder truth caller
    (phaseBuild stageN) (phaseRoles stageN) before values.length sourceTail active sourceActual scratchActual
      (phaseBuild_body truth stageN caller)
  have frame (slot : RatInput.Stack) (n4 : slot≠4) (n10 : slot≠10) (n11 : slot≠11) :
      middle.stk slot=before.stk slot := by
    rw [contents]
    cases stageN with
    | false =>
      change (if slot=0 then _ else if slot=4 then _ else if slot=10 then _ else if slot=11 then _ else before.stk slot)=_
      by_cases n0 : slot=0
      · subst slot; exact source.symm
      · simp only [n0,n4,n10,n11,ite_false]
    | true =>
      change (if slot=1 then _ else if slot=4 then _ else if slot=10 then _ else if slot=11 then _ else before.stk slot)=_
      by_cases n1 : slot=1
      · subst slot; exact source.symm
      · simp only [n1,n4,n10,n11,ite_false]
  have activeRound : middle.l=some (skipRound stageN 0) := by
    rw [port]
    cases stageN <;> rfl
  have counter : middle.stk 10=RootB234.RuntimeCounter.Round.Raw.packet (PSTRTMNatValue017.rawPayload values.length) := by
    rw [contents]
    cases stageN <;> rfl
  have left : middle.stk 11=[false] := by rw [contents]; cases stageN <;> rfl
  have temp : middle.stk 4=[] := by rw [contents]; cases stageN <;> rfl
  have tableActual : middle.stk 2=PacketLists.rats values tableTail :=
    (frame 2 (by decide) (by decide) (by decide)).trans table
  obtain ⟨final,skipRun,finalDigits,finalPort,context,finalTable,archive,counterFinal,
    zero,width,leftFinal,scratchFinal,frameFinal⟩ := actual_skip truth stageN caller values middle _ tableTail
      activeRound counter left temp (PSTRTMNatValue017.valueDigits_rawPayload values.length) tableActual
  let whole := builderRun.append skipRun
  refine ⟨final,whole,finalDigits,finalPort,context.trans builderContext,finalTable,?_,
    counterFinal,zero,width,leftFinal,scratchFinal,?_⟩
  · rw [archive,frame 15 (by decide) (by decide) (by decide)]
  · intro slot safe
    exact (frameFinal slot safe).trans (frame slot safe.2.1 safe.2.2.1 safe.2.2.2.1)

end B23_4_RatWordPrep.Lookup
