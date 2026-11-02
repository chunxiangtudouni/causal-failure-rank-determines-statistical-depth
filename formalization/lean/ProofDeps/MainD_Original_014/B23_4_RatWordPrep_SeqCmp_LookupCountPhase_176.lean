module

public import B23_4_RatWordPrep_SeqCmp_LookupCountSkip_174

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Lookup.Count

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

def setupWork (mass number : Nat) : Nat := 2*mass+2*(PSTRTMNatValue017.rawPayload number).length+14
noncomputable def phaseMass (truth : Bool) (caller : Statement C) (number mass : Nat) : Nat :=
  mass+pushCap truth caller*setupWork mass number
noncomputable def phaseWork (truth : Bool) (caller : Statement C) (values : List Rat) (mass : Nat) : Nat :=
  setupWork mass values.length+skipWork values (phaseMass truth caller values.length mass)

theorem phaseMass_mono (truth : Bool) (caller : Statement C) (number : Nat) {a b : Nat} (bound : a≤b) :
    phaseMass truth caller number a≤phaseMass truth caller number b := by
  unfold phaseMass setupWork
  nlinarith

theorem phaseWork_mono (truth : Bool) (caller : Statement C) (values : List Rat) {a b : Nat} (bound : a≤b) :
    phaseWork truth caller values a≤phaseWork truth caller values b := by
  have mass := phaseMass_mono truth caller values.length bound
  unfold phaseWork skipWork setupWork
  nlinarith

/-- The actual prefix count is obtained from the physical query0 or N1
packet. The same trace then runs all real counter/packet-transfer rounds. -/
theorem actual_phase (truth stageN : Bool) (caller : Statement C) (values : List Rat)
    (before : State C) (sourceTail tableTail : List Bool)
    (active : before.l=some (phaseBuild stageN 0)) (scratch : before.stk 4=[])
    (source : before.stk (if stageN then 1 else 0)=NatField.packet values.length sourceTail)
    (table : before.stk 2=PacketLists.rats values tableTail) :
    ∃ (final : State C) (run : Segment truth caller before final) (finalDigits : List Bool),
      final.l=some (skipRound stageN 7) ∧ final.var.2.2=before.var.2.2 ∧
      final.stk 2=tableTail ∧ final.stk 15=PacketLists.rats values.reverse (before.stk 15) ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet finalDigits ∧
      PSTRTMIncrement009.valueDigits finalDigits=0 ∧
      finalDigits.length=(PSTRTMNatValue017.rawPayload values.length).length ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      (∀ slot,SkipFrame slot→final.stk slot=before.stk slot) ∧
      RatInput.occupied final.stk≤phaseMass truth caller values.length (RatInput.occupied before.stk) ∧
      run.trace.length≤phaseWork truth caller values (RatInput.occupied before.stk) := by
  have sourceActual : before.stk (phaseRoles stageN 8)=NatField.packet values.length sourceTail := by
    cases stageN <;> exact source
  have scratchActual : before.stk (phaseRoles stageN 4)=[] := by cases stageN <;> exact scratch
  obtain ⟨middle,builderRun,port,builderContext,contents,buildTime⟩ := actual_builder truth caller
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
    zero,width,leftFinal,scratchFinal,frameFinal,skipMass,skipTime⟩ := actual_skip truth stageN caller values middle _ tableTail
      activeRound counter left temp (PSTRTMNatValue017.valueDigits_rawPayload values.length) tableActual
  have paidBuild : builderRun.trace.length≤setupWork (RatInput.occupied before.stk) values.length := by
    have a := RatInput.Encoder.point_mass before.stk 10
    have b := RatInput.Encoder.point_mass before.stk 11
    have rawBound : builderRun.trace.length≤(before.stk 10).length+(before.stk 11).length+
        2*(PSTRTMNatValue017.rawPayload values.length).length+14 := by
      cases stageN <;> exact buildTime
    unfold setupWork
    omega
  have middleMass := WordFinish.Resources.trace_mass (pushCap truth caller) (pushes truth caller)
    builderRun.trace before (RatInput.occupied before.stk) builderRun.first builderRun.chain (Nat.le_refl _)
      middle (List.mem_of_getLast? builderRun.last)
  have massBound : RatInput.occupied middle.stk≤phaseMass truth caller values.length (RatInput.occupied before.stk) :=
    middleMass.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ paidBuild) _)
  have paidSkip : skipRun.trace.length≤skipWork values (phaseMass truth caller values.length (RatInput.occupied before.stk)) := by
    apply skipTime.trans
    unfold skipWork
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right massBound 1)) _
  let whole := builderRun.append skipRun
  refine ⟨final,whole,finalDigits,finalPort,context.trans builderContext,finalTable,?_,
    counterFinal,zero,width,leftFinal,scratchFinal,?_,skipMass.le.trans massBound,?_⟩
  · rw [archive,frame 15 (by decide) (by decide) (by decide)]
  · intro slot safe
    exact (frameFinal slot safe).trans (frame slot safe.2.1 safe.2.2.1 safe.2.2.2.1)
  · have joined := append_length_le builderRun skipRun
    change (builderRun.append skipRun).trace.length≤_
    unfold phaseWork
    omega

end B23_4_RatWordPrep.Lookup.Count
