module

public import B23_4_RatWordPrep_SeqCmp_LookupCountCalls_173
public import B23_4_RatWordPrep_SeqCmp_LookupCounters_094
public import B23_4_RatWordPrep_SeqCmp_PacketLists_090

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

def moveWork (values : List Rat) : Nat := (values.map (fun x => 3*RatInput.Encoder.fieldSize x+14)).sum
def skipWork (values : List Rat) (mass : Nat) : Nat := 256*(values.length+1)*(mass+1)+moveWork values

theorem actual_skip (truth stageN : Bool) (caller : Statement C) (values : List Rat)
    (before : State C) (digits tail : List Bool)
    (active : before.l=some (skipRound stageN 0))
    (counter : before.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits)
    (left : before.stk 11=[false]) (scratch : before.stk 4=[])
    (count : PSTRTMIncrement009.valueDigits digits=values.length)
    (table : before.stk 2=PacketLists.rats values tail) :
    ∃ (final : State C) (run : Segment truth caller before final) (finalDigits : List Bool),
      final.l=some (skipRound stageN 7) ∧ final.var.2.2=before.var.2.2 ∧ final.stk 2=tail ∧
      final.stk 15=PacketLists.rats values.reverse (before.stk 15) ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet finalDigits ∧
      PSTRTMIncrement009.valueDigits finalDigits=0 ∧ finalDigits.length=digits.length ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      (∀ slot,SkipFrame slot→final.stk slot=before.stk slot) ∧
      RatInput.occupied final.stk=RatInput.occupied before.stk ∧
      run.trace.length≤skipWork values (RatInput.occupied before.stk) := by
  induction values generalizing before digits with
  | nil =>
    obtain ⟨final,run,port,context,contents,time,mass⟩ := actual_round truth caller (skipRound stageN)
      before digits active counter left scratch (skipRound_body truth stageN caller)
    have zero : PSTRTMIncrement009.valueDigits digits=0 := count
    have frame (slot : RatInput.Stack) (n4 : slot≠4) (n10 : slot≠10) (n11 : slot≠11) :
        final.stk slot=before.stk slot := by
      rw [contents]
      exact RootB234.RuntimeCounter.Round.cells_frame _ _ _ _ slot
        (by simp only [RootB234.RuntimeCounter.Round.Work,n4,n10,n11,or_self,not_false_eq_true])
    refine ⟨final,run,RootB234.RuntimeCounter.Round.Raw.outputDigits digits,?_,context,?_,?_,?_,?_,?_,?_,?_,?_,mass,by simpa only [skipWork,moveWork,List.length_nil,List.map_nil,List.sum_nil,Nat.zero_add,Nat.mul_one,Nat.add_zero] using time⟩
    · simpa only [zero,ite_true] using port
    · exact (frame 2 (by decide) (by decide) (by decide)).trans table
    · exact frame 15 (by decide) (by decide) (by decide)
    · rw [contents]; rfl
    · rw [RootB234.RuntimeCounter.Round.output_value,zero,Nat.zero_sub]
    · exact RootB234.RuntimeCounter.Round.output_width digits
    · rw [contents]; rfl
    · rw [contents]; rfl
    · intro slot safe
      exact frame slot safe.2.1 safe.2.2.1 safe.2.2.2.1
  | cons x values ih =>
    obtain ⟨middle,roundRun,port,roundContext,roundContents,roundTime,roundMass⟩ := actual_round truth caller
      (skipRound stageN) before digits active counter left scratch (skipRound_body truth stageN caller)
    have positive : PSTRTMIncrement009.valueDigits digits≠0 := by
      simp only [List.length_cons] at count
      omega
    have frameRound (slot : RatInput.Stack) (n4 : slot≠4) (n10 : slot≠10) (n11 : slot≠11) :
        middle.stk slot=before.stk slot := by
      rw [roundContents]
      exact RootB234.RuntimeCounter.Round.cells_frame _ _ _ _ slot
        (by simp only [RootB234.RuntimeCounter.Round.Work,n4,n10,n11,or_self,not_false_eq_true])
    have atMove : middle.l=some (skipMove stageN 0) := by
      rw [port]
      simp only [positive,ite_false]
      cases stageN <;> rfl
    have source : middle.stk (missRoles 15)=RatInput.Encoder.packet x (PacketLists.rats values tail) := by
      change middle.stk 2=_
      rw [frameRound 2 (by decide) (by decide) (by decide)]
      exact table
    have temp : middle.stk (missRoles 4)=[] := by rw [roundContents]; rfl
    obtain ⟨next,moveRun,movePort,moveContext,moveContents,moveTime,moveMass⟩ :=
      actual_move truth caller (skipMove stageN) missRoles middle x (PacketLists.rats values tail)
        atMove source temp (skipMove_body truth stageN caller)
    have nextActive : next.l=some (skipRound stageN 0) := by
      rw [movePort]
      cases stageN <;> rfl
    have frameMove (slot : RatInput.Stack) (n2 : slot≠2) (n4 : slot≠4) (n15 : slot≠15) :
        next.stk slot=middle.stk slot := by
      rw [moveContents]
      change (if slot=2 then _ else if slot=4 then _ else if slot=15 then _ else middle.stk slot)=_
      simp only [n2,n4,n15,ite_false]
    let nextDigits := RootB234.RuntimeCounter.Round.Raw.outputDigits digits
    have nextCounter : next.stk 10=RootB234.RuntimeCounter.Round.Raw.packet nextDigits := by
      rw [frameMove 10 (by decide) (by decide) (by decide),roundContents]; rfl
    have nextLeft : next.stk 11=[false] := by
      rw [frameMove 11 (by decide) (by decide) (by decide),roundContents]; rfl
    have nextScratch : next.stk 4=[] := by rw [moveContents]; rfl
    have nextCount : PSTRTMIncrement009.valueDigits nextDigits=values.length := by
      rw [RootB234.RuntimeCounter.Round.output_value,count,List.length_cons,Nat.add_sub_cancel]
    have nextTable : next.stk 2=PacketLists.rats values tail := by rw [moveContents]; rfl
    have nextArchive : next.stk 15=RatInput.Encoder.packet x (before.stk 15) := by
      rw [moveContents]
      change RatInput.Encoder.packet x (middle.stk 15)=_
      rw [frameRound 15 (by decide) (by decide) (by decide)]
    obtain ⟨final,tailRun,finalDigits,finalPort,tailContext,finalTable,finalArchive,finalCounter,
      zero,width,finalLeft,finalScratch,finalFrame,tailMass,tailTime⟩ :=
      ih next nextDigits nextActive nextCounter nextLeft nextScratch nextCount nextTable
    let whole := (roundRun.append moveRun).append tailRun
    refine ⟨final,whole,finalDigits,finalPort,tailContext.trans (moveContext.trans roundContext),finalTable,
      ?_,finalCounter,zero,width.trans (RootB234.RuntimeCounter.Round.output_width digits),finalLeft,finalScratch,?_,tailMass.trans (moveMass.trans roundMass),?_⟩
    · rw [finalArchive,nextArchive,List.reverse_cons,PacketLists.rats_append]
      rfl
    · intro slot safe
      exact (finalFrame slot safe).trans ((frameMove slot safe.1 safe.2.1 safe.2.2.2.2).trans
        (frameRound slot safe.2.1 safe.2.2.1 safe.2.2.2.1))
    · have nextMass : RatInput.occupied next.stk=RatInput.occupied before.stk := moveMass.trans roundMass
      rw [nextMass] at tailTime
      have j2 := append_length_le roundRun moveRun
      have j3 := append_length_le (roundRun.append moveRun) tailRun
      change ((roundRun.append moveRun).append tailRun).trace.length≤_
      simp only [skipWork,moveWork,List.length_cons,List.map_cons,List.sum_cons] at tailTime ⊢
      nlinarith

end B23_4_RatWordPrep.Lookup.Count
