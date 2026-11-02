module

public import RootB234_PrepEntry_StageChannelsLoopBounds_063

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageChannels

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C : Type*}

theorem actual_loop_bounded (right : Bool) (caller : Statement C) (before : State C)
    (values : List Rat) (digits : List Bool) (suffix : List Bool) (bound : Nat)
    (active : before.l=some (roundPoint right))
    (counter : before.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits)
    (left : before.stk 11=[false]) (scratch : before.stk 4=[])
    (count : PSTRTMIncrement009.valueDigits digits=values.length)
    (stream : ListBlank.mk (before.stk 0)=ListBlank.mk (Channels.fields values++suffix++[true]))
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    ∃ (final : State C) (run : Segment caller before final) (finalDigits : List Bool),
      final.l=some (afterLoop right) ∧ final.var.2=before.var.2 ∧
      final.stk 15=before.stk 15 ∧
      final.stk (archiveSlot right)=Channels.archived values (before.stk (archiveSlot right)) ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk (suffix++[true]) ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet finalDigits ∧
      PSTRTMIncrement009.valueDigits finalDigits=0 ∧ finalDigits.length=digits.length ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      (∀ slot,LoopFrame right slot→final.stk slot=before.stk slot) ∧
      (∀ slot,(final.stk slot).length≤bound+Bounds.credits values) ∧ run.trace.length≤Bounds.limit values bound := by
  let oldBefore:=loopEntry right before
  have oldCounter : oldBefore.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits := by
    cases right <;> exact counter
  have oldLeft : oldBefore.stk 11=[false] := by cases right <;> exact left
  have oldScratch : oldBefore.stk 4=[] := by cases right <;> exact scratch
  have oldStream : ListBlank.mk (oldBefore.stk 0)=ListBlank.mk (Channels.fields values++suffix++[true]) := by
    cases right <;> exact stream
  have oldBound : ∀ slot,(oldBefore.stk slot).length≤bound := by
    intro slot
    change (before.stk ((loopRoles right) slot)).length≤bound
    exact bounded _
  obtain ⟨oldFinal,oldRun,finalDigits,done,context,packet,stored,cursor,outCounter,zero,width,outLeft,outScratch,frame,finalBound,time⟩:=
    Bounds.actual_old_loop (.halt : Channels.Statement (StageFront.Store C)) values oldBefore digits suffix bound
      rfl oldCounter oldLeft oldScratch count oldStream oldBound
  have path:=loop_path right caller oldRun.trace oldBefore oldFinal oldRun.first oldRun.chain oldRun.last rfl done
  let run : Segment caller before (loopCfg right oldFinal):=
    ⟨oldRun.trace.map (loopCfg right),path.1.trans (congrArg some (loop_shared right before active)),path.2.1,path.2.2⟩
  refine ⟨loopCfg right oldFinal,run,finalDigits,?_,?_,?_,?_,?_,?_,zero,width,?_,?_,?_,?_,?_⟩
  · cases right <;> change oldFinal.l.map _=some _ <;> rw [done] <;> rfl
  · cases right <;> exact congrArg OriginalPrelude.callerContext context
  · cases right <;> exact packet
  · cases right <;> exact stored
  · cases right <;> exact cursor
  · cases right <;> exact outCounter
  · cases right <;> exact outLeft
  · cases right <;> exact outScratch
  · intro slot safe
    have oldSafe : Channels.LoopFrame ((loopRoles right).symm slot) := by
      cases right <;> fin_cases slot <;>
        simp_all [Channels.LoopFrame,LoopFrame,archiveSlot,loopRoles,leftRoles,rightRoles,Equiv.swap_apply_def]
    have same:=frame _ oldSafe
    cases right <;> fin_cases slot <;> exact same

  · intro slot
    cases right
    · exact finalBound (leftRoles.symm slot)
    · exact finalBound (rightRoles.symm slot)
  · simpa only [run,List.length_map] using time

end RootB234.PrepEntry.StageChannels
