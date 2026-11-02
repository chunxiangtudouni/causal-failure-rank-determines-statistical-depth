module

public import RootB234_PrepEntry_StageChannelsCalls_059

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

def loopRoles (right : Bool) : RatInput.Stack ≃ RatInput.Stack := if right then rightRoles else leftRoles
def loopCfg (right : Bool) : Channels.State (StageFront.Store C) → State C := if right then rightCfg else leftCfg
def archiveSlot (right : Bool) : RatInput.Stack := if right then 6 else 2
def afterLoop (right : Bool) : Label := if right then .done else .buildRight 0

theorem loop_path (right : Bool) (caller : Statement C) (run : List (Channels.State (StageFront.Store C)))
    (before final : Channels.State (StageFront.Store C)) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (Channels.program .halt) a=some b))
    (last : run.getLast?=some final) (active : before.l=some (.round 0)) (done : final.l=some .done) :
    (run.map (loopCfg right)).head?=some (loopCfg right before) ∧
    (run.map (loopCfg right)).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map (loopCfg right)).getLast?=some (loopCfg right final) := by
  cases right
  · exact left_path caller run before final first chain last active done
  · exact right_path caller run before final first chain last active done

def loopEntry (right : Bool) (before : State C) : Channels.State (StageFront.Store C) :=
  ⟨some (.round 0),(channelIso C).symm before.var,StackIso.slots (loopRoles right).symm before.stk⟩

theorem loop_shared (right : Bool) (before : State C) (active : before.l=some (roundPoint right)) :
    loopCfg right (loopEntry right before)=before := by
  cases before with
  | mk point memory bank =>
    change point=some (roundPoint right) at active
    subst point
    cases right <;> change (⟨some _,channelIso C ((channelIso C).symm memory),
      StackIso.slots _ (StackIso.slots _ bank)⟩ : State C)=_
    all_goals
      rw [Equiv.apply_symm_apply]
      congr 1
      funext slot
      fin_cases slot <;> rfl

def LoopFrame (right : Bool) (slot : RatInput.Stack) : Prop :=
  slot≠0 ∧ slot≠1 ∧ slot≠archiveSlot right ∧ slot≠4 ∧ slot≠10 ∧ slot≠11 ∧ slot≠15

/-- A static transport of the SAME frozen channel trace. The original
counter performs each real borrow/zero probe; the actual getter advances
the original stream and its packet mover restores the old15 tail. -/
theorem actual_loop (right : Bool) (caller : Statement C) (before : State C)
    (values : List Rat) (digits : List Bool) (suffix : List Bool)
    (active : before.l=some (roundPoint right))
    (counter : before.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits)
    (left : before.stk 11=[false]) (scratch : before.stk 4=[])
    (count : PSTRTMIncrement009.valueDigits digits=values.length)
    (stream : ListBlank.mk (before.stk 0)=ListBlank.mk (Channels.fields values++suffix++[true])) :
    ∃ (final : State C) (_run : Segment caller before final) (finalDigits : List Bool),
      final.l=some (afterLoop right) ∧ final.var.2=before.var.2 ∧
      final.stk 15=before.stk 15 ∧
      final.stk (archiveSlot right)=Channels.archived values (before.stk (archiveSlot right)) ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk (suffix++[true]) ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet finalDigits ∧
      PSTRTMIncrement009.valueDigits finalDigits=0 ∧ finalDigits.length=digits.length ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      ∀ slot,LoopFrame right slot→final.stk slot=before.stk slot := by
  let oldBefore:=loopEntry right before
  have oldCounter : oldBefore.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits := by
    cases right <;> exact counter
  have oldLeft : oldBefore.stk 11=[false] := by cases right <;> exact left
  have oldScratch : oldBefore.stk 4=[] := by cases right <;> exact scratch
  have oldStream : ListBlank.mk (oldBefore.stk 0)=ListBlank.mk (Channels.fields values++suffix++[true]) := by
    cases right <;> exact stream
  obtain ⟨oldFinal,oldRun,finalDigits,done,context,packet,stored,cursor,outCounter,zero,width,outLeft,outScratch,frame⟩:=
    Channels.actual_loop (.halt : Channels.Statement (StageFront.Store C)) values oldBefore digits suffix
      rfl oldCounter oldLeft oldScratch count oldStream
  have path:=loop_path right caller oldRun.trace oldBefore oldFinal oldRun.first oldRun.chain oldRun.last rfl done
  let run : Segment caller before (loopCfg right oldFinal):=
    ⟨oldRun.trace.map (loopCfg right),path.1.trans (congrArg some (loop_shared right before active)),path.2.1,path.2.2⟩
  refine ⟨loopCfg right oldFinal,run,finalDigits,?_,?_,?_,?_,?_,?_,zero,width,?_,?_,?_⟩
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

end RootB234.PrepEntry.StageChannels
