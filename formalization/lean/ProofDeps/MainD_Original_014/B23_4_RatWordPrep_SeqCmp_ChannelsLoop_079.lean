module

public import B23_4_RatWordPrep_SeqCmp_ChannelsCalls_078

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Channels

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

def fields (values : List Rat) : List Bool := values.flatMap (fun x => encodeDatum (.rational x))
def archived (values : List Rat) (tail : List Bool) : List Bool :=
  values.foldl (fun cells x => RatInput.Encoder.packet x cells) tail

def LoopFrame (slot : RatInput.Stack) : Prop :=
  slot≠0 ∧ slot≠1 ∧ slot≠2 ∧ slot≠4 ∧ slot≠10 ∧ slot≠11 ∧ slot≠15

/-- The induction only describes the original stream. Runtime branch
selection comes from the real counter, with one positive round per field
and one final zero probe. No path/count/width/fuel is supplied to source. -/
theorem actual_loop (caller : Statement C) (values : List Rat) (before : State C)
    (digits : List Bool) (suffix : List Bool)
    (active : before.l=some (.round 0))
    (counter : before.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits)
    (left : before.stk 11=[false]) (scratch : before.stk 4=[])
    (count : PSTRTMIncrement009.valueDigits digits=values.length)
    (stream : ListBlank.mk (before.stk 0)=ListBlank.mk (fields values++suffix++[true])) :
    ∃ (final : State C) (_run : Segment caller before final) (finalDigits : List Bool),
      final.l=some .done ∧ final.var.2=before.var.2 ∧
      final.stk 15=before.stk 15 ∧ final.stk 2=archived values (before.stk 2) ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk (suffix++[true]) ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet finalDigits ∧
      PSTRTMIncrement009.valueDigits finalDigits=0 ∧ finalDigits.length=digits.length ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      ∀ slot,LoopFrame slot→final.stk slot=before.stk slot := by
  induction values generalizing before digits with
  | nil =>
    obtain ⟨final,run,port,context,rightFinal,leftFinal,scratchFinal,frame,_time⟩ :=
      actual_round caller before digits active counter left scratch
    have zero : PSTRTMIncrement009.valueDigits digits=0 := count
    refine ⟨final,run,RootB234.RuntimeCounter.Round.Raw.outputDigits digits,?_,context,?_,?_,?_,rightFinal,?_,?_,leftFinal,scratchFinal,?_⟩
    · simpa only [zero,ite_true] using port
    · exact frame 15 (by decide) (by decide) (by decide)
    · exact frame 2 (by decide) (by decide) (by decide)
    · rw [frame 0 (by decide) (by decide) (by decide)]
      simpa only [fields,List.flatMap_nil,List.nil_append] using stream
    · rw [RootB234.RuntimeCounter.Round.output_value,zero,Nat.zero_sub]
    · exact RootB234.RuntimeCounter.Round.output_width digits
    · intro slot safe
      exact frame slot safe.2.2.2.1 safe.2.2.2.2.1 safe.2.2.2.2.2.1
  | cons x later ih =>
    obtain ⟨readState,roundRun,port,roundContext,rightRound,leftRound,scratchRound,roundFrame,_roundTime⟩ :=
      actual_round caller before digits active counter left scratch
    have positive : PSTRTMIncrement009.valueDigits digits≠0 := by
      simp only [List.length_cons] at count
      omega
    have atRead : readState.l=some (.read .boot) := by simpa only [positive,ite_false] using port
    have readStream : ListBlank.mk (readState.stk 0)=
        ListBlank.mk (encodeDatum (.rational x)++(fields later++suffix)++[true]) := by
      rw [roundFrame 0 (by decide) (by decide) (by decide)]
      simpa only [fields,List.flatMap_cons,List.append_assoc] using stream
    obtain ⟨moveState,readRun,atMove,readContext,packet,readCursor,readFrame,_readTime⟩ :=
      actual_read caller readState x (fields later++suffix) atRead readStream
    have moveScratch : moveState.stk 4=[] :=
      (readFrame 4 (by decide) (by decide) (by decide)).trans scratchRound
    obtain ⟨next,moveRun,atNext,moveContext,restored,stored,scratchNext,moveFrame,_moveTime⟩ :=
      actual_move caller moveState x (readState.stk 15) atMove packet moveScratch
    let nextDigits := RootB234.RuntimeCounter.Round.Raw.outputDigits digits
    have nextCounter : next.stk 10=RootB234.RuntimeCounter.Round.Raw.packet nextDigits := by
      rw [moveFrame 10 (by decide) (by decide) (by decide),
        readFrame 10 (by decide) (by decide) (by decide)]
      exact rightRound
    have nextLeft : next.stk 11=[false] := by
      rw [moveFrame 11 (by decide) (by decide) (by decide),
        readFrame 11 (by decide) (by decide) (by decide)]
      exact leftRound
    have nextCount : PSTRTMIncrement009.valueDigits nextDigits=later.length := by
      rw [RootB234.RuntimeCounter.Round.output_value,count,List.length_cons,Nat.add_sub_cancel]
    have nextStream : ListBlank.mk (next.stk 0)=ListBlank.mk (fields later++suffix++[true]) := by
      rw [moveFrame 0 (by decide) (by decide) (by decide)]
      exact readCursor
    obtain ⟨final,tailRun,finalDigits,atDone,tailContext,tailPacket,tailTable,tailCursor,
      tailCounter,tailZero,tailWidth,tailLeft,tailScratch,tailFrame⟩ :=
      ih next nextDigits atNext nextCounter nextLeft scratchNext nextCount nextStream
    let whole := ((roundRun.append readRun).append moveRun).append tailRun
    refine ⟨final,whole,finalDigits,atDone,?_,?_,?_,tailCursor,tailCounter,tailZero,?_,tailLeft,tailScratch,?_⟩
    · exact tailContext.trans (moveContext.trans (readContext.trans roundContext))
    · exact tailPacket.trans (restored.trans (roundFrame 15 (by decide) (by decide) (by decide)))
    · rw [tailTable,stored,readFrame 2 (by decide) (by decide) (by decide),
        roundFrame 2 (by decide) (by decide) (by decide)]
      rfl
    · exact tailWidth.trans (RootB234.RuntimeCounter.Round.output_width digits)
    · intro slot safe
      exact (tailFrame slot safe).trans
        ((moveFrame slot safe.2.2.1 safe.2.2.2.1 safe.2.2.2.2.2.2).trans
          ((readFrame slot safe.1 safe.2.1 safe.2.2.2.2.2.2).trans
            (roundFrame slot safe.2.2.2.1 safe.2.2.2.2.1 safe.2.2.2.2.2.1)))

end B23_4_RatWordPrep.Channels
