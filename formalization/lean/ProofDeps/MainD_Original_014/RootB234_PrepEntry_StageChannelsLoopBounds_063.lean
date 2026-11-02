module

public import RootB234_PrepEntry_StageChannelsCallBounds_062

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageChannels.Bounds

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C : Type*}

theorem limit_cons (x : Rat) (later : List Rat) (bound : Nat) :
    4096*bound+256+RawGetter.time x+(3*RatInput.Encoder.fieldSize x+14)+
      limit later (bound+credit x)≤limit (x::later) bound := by
  simp only [limit,credits_cons,List.length_cons,credit]
  nlinarith only [Nat.zero_le (RawGetter.time x),Nat.zero_le (RatInput.Encoder.fieldSize x),Nat.zero_le (credits later)]

/-- Strengthens the frozen079 proof with additive endpoint credit and a
time bound. It executes exactly079's round/read/move source; the list is
used only to prove the real counter consumes the original fields. -/
theorem actual_old_loop (caller : Channels.Statement C) (values : List Rat) (before : Channels.State C)
    (digits : List Bool) (suffix : List Bool) (bound : Nat)
    (active : before.l=some (.round 0))
    (counter : before.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits)
    (left : before.stk 11=[false]) (scratch : before.stk 4=[])
    (count : PSTRTMIncrement009.valueDigits digits=values.length)
    (stream : ListBlank.mk (before.stk 0)=ListBlank.mk (Channels.fields values++suffix++[true]))
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    ∃ (final : Channels.State C) (run : Channels.Segment caller before final) (finalDigits : List Bool),
      final.l=some .done ∧ final.var.2=before.var.2 ∧
      final.stk 15=before.stk 15 ∧ final.stk 2=Channels.archived values (before.stk 2) ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk (suffix++[true]) ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet finalDigits ∧
      PSTRTMIncrement009.valueDigits finalDigits=0 ∧ finalDigits.length=digits.length ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      (∀ slot,Channels.LoopFrame slot→final.stk slot=before.stk slot) ∧
      (∀ slot,(final.stk slot).length≤bound+credits values) ∧ run.trace.length≤limit values bound := by
  induction values generalizing before digits bound with
  | nil =>
    obtain ⟨final,run,port,context,rightFinal,leftFinal,scratchFinal,frame,time⟩:=
      Channels.actual_round caller before digits active counter left scratch
    have zero : PSTRTMIncrement009.valueDigits digits=0 := count
    refine ⟨final,run,RootB234.RuntimeCounter.Round.Raw.outputDigits digits,?_,context,?_,?_,?_,rightFinal,?_,?_,
      leftFinal,scratchFinal,?_,?_,?_⟩
    · simpa only [zero,ite_true] using port
    · exact frame 15 (by decide) (by decide) (by decide)
    · exact frame 2 (by decide) (by decide) (by decide)
    · rw [frame 0 (by decide) (by decide) (by decide)]
      simpa only [Channels.fields,List.flatMap_nil,List.nil_append] using stream
    · rw [RootB234.RuntimeCounter.Round.output_value,zero,Nat.zero_sub]
    · exact RootB234.RuntimeCounter.Round.output_width digits
    · intro slot safe
      exact frame slot safe.2.2.2.1 safe.2.2.2.2.1 safe.2.2.2.2.2.1
    · simpa only [credits_nil,Nat.add_zero] using
        round_bound before final digits bound counter left rightFinal leftFinal scratchFinal frame bounded
    · have scale:=round_scale before digits bound counter left scratch bounded
      dsimp only [limit,credits_nil,List.length_nil]
      nlinarith only [time,scale]
  | cons x later ih =>
    obtain ⟨readState,roundRun,port,roundContext,rightRound,leftRound,scratchRound,roundFrame,roundTime⟩:=
      Channels.actual_round caller before digits active counter left scratch
    have positive : PSTRTMIncrement009.valueDigits digits≠0 := by
      simp only [List.length_cons] at count
      omega
    have atRead : readState.l=some (.read .boot) := by simpa only [positive,ite_false] using port
    have readStream : ListBlank.mk (readState.stk 0)=
        ListBlank.mk (encodeDatum (.rational x)++(Channels.fields later++suffix)++[true]) := by
      rw [roundFrame 0 (by decide) (by decide) (by decide)]
      simpa only [Channels.fields,List.flatMap_cons,List.append_assoc] using stream
    have roundBound:=round_bound before readState digits bound counter left rightRound leftRound scratchRound roundFrame bounded
    obtain ⟨moveState,readRun,atMove,readContext,packet,readCursor,readFrame,readTime,readBound⟩:=
      actual_read caller readState x (Channels.fields later++suffix) bound atRead readStream roundBound
    have moveScratch : moveState.stk 4=[] := (readFrame 4 (by decide) (by decide) (by decide)).trans scratchRound
    obtain ⟨next,moveRun,atNext,moveContext,restored,stored,scratchNext,moveFrame,moveTime⟩:=
      Channels.actual_move caller moveState x (readState.stk 15) atMove packet moveScratch
    let nextDigits:=RootB234.RuntimeCounter.Round.Raw.outputDigits digits
    have nextCounter : next.stk 10=RootB234.RuntimeCounter.Round.Raw.packet nextDigits := by
      rw [moveFrame 10 (by decide) (by decide) (by decide),readFrame 10 (by decide) (by decide) (by decide)]
      exact rightRound
    have nextLeft : next.stk 11=[false] := by
      rw [moveFrame 11 (by decide) (by decide) (by decide),readFrame 11 (by decide) (by decide) (by decide)]
      exact leftRound
    have nextCount : PSTRTMIncrement009.valueDigits nextDigits=later.length := by
      rw [RootB234.RuntimeCounter.Round.output_value,count,List.length_cons,Nat.add_sub_cancel]
    have nextStream : ListBlank.mk (next.stk 0)=ListBlank.mk (Channels.fields later++suffix++[true]) := by
      rw [moveFrame 0 (by decide) (by decide) (by decide)]
      exact readCursor
    have nextBound : ∀ slot,(next.stk slot).length≤bound+credit x := by
      have moveBound:=move_bound moveState next x (readState.stk 15) _ packet restored stored scratchNext moveFrame readBound
      intro slot
      have one:=moveBound slot
      dsimp only [credit]
      omega
    obtain ⟨final,tailRun,finalDigits,atDone,tailContext,tailPacket,tailTable,tailCursor,
      tailCounter,tailZero,tailWidth,tailLeft,tailScratch,tailFrame,tailBound,tailTime⟩:=
      ih next nextDigits (bound+credit x) atNext nextCounter nextLeft scratchNext nextCount nextStream nextBound
    let whole:=((roundRun.append readRun).append moveRun).append tailRun
    refine ⟨final,whole,finalDigits,atDone,?_,?_,?_,tailCursor,tailCounter,tailZero,?_,tailLeft,tailScratch,?_,?_,?_⟩
    · exact tailContext.trans (moveContext.trans (readContext.trans roundContext))
    · exact tailPacket.trans (restored.trans (roundFrame 15 (by decide) (by decide) (by decide)))
    · rw [tailTable,stored,readFrame 2 (by decide) (by decide) (by decide),roundFrame 2 (by decide) (by decide) (by decide)]
      rfl
    · exact tailWidth.trans (RootB234.RuntimeCounter.Round.output_width digits)
    · intro slot safe
      exact (tailFrame slot safe).trans
        ((moveFrame slot safe.2.2.1 safe.2.2.2.1 safe.2.2.2.2.2.2).trans
          ((readFrame slot safe.1 safe.2.1 safe.2.2.2.2.2.2).trans
            (roundFrame slot safe.2.2.2.1 safe.2.2.2.2.1 safe.2.2.2.2.2.1)))
    · intro slot
      simpa only [credits_cons,Nat.add_assoc] using tailBound slot
    · have count1:=append_count roundRun readRun
      have count2:=append_count (roundRun.append readRun) moveRun
      have count3:=append_count ((roundRun.append readRun).append moveRun) tailRun
      have scale:=round_scale before digits bound counter left scratch bounded
      have roundCap : roundRun.trace.length≤4096*bound+256 := by nlinarith only [roundTime,scale]
      have sum : whole.trace.length≤4096*bound+256+RawGetter.time x+(3*RatInput.Encoder.fieldSize x+14)+limit later (bound+credit x) := by
        dsimp only [whole]
        omega
      exact sum.trans (limit_cons x later bound)

end RootB234.PrepEntry.StageChannels.Bounds
