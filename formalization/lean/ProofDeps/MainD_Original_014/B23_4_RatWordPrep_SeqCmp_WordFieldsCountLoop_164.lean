module

public import B23_4_RatWordPrep_SeqCmp_WordFieldsCountCalls_163
public import B23_4_RatWordPrep_SeqCmp_WordFieldsLoop_087

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFields.Count

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

def readWork (values : List Nat) : Nat := (values.map RawNat.time).sum
def moveWork (values : List Nat) : Nat := (values.map (fun x => 3*(PSTRTMNatValue017.rawPayload x).length+6)).sum
def loopBudget (values : List Nat) (allowance : Nat) : Nat :=
  256*(values.length+1)*(allowance+1)+readWork values+moveWork values

/-- Actual original word-symbol loop with a linear physical mass potential.
Each getter contributes only its field-local count; counter rounds and
packet moves preserve mass. The same witness retains all old ABI facts. -/
theorem actual_loop (caller : Statement C) (values : List Nat) (before : State C)
    (digits : List Bool) (suffix : List Bool) (allowance : Nat)
    (active : before.l=some (.round 0))
    (counter : before.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits)
    (left : before.stk 11=[false]) (scratch : before.stk 4=[])
    (count : PSTRTMIncrement009.valueDigits digits=values.length)
    (stream : ListBlank.mk (before.stk 0)=ListBlank.mk (fields values++suffix++[true]))
    (potential : RatInput.occupied before.stk+pushCap caller*readWork values≤allowance) :
    ∃ (final : State C) (run : Segment caller before final) (finalDigits : List Bool),
      final.l=some .done ∧ final.var.2.2=before.var.2.2 ∧
      final.stk 15=before.stk 15 ∧ final.stk 3=archived values (before.stk 3) ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk (suffix++[true]) ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet finalDigits ∧
      PSTRTMIncrement009.valueDigits finalDigits=0 ∧ finalDigits.length=digits.length ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      (∀ slot,LoopFrame slot → final.stk slot=before.stk slot) ∧
      RatInput.occupied final.stk≤allowance ∧ run.trace.length≤loopBudget values allowance := by
  induction values generalizing before digits with
  | nil =>
    obtain ⟨final,run,port,context,rightFinal,leftFinal,scratchFinal,frame,time,mass⟩ :=
      actual_round caller before digits active counter left scratch
    have zero : PSTRTMIncrement009.valueDigits digits=0 := count
    have room : RatInput.occupied before.stk≤allowance := by
      simpa only [readWork,List.map_nil,List.sum_nil,Nat.mul_zero,Nat.add_zero] using potential
    refine ⟨final,run,RootB234.RuntimeCounter.Round.Raw.outputDigits digits,?_,context,?_,?_,?_,rightFinal,?_,?_,leftFinal,scratchFinal,?_,mass.trans_le room,?_⟩
    · simpa only [zero,ite_true] using port
    · exact frame 15 (by decide) (by decide) (by decide)
    · exact frame 3 (by decide) (by decide) (by decide)
    · rw [frame 0 (by decide) (by decide) (by decide)]
      simpa only [fields,List.flatMap_nil,List.nil_append] using stream
    · rw [RootB234.RuntimeCounter.Round.output_value,zero,Nat.zero_sub]
    · exact RootB234.RuntimeCounter.Round.output_width digits
    · intro slot safe
      exact frame slot safe.2.2.2.1 safe.2.2.2.2.1 safe.2.2.2.2.2.1
    · change run.trace.length≤256*(allowance+1)
      exact time.trans (Nat.mul_le_mul_left 256 (Nat.add_le_add_right room 1))
  | cons x later ih =>
    obtain ⟨readState,roundRun,port,roundContext,rightRound,leftRound,scratchRound,roundFrame,roundTime,roundMass⟩ :=
      actual_round caller before digits active counter left scratch
    have positive : PSTRTMIncrement009.valueDigits digits≠0 := by
      simp only [List.length_cons] at count
      omega
    have atRead : readState.l=some (.symbol .boot) := by simpa only [positive,ite_false] using port
    have readStream : ListBlank.mk (readState.stk 0)=
        ListBlank.mk (encodeDatum (.natural x)++(fields later++suffix)++[true]) := by
      rw [roundFrame 0 (by decide) (by decide) (by decide)]
      simpa only [fields,List.flatMap_cons,List.append_assoc] using stream
    obtain ⟨moveState,readRun,atMove,readContext,packet,readCursor,readFrame,readTime,readMass⟩ :=
      actual_natural true caller readState x (fields later++suffix) atRead readStream
    have moveScratch : moveState.stk 4=[] :=
      (readFrame 4 (by decide) (by decide) (by decide)).trans scratchRound
    obtain ⟨next,moveRun,atNext,moveContext,restored,stored,scratchNext,moveFrame,moveTime,moveMass⟩ :=
      actual_natural_move true caller moveState x (readState.stk 15) atMove packet moveScratch
    let nextDigits := RootB234.RuntimeCounter.Round.Raw.outputDigits digits
    have nextCounter : next.stk 10=RootB234.RuntimeCounter.Round.Raw.packet nextDigits := by
      rw [moveFrame 10 (by decide) (by decide) (by decide),readFrame 10 (by decide) (by decide) (by decide)]
      exact rightRound
    have nextLeft : next.stk 11=[false] := by
      rw [moveFrame 11 (by decide) (by decide) (by decide),readFrame 11 (by decide) (by decide) (by decide)]
      exact leftRound
    have nextCount : PSTRTMIncrement009.valueDigits nextDigits=later.length := by
      rw [RootB234.RuntimeCounter.Round.output_value,count,List.length_cons,Nat.add_sub_cancel]
    have nextStream : ListBlank.mk (next.stk 0)=ListBlank.mk (fields later++suffix++[true]) := by
      rw [moveFrame 0 (by decide) (by decide) (by decide)]
      exact readCursor
    have nextPotential : RatInput.occupied next.stk+pushCap caller*readWork later≤allowance := by
      rw [moveMass]
      rw [roundMass] at readMass
      have original : RatInput.occupied before.stk+pushCap caller*RawNat.time x+pushCap caller*readWork later≤allowance := by
        simpa only [readWork,List.map_cons,List.sum_cons,Nat.mul_add,Nat.add_assoc] using potential
      omega
    obtain ⟨final,tailRun,finalDigits,atDone,tailContext,tailPacket,tailTable,tailCursor,
      tailCounter,tailZero,tailWidth,tailLeft,tailScratch,tailFrame,tailMass,tailTime⟩ :=
      ih next nextDigits atNext nextCounter nextLeft scratchNext nextCount nextStream nextPotential
    let whole := ((roundRun.append readRun).append moveRun).append tailRun
    refine ⟨final,whole,finalDigits,atDone,?_,?_,?_,tailCursor,tailCounter,tailZero,?_,tailLeft,tailScratch,?_,tailMass,?_⟩
    · exact tailContext.trans (moveContext.trans ((congrArg (fun memory : Channels.Store C => memory.2) readContext).trans roundContext))
    · exact tailPacket.trans (restored.trans (roundFrame 15 (by decide) (by decide) (by decide)))
    · rw [tailTable,stored,readFrame 3 (by decide) (by decide) (by decide),roundFrame 3 (by decide) (by decide) (by decide)]
      rfl
    · exact tailWidth.trans (RootB234.RuntimeCounter.Round.output_width digits)
    · intro slot safe
      exact (tailFrame slot safe).trans
        ((moveFrame slot safe.2.2.1 safe.2.2.2.1 safe.2.2.2.2.2.2).trans
          ((readFrame slot safe.1 safe.2.1 safe.2.2.2.2.2.2).trans
            (roundFrame slot safe.2.2.2.1 safe.2.2.2.2.1 safe.2.2.2.2.2.1)))
    · have room : RatInput.occupied before.stk≤allowance := by omega
      have boundedRound := roundTime.trans (Nat.mul_le_mul_left 256 (Nat.add_le_add_right room 1))
      have a := append_length_le roundRun readRun
      have b := append_length_le (roundRun.append readRun) moveRun
      have c := append_length_le ((roundRun.append readRun).append moveRun) tailRun
      have budgetStep : loopBudget (x::later) allowance=
          256*(allowance+1)+RawNat.time x+(3*(PSTRTMNatValue017.rawPayload x).length+6)+loopBudget later allowance := by
        simp only [loopBudget,readWork,moveWork,List.length_cons,List.map_cons,List.sum_cons]
        ring
      change (((roundRun.append readRun).append moveRun).append tailRun).trace.length≤_
      rw [budgetStep]
      omega

end B23_4_RatWordPrep.WordFields.Count
