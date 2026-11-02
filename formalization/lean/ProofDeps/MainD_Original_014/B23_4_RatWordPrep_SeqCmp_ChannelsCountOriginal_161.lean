module

public import B23_4_RatWordPrep_SeqCmp_ChannelsCountLoop_160
public import B23_4_RatWordPrep_SeqCmp_ChannelsOriginal_081

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Channels.Count

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

def preludeBudget (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Nat :=
  OriginalPrelude.coefficient*((wordInput E target word).length+1)^OriginalPrelude.degree
def buildWork (number : Nat) : Nat := 2*(PSTRTMNatValue017.rawPayload number).length+14
noncomputable def originalAllowance (caller : Statement C) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Nat :=
  preludeBudget E target word+pushCap caller*(buildWork E.alphabetSize+readWork (channelValues E))
noncomputable def originalBudget (caller : Statement C) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Nat :=
  preludeBudget E target word+buildWork E.alphabetSize+
    loopBudget (channelValues E) (originalAllowance caller E target word)

/-- Reuses the frozen original Prelude degree16 witness and adds only
actual builder/getter/counter/transport counts. The original complete
channel ABI is retained, with a linear cumulative mass potential. -/
theorem actual_original (caller : Statement C) (context : C)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ (final : State C) (run : Segment caller (entry context (wordInput E target word)) final)
      (finalDigits : List Bool),
      final.l=some .done ∧
      OriginalFee.context (OriginalPrelude.feeMemory final.var.2)=context ∧
      final.stk 8=NatField.packet E.alphabetSize [] ∧
      final.stk 15=RatInput.Encoder.packet E.observationFee
        (RatInput.Encoder.packet (1-E.priorOne) (RatInput.Encoder.packet E.priorOne [])) ∧
      final.stk 2=archived (channelValues E) [] ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk (afterChannels E target word++[true]) ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet finalDigits ∧
      PSTRTMIncrement009.valueDigits finalDigits=0 ∧
      finalDigits.length=(false::PSTRTMNatValue017.rawPayload E.alphabetSize).length ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧
      (final.stk 7=[] ∧ final.stk 3=[] ∧ final.stk 5=[] ∧ final.stk 6=[] ∧
        final.stk 9=[] ∧ final.stk 12=[] ∧ final.stk 13=[] ∧ final.stk 14=[]) ∧
      RatInput.occupied final.stk≤originalAllowance caller E target word ∧
      run.trace.length≤originalBudget caller E target word := by
  obtain ⟨preludeTrace,preludeFinal,_beforeRead,facts⟩ := OriginalPrelude.actual_polynomial context E target word
  have path := prelude_path caller default preludeTrace _ preludeFinal facts.first facts.chain facts.last facts.active
  let preludeState := preludeCfg default preludeFinal
  let front : Segment caller (entry context (wordInput E target word)) preludeState :=
    ⟨preludeTrace.map (preludeCfg default),path.1,path.2.1,path.2.2⟩
  have atBuild : preludeState.l=some (.build 0) := by
    change preludeFinal.l.map preludeLabel=_
    rw [facts.active]
    rfl
  have preludeMass : RatInput.occupied preludeState.stk≤preludeBudget E target word :=
    (facts.boundaries preludeFinal (List.mem_of_getLast? facts.last)).2.2.1
  have frontTime : front.trace.length≤preludeBudget E target word := by
    simpa only [front,List.length_map,preludeBudget] using facts.time
  obtain ⟨loopEntry,buildRun,atRound,buildContext,counter,left,scratch,buildFrame,buildTime⟩ :=
    actual_build caller preludeState E.alphabetSize [] atBuild facts.cache facts.owned.2.2.1
  have free10 : preludeState.stk 10=[] := facts.free 10 (by decide)
  have free11 : preludeState.stk 11=[] := facts.free 11 (by decide)
  have paidBuild : buildRun.trace.length≤buildWork E.alphabetSize := by
    rw [free10,free11] at buildTime
    simpa only [List.length_nil,Nat.zero_add,buildWork] using buildTime
  have buildMass := WordFinish.Resources.trace_mass (pushCap caller) (pushes caller)
    buildRun.trace preludeState (RatInput.occupied preludeState.stk) buildRun.first buildRun.chain
      (Nat.le_refl _) loopEntry (List.mem_of_getLast? buildRun.last)
  have loopMass : RatInput.occupied loopEntry.stk≤preludeBudget E target word+pushCap caller*buildWork E.alphabetSize :=
    buildMass.trans (Nat.add_le_add preludeMass (Nat.mul_le_mul_left _ paidBuild))
  have count : PSTRTMIncrement009.valueDigits (false::PSTRTMNatValue017.rawPayload E.alphabetSize)=(channelValues E).length :=
    (RootB234.RuntimeCounter.Round.Public.twice_value E.alphabetSize).trans (channel_count E).symm
  have stream : ListBlank.mk (loopEntry.stk 0)=
      ListBlank.mk (fields (channelValues E)++afterChannels E target word++[true]) := by
    rw [buildFrame 0 (by decide) (by decide) (by decide)]
    have rightTape := congrArg Tape.right₀ facts.cursor
    simp only [Tape.mk₂,Tape.mk'_right₀] at rightTape
    rw [afterFee_split] at rightTape
    exact rightTape
  have potential : RatInput.occupied loopEntry.stk+pushCap caller*readWork (channelValues E)≤originalAllowance caller E target word := by
    unfold originalAllowance
    nlinarith
  obtain ⟨final,loopRun,finalDigits,atDone,loopContext,priorPacket,table,cursor,
    finalCounter,zero,width,finalLeft,finalScratch,loopFrame,finalMass,loopTime⟩ :=
    actual_loop caller (channelValues E) loopEntry _ (afterChannels E target word)
      (originalAllowance caller E target word) atRound counter left scratch count stream potential
  let whole := (front.append buildRun).append loopRun
  have baseEq : final.var.2=preludeFinal.var := loopContext.trans buildContext
  have framed (slot : RatInput.Stack) (safe : LoopFrame slot) : final.stk slot=preludeFinal.stk slot :=
    (loopFrame slot safe).trans (buildFrame slot safe.2.2.2.1 safe.2.2.2.2.1 safe.2.2.2.2.2.1)
  refine ⟨final,whole,finalDigits,atDone,?_,?_,?_,?_,cursor,finalCounter,zero,width,finalLeft,finalScratch,?_,finalMass,?_⟩
  · exact (congrArg (fun memory => OriginalFee.context (OriginalPrelude.feeMemory memory)) baseEq).trans facts.context_eq
  · exact (framed 8 (by decide)).trans facts.cache
  · exact priorPacket.trans ((buildFrame 15 (by decide) (by decide) (by decide)).trans facts.packet)
  · rw [table,buildFrame 2 (by decide) (by decide) (by decide)]
    change archived (channelValues E) (preludeFinal.stk 2)=archived (channelValues E) []
    rw [facts.free 2 (Or.inl rfl)]
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact (framed 7 (by decide)).trans facts.owned.1
    · exact (framed 3 (by decide)).trans facts.owned.2.1
    · exact (framed 5 (by decide)).trans facts.owned.2.2.2.1
    · exact (framed 6 (by decide)).trans facts.owned.2.2.2.2.1
    · exact (framed 9 (by decide)).trans (facts.free 9 (Or.inr (Or.inl rfl)))
    · exact (framed 12 (by decide)).trans facts.owned.2.2.2.2.2.1
    · exact (framed 13 (by decide)).trans facts.owned.2.2.2.2.2.2.1
    · exact (framed 14 (by decide)).trans facts.owned.2.2.2.2.2.2.2
  · have a := append_length_le front buildRun
    have b := append_length_le (front.append buildRun) loopRun
    change ((front.append buildRun).append loopRun).trace.length≤_
    unfold originalBudget
    omega

end B23_4_RatWordPrep.Channels.Count
