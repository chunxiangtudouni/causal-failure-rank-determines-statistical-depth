module

public import B23_4_RatWordPrep_SeqCmp_OddsInitCount_171
public import B23_4_RatWordPrep_SeqCmp_WordPackCountOriginal_170
public import B23_4_RatWordPrep_SeqCmp_OddsInitDivide_115

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.OddsInit.Count

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

noncomputable def originalBudget (caller : Statement C) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Nat :=
  WordPack.Count.originalBudget (C:=C) E target word+
    swapWork E.observationFee E.priorOne (1-E.priorOne)+
    (7*WordFinish.Resources.binaryScaleCoefficient RatMulDiv.divCoefficient+137)*
      (WordPack.Count.originalMass E target word+
        pushCap caller*swapWork E.observationFee E.priorOne (1-E.priorOne)+1)^4

/-- Entire original input to initial rational prior odds plus the original
lookup data. Fee disposal, the packet exchange and division are all paid
on the same fixed source with all future finite auxiliaries preallocated. -/
theorem actual_original (caller : Statement C) (context : C)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ (final : State C) (run : Segment caller (entry context (wordInput E target word)) final),
      final.l=some .done ∧
      OriginalFee.context (OriginalPrelude.feeMemory final.var.2.2.2)=context ∧
      final.stk 0=PacketLists.naturals (WordFields.symbolValues E word) [] ∧
      final.stk 1=NatField.packet E.alphabetSize (RatInput.Encoder.packet target []) ∧
      final.stk 2=PacketLists.rats (Channels.channelValues E) [] ∧
      final.stk 15=RatInput.Encoder.packet (E.priorOne/(1-E.priorOne)) [] ∧ final.stk 7=[] ∧
      (∀ slot,Owned slot→final.stk slot=[]) ∧
      (∃ digits,final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet digits ∧
        digits.length=(PSTRTMNatValue017.rawPayload word.1).length ∧ final.stk 11=[false]) ∧
      run.trace.length≤originalBudget caller E target word := by
  obtain ⟨packed,packRun,digits,active,contextEq,wordQueue,metadata,table,source,
    counter,_zero,width,left,owned,packMass,packTime⟩ := WordPack.Count.actual_original .halt context E target word
  have path := prep_path caller default packRun.trace _ packed packRun.first packRun.chain packRun.last active
  let beforeInit := prepCfg default packed
  let front : Segment caller (entry context (wordInput E target word)) beforeInit :=
    ⟨packRun.trace.map (prepCfg default),path.1,path.2.1,path.2.2⟩
  have atInit : beforeInit.l=some (.fee 0) := by
    change packed.l.map prepLabel=_
    rw [active]
    rfl
  have clean : ∀ slot,Owned slot→beforeInit.stk slot=[] := by
    intro slot selected
    fin_cases slot <;> first
    | exact owned.1
    | exact owned.2.1
    | exact owned.2.2.1
    | exact owned.2.2.2.1
    | exact owned.2.2.2.2.2.1
    | exact owned.2.2.2.2.2.2.1
    | exact owned.2.2.2.2.2.2.2.1
    | exact owned.2.2.2.2.2.2.2.2.1
    | exact owned.2.2.2.2.2.2.2.2.2
    | simp [Owned] at selected
  obtain ⟨final,initRun,atDone,baseEq,odds,scratch,finalOwned,frame,initTime⟩ := actual_initialize caller beforeInit
    E.observationFee E.priorOne (1-E.priorOne) atInit clean source
  let whole := front.append initRun
  refine ⟨final,whole,atDone,?_,?_,?_,?_,odds,?_,finalOwned,?_,?_⟩
  · exact (congrArg (fun memory => OriginalFee.context (OriginalPrelude.feeMemory memory)) baseEq).trans contextEq
  · exact (frame 0 (by decide)).trans wordQueue
  · exact (frame 1 (by decide)).trans metadata
  · exact (frame 2 (by decide)).trans table
  · exact scratch.trans owned.2.2.2.2.1
  · exact ⟨digits,(frame 10 (by decide)).trans counter,width,(frame 11 (by decide)).trans left⟩
  · have frontTime : front.trace.length≤WordPack.Count.originalBudget (C:=C) E target word := by
      simpa only [front,List.length_map] using packTime
    have paidInit : initRun.trace.length≤swapWork E.observationFee E.priorOne (1-E.priorOne)+
        (7*WordFinish.Resources.binaryScaleCoefficient RatMulDiv.divCoefficient+137)*
          (WordPack.Count.originalMass E target word+
            pushCap caller*swapWork E.observationFee E.priorOne (1-E.priorOne)+1)^4 := by
      change initRun.trace.length≤swapWork E.observationFee E.priorOne (1-E.priorOne)+
        (7*WordFinish.Resources.binaryScaleCoefficient RatMulDiv.divCoefficient+137)*
          (RatInput.occupied packed.stk+pushCap caller*swapWork E.observationFee E.priorOne (1-E.priorOne)+1)^4 at initTime
      rw [packMass] at initTime
      exact initTime
    have joined := front.append_length_le initRun
    change (front.append initRun).trace.length≤_
    unfold originalBudget
    omega

end B23_4_RatWordPrep.OddsInit.Count
