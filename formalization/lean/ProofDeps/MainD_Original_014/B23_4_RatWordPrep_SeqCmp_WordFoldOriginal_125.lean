module

public import B23_4_RatWordPrep_SeqCmp_WordFoldSemantics_124
public import B23_4_RatWordPrep_SeqCmp_OddsInitOriginal_116

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFold

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

/-- Entire ORIGINAL wordInput to the actual original rationalWordOdds
packet. Every symbol is consumed by the same fixed double-lookup,
division/multiplication source; the final real EOF returns active done.
Threshold operands/WordOutput/final HALT are the remaining continuation. -/
theorem actual_original (caller : Statement C) (context : C)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ (final : State C) (_run : Segment caller (entry context (wordInput E target word)) final),
      final.l=some .done ∧
      OriginalFee.context (OriginalPrelude.feeMemory final.var.2.2.2)=context ∧
      final.stk 0=[] ∧ final.stk 1=NatField.packet E.alphabetSize (RatInput.Encoder.packet target []) ∧
      final.stk 2=PacketLists.rats (Channels.channelValues E) [] ∧
      final.stk 15=RatInput.Encoder.packet (E.rationalWordOdds word) [] ∧ final.stk 7=[] ∧
      (∀ slot,Owned slot→final.stk slot=[]) := by
  obtain ⟨initialized,initRun,active,contextEq,queries,metadata,table,odds,scratch,owned⟩ :=
    OddsInit.actual_original .halt context E target word
  have path := init_path caller initRun.trace _ initialized initRun.first initRun.chain initRun.last active
  let beforeLoop := initCfg initialized
  let front : Segment caller (entry context (wordInput E target word)) beforeLoop :=
    ⟨initRun.trace.map initCfg,path.1,path.2.1,path.2.2⟩
  have atLoop : beforeLoop.l=some .check := by
    change initialized.l.map initLabel=_
    rw [active]
    rfl
  have query : beforeLoop.stk 0=PacketLists.naturals ((symbols E word).map Fin.val) [] := by
    rw [symbols_values]
    exact queries
  obtain ⟨final,loopRun,atDone,baseEq,empty,metaFinal,tableFinal,oddsFinal,scratchFinal,ownedFinal⟩ :=
    actual_loop caller E (symbols E word) beforeLoop (E.priorOne/(1-E.priorOne))
      (RatInput.Encoder.packet target []) atLoop query metadata table odds owned
  let whole := front.append loopRun
  refine ⟨final,whole,atDone,?_,empty,metaFinal.trans metadata,tableFinal.trans table,?_,scratchFinal.trans scratch,ownedFinal⟩
  · exact (congrArg (fun memory => OriginalFee.context (OriginalPrelude.feeMemory memory)) baseEq).trans contextEq
  · rw [oddsFinal,value_original]

/-- Width is charged to the original input, on the actual normalized odds
packet produced above. No iterative multiplicative workspace recurrence. -/
theorem original_odds_field_bound (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    RatInput.Encoder.fieldSize (E.rationalWordOdds word)≤
      RootB23.WordOddsBits.prefixBound E target word word.1 :=
  (RootB23.WordOddsBits.original_pair_bounds E target word).2.2.2

end B23_4_RatWordPrep.WordFold
