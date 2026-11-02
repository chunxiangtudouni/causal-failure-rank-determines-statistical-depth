module

public import B23_4_RatWordPrep_SeqCmp_WordFoldCountLoop_185
public import B23_4_RatWordPrep_SeqCmp_WordFoldOriginal_125
public import B23_4_RatWordPrep_SeqCmp_OddsInitCountOriginal_172

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFold.Count

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

theorem original_potential (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    potential E (symbols E word) (E.priorOne/(1-E.priorOne))≤8*((wordInput E target word).length+1)^2 := by
  let B := (wordInput E target word).length
  have terms : ∀ term∈(symbols E word).map (fun symbol => RatInput.Encoder.fieldSize (E.channel true symbol)+
      RatInput.Encoder.fieldSize (E.channel false symbol)),term≤2*B := by
    intro term member
    obtain ⟨symbol,_present,rfl⟩ := List.mem_map.mp member
    have a := RootB23.WordOddsBits.channel_width_le_input E target word true symbol
    have b := RootB23.WordOddsBits.channel_width_le_input E target word false symbol
    simp only [RootB23.WordOddsBits.ratInput_fieldSize_eq]
    omega
  have sum := List.sum_le_length_nsmul ((symbols E word).map (fun symbol =>
    RatInput.Encoder.fieldSize (E.channel true symbol)+RatInput.Encoder.fieldSize (E.channel false symbol))) (2*B) terms
  have length : (symbols E word).length=word.1 := by simp only [symbols,List.length_map,List.length_finRange]
  simp only [List.length_map,Nat.nsmul_eq_mul,length] at sum
  have prior := RootB23.WordOddsBits.prior_odds_width_le_input E target word
  change RootB23.WordOddsBits.width (E.priorOne/(1-E.priorOne))≤3*B at prior
  have count : word.1≤B := WordFinish.Resources.word_length_le_input E target word
  have paid := sum.trans (Nat.mul_le_mul_right (2*B) count)
  change _≤8*(B+1)^2
  unfold potential
  rw [RootB23.WordOddsBits.ratInput_fieldSize_eq]
  nlinarith

noncomputable def originalBudget (caller : Statement C) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Nat :=
  OddsInit.Count.originalBudget (.halt : OddsInit.Statement C) E target word+
    loopBudget caller E.alphabetSize (wordInput E target word).length word.1

/-- Entire ORIGINAL wordInput to the actual original rationalWordOdds
packet. Every symbol is consumed by the same fixed double-lookup,
division/multiplication source; the final real EOF returns active done.
Threshold operands/WordOutput/final HALT are the remaining continuation. -/
theorem actual_original (caller : Statement C) (context : C)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ (final : State C) (run : Segment caller (entry context (wordInput E target word)) final),
      final.l=some .done ∧
      OriginalFee.context (OriginalPrelude.feeMemory final.var.2.2.2)=context ∧
      final.stk 0=[] ∧ final.stk 1=NatField.packet E.alphabetSize (RatInput.Encoder.packet target []) ∧
      final.stk 2=PacketLists.rats (Channels.channelValues E) [] ∧
      final.stk 15=RatInput.Encoder.packet (E.rationalWordOdds word) [] ∧ final.stk 7=[] ∧
      (∀ slot,Owned slot→final.stk slot=[]) ∧
      CounterSafe (wordInput E target word).length final.stk ∧
      run.trace.length≤originalBudget caller E target word := by
  obtain ⟨initialized,initRun,active,contextEq,queries,metadata,table,odds,scratch,owned,counterInit,initTime⟩ :=
    OddsInit.Count.actual_original .halt context E target word
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
  have count : (symbols E word).length≤(wordInput E target word).length := by
    simpa only [symbols,List.length_map,List.length_finRange] using WordFinish.Resources.word_length_le_input E target word
  have safe : CounterSafe (wordInput E target word).length beforeLoop.stk := by
    obtain ⟨digits,right,width,left⟩ := counterInit
    refine ⟨scratch,left,?_⟩
    change (initialized.stk 10).length≤_
    rw [right,RootB234.RuntimeCounter.Round.packet_length,width]
    have raw := (WordFinish.Resources.rawPayload_le_number word.1).trans
      (Nat.add_le_add_right (WordFinish.Resources.word_length_le_input E target word) 1)
    omega
  obtain ⟨final,loopRun,atDone,baseEq,empty,metaFinal,tableFinal,oddsFinal,scratchFinal,ownedFinal,safeFinal,loopTime⟩ :=
    actual_loop caller E (symbols E word) target word beforeLoop (E.priorOne/(1-E.priorOne))
      atLoop query metadata table odds owned count (original_potential E target word) safe
  let whole := front.append loopRun
  refine ⟨final,whole,atDone,?_,empty,metaFinal.trans metadata,tableFinal.trans table,?_,scratchFinal.trans scratch,ownedFinal,safeFinal,?_⟩
  · exact (congrArg (fun memory => OriginalFee.context (OriginalPrelude.feeMemory memory)) baseEq).trans contextEq
  · rw [oddsFinal,value_original]

  · have frontTime : front.trace.length≤OddsInit.Count.originalBudget (.halt : OddsInit.Statement C) E target word := by
      simpa only [front,List.length_map] using initTime
    have length : (symbols E word).length=word.1 := by simp only [symbols,List.length_map,List.length_finRange]
    rw [length] at loopTime
    have joined := front.append_length_le loopRun
    change (front.append loopRun).trace.length≤_
    unfold originalBudget
    omega

end B23_4_RatWordPrep.WordFold.Count
