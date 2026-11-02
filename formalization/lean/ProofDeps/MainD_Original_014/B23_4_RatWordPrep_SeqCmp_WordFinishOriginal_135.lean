module

public import B23_4_RatWordPrep_SeqCmp_WordFinishOperands_132
public import B23_4_RatWordPrep_SeqCmp_WordFinishSerialize_133
public import B23_4_RatWordPrep_SeqCmp_WordFinishHalt_134

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

theorem fold_path (caller : Statement C) (run : List (WordFold.State C))
    (before final : WordFold.State C) (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (WordFold.program .halt) a=some b))
    (last : run.getLast?=some final) (active : final.l=some .done) :
    (run.map foldCfg).head?=some (foldCfg before) ∧
    (run.map foldCfg).IsChain (fun a b => TM2.step (program caller) a=some b) ∧
    (run.map foldCfg).getLast?=some (foldCfg final) := by
  have proper := NativeMulLink.no_early_halt_port (WordFold.program .halt) .done rfl run final chain last active
  have mapped := LabelMap.actual_path_on foldLabel (WordFold.program .halt) (program caller)
    run before final first chain last (by
      intro current member point selected
      have different : point≠.done := by intro equal; subst point; exact proper current member selected
      simp only [foldLabel,different,ite_false,program])
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

/-- One fixed original-input source, actual lookup/odds/threshold loops,
three physical comparisons and OR, complete original WordOutput,
then paid physical movement to stack0 and literal final HALT.
Whole-original resource and preparation acceptance are separate claims. -/
theorem actual_original (caller : Statement C) (context : C)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ (final : State C) (_run : Segment caller (entry context (wordInput E target word)) final),
      final.l=none ∧ TM2.step (program caller) final=none ∧
      OriginalFee.context (OriginalPrelude.feeMemory final.var.2.2.2)=context ∧
      final.stk 0=wordOutput E target word ∧ final.stk 3=[] ∧ final.stk 13=[] ∧
      final.stk 15=RatInput.Encoder.packet (E.rationalWordOdds word) [] := by
  obtain ⟨foldFinal,foldRun,foldPort,originalContext,queryEmpty,metadata,table,odds,_scratch,owned⟩ :=
    WordFold.actual_original .halt context E target word
  have path := fold_path caller foldRun.trace _ foldFinal foldRun.first foldRun.chain foldRun.last foldPort
  let beforeBoot := foldCfg foldFinal
  let front : Segment caller (entry context (wordInput E target word)) beforeBoot :=
    ⟨foldRun.trace.map foldCfg,path.1,path.2.1,path.2.2⟩
  have activeBoot : beforeBoot.l=some (.metadata 2) := by
    change foldFinal.l.map foldLabel=_
    rw [foldPort]
    rfl
  obtain ⟨bootFinal,bootRun,bootPort,bootContext,bootShape⟩ := actual_bootstrap caller beforeBoot
    E.alphabetSize target (E.rationalWordOdds word) (Channels.channelValues E)
      activeBoot queryEmpty metadata table odds owned
  obtain ⟨operandFinal,operandRun,operandPort,operandContext,operandShape⟩ := actual_operands caller bootFinal
    beforeBoot.stk target (E.rationalWordOdds word) (Channels.channelValues E) bootPort bootShape
  have operandPacket : operandFinal.stk 15=SeqCmp.Word.input (E.rationalWordOdds word)
      (target/(1-target)) ((1-target)/target) [] := by
    rw [operandShape]
    exact operand_packet beforeBoot.stk target (E.rationalWordOdds word) (Channels.channelValues E)
  have operandOwned : ∀ slot,WordFold.Owned slot → operandFinal.stk slot=[] := by
    rw [operandShape]
    exact layout_owned _ _
  obtain ⟨serialized,serializeRun,serializePort,serializeContext,output,empty3,retained,_serializeScratch,_serializeTime⟩ :=
    actual_word caller operandFinal E target word operandPort operandPacket operandOwned
  obtain ⟨final,haltRun,halted,haltStep,haltContext,exactOutput,emptyFinal3,emptyFinal13,frame,_haltTime⟩ :=
    actual_halt caller serialized (wordOutput E target word) serializePort empty3 output
  let whole := (((front.append bootRun).append operandRun).append serializeRun).append haltRun
  refine ⟨final,whole,halted,haltStep,?_,exactOutput,emptyFinal3,emptyFinal13,?_⟩
  · have base := haltContext.trans (serializeContext.trans (operandContext.trans bootContext))
    exact (congrArg (fun memory => OriginalFee.context (OriginalPrelude.feeMemory memory)) base).trans originalContext
  · exact (frame 15 (by simp [RootB234.WordFinalizer.Work])).trans retained

end B23_4_RatWordPrep.WordFinish
