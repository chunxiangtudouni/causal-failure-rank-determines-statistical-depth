module

public import B23_4_RatWordPrep_SeqCmp_WordPlanResources_150
public import B23_4_RatWordPrep_SeqCmp_WordTailScale_154

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

/-- Complete actual threshold/operand/comparison/WordOutput/HALT tail.
All five resource components concern the SAME trace. The only physical
premise is the actual normalized getter/odds return layout. -/
theorem actual_tail_resources (caller : Statement C) (before : State C)
    (frame : RatInput.Stack → List Bool) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord)
    (active : before.l=some (.packet .targetForSub 0))
    (shape : before.stk=layout frame (initialData target (E.rationalWordOdds word) (Channels.channelValues E))) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=none ∧ TM2.step (program caller) final=none ∧
      final.var.2.2.2=before.var.2.2.2 ∧ final.stk 0=wordOutput E target word ∧
      final.stk 3=[] ∧ final.stk 13=[] ∧ final.stk 15=RatInput.Encoder.packet (E.rationalWordOdds word) [] ∧
      RunBounds caller run (21*tailBudget frame E target word) (tailBudget frame E target word) (tailBudget frame E target word) ∧
      traceClockSum (program caller) run.trace≤21*(tailBudget frame E target word)^2 ∧
      run.trace.length+traceClockSum (program caller) run.trace≤
        (21*tailBudget frame E target word)*(tailBudget frame E target word+1) := by
  obtain ⟨operandsFinal,operandRun,operandPort,operandContext,operandShape,operandBounds,_operandClock,_operandCharge⟩ :=
    actual_operands_resources caller before frame E target word active shape
  have produced : operandsFinal.stk 15=SeqCmp.Word.input (E.rationalWordOdds word)
      (target/(1-target)) ((1-target)/target) [] := by
    rw [operandShape]
    exact operand_packet frame target (E.rationalWordOdds word) (Channels.channelValues E)
  have clean : ∀ slot,WordFold.Owned slot → operandsFinal.stk slot=[] := by
    rw [operandShape]
    exact layout_owned _ _
  have capacity : PlanData E target word (operandData target (E.rationalWordOdds word) (Channels.channelValues E)) := by
    rw [←stageData19_eq]
    exact stageCapacity19 E target word
  obtain ⟨serialized,wordRun,wordPort,wordContext,wordContents,wordBounds⟩ :=
    actual_word_resources caller operandsFinal E target word operandPort produced clean
  have output : serialized.stk 13=wordOutput E target word := by rw [wordContents]; rfl
  have empty : serialized.stk 3=[] := by rw [wordContents]; rfl
  obtain ⟨final,haltRun,halted,stopped,haltContext,haltContents,haltBounds,_haltClock,_haltCharge⟩ :=
    actual_halt_resources caller serialized (wordOutput E target word) wordPort empty output
  have cap := planBudget_le_tail frame E target word
  have frontBounds := operandBounds.mono (Nat.mul_le_mul_left 19 cap) cap cap
  have middleBounds := word_tail_bounds frame E target word _ capacity operandShape wordBounds
  have backBounds := halt_tail_bounds frame E target word _ capacity operandShape wordBounds haltBounds
  have firstJoin := append_uniform frontBounds middleBounds
  have total := append_uniform firstJoin backBounds
  let whole := (operandRun.append wordRun).append haltRun
  refine ⟨final,whole,halted,stopped,haltContext.trans (wordContext.trans operandContext),?_,?_,?_,?_,total,?_,?_⟩
  · rw [haltContents]
    rfl
  · rw [haltContents]
    rfl
  · rw [haltContents]
    rfl
  · rw [haltContents]
    change serialized.stk 15=_
    rw [wordContents]
    rfl
  · exact total.clockSum.trans_eq (by ring)
  · exact total.charge

end B23_4_RatWordPrep.WordFinish.Resources
