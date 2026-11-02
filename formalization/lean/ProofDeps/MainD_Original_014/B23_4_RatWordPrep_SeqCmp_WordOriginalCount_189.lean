module

public import B23_4_RatWordPrep_SeqCmp_WordFoldCountOriginal_186
public import B23_4_RatWordPrep_SeqCmp_WordFinishCountBootstrap_187
public import B23_4_RatWordPrep_SeqCmp_WordTailResources_155
public import B23_4_RatWordPrep_SeqCmp_WordFinishOriginal_135

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

def originalTailScale (bound : Nat) : Nat :=
  2*(bound+1)+4+2*bound+28*(16*(bound+1)^2+6)+1

noncomputable def originalTimeBound (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Nat :=
  WordFold.Count.originalBudget (.halt : WordFold.Statement C) E target word+
    5*(PSTRTMNatValue017.rawPayload E.alphabetSize).length+10+
    21*tailCoefficient*(originalTailScale (wordInput E target word).length)^4

/-- Actual whole original WORD count: all original parsing, both lookup
rows, normalized odds arithmetic, three comparisons, serialization and
literal HALT occur on this one fixed-source trace. -/
theorem actual_original_count (caller : Statement C) (context : C)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ (final : State C) (run : Segment caller (entry context (wordInput E target word)) final),
      final.l=none ∧ TM2.step (program caller) final=none ∧
      OriginalFee.context (OriginalPrelude.feeMemory final.var.2.2.2)=context ∧
      final.stk 0=wordOutput E target word ∧ final.stk 3=[] ∧ final.stk 13=[] ∧
      final.stk 15=RatInput.Encoder.packet (E.rationalWordOdds word) [] ∧
      run.trace.length≤originalTimeBound (C:=C) E target word := by
  obtain ⟨foldFinal,foldRun,foldPort,originalContext,queryEmpty,metadata,table,odds,_scratch,owned,safe,foldTime⟩ :=
    WordFold.Count.actual_original .halt context E target word
  have path := fold_path caller foldRun.trace _ foldFinal foldRun.first foldRun.chain foldRun.last foldPort
  let beforeBoot := foldCfg foldFinal
  let front : Segment caller (entry context (wordInput E target word)) beforeBoot :=
    ⟨foldRun.trace.map foldCfg,path.1,path.2.1,path.2.2⟩
  have activeBoot : beforeBoot.l=some (.metadata 2) := by
    change foldFinal.l.map foldLabel=_
    rw [foldPort]
    rfl
  obtain ⟨bootFinal,bootRun,bootPort,bootContext,bootShape,bootTime⟩ := actual_bootstrap_count caller beforeBoot
    E.alphabetSize target (E.rationalWordOdds word) (Channels.channelValues E)
      activeBoot queryEmpty metadata table odds owned
  obtain ⟨final,tailRun,halted,stopped,tailContext,output,empty3,empty13,retained,tailBounds,_clock,_charge⟩ :=
    actual_tail_resources caller bootFinal beforeBoot.stk E target word bootPort bootShape
  let B := (wordInput E target word).length
  have frameBound : frameMass beforeBoot.stk≤2*(B+1)+4 := by
    change (foldFinal.stk 7).length+(foldFinal.stk 10).length+(foldFinal.stk 11).length≤_
    rw [safe.1,safe.2.1]
    have count := safe.2.2
    change (foldFinal.stk 10).length≤2*(B+1)+3 at count
    simp only [List.length_nil,List.length_cons,Nat.zero_add]
    omega
  have scaleBound : planScale beforeBoot.stk E target word≤originalTailScale B := by
    unfold planScale originalTailScale
    change frameMass beforeBoot.stk+2*B+28*(16*(B+1)^2+6)+1≤_
    omega
  have paidTail := tailBounds.count.trans (Nat.mul_le_mul_left 21
    (Nat.mul_le_mul_left tailCoefficient (Nat.pow_le_pow_left scaleBound 4)))
  have frontTime : front.trace.length≤WordFold.Count.originalBudget (.halt : WordFold.Statement C) E target word := by
    simpa only [front,List.length_map] using foldTime
  let whole := (front.append bootRun).append tailRun
  refine ⟨final,whole,halted,stopped,?_,output,empty3,empty13,retained,?_⟩
  · exact (congrArg (fun memory => OriginalFee.context (OriginalPrelude.feeMemory memory))
      (tailContext.trans bootContext)).trans originalContext
  · have j2 := front.append_length_le bootRun
    have j3 := (front.append bootRun).append_length_le tailRun
    change ((front.append bootRun).append tailRun).trace.length≤_
    unfold originalTimeBound
    change ((front.append bootRun).append tailRun).trace.length≤
      WordFold.Count.originalBudget (.halt : WordFold.Statement C) E target word+
        5*(PSTRTMNatValue017.rawPayload E.alphabetSize).length+10+21*tailCoefficient*(originalTailScale B)^4
    have paidTail' : tailRun.trace.length≤21*tailCoefficient*(originalTailScale B)^4 := by
      simpa only [Nat.mul_assoc] using paidTail
    omega

end B23_4_RatWordPrep.WordFinish.Resources
