module

public import Common.PSTR_WordBool_RatInputComplementRun_097

/-! One common positive coefficient and degree8, fixed before ALL original
experiments/words, bounds this actual original prior-complement component. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatInput.Complement

open Turing PSTRWordVM RationalControllerComputation PaperProofs.Statistics
open PA17TMRatArithmeticAddSubFull079

variable {C : Type*}

def baseCoefficient : Nat:=2097152+addSubResourceCoefficient*2097153^4+8
def coefficient : Nat:=64*(baseCoefficient+8192)

theorem coefficient_positive : 0<coefficient:=by unfold coefficient;omega

theorem space_polynomial (length : Nat) : space length≤baseCoefficient*(length+1)^8 := by
  have positive : 1≤(length+1)^2:=Nat.pow_le_pow_left (show 1≤length+1 by omega) 2
  have positive8 : 1≤(length+1)^8:=Nat.pow_le_pow_left (show 1≤length+1 by omega) 8
  have powers : (length+1)^2≤(length+1)^8:=Nat.pow_le_pow_right (by omega) (by decide : 2≤8)
  have inner : 16*frontBound length+1≤2097153*(length+1)^2 :=by unfold frontBound;omega
  have raw : rawBound length≤(addSubResourceCoefficient*2097153^4)*(length+1)^8 := by
    have bound:=Nat.mul_le_mul_left addSubResourceCoefficient (Nat.pow_le_pow_left inner 4)
    simpa only [rawBound,mul_pow,←pow_mul,Nat.mul_assoc] using bound
  calc
    space length=16*frontBound length+rawBound length+8:=rfl
    _≤2097152*(length+1)^8+(addSubResourceCoefficient*2097153^4)*(length+1)^8+8*(length+1)^8:=by
      have front:=Nat.mul_le_mul_left 2097152 powers
      have extra:=Nat.mul_le_mul_left 8 positive8
      unfold frontBound
      omega
    _=baseCoefficient*(length+1)^8:=by unfold baseCoefficient;ring

theorem resource_envelope (length : Nat) :
    4096*(length+1)^2+4*space length+20≤coefficient*(length+1)^8 ∧
      space length≤coefficient*(length+1)^8 ∧
      16*space length≤coefficient*(length+1)^8 ∧
      space length+15≤coefficient*(length+1)^8 ∧
      30*(space length+16)≤coefficient*(length+1)^8 := by
  have bound:=space_polynomial length
  have positive : 1≤(length+1)^8:=Nat.pow_le_pow_left (show 1≤length+1 by omega) 8
  have powers : (length+1)^2≤(length+1)^8:=Nat.pow_le_pow_right (by omega) (by decide : 2≤8)
  have small:=Nat.mul_le_mul_left 4096 powers
  have expansion : coefficient*(length+1)^8=64*(baseCoefficient*(length+1)^8)+524288*(length+1)^8 := by
    unfold coefficient
    ring
  rw [expansion]
  omega

theorem actual_original_complement_uniform (context : C) (nativeMemory : CalleeFlags) (readerMemory : Reader)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    let bits:=wordInput E target word
    let budget:=coefficient*(bits.length+1)^8
    ∃ (trace : List (State C)) (final parsed : State C),
      trace.head?=some (initial context nativeMemory readerMemory bits) ∧
      trace.IsChain (fun a b=>TM2.step (program .halt) a=some b) ∧
      trace.getLast?=some final ∧ parsed∈trace ∧ final.l=some .done ∧
      final.var.1.1.1.1.1=context ∧
      final.stk=Encoder.bank parsed.stk
        (Encoder.packet (1-E.priorOne) (Encoder.packet E.priorOne [])) [] [] [] [] [] [] [] [] ∧
      Tape.mk' (ListBlank.mk (parsed.stk 1)) (ListBlank.mk (parsed.stk 0))=Tape.mk₂
        (PA17TMRatArithmeticParse002.bothLeft
          (false::PA17TMRatArithmeticParse002.sign E.priorOne::PSTRTMWordPriorFront215.priorBase E target word)
          (PA17TMRatArithmeticParse002.numeratorDigits E.priorOne)
          (PA17TMRatArithmeticParse002.denominatorDigits E.priorOne)) (PSTRTMWordPriorFront215.afterPrior E target word) ∧
      trace.length≤budget ∧
      (∀ current∈trace,(∀ slot,(current.stk slot).length≤budget) ∧ RatInput.occupied current.stk≤budget) ∧
      (∀ current∈trace,∀ point,current.l=some point→
        (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
          ∀ slot,(node.2 slot).length≤budget) ∧
        ScannerStatement.clock (program .halt point) current.var current.stk≤budget) ∧
      ∀ current∈trace.dropLast,current.l≠some .done := by
  dsimp only
  obtain ⟨trace,final,parsed,first,chain,last,parsedMember,active,contextFinal,contentsFinal,tape,count,bounds,nodes⟩:=
    actual_original_complement context nativeMemory readerMemory E target word
  have envelope:=resource_envelope (wordInput E target word).length
  refine ⟨trace,final,parsed,first,chain,last,parsedMember,active,contextFinal,contentsFinal,tape,
    count.trans envelope.1,?_,?_,?_⟩
  · intro current member
    exact ⟨fun slot=>((bounds current member).1 slot).trans envelope.2.1,
      (bounds current member).2.trans envelope.2.2.1⟩
  · intro current member point selected
    have actual:=nodes current member point selected
    exact ⟨fun node nodeMember slot=>(actual.1 node nodeMember slot).trans envelope.2.2.2.1,
      actual.2.trans envelope.2.2.2.2⟩
  · exact NativeMulLink.no_early_halt_port (program .halt) .done rfl trace final chain last active

end PaperProofs.Common.Native.PSTRWordBool.RatInput.Complement
