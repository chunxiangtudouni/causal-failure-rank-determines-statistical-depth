module
public import Structure.PA17_TM_RatArithmetic_Outer_025e

/-! Original-input polynomial resources for the actual raw/loop code.
The one outstanding INTERNAL assumption is the actual023 one-pass body;
the later concrete instance must discharge it before any allocator claim. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOuter025

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticBookmark014

def BodyRunContract {states : Nat} (body : Machine states) (k : Nat) : Prop :=
  ∀ (x y : Rat) (h n : Nat), ∃ trace,
    PSTRTMSeq005.RunsFrom body
      ⟨0,(popNxFound h (sign x) (bankAt x y n)).Tape⟩ trace
      ⟨Fin.last states,(popNxInitial h (sign x) (bankAt x y (n+k*fieldWidth x y))).Tape⟩ ∧
    trace.length≤passFee k (fieldWidth x y) n

theorem raw_allocation_polynomial_of_body {states : Nat} (body : Machine states) (k : Nat)
    (bodyRun : BodyRunContract body k) (x y : Rat) :
    ∃ trace, Runs (rawLoopMachine body) (encode [.rational x,.rational y]) trace
      (rawLoopSavedFinal body (mNx x y) (sign x) (bankAt x y (k*(fieldWidth x y)^2))) ∧
      trace.length≤(32*k+1026)*((encode [.rational x,.rational y]).length+1)^4 ∧
      ∀ prefixLength,
        visitedSpace (rawLoopMachine body) (encode [.rational x,.rational y]).length
          (trace.take prefixLength) ≤
            (32*k+1026)*((encode [.rational x,.rational y]).length+1)^4 := by
  obtain ⟨trace,run,timeBound⟩ := raw_allocation_from_body body k bodyRun x y
  let i := (encode [.rational x,.rational y]).length
  have widthBound := original_width_le_input x y
  have hp : (fieldWidth x y+1)^4≤(i+1)^4 :=
    Nat.pow_le_pow_left (by omega) 4
  have ht : trace.length≤(16*k+512)*(i+1)^4 :=
    timeBound.trans (Nat.mul_le_mul_left _ hp)
  have hi : i+1≤(i+1)^4 := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right (by omega : (1 : Nat) ≤ i + 1) (by decide : (1 : Nat) ≤ 4)
  have hc : 16*k+512≤32*k+1026 := by omega
  refine ⟨trace,run,ht.trans (Nat.mul_le_mul_right _ hc),?_⟩
  intro prefixLength
  have hs := PSTRTMTrace002.visitedSpace_le (rawLoopMachine body) i (trace.take prefixLength)
  have hl : (trace.take prefixLength).length≤trace.length := by
    simp only [List.length_take]
    omega
  change visitedSpace (rawLoopMachine body) i (trace.take prefixLength)≤(32*k+1026)*(i+1)^4
  calc
    _ ≤ (i+1)+2*((16*k+512)*(i+1)^4) := by omega
    _ ≤ (i+1)^4+2*((16*k+512)*(i+1)^4) := Nat.add_le_add_right hi _
    _ = (32*k+1025)*(i+1)^4 := by ring
    _ ≤ (32*k+1026)*(i+1)^4 := Nat.mul_le_mul_right _ (by omega)

theorem raw_allocation_final_tape {states : Nat} (body : Machine states) (memory : Fin 32)
    (sx : Bool) (bank : List Bool) :
    (rawLoopSavedFinal body memory sx bank).Tape=Tape.mk₂ [false]
      (prefixRight sx bank) := rfl

/-- This is explicitly conditional on a proved one-pass machine; it is not
the final allocator theorem. The concrete023 instance must remove bodyRun. -/
theorem allocation_code_of_body {sourceStates : Nat} (body : Machine sourceStates) (k : Nat)
    (bodyRun : BodyRunContract body k) :
    ∃ states c d : Nat, ∃ program : Machine states, 0<c ∧ 0<d ∧
      ∀ x y : Rat, ∃ trace final,
        Runs program (encode [.rational x,.rational y]) trace final ∧
        final.Tape=Tape.mk₂ [false]
          (prefixRight (sign x) (bankAt x y (k*(fieldWidth x y)^2))) ∧
        final.q.val=(mNx x y).val*(rawLoopCapacity sourceStates+1)+
          (rawLoopCapacity sourceStates+1)+7 ∧
        trace.length≤c*((encode [.rational x,.rational y]).length+1)^d ∧
        ∀ prefixLength,
          visitedSpace program (encode [.rational x,.rational y]).length (trace.take prefixLength) ≤
            c*((encode [.rational x,.rational y]).length+1)^d := by
  refine ⟨totalStates 32 (rawLoopCapacity sourceStates),32*k+1026,4,rawLoopMachine body,
    by omega,by decide,?_⟩
  intro x y
  obtain ⟨trace,run,timeBound,spaceBound⟩ := raw_allocation_polynomial_of_body body k bodyRun x y
  refine ⟨trace,rawLoopSavedFinal body (mNx x y) (sign x) (bankAt x y (k*(fieldWidth x y)^2)),
    run,raw_allocation_final_tape _ _ _ _,?_,timeBound,spaceBound⟩
  rw [rawLoop_saved_final_label]
  ring

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticOuter025
