module
public import Structure.PA17_TM_RatArithmetic_PairExcursion_041a
public import Structure.PA17_TM_RatArithmetic_CopyLoop_042b

/-! First complete multiplication chain, stage 1: instantiate the SINGLE
frozen physical copy loop with the actual shared-B excursion. No new copying
algorithm is introduced. Later stages discharge SourceCorrect with the fixed
original/cached source routes and compose real allocation/native/output code. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMul047

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticPairExcursion041

theorem excursion_room (a b : Nat) : 8≤excursionCap a b := by
  unfold excursionCap
  omega

def sharedLoopMachine {a b : Nat} (route : SourceRoute a b) :
    Machine (totalStates 2 (excursionCap a b)) :=
  PA17TMRatArithmeticCopyLoop042.loopMachine (s:=excursionCap a b) (excursion_room a b)
    (excursionMachine route) (Fin.last (excursionCap a b))

def sharedLoopPort (a b : Nat) : Fin (totalStates 2 (excursionCap a b)+1) :=
  PA17TMRatArithmeticCopyLoop042.haltLabel (s:=excursionCap a b) (excursion_room a b)

def sharedWork {a b : Nat} (route : SourceRoute a b) (gap : Nat)
    (first copied : List Bool) : List Bool := route.footerBit::workSuffix gap first copied

def sharedFee (cost gap : Nat) (first later copied : List Bool) : Nat :=
  4*later.length+2*cost+2*gap+4*first.length+4*copied.length+42

theorem actual_shared_excursions {a b : Nat} (route : SourceRoute a b) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost gap : Nat) (first : List Bool)
    (routes : SourceCorrect route context finish cost) :
    PA17TMRatArithmeticCopyLoop042.ExcursionCorrect
      (excursionMachine route) (Fin.last (excursionCap a b)) context
      (sharedWork route gap first) (sharedFee cost gap first) := by
  intro left later copied bit firstFalse
  have run := excursion_bounded route context finish cost routes left later first copied bit gap firstFalse
  simpa only [PA17TMRatArithmeticCopyLoop042.sourceWord,sharedWork,sharedFee,sourceWord] using run

theorem source_end_false {a b : Nat} (route : SourceRoute a b) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost gap : Nat) (first copied : List Bool)
    (routes : SourceCorrect route context finish cost) :
    (context++sharedWork route gap first copied).head?=some false := by
  cases context with
  | nil =>
    have hf : route.footerBit=false := routes.end_false
    simp only [List.nil_append,sharedWork,List.head?_cons,hf]
  | cons bit later =>
    have hf : bit=false := routes.end_false
    simp only [List.cons_append,List.head?_cons,hf]

theorem shared_loop_bounded {a b : Nat} (route : SourceRoute a b) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost gap : Nat) (first digits left copied : List Bool)
    (routes : SourceCorrect route context finish cost) (firstFalse : (copied++digits).headD false=false) :
    BoundedRun (sharedLoopMachine route)
      (Tape.mk₂ left (sourceWord route context digits (workSuffix gap first copied))) (sharedLoopPort a b)
      (Tape.mk₂ (false::PA17TMRatArithmeticFarLoad031.passedLeft left digits)
        (context++route.footerBit::workSuffix gap first (copied++digits)))
      (PA17TMRatArithmeticCopyLoop042.loopFee (sharedFee cost gap first) copied digits) := by
  have run := PA17TMRatArithmeticCopyLoop042.loop_bounded
    (s:=excursionCap a b) (excursion_room a b) (excursionMachine route) (Fin.last (excursionCap a b))
    context (sharedWork route gap first) (sharedFee cost gap first)
    (actual_shared_excursions route context finish cost gap first routes)
    (fun copied => source_end_false route context finish cost gap first copied routes)
    digits left copied firstFalse
  simpa only [sharedLoopMachine,sharedLoopPort,PA17TMRatArithmeticCopyLoop042.sourceWord,
    sourceWord,sharedWork] using run

theorem shared_loop_fee_le (cost gap : Nat) (first copied digits : List Bool) :
    PA17TMRatArithmeticCopyLoop042.loopFee (sharedFee cost gap first) copied digits ≤
      digits.length*(4*(digits.length+copied.length)+(2*cost+2*gap+4*first.length+42)+5)+3 := by
  apply PA17TMRatArithmeticCopyLoop042.loopFee_affine
  intro later copied
  unfold sharedFee
  omega

theorem shared_loop_port_value (a b : Nat) : (sharedLoopPort a b).val=3 :=
  PA17TMRatArithmeticCopyLoop042.haltLabel_value (excursion_room a b)

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMul047
