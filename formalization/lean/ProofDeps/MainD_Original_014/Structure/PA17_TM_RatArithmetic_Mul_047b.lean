module
public import Structure.PA17_TM_RatArithmetic_Mul_047a
public import Structure.PA17_TM_RatArithmetic_PairExcursion_041c

/-! Multiplication chain, stage 2: real shared-B initialization, the SAME
frozen042 copy loop instantiated in047a, and the actual EOF-to-B trip.
Source canonical restoration/final original-FALSE handling can consume the
explicit before-final interface; they are never silently assumed here. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMul047

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticPairExcursion041

def sharedLoopCap (a b : Nat) : Nat := totalStates 2 (excursionCap a b)
def sharedBeforeCap (a b : Nat) : Nat := (a+31+b+1)+sharedLoopCap a b+1
def sharedCopyCap (a b : Nat) : Nat := sharedBeforeCap a b+finalCap a+1

attribute [local implicit_reducible] sharedLoopCap sharedBeforeCap sharedCopyCap

def sharedBeforeMachine {a b : Nat} (route : SourceRoute a b) : Machine (sharedBeforeCap a b) :=
  PSTRTMSeq005.seqMachine (a:=a+31+b+1) (b:=sharedLoopCap a b)
    (startupMachine route) (sharedLoopMachine route)

def sharedBeforePort (a b : Nat) : Fin (sharedBeforeCap a b+1) :=
  PSTRTMSeq005.rightLabel (a:=a+31+b+1) (sharedLoopPort a b)

def sharedCopyMachine {a b : Nat} (route : SourceRoute a b) : Machine (sharedCopyCap a b) :=
  PSTRTMSeq005.seqMachine (a:=sharedBeforeCap a b) (b:=finalCap a)
    (sharedBeforeMachine route) (finalMachine route)

def sharedCopyPort (a b : Nat) : Fin (sharedCopyCap a b+1) :=
  PSTRTMSeq005.rightLabel (a:=sharedBeforeCap a b) (Fin.last (finalCap a))

def sharedCopyFee (digits first : List Bool) (cost gap : Nat) : Nat :=
  4*digits.length^2+(2*cost+2*gap+4*first.length+51)*digits.length+
    3*cost+3*gap+6*first.length+42

theorem passed_finish {a b : Nat} (route : SourceRoute a b) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (routes : SourceCorrect route context finish cost) (left digits : List Bool) :
    finish (PA17TMRatArithmeticFarLoad031.passedLeft left digits) []=finish left digits := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    rw [PA17TMRatArithmeticFarLoad031.passedLeft,ih,routes.finish_cons]

theorem shared_before_bounded {a b : Nat} (route : SourceRoute a b) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost gap : Nat) (archive digits first : List Bool)
    (routes : SourceCorrect route context finish cost) (clamped : digits.headD false=false) :
    BoundedRun (sharedBeforeMachine route)
      (Tape.mk₂ (false::archive) (sourceWord route context digits (workSuffix gap first []))) (sharedBeforePort a b)
      (Tape.mk₂ (false::PA17TMRatArithmeticFarLoad031.passedLeft (false::archive) digits)
        (context++route.footerBit::workSuffix gap first digits))
      ((4*digits.length+2*cost+2*gap+4*first.length+30)+
        PA17TMRatArithmeticCopyLoop042.loopFee (sharedFee cost gap first) [] digits) := by
  have hs := startup_bounded route context finish cost routes archive digits first gap
  have hl := shared_loop_bounded route context finish cost gap first digits (false::archive) [] routes
    (by simpa only [List.nil_append] using clamped)
  simp only [List.nil_append] at hl
  have combined := hs.seq hl
  simpa only [sharedBeforeMachine,sharedBeforePort,sharedBeforeCap,sharedLoopCap] using combined

theorem shared_copy_bounded {a b : Nat} (route : SourceRoute a b) (context : List Bool)
    (finish : List Bool → List Bool → List Bool) (cost gap : Nat) (archive digits first : List Bool)
    (routes : SourceCorrect route context finish cost) (clamped : digits.headD false=false) :
    BoundedRun (sharedCopyMachine route)
      (Tape.mk₂ (false::archive) (sourceWord route context digits (workSuffix gap first []))) (sharedCopyPort a b)
      (Tape.mk₂ (destinationLeft route gap (finish (false::archive) digits) first)
        (PA17TMRatArithmeticCopy006.workspace digits)) (sharedCopyFee digits first cost gap) := by
  have hb := shared_before_bounded route context finish cost gap archive digits first routes clamped
  have hf := final_bounded route context finish cost routes
    (PA17TMRatArithmeticFarLoad031.passedLeft (false::archive) digits) first digits gap clamped
  have finish_eq := passed_finish route context finish cost routes (false::archive) digits
  rw [finish_eq] at hf
  have combined := hb.seq hf
  have loopBound := shared_loop_fee_le cost gap first [] digits
  simp only [List.length_nil,Nat.add_zero] at loopBound
  have bound : ((4*digits.length+2*cost+2*gap+4*first.length+30)+
      PA17TMRatArithmeticCopyLoop042.loopFee (sharedFee cost gap first) [] digits)+
      (cost+gap+2*first.length+9)≤sharedCopyFee digits first cost gap := by
    unfold sharedCopyFee
    nlinarith
  simpa only [sharedCopyMachine,sharedCopyPort,sharedCopyCap] using combined.mono bound

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMul047
