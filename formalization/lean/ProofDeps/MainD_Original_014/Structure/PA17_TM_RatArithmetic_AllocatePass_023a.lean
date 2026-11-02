module
public import Structure.PA17_TM_RatArithmetic_Width_018k
public import Structure.PA17_TM_RatArithmetic_Allocate_013f

/-! Original-bank allocator pass. After the genuine temporary flag has
been located, restore it by LEFT, WRITE TRUE, RIGHT. No value, distance,
gap length or original bit tuple is supplied to this fixed code. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
open PA17TMRatArithmeticWidth018

def restoreBackMachine : Machine 3 := fun q _ =>
  match q.val with
  | 0 => some (1,.move .left)
  | 1 => some (2,.write true)
  | 2 => some (3,.move .right)
  | _ => none

def restoreState (q : Fin 4) (left right : List Bool) : MachineState 3 := ⟨q,Turing.Tape.mk₂ left right⟩

def restoreBackTrace (archive right : List Bool) : List (MachineState 3) :=
  [restoreState 0 (false::archive) right,restoreState 1 archive (false::right),
   restoreState 2 archive (true::right),restoreState 3 (true::archive) right]

theorem restoreBack_runsFrom (archive right : List Bool) :
    PSTRTMSeq005.RunsFrom restoreBackMachine (restoreState 0 (false::archive) right)
      (restoreBackTrace archive right) (restoreState 3 (true::archive) right) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [restoreBackTrace,List.isChain_cons_cons,Turing.TM0.step,restoreBackMachine,restoreState,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,restoreBackMachine,restoreState]

theorem restoreBackTrace_length (archive right : List Bool) : (restoreBackTrace archive right).length=4 := rfl

def gapTail (n : Nat) : List Bool := List.replicate n false++[true]

def pushField (left digits : List Bool) : List Bool :=
  false::(PSTRTMRawNat010.leftBlocks digits.reverse++left)

def yHeaderLeft (left : List Bool) : List Bool := false::false::left

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
