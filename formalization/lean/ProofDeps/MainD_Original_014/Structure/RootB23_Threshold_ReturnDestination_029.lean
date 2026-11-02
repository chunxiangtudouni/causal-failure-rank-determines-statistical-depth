module
public import Structure.RootB23_Threshold_ReturnCopyLoop_028

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnDestination
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticFarLoad031

/-- The destination TRUE is really written immediately east of the
badRisk footer. The guard and workspace are in the actual infinite blank
RIGHT tail. No internal archive/gap is removed by blank-tail identities. -/
def ownMachine : Machine 3 := fun q _ =>
  match q.val with
  | 0=>some (1,.move .right)
  | 1=>some (2,.write true)
  | 2=>some (3,.move .left)
  | _=>none
def ownTrace (archive : List Bool) : List (MachineState 3) :=
  [⟨0,Tape.mk₂ archive [false]⟩,
   ⟨1,Tape.mk₂ (false::archive) []⟩,
   ⟨2,Tape.mk₂ (false::archive) [true]⟩,
   ⟨3,Tape.mk₂ archive (false::workSuffix 0 [])⟩]
theorem own_bounded (archive : List Bool) :
    BoundedRun ownMachine (Tape.mk₂ archive [false]) 3
      (Tape.mk₂ archive (false::workSuffix 0 [])) 4 := by
  have blankFT : ListBlank.mk ([false,true,false,false,false] : List Bool)=ListBlank.mk [false,true] :=
    PA17TMDivisionTape005.blank_false_suffix [false,true] 3
  refine ⟨ownTrace archive,⟨rfl,?_,rfl,?_⟩,by rfl⟩
  · simp [ownTrace,List.isChain_cons_cons,TM0.step,ownMachine,Tape.mk₂,workSuffix,
      PA17TMRatArithmeticCopy006.workspace,PSTRTMIncrement009.blocks,blankFT]
  · simp [TM0.step,ownMachine]

def reservePrefixMachine (capped : Bool) : Machine 196 := PSTRTMSeq005.seqMachine (ReturnRoute.out capped) ownMachine
def reserveMachine (capped : Bool) : Machine 389 := PSTRTMSeq005.seqMachine (reservePrefixMachine capped) (ReturnRoute.back capped)
def reservePort (capped : Bool) : Fin 390 := PSTRTMSeq005.rightLabel (a:=196) (ReturnRoute.backPort capped)
theorem reserve_bounded (capped : Bool) (x y q : Rat) (nonnegative : 0≤x) (qNonnegative : 0≤q)
    (credit : ℕ) (archive digits : List Bool) :
    BoundedRun (reserveMachine capped)
      (Tape.mk₂ (false::archive) (RoutedCopy.fieldWord (ReturnRoute.context capped x y q credit) digits []))
      (reservePort capped)
      (Tape.mk₂ (false::archive) (RoutedCopy.fieldWord (ReturnRoute.context capped x y q credit) digits (workSuffix 0 [])))
      (4*digits.length+2*ReturnRoute.cost capped x y q credit+4) := by
  have out:=ReturnCopy.out_bounded capped x y q nonnegative credit (false::archive) digits []
  have own:=own_bounded (ReturnRoute.finish capped x y q credit (false::archive) digits)
  have back:=ReturnCopy.back_bounded capped x y q nonnegative qNonnegative credit archive digits (workSuffix 0 [])
  exact ((out.seq own).seq back).mono (by omega)

def code (capped : Bool) : Machine 2380 := PSTRTMSeq005.seqMachine (reserveMachine capped) (ReturnCopy.copyMachine capped)
def destinationLeft (capped : Bool) (x y q : Rat) (credit : ℕ) (archive digits : List Bool) : List Bool :=
  RoutedCopy.destinationLeft 0 (ReturnRoute.finish capped x y q credit (false::archive) digits)
def fee (capped : Bool) (x y q : Rat) (credit : ℕ) (digits : List Bool) : ℕ :=
  (4*digits.length+2*ReturnRoute.cost capped x y q credit+4)+ReturnCopy.copyFee capped x y q credit digits 0

/-- The entire first B far-copy: actual destination initialization,
actual bit-by-bit excursions across retained bank/counters/cap scratch,
and a real final trip to the copied B DATA head. The original B, all
original fields and the actual badRisk Datum remain on the same WEST. -/
theorem bounded (capped : Bool) (x y q : Rat) (nonnegative : 0≤x) (qNonnegative : 0≤q)
    (credit : ℕ) (archive digits : List Bool) :
    BoundedRun (code capped)
      (Tape.mk₂ (false::archive) (RoutedCopy.fieldWord (ReturnRoute.context capped x y q credit) digits [])) 2380
      (Tape.mk₂ (destinationLeft capped x y q credit archive digits) (PSTRTMIncrement009.blocks digits))
      (fee capped x y q credit digits) := by
  have reserved:=reserve_bounded capped x y q nonnegative qNonnegative credit archive digits
  have copied:=ReturnCopy.copy_bounded capped x y q nonnegative qNonnegative credit archive digits 0
  have finalEq : Tape.mk₂ (destinationLeft capped x y q credit archive digits)
      (PA17TMRatArithmeticCopy006.workspace digits)=
      Tape.mk₂ (destinationLeft capped x y q credit archive digits) (PSTRTMIncrement009.blocks digits) :=
    PA17TMDivisionTape005.tape_owned00 _ _
  dsimp only [destinationLeft] at finalEq
  rw [finalEq] at copied
  exact (reserved.seq copied).mono (by rfl)

theorem contract (capped : Bool) (x y q : Rat) (nonnegative : 0≤x) (qNonnegative : 0≤q)
    (credit : ℕ) (archive digits : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom (code capped)
      ⟨0,Tape.mk₂ (false::archive) (RoutedCopy.fieldWord (ReturnRoute.context capped x y q credit) digits [])⟩ trace
      ⟨2380,Tape.mk₂ (destinationLeft capped x y q credit archive digits) (PSTRTMIncrement009.blocks digits)⟩ ∧
      trace.length≤fee capped x y q credit digits ∧
      ∀ chargedLength clock, visitedSpace (code capped) chargedLength (trace.take clock)≤
        chargedLength+2*fee capped x y q credit digits+1 := by
  obtain ⟨trace,run,time⟩:=bounded capped x y q nonnegative qNonnegative credit archive digits
  refine ⟨trace,run,time,?_⟩
  intro chargedLength clock
  have space:=PSTRTMTrace002.visitedSpace_le (code capped) chargedLength (trace.take clock)
  have taken : (trace.take clock).length≤trace.length := by rw [List.length_take];exact Nat.min_le_right _ _
  omega

end RootB23.Threshold.ReturnDestination
