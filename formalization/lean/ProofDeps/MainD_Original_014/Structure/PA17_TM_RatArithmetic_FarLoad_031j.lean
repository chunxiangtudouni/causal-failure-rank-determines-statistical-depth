module
public import Structure.PA17_TM_RatArithmetic_FarLoad_031i

/-! Typed consumers of the actual014 saved-memory port. These machines
start at the produced original header with real allocated blank workspace;
the input parser/allocator is not supplied by a free head or window oracle. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticParse002 (numeratorDigits denominatorDigits sign)
open PA17TMRatArithmeticBookmark014 (mNx observedFirst)

def globalSourceLeft (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool) : List Bool :=
  nxFinish dxTail nyTail dyTail (PA17TMRatArithmeticWidth018.prefixLeft sx counter) (false::nxTail)

theorem source_finish_global (field : SourceField) (sx : Bool)
    (counter nxTail dxTail nyTail dyTail : List Bool) :
    sourceFinish field dxTail nyTail dyTail
      (false::sourceArchive field sx counter nxTail dxTail nyTail)
      (false::sourceTail field nxTail dxTail nyTail dyTail)=
      globalSourceLeft sx counter nxTail dxTail nyTail dyTail := by
  cases field <;> rfl

def originalDigits (field : SourceField) (x y : Rat) : List Bool :=
  match field with
  | .dy => denominatorDigits y | .ny => numeratorDigits y
  | .dx => denominatorDigits x | .nx => numeratorDigits x

theorem originalDigits_ne_nil (field : SourceField) (x y : Rat) : originalDigits field x y≠[] := by
  cases field
  · exact PA17TMRatArithmeticBookmark014.denominator_ne_nil y
  · exact PA17TMRatArithmeticBookmark014.numerator_ne_nil y
  · exact PA17TMRatArithmeticBookmark014.denominator_ne_nil x
  · exact PA17TMRatArithmeticBookmark014.numerator_ne_nil x

/-- This bit is obtained from the actual five read-and-clear transitions
of014. It is not an additional caller flag or machine-construction input. -/
theorem actual_saved_source_bit (field : SourceField) (x y : Rat) :
    (mNx x y).val.testBit (sourceSlot field)=observedFirst (originalDigits field x y) := by
  obtain ⟨hdy,hny,_,hdx,hnx⟩ := PA17TMRatArithmeticBookmark014.observed_memory_bits x y
  cases field
  · exact hdy
  · exact hny
  · exact hdx
  · exact hnx

theorem actual_restored_source (field : SourceField) (x y : Rat) :
    (mNx x y).val.testBit (sourceSlot field)::sourceTail field
      (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail=
      originalDigits field x y := by
  rw [actual_saved_source_bit]
  have hh := (PA17TMRatArithmeticBookmark014.digits_observedFirst (originalDigits field x y)
    (originalDigits_ne_nil field x y)).symm
  cases field <;> exact hh

def ratHeaderTape (x y : Rat) (counter : List Bool) (gap : Nat) : Tape Bool :=
  headerTape (sign x) counter (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail gap

def ratGlobalLeft (x y : Rat) (counter : List Bool) : List Bool :=
  globalSourceLeft (sign x) counter (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail

def ratLoaderFee (field : SourceField) (x y : Rat) (gap : Nat) : Nat :=
  navigationFee (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail+
    copyFee (false::sourceTail field (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail)
      (sourceCost field (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail) gap+2

/-- Four machines, fixed before forall x,y. The real incoming32-state
memory selects the final WRITE; source first DATA remains clampedFALSE,
the entire source bank is retained, and DEST is the genuine raw Nat field. -/
theorem rat_loader_contract (field : SourceField) (x y : Rat) (counter : List Bool) (gap inputLength : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (originalLoader 31 field)
      (blockCfg (mNx x y) (⟨0,ratHeaderTape x y counter gap⟩ : MachineState 435)) trace
      (blockCfg (mNx x y) (⟨435,Tape.mk₂ (destinationLeft gap (ratGlobalLeft x y counter))
        (PA17TMRatArithmeticCopy006.workspace (originalDigits field x y))⟩ : MachineState 435)) ∧
      trace.length≤ ratLoaderFee field x y gap ∧
      ∀ k, visitedSpace (originalLoader 31 field) inputLength (trace.take k) ≤
        inputLength+2*ratLoaderFee field x y gap+1 := by
  have h := original_loader_contract 31 field (mNx x y) (sign x) counter
    (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
    gap inputLength
  rw [source_finish_global,actual_restored_source] at h
  exact h

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
