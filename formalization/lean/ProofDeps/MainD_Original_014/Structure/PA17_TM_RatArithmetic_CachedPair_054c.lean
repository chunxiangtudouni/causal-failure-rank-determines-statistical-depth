module
public import Structure.PA17_TM_RatArithmetic_CachedPair_054b
public import Structure.PA17_TM_RatArithmetic_PairInput_050d

/-! The concrete second multiplication input, Dx/Dy, comes from the actual
014 observed low carry bits. Existing M and all other bank contents remain
arbitrary physical records. No denominator, saved bit or answer is passed
as an additional original machine input. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPair054

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticCachedLoad038
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticPairInput050
open PA17TMRatArithmeticBookmark014 PA17TMRatArithmeticParse002
attribute [local implicit_reducible] originalFirstCap originalReadyCap originalPairCap totalStates

def originalPairTime (fieldA fieldB : SourceField) (memory j : Nat) (first : RecordSpec)
    (records : List RecordSpec) (nxTail dxTail nyTail dyTail : List Bool) (gap a b : Nat) : Nat :=
  originalBankRowTime fieldA .plain j gap first records nxTail dxTail nyTail dyTail []+
    originalHomeFee j first records nxTail dxTail nyTail dyTail gap+
    originalBankRowTime fieldB .shared j gap first records nxTail dxTail nyTail dyTail
      (restoredDigits fieldA memory nxTail dxTail nyTail dyTail)+
    64*((PA17TMRatArithmeticPairEncode017.payload a).length+
      (PA17TMRatArithmeticPairEncode017.payload b).length+1)^2

theorem original_pair_fee_le (fieldA fieldB : SourceField) (memory j : Nat) (first : RecordSpec)
    (records : List RecordSpec) (nxTail dxTail nyTail dyTail : List Bool) (gap a b : Nat) :
    originalPairFee fieldA fieldB memory j first records nxTail dxTail nyTail dyTail gap a b≤
      originalPairTime fieldA fieldB memory j first records nxTail dxTail nyTail dyTail gap a b := by
  have ha := original_bank_row_fee_le fieldA .plain j gap first records nxTail dxTail nyTail dyTail []
  have hb := original_bank_row_fee_le fieldB .shared j gap first records nxTail dxTail nyTail dyTail
    (restoredDigits fieldA memory nxTail dxTail nyTail dyTail)
  unfold originalPairFee originalReadyFee originalFirstFee originalPairTime
  omega

theorem denominatorX_restored (memory : Nat) (x y : Rat) (holds : memory%32=(mNx x y).val) :
    restoredDigits .dx memory (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=PA17TMRatArithmeticPairEncode017.payload x.den := by
  rw [actual_restored_with_carry .dx memory x y holds]
  rfl

theorem denominatorY_restored (memory : Nat) (x y : Rat) (holds : memory%32=(mNx x y).val) :
    restoredDigits .dy memory (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=PA17TMRatArithmeticPairEncode017.payload y.den := by
  rw [actual_restored_with_carry .dy memory x y holds]
  rfl

def denominatorInput (x y : Rat) (counter : List Bool) (first : RecordSpec)
    (records : List RecordSpec) (gap : Nat) : Tape Bool :=
  originalWorkHeader (PA17TMRatArithmeticParse002.sign x) counter
    (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
    first records gap

def denominatorOutput (x y : Rat) (counter : List Bool) (first : RecordSpec)
    (records : List RecordSpec) (gap : Nat) : Tape Bool :=
  originalNativeInput (PA17TMRatArithmeticParse002.sign x) counter
    (numeratorDigits x).tail (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail
    first records gap x.den y.den

def denominatorFee (memory j : Nat) (x y : Rat) (first : RecordSpec) (records : List RecordSpec)
    (gap : Nat) : Nat :=
  originalPairFee .dx .dy memory j first records (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail gap x.den y.den

/-- This is an internal row contract after the actual allocator/control
producer. The code fixes Dx/Dy and j before all x/y, including x=0 or y=0.
The hold fact is the preserved real014 incoming row, never a raw input. -/
theorem denominator_contract (p j : Nat) (memory : Fin (p+1)) (x y : Rat)
    (holds : memory.val%32=(mNx x y).val) (counter : List Bool) (first : RecordSpec)
    (records : List RecordSpec) (hj : records.length=j) (gap : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (originalPairMachine p .dx .dy j)
        (blockCfg memory (⟨0,denominatorInput x y counter first records gap⟩ : MachineState (originalPairCap j))) trace
        (blockCfg memory (⟨originalPairPort j,denominatorOutput x y counter first records gap⟩ :
          MachineState (originalPairCap j))) ∧
      trace.length≤denominatorFee memory.val j x y first records gap ∧
      ∀ k inputLength, visitedSpace (originalPairMachine p .dx .dy j) inputLength (trace.take k)≤
        inputLength+2*denominatorFee memory.val j x y first records gap+1 := by
  have ha : restoredDigits .dx memory.val (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=PA17TMRatArithmeticPairEncode017.payload x.den :=
    denominatorX_restored memory.val x y holds
  have hb : restoredDigits .dy memory.val (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=PA17TMRatArithmeticPairEncode017.payload y.den :=
    denominatorY_restored memory.val x y holds
  exact original_pair_contract p .dx .dy j memory first records hj
    (PA17TMRatArithmeticParse002.sign x) counter (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail gap x.den y.den ha hb

theorem denominator_carry_preserved (p j : Nat) (memory : Fin (p+1)) :
    phaseOf (label memory (originalPairPort j))=memory := phaseOf_label _ _

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPair054

