module
public import Structure.PA17_TM_RatArithmetic_PairInput_050c
public import Structure.PA17_TM_RatArithmetic_Outer_025e

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairInput050

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticFarLoad031 PA17TMRatArithmeticBookmark014
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticSignRead021
attribute [local implicit_reducible] pairCap totalStates

theorem sourceSlot_lt_five (field : SourceField) : sourceSlot field<5 := by
  cases field <;> decide

theorem low_carry_bit (field : SourceField) (memory : Nat) (old : Fin 32)
    (holds : memory%32=old.val) : memory.testBit (sourceSlot field)=old.val.testBit (sourceSlot field) := by
  have hlt := sourceSlot_lt_five field
  have h : (memory%32).testBit (sourceSlot field)=memory.testBit (sourceSlot field) := by
    simpa only [show (2 : Nat)^5=32 from rfl,decide_eq_true hlt,Bool.true_and] using
      Nat.testBit_mod_two_pow memory 5 (sourceSlot field)
  rw [←h,holds]

/-- The only canonical restoration facts come from014's actual read/clear
trace and the old-memory part of a real incoming row. SX high carry is opaque. -/
theorem actual_restored_with_carry (field : SourceField) (memory : Nat) (x y : Rat)
    (holds : memory%32=(mNx x y).val) :
    restoredDigits field memory (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=originalDigits field x y := by
  rw [restoredDigits,low_carry_bit field memory (mNx x y) holds]
  exact actual_restored_source field x y

def firstMInput (x y : Rat) (counter : List Bool) (gap : Nat) : Tape Bool := ratHeaderTape x y counter gap
def firstMOutput (x y : Rat) (counter : List Bool) (gap : Nat) : Tape Bool :=
  nativeInputTape (sign x) counter (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail gap x.num.natAbs y.num.natAbs

def firstMFee (memory : Nat) (x y : Rat) (gap : Nat) : Nat :=
  pairFee .nx .ny memory (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail gap x.num.natAbs y.num.natAbs

/-- The49 allocator's actual header tape and the031 loader entry differ
only by displayed zero cells at the genuine far-right blank tail. -/
theorem firstMInput_allocator (x y : Rat) (counter : List Bool) (gap : Nat) :
    firstMInput x y counter gap=Tape.mk₂ counter (PA17TMRatArithmeticWidth018.prefixRight (sign x)
      (PA17TMRatArithmeticOuter025.bankAt x y gap)) := by
  let word := PA17TMRatArithmeticWidth018.prefixRight (sign x) (PA17TMRatArithmeticOuter025.bankAt x y gap)
  have right : PA17TMRatArithmeticWidth018.prefixRight (sign x)
      (sourceBank (numeratorDigits x).tail (denominatorDigits x).tail
        (numeratorDigits y).tail (denominatorDigits y).tail (workSuffix gap []))=word++[false,false,false] := by
    simp only [sourceBank_widthBank,word,PA17TMRatArithmeticOuter025.bankAt,
      PA17TMRatArithmeticWidth018.originalBank,clampFirst,workSuffix,PA17TMRatArithmeticCopy006.workspace,
      PA17TMRatArithmeticWidth018.prefixRight,PA17TMRatArithmeticWidth018.bank,PA17TMRatArithmeticWidth018.nxStream,
      PSTRTMIncrement009.blocks,List.flatMap_nil,List.append_assoc,List.cons_append,List.nil_append]
  have blank : Tape.mk₂ counter (word++[false,false,false])=Tape.mk₂ counter word := by
    calc
      _ = Tape.mk₂ counter (((word++[false])++[false])++[false]) := by
        simp only [List.append_assoc,List.cons_append,List.nil_append]
      _ = _ := by rw [PA17TMRatArithmeticPairEncode017.tape_trailing_false,
        PA17TMRatArithmeticPairEncode017.tape_trailing_false,PA17TMRatArithmeticPairEncode017.tape_trailing_false]
  change Tape.mk₂ counter (PA17TMRatArithmeticWidth018.prefixRight (sign x)
    (sourceBank (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail (workSuffix gap [])))=_
  rw [right]
  exact blank

/-- Concrete first multiplication arguments, fixed .nx/.ny code before
ALL x/y. The carry invariant is an internal producer poststate fact, not
an original input qualification. The49 frontend physically supplies it. -/
theorem firstM_contract (p : Nat) (memory : Fin (p+1)) (x y : Rat)
    (holds : memory.val%32=(mNx x y).val) (counter : List Bool) (gap : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (pairInputMachine p .nx .ny)
        ⟨pairEntry p memory,firstMInput x y counter gap⟩ trace
        ⟨pairPort p memory,firstMOutput x y counter gap⟩ ∧
      trace.length≤firstMFee memory.val x y gap ∧
      ∀ prefixLength chargedL, visitedSpace (pairInputMachine p .nx .ny) chargedL (trace.take prefixLength)≤
        chargedL+2*firstMFee memory.val x y gap+1 := by
  have ha : restoredDigits .nx memory.val (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=PA17TMRatArithmeticPairEncode017.payload x.num.natAbs := by
    simpa only [originalDigits,numeratorDigits,PA17TMRatArithmeticPairEncode017.payload] using
      actual_restored_with_carry .nx memory.val x y holds
  have hb : restoredDigits .ny memory.val (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=PA17TMRatArithmeticPairEncode017.payload y.num.natAbs := by
    simpa only [originalDigits,numeratorDigits,PA17TMRatArithmeticPairEncode017.payload] using
      actual_restored_with_carry .ny memory.val x y holds
  exact pairInput_contract p .nx .ny memory (sign x) counter (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail gap x.num.natAbs y.num.natAbs ha hb

/-- This is the actual64-row form consumed AFTER049's physical SX read.
selectedMemory names its real exit interpretation; no free entry relabel
from the original input is claimed here. -/
theorem firstM64_contract (x y : Rat) (counter : List Bool) (gap : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (pairInputMachine 63 .nx .ny)
        ⟨pairEntry 63 (selectedMemory (mNx x y) (sign x)),firstMInput x y counter gap⟩ trace
        ⟨pairPort 63 (selectedMemory (mNx x y) (sign x)),firstMOutput x y counter gap⟩ ∧
      trace.length≤firstMFee (selectedMemory (mNx x y) (sign x)).val x y gap ∧
      ∀ prefixLength chargedL, visitedSpace (pairInputMachine 63 .nx .ny) chargedL (trace.take prefixLength)≤
        chargedL+2*firstMFee (selectedMemory (mNx x y) (sign x)).val x y gap+1 :=
  firstM_contract 63 _ x y (selectedMemory_retains_old _ _) counter gap

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairInput050
