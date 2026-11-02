module
public import Structure.PA17_TM_RatArithmetic_MulClosure_059a
public import Structure.PA17_TM_RatArithmetic_FirstRaw_052c
public import Structure.PA17_TM_RatArithmetic_CachedPair_054f

/-! Exact physical boundaries between the already-executed components.
Only terminal FALSE descriptors in the genuine right blank tail are
identified. No internal guard, OWN, source, cache or head is removed. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulClosure059

open Turing PA17TMRatArithmeticWidth018 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticCachedPass036
open PA17TMRatArithmeticCachedOuter043 PA17TMRatArithmeticMulFields048
open PA17TMRatArithmeticWideCache045 PA17TMRatArithmeticCachedPair054
open PA17TMRatArithmeticNativeTail055 (resultRecord)

def bankHeader (x y : Rat) (records : List RecordSpec) : Tape Bool :=
  Tape.mk₂ [false] (prefixRight (sign x) (originalBank x y (bankTail records [])))

def bankWork (x y : Rat) (first : RecordSpec) (later : List RecordSpec) (gap : Nat) : Tape Bool :=
  originalWorkHeader (sign x) [false] (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail first later gap

def bankNative (x y : Rat) (first : RecordSpec) (later : List RecordSpec) (gap a b : Nat) : Tape Bool :=
  originalNativeInput (sign x) [false] (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail first later gap a b

theorem home_is_header (x y : Rat) (first : RecordSpec) (later : List RecordSpec) :
    PA17TMRatArithmeticReturnHome037.homeOutput (sign x) [false]
      (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) first later []=
      bankHeader x y (first::later) := rfl

theorem first_is_header (x y : Rat) (gap : Nat) :
    PA17TMRatArithmeticFirstMul051.firstCycleOutput x y [false] gap=
      bankHeader x y [resultRecord gap (productMagnitude x y)] := rfl

private theorem header_word_append (x y : Rat) (records : List RecordSpec) (word suffix : List Bool) :
    prefixRight (sign x) (originalBank x y (bankTail records (word++suffix)))=
      prefixRight (sign x) (originalBank x y (bankTail records word))++suffix := by
  simp only [bankTail_append,originalBank,prefixRight,bank,nxStream,List.append_assoc,List.cons_append]

private theorem initial_workspace_descriptor (gap : Nat) :
    PA17TMRatArithmeticCachedLoad038.copyWork .plain gap [] []=
      gapWord gap++[false,false,false] := by
  unfold PA17TMRatArithmeticCachedLoad038.copyWork PA17TMRatArithmeticCachedLoad038.plainWorkSuffix
    PA17TMRatArithmeticFarLoad031.workSuffix PA17TMRatArithmeticCopy006.workspace
    gapWord PA17TMRatArithmeticAllocatePass023.gapTail PSTRTMIncrement009.blocks
  simp only [List.flatMap_nil,List.nil_append,List.append_assoc,List.cons_append]

/-- The real allocator already made its far TRUE anchor. The future
loader still really writes OWN00; the three FALSEs here are blank notation. -/
theorem allocated_is_work (x y : Rat) (first : RecordSpec) (later : List RecordSpec) (gap : Nat) :
    Tape.mk₂ [false] (prefixRight (sign x) (originalBank x y (cachedTail (first::later) gap)))=
      bankWork x y first later gap := by
  unfold bankWork originalWorkHeader headerInput PA17TMRatArithmeticMul047.sourceHeaderTape
  rw [PA17TMRatArithmeticPairInput050.sourceBank_widthBank]
  change Tape.mk₂ [false] (prefixRight (sign x) (originalBank x y (cachedTail (first::later) gap)))=
    Tape.mk₂ [false] (prefixRight (sign x) (originalBank x y (bankTail (first::later)
      (PA17TMRatArithmeticCachedLoad038.copyWork .plain gap [] []))))
  rw [initial_workspace_descriptor,header_word_append]
  change Tape.mk₂ [false] (prefixRight (sign x) (originalBank x y (bankTail (first::later) (gapWord gap))))=
    Tape.mk₂ [false] (prefixRight (sign x) (originalBank x y (bankTail (first::later) (gapWord gap)))++
      [false,false,false])
  symm
  have blank := PA17TMRatArithmeticNativeRecord022.right_blank_reserve [false]
    (prefixRight (sign x) (originalBank x y (bankTail (first::later) (gapWord gap)))) 3
  simpa only [show List.replicate 3 false=[false,false,false] from rfl,List.append_nil] using blank

theorem native_is_tail_input (x y : Rat) (first : RecordSpec) (later : List RecordSpec) (gap a b : Nat) :
    bankNative x y first later gap a b=
      PA17TMRatArithmeticNativeTail055.tailInput (sign x) [false]
        (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
        (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) first later gap a b := by
  exact original_native_tail_geometry (sign x) [false] (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail first later gap a b

theorem tail_output_is_header (x y : Rat) (first : RecordSpec) (later : List RecordSpec) (gap value : Nat) :
    PA17TMRatArithmeticNativeTail055.tailOutput (sign x) [false]
      (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) first later gap value=
      bankHeader x y (first::(later++[resultRecord gap value])) := rfl

theorem last_record_is_zero_input (x y : Rat) (m d g u v : RecordSpec)
    (hu : u.digits=PSTRTMNatValue017.rawPayload (quotientNumerator x y)) :
    PA17TMRatArithmeticReturnHome037.homeInput (sign x) [false]
      (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m [d,g,u,v] []=
      PA17TMRatArithmeticReturnHome037.homeInput (sign x) [false]
        (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
        (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m
        (PA17TMRatArithmeticZeroCarry058.observedRecords [d,g] [v] u.gap (quotientNumerator x y)) [] := by
  have record_eq : u=resultRecord u.gap (quotientNumerator x y) := by
    cases u
    simp_all only [resultRecord]
  rw [record_eq]
  rfl

theorem zero_output_is_header (x y : Rat) (m d g u v : RecordSpec)
    (hu : u.digits=PSTRTMNatValue017.rawPayload (quotientNumerator x y)) :
    PA17TMRatArithmeticReturnHome037.homeOutput (sign x) [false]
      (false::(numeratorDigits x).tail) (false::(denominatorDigits x).tail)
      (false::(numeratorDigits y).tail) (false::(denominatorDigits y).tail) m
      (PA17TMRatArithmeticZeroCarry058.observedRecords [d,g] [v] u.gap (quotientNumerator x y)) []=
      bankHeader x y [m,d,g,u,v] := by
  have record_eq : u=resultRecord u.gap (quotientNumerator x y) := by
    cases u
    simp_all only [resultRecord]
  rw [record_eq]
  rfl

theorem original_native_scale_room (x y : Rat) :
    PA17TMRatArithmeticNativeCache030.window x.den y.den-2≤allocationK*(fieldWidth x y)^2 := by
  have hw : 1≤fieldWidth x y := by have h := fieldWidth_ge_four x y;omega
  exact allocated_room _ _ _ hw (five_scales x y).2.1

theorem cached_native_scale_rooms (x y : Rat) :
    PA17TMRatArithmeticNativeCache030.window (productMagnitude x y) (productDenominator x y)-2≤allocationK*(fieldWidth x y)^2 ∧
    PA17TMRatArithmeticNativeCache030.window (productMagnitude x y) (normalizer x y)-2≤allocationK*(fieldWidth x y)^2 ∧
    PA17TMRatArithmeticNativeCache030.window (productDenominator x y) (normalizer x y)-2≤allocationK*(fieldWidth x y)^2 := by
  have hw : 1≤fieldWidth x y := by have h := fieldWidth_ge_four x y;omega
  exact ⟨allocated_room _ _ _ hw (five_scales x y).2.2.1,
    allocated_room _ _ _ hw (five_scales x y).2.2.2.1,
    allocated_room _ _ _ hw (five_scales x y).2.2.2.2⟩

theorem all_result_widths (x y : Rat) :
    natBits (productMagnitude x y)≤fieldWidth x y ∧ natBits (productDenominator x y)≤fieldWidth x y ∧
    natBits (normalizer x y)≤fieldWidth x y ∧ natBits (quotientNumerator x y)≤fieldWidth x y ∧
    natBits (quotientDenominator x y)≤fieldWidth x y :=
  ⟨productMagnitude_bits x y,productDenominator_bits x y,normalizer_bits x y,(normalized_bits x y).1,(normalized_bits x y).2⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulClosure059
