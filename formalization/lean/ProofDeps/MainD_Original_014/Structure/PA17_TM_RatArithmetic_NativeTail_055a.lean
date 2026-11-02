module
public import Structure.PA17_TM_RatArithmetic_WideCache_045b
public import Structure.PA17_TM_RatArithmetic_ReturnHome_037b

/-! The four calls after the first M cache use the same actual native
record writer and physical returnHome program. Values and prior records
occur only in tape contracts, never in the finite code. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNativeTail055

open Turing PA17TMRatArithmeticWidth018 PA17TMRatArithmeticNativeRecord022
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticReturnHome037

def nativeRecordCap (states : Nat) : Nat := 5+(states+27+1)+1

def tailCap (states j : Nat) : Nat := nativeRecordCap states+homeCap (j+1)+1

def nativeTailMachine {states : Nat} (native : Machine states) (j : Nat) :
    Machine (tailCap states j) :=
  PSTRTMSeq005.seqMachine (recordMachine native) (returnHomeMachine (j+1))

def tailPort (states j : Nat) : Fin (tailCap states j+1) :=
  PSTRTMSeq005.rightLabel (a:=nativeRecordCap states) (homePort (j+1))

def lastArchive (sx : Bool) (counter nx dx ny dy : List Bool) (first : RecordSpec)
    (later : List RecordSpec) : List Bool :=
  bankLeft (firstLeft sx counter nx dx ny dy first) later

def tailInput (sx : Bool) (counter nx dx ny dy : List Bool) (first : RecordSpec)
    (later : List RecordSpec) (gap a b : Nat) : Tape Bool :=
  Tape.mk₂ (false::true::(List.replicate gap false++
    true::lastArchive sx counter nx dx ny dy first later)) (encodeNat a++encodeNat b)

def resultRecord (gap value : Nat) : RecordSpec := ⟨gap,PSTRTMNatValue017.rawPayload value⟩

def tailOutput (sx : Bool) (counter nx dx ny dy : List Bool) (first : RecordSpec)
    (later : List RecordSpec) (newGap value : Nat) : Tape Bool :=
  homeOutput sx counter nx dx ny dy first (later++[resultRecord newGap value]) []

def tailFee (j : Nat) (first : RecordSpec) (later : List RecordSpec)
    (nx dx ny dy : List Bool) (newGap a b value : Nat) : Nat :=
  65536*(PA17TMRatArithmeticNativeCache030.scale a b)^2+
    (totalGap (first::later)+newGap+2*(totalWidth (first::later)+natBits value)+
      12*(j+1)+2*bankWidth nx dx ny dy+49)

theorem tailCap_eq (states j : Nat) : tailCap states j=states+13*j+99 := by
  simp only [tailCap,nativeRecordCap,homeCap_eq]
  omega

theorem tailPort_value (states j : Nat) : (tailPort states j).val=tailCap states j := by
  have h34 : (34 : Fin 35).val=34 := by decide
  simp only [tailPort,PSTRTMSeq005.rightLabel,homePort,firstCap,homeCap,
    PA17TMRatArithmeticBankWalk033.backwardCap_eq,nativeRecordCap,tailCap,h34]
  omega

theorem bankLeft_append (archive : List Bool) (left right : List RecordSpec) :
    bankLeft archive (left++right)=bankLeft (bankLeft archive left) right := by
  induction left generalizing archive with
  | nil => rfl
  | cons item rest ih => exact ih _

theorem totalGap_append (left right : List RecordSpec) :
    totalGap (left++right)=totalGap left+totalGap right := by
  induction left with
  | nil => simp only [List.nil_append,totalGap,Nat.zero_add]
  | cons item rest ih => simp only [List.cons_append,totalGap,ih,Nat.add_assoc]

theorem totalWidth_append (left right : List RecordSpec) :
    totalWidth (left++right)=totalWidth left+totalWidth right := by
  induction left with
  | nil => simp only [List.nil_append,totalWidth,Nat.zero_add]
  | cons item rest ih => simp only [List.cons_append,totalWidth,ih,Nat.add_assoc]

theorem newRecord_home (sx : Bool) (counter nx dx ny dy : List Bool) (first : RecordSpec)
    (later : List RecordSpec) (newGap value : Nat) :
    Tape.mk₂ (PA17TMRatArithmeticStore019.recordLeft
      (List.replicate newGap false++true::lastArchive sx counter nx dx ny dy first later) value) [true]=
      homeInput sx counter nx dx ny dy first (later++[resultRecord newGap value]) [] := by
  simp only [homeInput,bankEnd,bankLeft_append,bankLeft]
  rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNativeTail055
