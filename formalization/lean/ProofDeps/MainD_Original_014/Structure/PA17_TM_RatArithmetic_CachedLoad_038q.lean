module
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038n
public import Structure.PA17_TM_RatArithmetic_Mul_047c

/-! Original source through an existing nonempty bank, to either physical
destination. The per-bit route genuinely uses temporary originalTRUE; EOF
instead takes the oldFALSE-preserving forwardAny path. One042 loop only. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticBankWalk033

def copyWork : Destination → Nat → List Bool → List Bool → List Bool
  | .plain, gap, _, copied => plainWorkSuffix gap copied
  | .shared, gap, a, copied => PA17TMRatArithmeticPairExcursion041.workSuffix gap a copied

theorem copyWork_clamped (kind : Destination) (gap : Nat) (a tail : List Bool) :
    copyWork kind gap a (false::tail)=destinationSuffix kind a (copiedTail tail []) gap := by
  have hc : copiedTail tail []=true::(PSTRTMIncrement009.blocks tail++[false,false]) := by
    simp only [copiedTail,List.append_nil]
  rw [hc]
  cases kind with
  | plain =>
    simp only [copyWork,plainWorkSuffix,PA17TMRatArithmeticFarLoad031.workSuffix,
      destinationSuffix,destinationWord,PA17TMRatArithmeticCopy006.workspace,flagged_cons,List.cons_append]
  | shared =>
    simp only [copyWork,PA17TMRatArithmeticPairExcursion041.workSuffix,
      destinationSuffix,destinationWord,PA17TMRatArithmeticCopy006.workspace,flagged_cons,List.cons_append]

def originalBankBeforeCap (j : Nat) : Destination → Nat
  | .plain => plainBeforeCap (originalOutCap j) (originalBackCap j)
  | .shared => PA17TMRatArithmeticMul047.sharedBeforeCap (originalOutCap j) (originalBackCap j)
def originalBankBeforeMachine (route : PA17TMRatArithmeticFarLoad031.FarRoute) (j : Nat) :
    (kind : Destination) → Machine (originalBankBeforeCap j kind)
  | .plain => plainBeforeMachine (originalFarRoute route j)
  | .shared => PA17TMRatArithmeticMul047.sharedBeforeMachine (originalFarRoute route j)
def originalBankBeforePort (j : Nat) : (kind : Destination) → Fin (originalBankBeforeCap j kind+1)
  | .plain => plainBeforePort (originalOutCap j) (originalBackCap j)
  | .shared => PA17TMRatArithmeticMul047.sharedBeforePort (originalOutCap j) (originalBackCap j)
def originalBankBeforeFee (kind : Destination) (cost gap : Nat) (digits a : List Bool) : Nat :=
  match kind with
  | .plain => (4*digits.length+2*cost+2*gap+19)+
      PA17TMRatArithmeticCopyLoop042.loopFee (plainLoopFee cost gap) [] digits
  | .shared => (4*digits.length+2*cost+2*gap+4*a.length+30)+
      PA17TMRatArithmeticCopyLoop042.loopFee (PA17TMRatArithmeticMul047.sharedFee cost gap a) [] digits

def originalBankBeforeTime (cost gap : Nat) (digits a : List Bool) : Nat :=
  4*digits.length^2+(2*cost+2*gap+4*a.length+51)*digits.length+2*cost+2*gap+4*a.length+33

theorem original_bank_before_fee_le (kind : Destination) (cost gap : Nat) (digits a : List Bool) :
    originalBankBeforeFee kind cost gap digits a≤originalBankBeforeTime cost gap digits a := by
  cases kind with
  | plain =>
    have hf : ∀ r c, plainLoopFee cost gap r c≤4*(r.length+c.length)+(2*cost+2*gap+32) := by
      intro r c
      unfold plainLoopFee
      omega
    have hl := PA17TMRatArithmeticCopyLoop042.loopFee_affine (plainLoopFee cost gap)
      4 (2*cost+2*gap+32) hf [] digits
    simp only [List.length_nil] at hl
    have hp : 0≤(4*a.length)*digits.length := Nat.zero_le _
    unfold originalBankBeforeFee originalBankBeforeTime
    nlinarith
  | shared =>
    have hl := PA17TMRatArithmeticMul047.shared_loop_fee_le cost gap a [] digits
    simp only [List.length_nil] at hl
    unfold originalBankBeforeFee originalBankBeforeTime
    nlinarith

theorem original_bank_before_bounded (route : PA17TMRatArithmeticFarLoad031.FarRoute)
    (context : List Bool) (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (correct : PA17TMRatArithmeticFarLoad031.RouteCorrect route context finish cost)
    (j : Nat) (first : RecordSpec) (records : List RecordSpec) (hj : records.length=j)
    (kind : Destination) (archive tail a : List Bool) (gap : Nat) :
    BoundedRun (originalBankBeforeMachine route j kind)
      (Tape.mk₂ (false::archive) (PA17TMRatArithmeticFarLoad031.fieldWord context (false::tail)
        (bankTail (first::records) (copyWork kind gap a [])))) (originalBankBeforePort j kind)
      (Tape.mk₂ (false::PA17TMRatArithmeticFarLoad031.passedLeft (false::archive) (false::tail))
        (context++false::bankTail (first::records) (copyWork kind gap a (false::tail))))
      (originalBankBeforeFee kind (originalFarCost cost j first records) gap (false::tail) a) := by
  have routes := originalFar_correct route context finish cost correct j first records hj
  cases kind with
  | plain =>
    have hb := plain_before_bounded (originalFarRoute route j) (originalFarContext context first records)
      (originalFarFinish finish (first::records)) (originalFarCost cost j first records) gap archive (false::tail) routes rfl
    simpa only [originalBankBeforeMachine,originalBankBeforePort,originalBankBeforeCap,
      originalBankBeforeFee,copyWork,originalFarRoute,originalFarContext_word,
      PA17TMRatArithmeticPairExcursion041.sourceWord,PA17TMRatArithmeticFarLoad031.fieldWord] using hb
  | shared =>
    have hb := PA17TMRatArithmeticMul047.shared_before_bounded (originalFarRoute route j)
      (originalFarContext context first records) (originalFarFinish finish (first::records))
      (originalFarCost cost j first records) gap archive (false::tail) a routes rfl
    simpa only [originalBankBeforeMachine,originalBankBeforePort,originalBankBeforeCap,
      originalBankBeforeFee,copyWork,originalFarRoute,originalFarContext_word,
      PA17TMRatArithmeticPairExcursion041.sourceWord,PA17TMRatArithmeticFarLoad031.fieldWord] using hb

def originalBankCopyCap (j : Nat) (kind : Destination) : Nat :=
  originalBankBeforeCap j kind+originalToDestCap (j+1)+1
def originalBankCopyMachine (route : PA17TMRatArithmeticFarLoad031.FarRoute) (j : Nat) (kind : Destination) :
    Machine (originalBankCopyCap j kind) :=
  PSTRTMSeq005.seqMachine (a:=originalBankBeforeCap j kind) (b:=originalToDestCap (j+1))
    (originalBankBeforeMachine route j kind) (originalToDestMachine route (j+1) kind)
def originalBankCopyPort (j : Nat) (kind : Destination) : Fin (originalBankCopyCap j kind+1) :=
  PSTRTMSeq005.rightLabel (a:=originalBankBeforeCap j kind) (originalToDestPort (j+1) kind)
def originalBankCopyFee (kind : Destination) (cost j gap : Nat) (first : RecordSpec)
    (records : List RecordSpec) (tail a : List Bool) : Nat :=
  originalBankBeforeFee kind (originalFarCost cost j first records) gap (false::tail) a+
    (cost+totalGap (first::records)+2*totalWidth (first::records)+9*(j+1)+3+destinationFee kind a.length gap)

def originalBankCopyTime (kind : Destination) (cost j gap : Nat) (first : RecordSpec)
    (records : List RecordSpec) (tail a : List Bool) : Nat :=
  originalBankBeforeTime (originalFarCost cost j first records) gap (false::tail) a+
    (cost+totalGap (first::records)+2*totalWidth (first::records)+9*(j+1)+3+destinationFee kind a.length gap)

theorem original_bank_copy_fee_le (kind : Destination) (cost j gap : Nat) (first : RecordSpec)
    (records : List RecordSpec) (tail a : List Bool) :
    originalBankCopyFee kind cost j gap first records tail a≤originalBankCopyTime kind cost j gap first records tail a := by
  have h := original_bank_before_fee_le kind (originalFarCost cost j first records) gap (false::tail) a
  unfold originalBankCopyFee originalBankCopyTime
  omega

/-- All original source clamps remain FALSE. Original footer ends FALSE;
all existing records and arbitrary A are preserved. DEST firstDATA is still
physically FALSE until the next actual saved-slot WRITE. -/
theorem original_bank_copy_bounded (route : PA17TMRatArithmeticFarLoad031.FarRoute)
    (context : List Bool) (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (correct : PA17TMRatArithmeticFarLoad031.RouteCorrect route context finish cost)
    (j : Nat) (first : RecordSpec) (records : List RecordSpec) (hj : records.length=j)
    (kind : Destination) (archive tail a : List Bool) (gap : Nat) :
    BoundedRun (originalBankCopyMachine route j kind)
      (Tape.mk₂ (false::archive) (PA17TMRatArithmeticFarLoad031.fieldWord context (false::tail)
        (bankTail (first::records) (copyWork kind gap a [])))) (originalBankCopyPort j kind)
      (Tape.mk₂ (destinationLeft kind
        (bankLeftAny false (finish (false::archive) (false::tail)) (first::records)) a gap true)
        (PA17TMRatArithmeticCopy006.workspace (false::tail)))
      (originalBankCopyFee kind cost j gap first records tail a) := by
  have hb := original_bank_before_bounded route context finish cost correct j first records hj kind archive tail a gap
  have hn : (first::records).length=j+1 := by simp only [List.length_cons,hj]
  have he := original_to_dest_bounded route context finish cost correct (j+1) (first::records) hn kind
    (PA17TMRatArithmeticFarLoad031.passedLeft (false::archive) (false::tail)) a (copiedTail tail []) gap
  rw [PA17TMRatArithmeticFarLoad031.passedLeft_finish route context finish cost correct] at he
  have hc := copyWork_clamped kind gap a tail
  rw [hc] at hb
  have result := hb.seq he
  simpa only [originalBankCopyMachine,originalBankCopyCap,originalBankCopyPort,originalBankCopyFee,
    bankEndBitAny,PA17TMRatArithmeticCopy006.workspace,copiedTail,flagged_cons,
    List.cons_append,List.append_nil] using result

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
