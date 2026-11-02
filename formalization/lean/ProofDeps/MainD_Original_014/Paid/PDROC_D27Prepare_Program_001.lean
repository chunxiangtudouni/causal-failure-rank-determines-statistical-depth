module

public import Paid.PDCompute_SolverSlotMoves_025
public import Paid.PDMenu_ComputeFrame_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDROC.D27Prepare.Program

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (loadSlot storeSlot linearExecute)
open PDCompute.Solver (constantSlot copySlot ratBinarySlots)
open PDMenu.ComputeFrame

/- Parameter-independent addresses; the original six input and thirteen
output cells retain their original order. All stores are below 64. -/
namespace Slot
abbrev stages := 0
abbrev tools := 1
abbrev gamma := 2
abbrev risk := 3
abbrev reviewFee := 4
abbrev fee := 5
abbrev t0 := 6
abbrev M := 7
abbrev E := 8
abbrev Q := 9
abbrev J := 10
abbrev Lambda := 11
abbrev zeta := 12
abbrev natZero := 13
abbrev natOne := 14
abbrev natTwo := 15
abbrev ratZero := 16
abbrev ratOne := 17
abbrev ratTwo := 18
abbrev ratThree := 19
abbrev ratFour := 20
abbrev ratHalf := 21
abbrev ratStages := 22
abbrev ratT0 := 23
abbrev gammaSquared := 24
abbrev variance := 25
abbrev varianceSquared := 26
abbrev majorityThreshold := 27
abbrev power := 28
abbrev menuRatio := 29
abbrev odds := 30
abbrev exponentThreshold := 31
abbrev workA := 32
abbrev workB := 33
abbrev workC := 34
abbrev dyadicCounter := 35
abbrev dyadic := 39
abbrev binomialIndex := 40
abbrev binomialChoose := 41
abbrev binomialTail := 42
abbrev firstFloor := 43
abbrev positiveFloor := 44
abbrev budgetRatio := 45
abbrev budgetCeil := 46
abbrev budgetHalve := 47
abbrev binomialRemaining := 48
abbrev binomialNext := 49
abbrev binomialRatio := 50
abbrev firstCeil := 52
abbrev secondCeil := 53
end Slot

abbrev pageWidth : ℕ := 256
abbrev pageCount : ℕ := 46
abbrev heapBound : ℕ := 64

def pc (page : ℕ) : ℕ := pageWidth*page

def go (page : ℕ) : List Instruction := [.jump (pc page)]

def branch (whenZero whenNonzero : ℕ) : List Instruction :=
  [.branchZero .flag (pc whenZero) (pc whenNonzero)]

/-- These additional macros are literal original ISA instructions, not
host arithmetic. As with the frozen rational macro, both reads precede
any write, so aliases are allowed. -/
def natBinarySlots (operation : NatOp) (left right target : ℕ) : List Instruction :=
  loadSlot left .total ++ loadSlot right .value ++
    [.natOp operation .total .total .value] ++ storeSlot target .total

def natToRatSlot (source target : ℕ) : List Instruction :=
  loadSlot source .total ++ [.natToRat .total .total] ++ storeSlot target .total

def natCompareSlots (comparison : Comparison) (left right : ℕ) : List Instruction :=
  loadSlot left .total ++ loadSlot right .value ++ [.natCompare comparison .flag .total .value]

def ratCompareSlots (comparison : Comparison) (left right : ℕ) : List Instruction :=
  loadSlot left .total ++ loadSlot right .value ++ [.ratCompare comparison .flag .total .value]

def inputSlot (address : ℕ) : List Instruction :=
  [.constant .address (.natural address),.loadInput .total .address] ++ storeSlot address .total

/-- For a nonnegative rational in source: write the integer quotient to
target and leave the remainder in flag. Denominators of rational cells
are positive. The following page increments exactly when flag is nonzero. -/
def ceilCore (source target : ℕ) : List Instruction :=
  loadSlot source .total ++
    [.numeratorAbs .old .total,.denominator .value .total,
      .natOp .divide .total .old .value] ++ storeSlot target .total ++
    [.natOp .modulo .flag .old .value]

def outputSlot (address : ℕ) : List Instruction := loadSlot address .total ++ [.output .total]

def prologue : List Instruction :=
  [.constant .fresh (.natural 0)] ++ (List.range 6).flatMap inputSlot ++
    constantSlot Slot.natZero (.natural 0) ++ constantSlot Slot.natOne (.natural 1) ++
    constantSlot Slot.natTwo (.natural 2) ++ constantSlot Slot.ratZero (.rational 0) ++
    constantSlot Slot.ratOne (.rational 1) ++ constantSlot Slot.ratTwo (.rational 2) ++
    constantSlot Slot.ratThree (.rational 3) ++ constantSlot Slot.ratFour (.rational 4) ++
    constantSlot Slot.ratHalf (.rational (1/2)) ++
    constantSlot Slot.t0 (.natural 1) ++ constantSlot Slot.M (.natural 0) ++
    constantSlot Slot.E (.natural 1) ++ constantSlot Slot.Q (.natural 1) ++
    constantSlot Slot.J (.natural 0) ++ go 1

def majoritySetup : List Instruction :=
  natToRatSlot Slot.stages Slot.ratStages ++
    ratBinarySlots .multiply Slot.gamma Slot.gamma Slot.gammaSquared ++
    ratBinarySlots .multiply Slot.ratFour Slot.gammaSquared Slot.workA ++
    ratBinarySlots .subtract Slot.ratOne Slot.workA Slot.variance ++
    ratBinarySlots .multiply Slot.variance Slot.variance Slot.varianceSquared ++
    ratBinarySlots .multiply Slot.ratTwo Slot.ratStages Slot.workA ++
    ratBinarySlots .divide Slot.risk Slot.workA Slot.workB ++
    ratBinarySlots .multiply Slot.workB Slot.workB Slot.majorityThreshold ++
    copySlot Slot.variance Slot.power

def majorityGuard : List Instruction := ratCompareSlots .lessEqual Slot.power Slot.majorityThreshold

def majorityStep : List Instruction :=
  natBinarySlots .add Slot.t0 Slot.natTwo Slot.t0 ++
    ratBinarySlots .multiply Slot.power Slot.varianceSquared Slot.power

def endpointSetup : List Instruction :=
  natToRatSlot Slot.t0 Slot.ratT0 ++
    ratBinarySlots .multiply Slot.ratFour Slot.ratStages Slot.workA ++
    ratBinarySlots .multiply Slot.workA Slot.ratT0 Slot.workA ++
    ratBinarySlots .divide Slot.risk Slot.workA Slot.menuRatio ++
    ratBinarySlots .multiply Slot.ratTwo Slot.gamma Slot.workA ++
    ratBinarySlots .add Slot.ratOne Slot.workA Slot.workB ++
    ratBinarySlots .subtract Slot.ratOne Slot.workA Slot.workC ++
    ratBinarySlots .divide Slot.workB Slot.workC Slot.odds ++
    copySlot Slot.ratOne Slot.power

def endpointGuard : List Instruction :=
  ratBinarySlots .add Slot.ratOne Slot.power Slot.workA ++
    ratBinarySlots .multiply Slot.menuRatio Slot.workA Slot.workA ++
    ratCompareSlots .lessEqual Slot.ratOne Slot.workA

def endpointStep : List Instruction :=
  natBinarySlots .add Slot.M Slot.natOne Slot.M ++
    ratBinarySlots .multiply Slot.power Slot.odds Slot.power

def exponentSetup : List Instruction :=
  ratBinarySlots .divide Slot.menuRatio Slot.ratThree Slot.workA ++
    ratBinarySlots .multiply Slot.gamma Slot.workA Slot.exponentThreshold ++
    copySlot Slot.ratHalf Slot.power

def exponentGuard : List Instruction := ratCompareSlots .lessEqual Slot.power Slot.exponentThreshold

def exponentStep : List Instruction :=
  natBinarySlots .add Slot.E Slot.natOne Slot.E ++
    ratBinarySlots .multiply Slot.power Slot.ratHalf Slot.power

def firstCeilSetup : List Instruction :=
  natToRatSlot Slot.M Slot.workA ++
    ratBinarySlots .add Slot.workA Slot.ratOne Slot.workA ++
    ratBinarySlots .divide Slot.workA Slot.gamma Slot.workA

def secondCeilSetup : List Instruction :=
  natToRatSlot Slot.E Slot.workA ++
    ratBinarySlots .multiply Slot.ratTwo Slot.workA Slot.workA ++
    ratBinarySlots .divide Slot.workA Slot.gammaSquared Slot.workA

def multiplierSetup : List Instruction :=
  ratBinarySlots .multiply Slot.ratFour Slot.reviewFee Slot.workA ++
    ratBinarySlots .multiply Slot.workA Slot.ratStages Slot.workA ++
    ratBinarySlots .multiply Slot.workA Slot.ratT0 Slot.workA ++
    ratBinarySlots .divide Slot.workA Slot.risk Slot.Lambda ++
    copySlot Slot.natZero Slot.dyadicCounter ++ copySlot Slot.ratOne Slot.dyadic

def dyadicStep : List Instruction :=
  natBinarySlots .add Slot.dyadicCounter Slot.natOne Slot.dyadicCounter ++
    ratBinarySlots .multiply Slot.dyadic Slot.ratHalf Slot.dyadic

def binomialSetup : List Instruction :=
  copySlot Slot.natZero Slot.binomialIndex ++ copySlot Slot.ratOne Slot.binomialChoose ++
    copySlot Slot.ratZero Slot.binomialTail

def binomialStep : List Instruction :=
  natBinarySlots .subtract Slot.stages Slot.binomialIndex Slot.binomialRemaining ++
    natBinarySlots .add Slot.binomialIndex Slot.natOne Slot.binomialNext ++
    natToRatSlot Slot.binomialRemaining Slot.workA ++ natToRatSlot Slot.binomialNext Slot.workB ++
    ratBinarySlots .divide Slot.workA Slot.workB Slot.binomialRatio ++
    ratBinarySlots .multiply Slot.binomialChoose Slot.binomialRatio Slot.binomialChoose ++
    copySlot Slot.binomialNext Slot.binomialIndex

def positiveFloorSetup : List Instruction :=
  ratBinarySlots .subtract Slot.zeta Slot.risk Slot.workA ++
    ratBinarySlots .multiply Slot.firstFloor Slot.workA Slot.positiveFloor ++
    ratCompareSlots .less Slot.ratZero Slot.positiveFloor

def budgetRatioSetup : List Instruction :=
  ratBinarySlots .multiply Slot.ratTwo Slot.Lambda Slot.workA ++
    ratBinarySlots .multiply Slot.workA Slot.risk Slot.workA ++
    ratBinarySlots .divide Slot.workA Slot.positiveFloor Slot.budgetRatio

def budgetHalveSetup : List Instruction :=
  natBinarySlots .subtract Slot.budgetCeil Slot.natOne Slot.budgetHalve ++
    copySlot Slot.natZero Slot.J

def budgetHalveStep : List Instruction :=
  natBinarySlots .divide Slot.budgetHalve Slot.natTwo Slot.budgetHalve ++
    natBinarySlots .add Slot.J Slot.natOne Slot.J

def emitPrepared : List Instruction := (List.range 13).flatMap outputSlot

/-- The only program text. The page selector and its padding are finite,
parameter-independent code construction; no input is evaluated here. -/
def pageCode : ℕ → List Instruction
  | 0 => prologue
  | 1 => majoritySetup ++ go 2
  | 2 => majorityGuard ++ branch 3 4
  | 3 => majorityStep ++ go 2
  | 4 => endpointSetup ++ go 5
  | 5 => endpointGuard ++ branch 6 7
  | 6 => endpointStep ++ go 5
  | 7 => exponentSetup ++ go 8
  | 8 => exponentGuard ++ branch 9 10
  | 9 => exponentStep ++ go 8
  | 10 => firstCeilSetup ++ go 11
  | 11 => ceilCore Slot.workA Slot.firstCeil ++ branch 13 12
  | 12 => natBinarySlots .add Slot.firstCeil Slot.natOne Slot.firstCeil ++ go 13
  | 13 => secondCeilSetup ++ go 14
  | 14 => ceilCore Slot.workA Slot.secondCeil ++ branch 16 15
  | 15 => natBinarySlots .add Slot.secondCeil Slot.natOne Slot.secondCeil ++ go 16
  | 16 => natCompareSlots .less Slot.firstCeil Slot.secondCeil ++ branch 17 18
  | 17 => copySlot Slot.firstCeil Slot.Q ++ go 19
  | 18 => copySlot Slot.secondCeil Slot.Q ++ go 19
  | 19 => natCompareSlots .less Slot.Q Slot.natOne ++ branch 21 20
  | 20 => copySlot Slot.natOne Slot.Q ++ go 21
  | 21 => multiplierSetup ++ go 22
  | 22 => natCompareSlots .less Slot.dyadicCounter Slot.stages ++ branch 24 23
  | 23 => dyadicStep ++ go 22
  | 24 => ratCompareSlots .equal Slot.fee Slot.ratZero ++ branch 25 26
  | 25 => ratBinarySlots .subtract Slot.ratOne Slot.dyadic Slot.zeta ++ go 32
  | 26 => binomialSetup ++ go 27
  | 27 => natCompareSlots .lessEqual Slot.binomialIndex Slot.stages ++ branch 31 28
  | 28 => natCompareSlots .less Slot.tools Slot.binomialIndex ++ branch 30 29
  | 29 => ratBinarySlots .add Slot.binomialTail Slot.binomialChoose Slot.binomialTail ++ go 30
  | 30 => binomialStep ++ go 27
  | 31 => ratBinarySlots .multiply Slot.binomialTail Slot.dyadic Slot.zeta ++ go 32
  | 32 => ratCompareSlots .equal Slot.fee Slot.ratZero ++ branch 34 33
  | 33 => copySlot Slot.reviewFee Slot.firstFloor ++ go 37
  | 34 => ratCompareSlots .lessEqual Slot.reviewFee Slot.fee ++ branch 36 35
  | 35 => copySlot Slot.reviewFee Slot.firstFloor ++ go 37
  | 36 => copySlot Slot.fee Slot.firstFloor ++ go 37
  | 37 => positiveFloorSetup ++ branch 38 39
  | 38 => copySlot Slot.natZero Slot.J ++ go 45
  | 39 => budgetRatioSetup ++ go 40
  | 40 => ceilCore Slot.budgetRatio Slot.budgetCeil ++ branch 42 41
  | 41 => natBinarySlots .add Slot.budgetCeil Slot.natOne Slot.budgetCeil ++ go 42
  | 42 => budgetHalveSetup ++ go 43
  | 43 => natCompareSlots .less Slot.natZero Slot.budgetHalve ++ branch 45 44
  | 44 => budgetHalveStep ++ go 43
  | 45 => emitPrepared ++ [.halt]
  | _ => [.halt]

def program : Program := Array.ofFn fun address : Fin (pageCount*pageWidth) =>
  ((pageCode (address.val/pageWidth))[address.val%pageWidth]?).getD .halt

theorem program_size : program.size = 11776 := by simp [program,pageCount,pageWidth]

theorem pageCode_fits (page : ℕ) : (pageCode page).length < pageWidth := by
  unfold pageCode
  split <;> decide

theorem program_fetch (page offset : ℕ) (hpage : page < pageCount) (hoffset : offset < pageWidth) :
    program[pc page+offset]?=some (((pageCode page)[offset]?).getD .halt) := by
  have hlt : pc page+offset < program.size := by rw [program_size]; dsimp only [pc,pageCount,pageWidth] at *; omega
  rw [Array.getElem?_eq_getElem hlt]
  simp only [program,Array.getElem_ofFn]
  have hd : (pc page+offset)/pageWidth=page := by dsimp only [pc,pageWidth] at *; omega
  have hm : (pc page+offset)%pageWidth=offset := by dsimp only [pc,pageWidth] at *; omega
  simp only [hd,hm]

theorem fetches_page (page : ℕ) (hpage : page < pageCount) :
    FetchesCode program (pc page) (pageCode page) := by
  intro offset hoffset
  rw [program_fetch page offset hpage (hoffset.trans (pageCode_fits page))]
  rw [List.getElem?_eq_getElem hoffset]
  rfl

/-- Any literal straight fragment can be certified using the same actual
fixed program. The resulting witnesses expose all strict-prefix states. -/
theorem literal_fragment_trace (input : List Cell) (code : List Instruction)
    (straight : StraightCode code) (before after : State)
    (fetch : FetchesCode program before.pc code)
    (execute : linearExecute input code before=some after) :
    ∃ trace : List State, trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 15*(code.length+1) ∧
      ∀ state ∈ trace.dropLast, ∃ count < code.length,
        linearExecute input (code.take count) before=some state :=
  linearExecute_trace_time program input code straight before after fetch execute

end PDROC.D27Prepare.Program
