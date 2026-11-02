module
public import Paid.PDCompute_Pack_Code_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver
open PDLower.CalibrationCompute (linearExecute loadSlot)

/-- Literal12-instruction arithmetic fragment at offset28, before any
pointer is stored. Multiplication uses runtime n/k, no host answer. -/
def pointerArithmeticCode : List Instruction :=
  loadSlot rowRemaining .index++loadSlot columnsPerRow .value++
  [.natOp .multiply .total .index .value,.constant .flag (.natural 6),
   .natOp .multiply .total .total .flag,.constant .flag (.natural 48),
   .natOp .add .total .total .flag,.natOp .add .total .total .fresh]

def pointerArithmeticResult (before : State) (base n k : ℕ) : State :=
  {before with register:=Function.update (Function.update (Function.update (Function.update
    (Function.update before.register .address (.natural (base+columnsPerRow))) .index (.natural (n+1)))
      .value (.natural (k+1))) .flag (.natural 48)) .total (.natural (resultBase base n k)),pc:=before.pc+12}

theorem pointerArithmeticCode_length : pointerArithmeticCode.length=12 := rfl

theorem pointerArithmetic_execute (input : List Cell) (before : State) (base n k : ℕ)
    (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (rows : values rowRemaining=.natural (n+1)) (columns : values columnsPerRow=.natural (k+1)) :
    linearExecute input pointerArithmeticCode before=some (pointerArithmeticResult before base n k) := by
  have rowLive:=header.live rowRemaining (by decide)
  have colLive:=header.live columnsPerRow (by decide)
  have rowAt:=(header.value rowRemaining (by decide)).trans rows
  have colAt:=(header.value columnsPerRow (by decide)).trans columns
  simp [pointerArithmeticCode,loadSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
    hbase,rowLive,colLive,rowAt,colAt,pointerArithmeticResult,Nat.add_assoc]
  funext register
  cases register <;>
    simp [resultBase,tableBase,headerWords,entryWords,PDCompute.Solver.entryCount,
      Nat.add_comm,Nat.add_left_comm,Nat.mul_comm,Nat.mul_assoc]

theorem pointerArithmetic_fields (before : State) (base n k : ℕ) :
    (pointerArithmeticResult before base n k).heap=before.heap ∧
    (pointerArithmeticResult before base n k).live=before.live ∧
    (pointerArithmeticResult before base n k).output=before.output ∧
    (pointerArithmeticResult before base n k).register .fresh=before.register .fresh ∧
    (pointerArithmeticResult before base n k).register .total=.natural (resultBase base n k) ∧
    (pointerArithmeticResult before base n k).pc=before.pc+12 := by
  simp [pointerArithmeticResult]

end PDCompute.Pack
