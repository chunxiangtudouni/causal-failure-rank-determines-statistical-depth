module

public import Paid.PDLower_CalibrationCompute_HeaderOps_027

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

def weightLoaded (before : State) (base endpoints level : ℕ) (error : ℚ) : State :=
  let a := loadSlotResult (loadSlotResult before base 1 .old) base 5 .index
  let address := endpoints+(level*2-1)
  {a with
    pc:=a.pc+8
    register:=Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update a.register .flag (.natural 1)) .index (.natural (level*2-1)))
          .address (.natural address))
        .old (.rational (1/2)))
      .total (.rational (1/2-error))}

def weightResult (before : State) (base endpoints level : ℕ) (error q : ℚ) : State :=
  let b := loadSlotResult (weightLoaded before base endpoints level error) base 11 .value
  {b with
    pc:=b.pc+3
    register:=Function.update
      (Function.update
        (Function.update b.register .value (.rational (1/2-q)))
        .old (.rational 0))
      .flag (.natural (if (1/2-q : ℚ)=0 then 1 else 0))}

/-- Actual endpoint load and denominator test. The endpoint value is
read from the real heap, rather than passed to the machine as an opcode. -/
theorem weight_execute (input : List Cell) (before : State) (base endpoints level : ℕ) (error q : ℚ)
    (fresh : before.register .fresh=.natural base)
    (endpointLive : base+1 ∈ before.live) (endpointValue : before.heap (base+1)=.natural endpoints)
    (levelLive : base+5 ∈ before.live) (levelValue : before.heap (base+5)=.natural level)
    (qLive : base+11 ∈ before.live) (qValue : before.heap (base+11)=.rational q)
    (errorLive : endpoints+(level*2-1) ∈ before.live)
    (errorValue : before.heap (endpoints+(level*2-1))=.rational error) :
    linearExecute input (basicBlock .weight).body before = some (weightResult before base endpoints level error q) := by
  simp [basicBlock,linearExecute,loadSlot,Instruction.execute,State.set,NatOp.eval,RatOp.eval,Comparison.rat,
    Cell.nat?,Cell.rat?,fresh,endpointLive,endpointValue,levelLive,levelValue,qLive,qValue,errorLive,errorValue,
    weightResult,weightLoaded,loadSlotResult,Nat.add_assoc]
  funext register
  cases register <;> simp

def divideResult (before : State) (numerator denominator : ℚ) : State :=
  {before with
    pc:=before.pc+1
    register:=Function.update before.register .value (.rational (numerator/denominator))}

theorem divide_execute (input : List Cell) (before : State) (numerator denominator : ℚ)
    (total : before.register .total=.rational numerator)
    (value : before.register .value=.rational denominator) (nonzero : denominator≠0) :
    linearExecute input (basicBlock .divide).body before = some (divideResult before numerator denominator) := by
  simp [basicBlock,linearExecute,Instruction.execute,State.set,Cell.rat?,RatOp.eval,total,value,nonzero,divideResult]

theorem zeroWeight_execute (input : List Cell) (before : State) :
    linearExecute input (basicBlock .zeroWeight).body before =
      some ({before with pc:=before.pc+1}.set .value (.rational 0)) := rfl

end PDLower.CalibrationCompute
