module
public import Paid.PDCompute_Pack_NaturalCap_054
public import Paid.PDCompute_Pack_InstructionBits_058
public import Paid.PDCompute_Pack_TraceInvariant_055

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute readOnly linearReadOnly_heap)

def natCellAt (state : State) (counter : ℕ) (target : Register) (value : ℕ) : State:=
  ({state with pc:=counter}).set target (.natural value)

theorem natCellAt_safe {state : State} {budget : ℕ} (safe : SafeBits state budget)
    (counter : ℕ) (target : Register) (value : ℕ) (pc : natBits counter ≤ budget) (cell : 1+natBits value ≤ budget) :
    SafeBits (natCellAt state counter target value) budget := (safe.withPC counter pc).set target (.natural value) cell

def pointerTailCode : List Instruction:=
  [.natOp .multiply .total .index .value,.constant .flag (.natural 6),
   .natOp .multiply .total .total .flag,.constant .flag (.natural 48),
   .natOp .add .total .total .flag,.natOp .add .total .total .fresh]

def pointerTailResult (before : State) (base n k : ℕ) : State:=
  let product:=(n+1)*(k+1)
  let oneState:=natCellAt before (before.pc+1) .total product
  let twoState:=natCellAt oneState (before.pc+2) .flag 6
  let threeState:=natCellAt twoState (before.pc+3) .total (product*6)
  let fourState:=natCellAt threeState (before.pc+4) .flag 48
  let fiveState:=natCellAt fourState (before.pc+5) .total (product*6+48)
  natCellAt fiveState (before.pc+6) .total (product*6+48+base)

theorem pointerTail_execute (input : List Cell) (before : State) (base n k : ℕ)
    (fresh : before.register .fresh=.natural base) (rows : before.register .index=.natural (n+1))
    (columns : before.register .value=.natural (k+1)) :
    linearExecute input pointerTailCode before=some (pointerTailResult before base n k) := by
  simp [pointerTailCode,pointerTailResult,natCellAt,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
    fresh,rows,columns,Nat.add_assoc]

/-- Every actual multiplication/addition intermediate fits the true
computed workspace cap. No repeated-loop bit-budget inflation is used. -/
theorem pointerTail_prefix_safe (input : List Cell) (before after : State) (base n k budget count : ℕ)
    (fresh : before.register .fresh=.natural base) (rows : before.register .index=.natural (n+1))
    (columns : before.register .value=.natural (k+1)) (safe : SafeBits before budget)
    (naturalBound : ∀ value ≤ naturalCap base n k,1+natBits value ≤ budget)
    (counter : natBits (before.pc+6) ≤ budget) (bound : count ≤ 6)
    (execute : linearExecute input (pointerTailCode.take count) before=some after) : SafeBits after budget := by
  let product:=(n+1)*(k+1)
  let s1:=natCellAt before (before.pc+1) .total product
  let s2:=natCellAt s1 (before.pc+2) .flag 6
  let s3:=natCellAt s2 (before.pc+3) .total (product*6)
  let s4:=natCellAt s3 (before.pc+4) .flag 48
  let s5:=natCellAt s4 (before.pc+5) .total (product*6+48)
  let s6:=natCellAt s5 (before.pc+6) .total (product*6+48+base)
  have pc (offset : ℕ) (inside : offset ≤ 6) : natBits (before.pc+offset) ≤ budget:=
    (natBits_mono (Nat.add_le_add_left inside before.pc)).trans counter
  have six : 6 ≤ naturalCap base n k:=by have cap:=naturalCap_small base n k;omega
  have scaled : product*6 ≤ naturalCap base n k:=by
    simpa only [product,Nat.mul_comm 6] using naturalCap_times_six base n k
  have shifted : product*6+48 ≤ naturalCap base n k:=by
    simpa only [product,Nat.mul_comm 6] using naturalCap_plus_header base n k
  have resultEq : product*6+48+base=resultBase base n k:=by
    unfold product resultBase tableBase headerWords entryWords PDCompute.Solver.entryCount
    omega
  have finalBound : product*6+48+base ≤ naturalCap base n k:=resultEq.symm ▸ naturalCap_resultBase base n k
  have safe1 : SafeBits s1 budget:=natCellAt_safe safe _ _ _ (pc 1 (by decide)) (naturalBound _ (naturalCap_product base n k))
  have safe2 : SafeBits s2 budget:=natCellAt_safe safe1 _ _ _ (pc 2 (by decide)) (naturalBound _ six)
  have safe3 : SafeBits s3 budget:=natCellAt_safe safe2 _ _ _ (pc 3 (by decide)) (naturalBound _ scaled)
  have safe4 : SafeBits s4 budget:=natCellAt_safe safe3 _ _ _ (pc 4 (by decide)) (naturalBound _ (naturalCap_small base n k))
  have safe5 : SafeBits s5 budget:=natCellAt_safe safe4 _ _ _ (pc 5 (by decide)) (naturalBound _ shifted)
  have safe6 : SafeBits s6 budget:=natCellAt_safe safe5 _ _ _ (pc 6 (by decide)) (naturalBound _ finalBound)
  interval_cases count <;>
    simp [pointerTailCode,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,fresh,rows,columns,Nat.add_assoc] at execute <;> subst after
  · exact safe
  · exact safe1
  · exact safe2
  · exact safe3
  · exact safe4
  · exact safe5
  · simpa [s6,s5,s4,s3,s2,s1,natCellAt,State.set,product,Nat.add_assoc] using safe6

end PDCompute.Pack
