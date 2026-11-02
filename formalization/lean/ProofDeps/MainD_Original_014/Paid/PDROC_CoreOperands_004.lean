module

public import Paid.PDROC_CoreOperands_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CoreOperands

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits PDROC.CalibrationRow.Operand

def directReadCode (slot : ℕ) (target : Register) : List Instruction :=
  [.constant .address (.natural slot),.load target .address]

def directReadResult (before : State) (slot : ℕ) (target : Register) : State :=
  let addressed := ({before with pc:=before.pc+1}).set .address (.natural slot)
  ({addressed with pc:=addressed.pc+1}).set target (before.heap slot)

theorem directRead_execute (input : List Cell) (before : State) (slot : ℕ) (target : Register)
    (live : slot∈before.live) :
    linearExecute input (directReadCode slot target) before=some (directReadResult before slot target) := by
  simp [directReadCode,directReadResult,linearExecute,Instruction.execute,State.set,Cell.nat?,live]

/-- This is the two-opcode direct-heap read occurring in frozen017,
not the different three-opcode fresh-relative loadSlot. -/
theorem directRead_prefix_safe (input : List Cell) (before : State) (slot budget : ℕ)
    (target : Register) (safe : SafeBits before budget) (live : slot∈before.live)
    (slotBits : (Cell.natural slot).bits≤budget) (pcBits : natBits (before.pc+2)≤budget) :
    PrefixSafe input (directReadCode slot target) before budget := by
  let addressed := ({before with pc:=before.pc+1}).set .address (.natural slot)
  have firstRun : linearExecute input [.constant .address (.natural slot)] before=some addressed := rfl
  have firstSafe := PrefixSafe.constant input before budget .address (.natural slot) safe slotBits
    ((PDROC.DataBits.natBits_mono (by omega : before.pc+1≤before.pc+2)).trans pcBits)
  have laterSafe := PrefixSafe.load input addressed budget target .address slot (firstSafe.final firstRun)
    (by simp [addressed,State.set]) live
    (by simpa only [addressed,State.set,Nat.add_assoc] using pcBits)
  exact PrefixSafe.append input [.constant .address (.natural slot)] [.load target .address]
    before addressed budget firstRun firstSafe laterSafe

def solverBaseResult (before : State) (m : ℕ) : State :=
  {before with
    register:=Function.update (Function.update before.register .fresh (.natural (99+2*m))) .address (.natural 99)
    pc:=before.pc+6}

theorem solverBase_execute (input : List Cell) (before : State) (m : ℕ)
    (live : 7∈before.live) (cell : before.heap 7=.natural m) :
    linearExecute input (RootD27.Core.solverHeapArgumentPrefix.take 6) before=some (solverBaseResult before m) := by
  have normalized : m*2+99=99+2*m := by omega
  simp [RootD27.Core.solverHeapArgumentPrefix,linearExecute,Instruction.execute,State.set,
    Cell.nat?,NatOp.eval,live,cell,normalized,solverBaseResult,Nat.add_assoc]
  all_goals
    funext target
    cases target <;> simp

def solverReadResult (before : State) : State :=
  directReadResult (directReadResult (directReadResult before 0 .index) 1 .value) 5 .flag

theorem solverReads_execute (input : List Cell) (before : State)
    (live : ∀ slot<13,slot∈before.live) :
    linearExecute input (RootD27.Core.solverHeapArgumentPrefix.drop 6) before=some (solverReadResult before) := by
  have first := directRead_execute input before 0 .index (live 0 (by decide))
  have second := directRead_execute input (directReadResult before 0 .index) 1 .value (live 1 (by decide))
  have third := directRead_execute input (directReadResult (directReadResult before 0 .index) 1 .value)
    5 .flag (live 5 (by decide))
  change linearExecute input (directReadCode 0 .index++(directReadCode 1 .value++directReadCode 5 .flag)) before=some (solverReadResult before)
  rw [linearExecute_append,first,Option.bind_some,linearExecute_append,second,Option.bind_some,third]
  rfl

theorem solverReads_prefix_safe (input : List Cell) (before : State) (budget : ℕ)
    (safe : SafeBits before budget) (live : ∀ slot<13,slot∈before.live)
    (small : 4≤budget) (pcBits : natBits (before.pc+6)≤budget) :
    PrefixSafe input (RootD27.Core.solverHeapArgumentPrefix.drop 6) before budget := by
  let first := directReadResult before 0 .index
  let second := directReadResult first 1 .value
  have firstRun := directRead_execute input before 0 .index (live 0 (by decide))
  have secondRun := directRead_execute input first 1 .value (live 1 (by decide))
  have firstSafe := directRead_prefix_safe input before 0 budget .index safe (live 0 (by decide))
    ((show (Cell.natural 0).bits≤4 by decide).trans small)
    ((PDROC.DataBits.natBits_mono (by omega : before.pc+2≤before.pc+6)).trans pcBits)
  have secondSafe := directRead_prefix_safe input first 1 budget .value (firstSafe.final firstRun) (live 1 (by decide))
    ((show (Cell.natural 1).bits≤4 by decide).trans small)
    (by simpa only [first,directReadResult,State.set,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+4≤before.pc+6)).trans pcBits))
  have thirdSafe := directRead_prefix_safe input second 5 budget .flag (secondSafe.final secondRun) (live 5 (by decide))
    ((show (Cell.natural 5).bits≤4 by decide).trans small)
    (by simpa only [second,first,directReadResult,State.set,Nat.add_assoc] using pcBits)
  have suffix := PrefixSafe.append input (directReadCode 1 .value) (directReadCode 5 .flag)
    first second budget secondRun secondSafe thirdSafe
  change PrefixSafe input (directReadCode 0 .index++(directReadCode 1 .value++directReadCode 5 .flag)) before budget
  exact PrefixSafe.append input (directReadCode 0 .index) (directReadCode 1 .value++directReadCode 5 .flag)
    before first budget firstRun firstSafe suffix

end PDROC.CoreOperands
