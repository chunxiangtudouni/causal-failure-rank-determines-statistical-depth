module

public import Paid.PDLower_CalibrationCompute_BitSegment_086
public import Paid.PDLower_CalibrationCompute_Gates_030
public import Paid.PDROC_CalibrationRow_OperandPrefix_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

theorem sumGate_prefix_safe (input : List Cell) (before : State) (base budget : ℕ) (header : Header)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base)
    (safe : SafeBits before budget) (address7 : 1+natBits (base+7)≤budget)
    (address5 : 1+natBits (base+5)≤budget)
    (zeroBits : (Cell.natural 0).bits≤budget) (oneBits : (Cell.natural 1).bits≤budget)
    (pcBits : natBits (before.pc+7)≤budget) :
    PrefixSafe input (basicBlock .sumGate).body before budget := by
  have cursor := represented.lookup (offset:=7) (value:=.natural header.cursor) rfl
  have level := represented.lookup (offset:=5) (value:=.natural header.level) rfl
  exact gate_prefix_safe input before base 7 5 header.cursor header.level budget safe fresh
    cursor.2 level.2 cursor.1 level.1 address7 address5 zeroBits oneBits pcBits

/-- The true strict sum-loop branch, not the outer lessEqual branch. -/
theorem sumGate_bitSegment (origin : ℕ) (input : List Cell) (before : State) (base budget : ℕ) (header : Header)
    (position : before.pc=labelAddress origin .sumGate)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base)
    (safe : SafeBits before budget) (address7 : 1+natBits (base+7)≤budget)
    (address5 : 1+natBits (base+5)≤budget)
    (zeroBits : (Cell.natural 0).bits≤budget) (oneBits : (Cell.natural 1).bits≤budget)
    (pcBits : natBits (before.pc+7)≤budget) (targets : ∀ label,natBits (labelAddress origin label)≤budget) :
    BitSegment origin input before
      {(sumGateResult before base header.cursor header.level) with
        pc:=labelAddress origin (if header.cursor<header.level then .sumCell else .sumFinish)} 135 budget := by
  let middle := sumGateResult before base header.cursor header.level
  let after : State := {middle with
    pc:=labelAddress origin (if header.cursor<header.level then .sumCell else .sumFinish)}
  have body : linearExecute input (basicBlock .sumGate).body before=some middle :=
    sumGate_execute input before base header represented fresh
  have control : (controlInstruction origin (basicBlock .sumGate).control).execute input middle=some after := by
    by_cases condition : header.cursor<header.level <;>
      simp [basicBlock,controlInstruction,Instruction.execute,middle,sumGateResult,after,condition,Cell.nat?]
  have prefixes := sumGate_prefix_safe input before base budget header represented fresh safe address7 address5 zeroBits oneBits pcBits
  have last := control_safe origin (basicBlock .sumGate).control input middle after budget (prefixes.final body) targets control
  exact BitSegment.ofBlock origin .sumGate input before middle after budget position body control
    (fun count _ state executed => prefixes count state executed) last

end PDLower.CalibrationCompute
