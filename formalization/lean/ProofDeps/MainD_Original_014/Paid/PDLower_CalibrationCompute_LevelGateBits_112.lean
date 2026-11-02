module

public import Paid.PDLower_CalibrationCompute_LevelGate_037
public import Paid.PDLower_CalibrationCompute_BitSegment_086
public import Paid.PDLower_CalibrationCompute_RowBitBudget_102

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

theorem levelGate_prefix_safe (input : List Cell) (before : State) (base budget : ℕ) (header : Header)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base) (safe : SafeBits before budget)
    (slot5Bits : 1+natBits (base+5)≤budget) (slot2Bits : 1+natBits (base+2)≤budget)
    (zeroBits : (Cell.natural 0).bits≤budget) (oneBits : (Cell.natural 1).bits≤budget)
    (nextBits : (Cell.natural (header.M+1)).bits≤budget) (pcBits : natBits (before.pc+9)≤budget) :
    PrefixSafe input (basicBlock .levelGate).body before budget := by
  have level := represented.lookup (offset:=5) (value:=.natural header.level) rfl
  have M := represented.lookup (offset:=2) (value:=.natural header.M) rfl
  let a := loadSlotResult before base 5 .index
  let b := loadSlotResult a base 2 .total
  let c := ({b with pc:=b.pc+1}).set .flag (.natural 1)
  let d := ({c with pc:=c.pc+1}).set .total (.natural (header.M+1))
  have pcSmall (offset : ℕ) (bounded : offset≤9) : natBits (before.pc+offset)≤budget :=
    (PDROC.DataBits.natBits_mono (Nat.add_le_add_left bounded before.pc)).trans pcBits
  have aRun : linearExecute input (loadSlot 5 .index) before=some a := loadSlot_execute input before base 5 .index fresh level.2
  have aSafe := PrefixSafe.loadSlot input before base 5 budget .index safe fresh level.2 slot5Bits (pcSmall 3 (by decide))
  have aFresh : a.register .fresh=.natural base := by simp [a,loadSlotResult,fresh]
  have bRun : linearExecute input (loadSlot 2 .total) a=some b := loadSlot_execute input a base 2 .total aFresh M.2
  have bSafe := PrefixSafe.loadSlot input a base 2 budget .total (aSafe.final aRun) aFresh M.2 slot2Bits
    (by simpa only [a,loadSlotResult,Nat.add_assoc] using pcSmall 6 (by decide))
  have cRun : linearExecute input [.constant .flag (.natural 1)] b=some c := rfl
  have cSafe := PrefixSafe.constant input b budget .flag (.natural 1) (bSafe.final bRun) oneBits
    (by simpa only [b,a,loadSlotResult,Nat.add_assoc] using pcSmall 7 (by decide))
  have dRun : linearExecute input [.natOp .add .total .total .flag] c=some d := by
    simp [linearExecute,Instruction.execute,Cell.nat?,NatOp.eval,d,c,b,a,loadSlotResult,State.set,M.1]
  have dSafe := PrefixSafe.natOp input c budget .add .total .total .flag header.M 1 (header.M+1)
    (cSafe.final cRun) (by simp [c,b,a,loadSlotResult,State.set,M.1]) (by simp [c,State.set]) rfl nextBits
    (by simpa only [c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcSmall 8 (by decide))
  have lastSafe := PrefixSafe.natCompare input d budget .lessEqual .flag .index .total header.level (header.M+1)
    (dSafe.final dRun) (by simp [d,c,b,a,loadSlotResult,State.set,level.1]) (by simp [d,State.set]) zeroBits oneBits
    (by simpa only [d,c,b,a,loadSlotResult,State.set,Nat.add_assoc] using pcBits)
  have tailD := PrefixSafe.append input [.natOp .add .total .total .flag] [.natCompare .lessEqual .flag .index .total]
    c d budget dRun dSafe lastSafe
  have tailC := PrefixSafe.append input [.constant .flag (.natural 1)]
    ([.natOp .add .total .total .flag]++[.natCompare .lessEqual .flag .index .total]) b c budget cRun cSafe tailD
  have tailB := PrefixSafe.append input (loadSlot 2 .total) ([.constant .flag (.natural 1)]++
    ([.natOp .add .total .total .flag]++[.natCompare .lessEqual .flag .index .total])) a b budget bRun bSafe tailC
  have all := PrefixSafe.append input (loadSlot 5 .index) (loadSlot 2 .total++([.constant .flag (.natural 1)]++
    ([.natOp .add .total .total .flag]++[.natCompare .lessEqual .flag .index .total]))) before a budget aRun aSafe tailB
  simpa only [basicBlock,List.append_assoc,List.cons_append,List.nil_append] using all

theorem levelGate_bitSegment (origin : ℕ) (input : List Cell) (before : State) (base budget : ℕ) (header : Header)
    (position : before.pc=labelAddress origin .levelGate) (represented : header.At before base)
    (fresh : before.register .fresh=.natural base) (safe : SafeBits before budget)
    (slot5Bits : 1+natBits (base+5)≤budget) (slot2Bits : 1+natBits (base+2)≤budget)
    (zeroBits : (Cell.natural 0).bits≤budget) (oneBits : (Cell.natural 1).bits≤budget)
    (nextBits : (Cell.natural (header.M+1)).bits≤budget) (pcBits : natBits (before.pc+9)≤budget)
    (targets : ∀ label,natBits (labelAddress origin label)≤budget) :
    BitSegment origin input before
      {(levelGateResult before base header.level header.M) with
        pc:=labelAddress origin (if header.level≤header.M+1 then .levelInit else .finish)} 165 budget := by
  let middle := levelGateResult before base header.level header.M
  let after : State := {middle with pc:=labelAddress origin (if header.level≤header.M+1 then .levelInit else .finish)}
  have body := levelGate_execute input before base header represented fresh
  have prefixes := levelGate_prefix_safe input before base budget header represented fresh safe slot5Bits slot2Bits zeroBits oneBits nextBits pcBits
  have control : (controlInstruction origin (basicBlock .levelGate).control).execute input middle=some after := by
    by_cases condition : header.level≤header.M+1 <;>
      simp [basicBlock,controlInstruction,Instruction.execute,middle,levelGateResult,after,condition,Cell.nat?]
  have last := control_safe origin (basicBlock .levelGate).control input middle after budget (prefixes.final body) targets control
  exact BitSegment.ofBlock origin .levelGate input before middle after budget position body control
    (fun count _ state executed => prefixes count state executed) last

theorem levelGate_caller_bits (P : Parameters) (origin base endpoints returnPC callerBudget Lgamma : ℕ) (input : List Cell)
    (initialCaller before : State) (header : Header)
    (arguments : CallArguments P base endpoints returnPC initialCaller) (initialSafe : SafeBits initialCaller callerBudget)
    (position : before.pc=labelAddress origin .levelGate) (represented : header.At before base)
    (fresh : before.register .fresh=.natural base) (safe : SafeBits before (calleeOperandBudget P origin callerBudget Lgamma))
    (M : header.M=P.certificate.M) :
    BitSegment origin input before
      {(levelGateResult before base header.level header.M) with
        pc:=labelAddress origin (if header.level≤header.M+1 then .levelInit else .finish)} 165
      (calleeOperandBudget P origin callerBudget Lgamma) := by
  let budget := calleeOperandBudget P origin callerBudget Lgamma
  have control := calleeOperandBudget_control P origin base endpoints returnPC callerBudget Lgamma initialCaller arguments initialSafe
  have nextBits : (Cell.natural (header.M+1)).bits≤budget := by
    rw [M]
    apply ControlBudget.nat P origin base budget _ control
    have width := (controlNaturalCap_lower P base).2.1
    unfold rowWidth at width
    omega
  exact levelGate_bitSegment origin input before base budget header position represented fresh safe
    (ControlBudget.slot P origin base budget 5 control (by decide)) (ControlBudget.slot P origin base budget 2 control (by decide))
    (ControlBudget.literal P origin base budget 0 control (by decide)) (ControlBudget.literal P origin base budget 1 control (by decide))
    nextBits (ControlBudget.pc_prefix P origin base budget control before .levelGate 9 position (by decide))
    (fun label => ControlBudget.pc_target P origin base budget control label)

end PDLower.CalibrationCompute
