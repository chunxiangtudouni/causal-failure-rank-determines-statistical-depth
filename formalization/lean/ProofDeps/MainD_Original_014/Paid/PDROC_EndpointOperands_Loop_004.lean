module

public import Paid.PDROC_EndpointOperands_Loop_003
public import Paid.PDROC_CalibrationRow_OperandPrefix_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver RootD27.Bits
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult)
open PDROC.CalibrationRow.Operand

/- Draft only until the frozen input receipt is admitted. -/

theorem rowCompare_prefix_safe (input : List Cell) (before : State)
    (base m M budget : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh = .natural base)
    (row : values 8 = .natural m) (stop : values 3 = .natural M)
    (safe : SafeBits before budget) (zeroBits : (Cell.natural 0).bits ≤ budget)
    (oneBits : (Cell.natural 1).bits ≤ budget)
    (addressBits : 1 + natBits (base + headerWords) ≤ budget)
    (pcBits : natBits (before.pc + 7) ≤ budget) :
    PrefixSafe input rowCompareCode before budget := by
  let first := loadSlotResult before base 8 .index
  let loaded := loadSlotResult first base 3 .total
  have slotBits (slot : ℕ) (inside : slot < headerWords) :
      1 + natBits (base + slot) ≤ budget :=
    (Nat.add_le_add_left (PDROC.DataBits.natBits_mono (by omega : base + slot ≤ base + headerWords)) 1).trans addressBits
  have firstRun := (header.loadSlot_execute input 8 .index (by decide) fresh).1
  have firstSafe := PrefixSafe.loadSlot input before base 8 budget .index safe fresh
    (header.live 8 (by decide)) (slotBits 8 (by decide))
    ((PDROC.DataBits.natBits_mono (by omega : before.pc + 3 ≤ before.pc + 7)).trans pcBits)
  have firstFresh : first.register .fresh = .natural base := by
    simp [first, loadSlotResult, fresh]
  have firstHeader : Header first base values := header
  have secondRun := (firstHeader.loadSlot_execute input 3 .total (by decide) firstFresh).1
  have secondSafe := PrefixSafe.loadSlot input first base 3 budget .total
    (firstSafe.final firstRun) firstFresh (firstHeader.live 3 (by decide)) (slotBits 3 (by decide))
    (by simpa only [first, loadSlotResult, Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc + 6 ≤ before.pc + 7)).trans pcBits))
  have firstIndex : first.register .index = .natural m :=
    (header.loadSlot_execute input 8 .index (by decide) fresh).2.trans row
  have loadedIndex : loaded.register .index = .natural m := by
    simpa only [loaded, loadSlotResult,
      Function.update_of_ne (by decide : (.index : Register) ≠ .total),
      Function.update_of_ne (by decide : (.index : Register) ≠ .address)] using firstIndex
  have loadedTotal : loaded.register .total = .natural M :=
    (firstHeader.loadSlot_execute input 3 .total (by decide) firstFresh).2.trans stop
  have compareSafe := PrefixSafe.natCompare input loaded budget .lessEqual .flag .index .total m M
    (secondSafe.final secondRun) loadedIndex loadedTotal zeroBits oneBits
    (by simpa only [loaded, first, loadSlotResult, Nat.add_assoc] using pcBits)
  have tail := PrefixSafe.append input (loadSlot 3 .total) [.natCompare .lessEqual .flag .index .total]
    first loaded budget secondRun secondSafe compareSafe
  change PrefixSafe input (loadSlot 8 .index ++
    (loadSlot 3 .total ++ [.natCompare .lessEqual .flag .index .total])) before budget
  exact PrefixSafe.append input (loadSlot 8 .index)
    (loadSlot 3 .total ++ [.natCompare .lessEqual .flag .index .total])
    before first budget firstRun firstSafe tail

end PDROC.EndpointOperands.Loop
