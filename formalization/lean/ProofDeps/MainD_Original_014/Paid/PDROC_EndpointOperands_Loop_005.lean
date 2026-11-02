module

public import Paid.PDROC_EndpointOperands_Loop_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver RootD27.Bits
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult storeSlot)
open PDROC.CalibrationRow.Operand

/- Draft only until the exact parent source/five-product receipt. -/

theorem incrementRow_prefix_safe (input : List Cell) (before : State)
    (base m budget : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh = .natural base)
    (row : values 8 = .natural m) (safe : SafeBits before budget)
    (oneBits : (Cell.natural 1).bits ≤ budget)
    (nextBits : (Cell.natural (m + 1)).bits ≤ budget)
    (addressBits : 1 + natBits (base + headerWords) ≤ budget)
    (pcBits : natBits (before.pc + 8) ≤ budget) :
    PrefixSafe input incrementRowCode before budget := by
  let loaded := loadSlotResult before base 8 .total
  let one := ({loaded with pc := loaded.pc + 1}).set .value (.natural 1)
  let counted := ({one with pc := one.pc + 1}).set .total (.natural (m + 1))
  have slotBits : 1 + natBits (base + 8) ≤ budget :=
    (Nat.add_le_add_left (PDROC.DataBits.natBits_mono
      (Nat.add_le_add_left (by decide : 8 ≤ headerWords) base)) 1).trans addressBits
  have loadRun := (header.loadSlot_execute input 8 .total (by decide) fresh).1
  have loadSafe := PrefixSafe.loadSlot input before base 8 budget .total safe fresh
    (header.live 8 (by decide)) slotBits
    ((PDROC.DataBits.natBits_mono (by omega : before.pc + 3 ≤ before.pc + 8)).trans pcBits)
  have loadedValue : loaded.register .total = .natural m :=
    (header.loadSlot_execute input 8 .total (by decide) fresh).2.trans row
  have oneRun : linearExecute input [.constant .value (.natural 1)] loaded = some one := rfl
  have oneSafe := PrefixSafe.constant input loaded budget .value (.natural 1)
    (loadSafe.final loadRun) oneBits
    (by simpa only [loaded, loadSlotResult, Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc + 4 ≤ before.pc + 8)).trans pcBits))
  have addRun : linearExecute input [.natOp .add .total .total .value] one = some counted := by
    simp [linearExecute, Instruction.execute, one, State.set, loadedValue, Cell.nat?, NatOp.eval, counted]
  have addSafe := PrefixSafe.natOp input one budget .add .total .total .value m 1 (m + 1)
    (oneSafe.final oneRun)
    (by simpa [one, State.set] using loadedValue)
    (by simp [one, State.set]) rfl nextBits
    (by simpa only [one, loaded, loadSlotResult, State.set, Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc + 5 ≤ before.pc + 8)).trans pcBits))
  have countedFresh : counted.register .fresh = .natural base := by
    simp [counted, one, loaded, loadSlotResult, State.set, fresh]
  have storeSafe := PrefixSafe.storeSlot input counted base 8 budget .total
    (addSafe.final addRun) countedFresh (by decide) slotBits
    (by simpa only [counted, one, loaded, loadSlotResult, State.set, Nat.add_assoc] using pcBits)
  have tail := PrefixSafe.append input [.natOp .add .total .total .value] (storeSlot 8 .total)
    one counted budget addRun addSafe storeSafe
  have suffix := PrefixSafe.append input [.constant .value (.natural 1)]
    ([.natOp .add .total .total .value] ++ storeSlot 8 .total)
    loaded one budget oneRun oneSafe tail
  change PrefixSafe input (loadSlot 8 .total ++ ([.constant .value (.natural 1)] ++
    ([.natOp .add .total .total .value] ++ storeSlot 8 .total))) before budget
  exact PrefixSafe.append input (loadSlot 8 .total)
    ([.constant .value (.natural 1)] ++ ([.natOp .add .total .total .value] ++ storeSlot 8 .total))
    before loaded budget loadRun loadSafe suffix

end PDROC.EndpointOperands.Loop
