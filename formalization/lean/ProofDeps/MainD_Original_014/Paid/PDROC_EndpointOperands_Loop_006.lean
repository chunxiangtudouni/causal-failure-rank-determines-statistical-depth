module

public import Paid.PDROC_EndpointOperands_Loop_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver RootD27.Bits
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult)
open PDROC.CalibrationRow.Operand

/- Draft only; the old return/address cells are read from live original
header slots and keep the caller budget. Only the actual 2M+3 arithmetic
and instruction addresses use the fixed new-natural envelope. -/

theorem returnPrefix_prefix_safe (input : List Cell) (before : State)
    (base M budget : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh = .natural base)
    (stop : values 3 = .natural M) (safe : SafeBits before budget)
    (natural : ∀ n, n ≤ 2 * M + 3 → (Cell.natural n).bits ≤ budget)
    (addressBits : 1 + natBits (base + headerWords) ≤ budget)
    (pcBits : natBits (before.pc + 13) ≤ budget) :
    PrefixSafe input returnPrefixCode before budget := by
  let first := loadSlotResult before base 1 .old
  let loaded := loadSlotResult first base 3 .index
  let two := ({loaded with pc := loaded.pc + 1}).set .total (.natural 2)
  let doubled := ({two with pc := two.pc + 1}).set .index (.natural (M * 2))
  let three := ({doubled with pc := doubled.pc + 1}).set .total (.natural 3)
  let counted := ({three with pc := three.pc + 1}).set .index (.natural (M * 2 + 3))
  have slotBits (slot : ℕ) (inside : slot < headerWords) :
      1 + natBits (base + slot) ≤ budget :=
    (Nat.add_le_add_left (PDROC.DataBits.natBits_mono (by omega : base + slot ≤ base + headerWords)) 1).trans addressBits
  have firstRun := (header.loadSlot_execute input 1 .old (by decide) fresh).1
  have firstSafe := PrefixSafe.loadSlot input before base 1 budget .old safe fresh
    (header.live 1 (by decide)) (slotBits 1 (by decide))
    ((PDROC.DataBits.natBits_mono (by omega : before.pc + 3 ≤ before.pc + 13)).trans pcBits)
  have firstFresh : first.register .fresh = .natural base := by
    simp [first, loadSlotResult, fresh]
  have firstHeader : Header first base values := header
  have loadedRun := (firstHeader.loadSlot_execute input 3 .index (by decide) firstFresh).1
  have loadedSafe := PrefixSafe.loadSlot input first base 3 budget .index
    (firstSafe.final firstRun) firstFresh (firstHeader.live 3 (by decide)) (slotBits 3 (by decide))
    (by simpa only [first, loadSlotResult, Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc + 6 ≤ before.pc + 13)).trans pcBits))
  have loadedIndex : loaded.register .index = .natural M :=
    (firstHeader.loadSlot_execute input 3 .index (by decide) firstFresh).2.trans stop
  have twoRun : linearExecute input [.constant .total (.natural 2)] loaded = some two := rfl
  have twoSafe := PrefixSafe.constant input loaded budget .total (.natural 2)
    (loadedSafe.final loadedRun) (natural 2 (by omega))
    (by simpa only [loaded, first, loadSlotResult, Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc + 7 ≤ before.pc + 13)).trans pcBits))
  have doubleRun : linearExecute input [.natOp .multiply .index .index .total] two = some doubled := by
    simp [linearExecute, Instruction.execute, two, State.set, loadedIndex, Cell.nat?, NatOp.eval, doubled]
  have doubleSafe := PrefixSafe.natOp input two budget .multiply .index .index .total M 2 (M * 2)
    (twoSafe.final twoRun) (by simpa [two, State.set] using loadedIndex)
    (by simp [two, State.set]) rfl (natural (M * 2) (by omega))
    (by simpa only [two, loaded, first, loadSlotResult, State.set, Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc + 8 ≤ before.pc + 13)).trans pcBits))
  have threeRun : linearExecute input [.constant .total (.natural 3)] doubled = some three := rfl
  have threeSafe := PrefixSafe.constant input doubled budget .total (.natural 3)
    (doubleSafe.final doubleRun) (natural 3 (by omega))
    (by simpa only [doubled, two, loaded, first, loadSlotResult, State.set, Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc + 9 ≤ before.pc + 13)).trans pcBits))
  have addRun : linearExecute input [.natOp .add .index .index .total] three = some counted := by
    simp [linearExecute, Instruction.execute, three, doubled, State.set, Cell.nat?, NatOp.eval, counted]
  have addSafe := PrefixSafe.natOp input three budget .add .index .index .total (M * 2) 3 (M * 2 + 3)
    (threeSafe.final threeRun) (by simp [three, doubled, State.set])
    (by simp [three, State.set]) rfl (natural (M * 2 + 3) (by omega))
    (by simpa only [three, doubled, two, loaded, first, loadSlotResult, State.set, Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc + 10 ≤ before.pc + 13)).trans pcBits))
  have countedFresh : counted.register .fresh = .natural base := by
    simp [counted, three, doubled, two, loaded, first, loadSlotResult, State.set, fresh]
  have countedHeader : Header counted base values := header
  have lastSafe := PrefixSafe.loadSlot input counted base 0 budget .address (addSafe.final addRun)
    countedFresh (countedHeader.live 0 (by decide)) (slotBits 0 (by decide))
    (by simpa only [counted, three, doubled, two, loaded, first, loadSlotResult, State.set, Nat.add_assoc] using pcBits)
  have tail5 := PrefixSafe.append input [.natOp .add .index .index .total] (loadSlot 0 .address)
    three counted budget addRun addSafe lastSafe
  have tail4 := PrefixSafe.append input [.constant .total (.natural 3)]
    ([.natOp .add .index .index .total] ++ loadSlot 0 .address)
    doubled three budget threeRun threeSafe tail5
  have tail3 := PrefixSafe.append input [.natOp .multiply .index .index .total]
    ([.constant .total (.natural 3)] ++ ([.natOp .add .index .index .total] ++ loadSlot 0 .address))
    two doubled budget doubleRun doubleSafe tail4
  have tail2 := PrefixSafe.append input [.constant .total (.natural 2)]
    ([.natOp .multiply .index .index .total] ++ ([.constant .total (.natural 3)] ++
      ([.natOp .add .index .index .total] ++ loadSlot 0 .address)))
    loaded two budget twoRun twoSafe tail3
  have tail1 := PrefixSafe.append input (loadSlot 3 .index)
    ([.constant .total (.natural 2)] ++ ([.natOp .multiply .index .index .total] ++
      ([.constant .total (.natural 3)] ++ ([.natOp .add .index .index .total] ++ loadSlot 0 .address))))
    first loaded budget loadedRun loadedSafe tail2
  change PrefixSafe input (loadSlot 1 .old ++ (loadSlot 3 .index ++
    ([.constant .total (.natural 2)] ++ ([.natOp .multiply .index .index .total] ++
      ([.constant .total (.natural 3)] ++ ([.natOp .add .index .index .total] ++ loadSlot 0 .address)))))) before budget
  exact PrefixSafe.append input (loadSlot 1 .old) _ before first budget firstRun firstSafe tail1

end PDROC.EndpointOperands.Loop
