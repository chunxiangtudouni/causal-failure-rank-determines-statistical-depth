module

public import Paid.PDROC_EndpointOperands_Loop_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Bits
open PDLower.CalibrationCompute (linearExecute)
open PDROC.CalibrationRow.Operand

def pairTailCode : List Instruction :=
  [.constant .value (.natural 2), .natOp .multiply .index .index .value,
    .constant .value (.natural 1), .natOp .add .index .index .value,
    .natOp .add .address .total .index, .store .address .flag,
    .natOp .add .address .address .value, .store .address .old]

/-- These are the actual two cache writes, not reads of old destination
cells. Both source cells already have caller B; every new natural is in
the finite real E+2m+2 envelope. The two stores keep all old live memory. -/
theorem pairTail_prefix_safe (input : List Cell) (before : State) (E m budget : ℕ)
    (safe : SafeBits before budget) (index : before.register .index = .natural m)
    (cache : before.register .total = .natural E)
    (natural : ∀ n, n ≤ E + 2 * m + 2 → (Cell.natural n).bits ≤ budget)
    (pcBits : natBits (before.pc + 8) ≤ budget) :
    PrefixSafe input pairTailCode before budget := by
  let two := ({before with pc := before.pc + 1}).set .value (.natural 2)
  let doubled := ({two with pc := two.pc + 1}).set .index (.natural (m * 2))
  let one := ({doubled with pc := doubled.pc + 1}).set .value (.natural 1)
  let indexed := ({one with pc := one.pc + 1}).set .index (.natural (m * 2 + 1))
  let addressed := ({indexed with pc := indexed.pc + 1}).set .address (.natural (E + (m * 2 + 1)))
  let stored : State :=
    {addressed with
      heap := Function.update addressed.heap (E + (m * 2 + 1)) (addressed.register .flag)
      live := insert (E + (m * 2 + 1)) addressed.live
      pc := addressed.pc + 1}
  let advanced := ({stored with pc := stored.pc + 1}).set .address (.natural (E + (m * 2 + 1) + 1))
  have twoRun : linearExecute input [.constant .value (.natural 2)] before = some two := rfl
  have twoSafe := PrefixSafe.constant input before budget .value (.natural 2) safe (natural 2 (by omega))
    ((PDROC.DataBits.natBits_mono (by omega : before.pc + 1 ≤ before.pc + 8)).trans pcBits)
  have doubleRun : linearExecute input [.natOp .multiply .index .index .value] two = some doubled := by
    simp [linearExecute, Instruction.execute, two, State.set, index, Cell.nat?, NatOp.eval, doubled]
  have doubleSafe := PrefixSafe.natOp input two budget .multiply .index .index .value m 2 (m * 2)
    (twoSafe.final twoRun) (by simpa [two, State.set] using index)
    (by simp [two, State.set]) rfl (natural (m * 2) (by omega))
    (by simpa only [two, State.set, Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc + 2 ≤ before.pc + 8)).trans pcBits))
  have oneRun : linearExecute input [.constant .value (.natural 1)] doubled = some one := rfl
  have oneSafe := PrefixSafe.constant input doubled budget .value (.natural 1)
    (doubleSafe.final doubleRun) (natural 1 (by omega))
    (by simpa only [doubled, two, State.set, Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc + 3 ≤ before.pc + 8)).trans pcBits))
  have indexRun : linearExecute input [.natOp .add .index .index .value] one = some indexed := by
    simp [linearExecute, Instruction.execute, one, doubled, State.set, Cell.nat?, NatOp.eval, indexed]
  have indexSafe := PrefixSafe.natOp input one budget .add .index .index .value (m * 2) 1 (m * 2 + 1)
    (oneSafe.final oneRun) (by simp [one, doubled, State.set]) (by simp [one, State.set]) rfl
    (natural (m * 2 + 1) (by omega))
    (by simpa only [one, doubled, two, State.set, Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc + 4 ≤ before.pc + 8)).trans pcBits))
  have addressRun : linearExecute input [.natOp .add .address .total .index] indexed = some addressed := by
    simp [linearExecute, Instruction.execute, indexed, one, doubled, two, State.set, cache,
      Cell.nat?, NatOp.eval, addressed]
  have addressSafe := PrefixSafe.natOp input indexed budget .add .address .total .index E (m * 2 + 1) (E + (m * 2 + 1))
    (indexSafe.final indexRun) (by simpa [indexed, one, doubled, two, State.set] using cache)
    (by simp [indexed, State.set]) rfl (natural (E + (m * 2 + 1)) (by omega))
    (by simpa only [indexed, one, doubled, two, State.set, Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc + 5 ≤ before.pc + 8)).trans pcBits))
  have addressValue : addressed.register .address = .natural (E + (m * 2 + 1)) := by
    simp [addressed, State.set]
  have storeRun : linearExecute input [.store .address .flag] addressed = some stored := by
    simp [linearExecute, Instruction.execute, addressValue, Cell.nat?, stored]
  have storeSafe := PrefixSafe.store input addressed budget .address .flag (E + (m * 2 + 1))
    (addressSafe.final addressRun) addressValue
    (by simpa only [addressed, indexed, one, doubled, two, State.set, Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc + 6 ≤ before.pc + 8)).trans pcBits))
  have advanceRun : linearExecute input [.natOp .add .address .address .value] stored = some advanced := by
    simp [linearExecute, Instruction.execute, stored, addressed, indexed, one, State.set,
      Cell.nat?, NatOp.eval, advanced]
  have advanceSafe := PrefixSafe.natOp input stored budget .add .address .address .value
    (E + (m * 2 + 1)) 1 (E + (m * 2 + 1) + 1) (storeSafe.final storeRun)
    (by simp [stored, addressed, State.set])
    (by simp [stored, addressed, indexed, one, State.set]) rfl
    (natural (E + (m * 2 + 1) + 1) (by omega))
    (by simpa only [stored, addressed, indexed, one, doubled, two, State.set, Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc + 7 ≤ before.pc + 8)).trans pcBits))
  have lastSafe := PrefixSafe.store input advanced budget .address .old (E + (m * 2 + 1) + 1)
    (advanceSafe.final advanceRun) (by simp [advanced, State.set])
    (by simpa only [advanced, stored, addressed, indexed, one, doubled, two, State.set, Nat.add_assoc] using pcBits)
  have tail6 := PrefixSafe.append input [.natOp .add .address .address .value] [.store .address .old]
    stored advanced budget advanceRun advanceSafe lastSafe
  have tail5 := PrefixSafe.append input [.store .address .flag]
    ([.natOp .add .address .address .value] ++ [.store .address .old]) addressed stored budget storeRun storeSafe tail6
  have tail4 := PrefixSafe.append input [.natOp .add .address .total .index]
    ([.store .address .flag] ++ ([.natOp .add .address .address .value] ++ [.store .address .old]))
    indexed addressed budget addressRun addressSafe tail5
  have tail3 := PrefixSafe.append input [.natOp .add .index .index .value]
    ([.natOp .add .address .total .index] ++ ([.store .address .flag] ++
      ([.natOp .add .address .address .value] ++ [.store .address .old])))
    one indexed budget indexRun indexSafe tail4
  have tail2 := PrefixSafe.append input [.constant .value (.natural 1)]
    ([.natOp .add .index .index .value] ++ ([.natOp .add .address .total .index] ++
      ([.store .address .flag] ++ ([.natOp .add .address .address .value] ++ [.store .address .old]))))
    doubled one budget oneRun oneSafe tail3
  have tail1 := PrefixSafe.append input [.natOp .multiply .index .index .value]
    ([.constant .value (.natural 1)] ++ ([.natOp .add .index .index .value] ++
      ([.natOp .add .address .total .index] ++ ([.store .address .flag] ++
        ([.natOp .add .address .address .value] ++ [.store .address .old])))))
    two doubled budget doubleRun doubleSafe tail2
  change PrefixSafe input ([.constant .value (.natural 2)] ++
    ([.natOp .multiply .index .index .value] ++ ([.constant .value (.natural 1)] ++
      ([.natOp .add .index .index .value] ++ ([.natOp .add .address .total .index] ++
        ([.store .address .flag] ++ ([.natOp .add .address .address .value] ++ [.store .address .old]))))))) before budget
  exact PrefixSafe.append input [.constant .value (.natural 2)] _ before two budget twoRun twoSafe tail1

end PDROC.EndpointOperands.Loop
