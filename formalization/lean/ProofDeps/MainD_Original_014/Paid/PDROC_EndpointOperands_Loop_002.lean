module

public import Paid.PDROC_EndpointOperands_Loop_001
public import Paid.PDROC_CalibrationRow_OperandPrefix_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver RootD27.Bits
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult storeSlot)
open PDROC.CalibrationRow.Operand

/- Draft only until exact frozen inputs are admitted. The numerical
row-cast premise is supplied by the concrete Math budget, not by a
machine-run oracle or a bound on arbitrary incoming scratch. -/

theorem castRow_prefix_safe (input : List Cell) (before : State)
    (base m budget : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh = .natural base)
    (row : values 8 = .natural m) (safe : SafeBits before budget)
    (castBits : (Cell.rational (m : ℚ)).bits ≤ budget)
    (addressBits : 1 + natBits (base + headerWords) ≤ budget)
    (pcBits : natBits (before.pc + 7) ≤ budget) :
    PrefixSafe input castRowCode before budget := by
  let loaded := loadSlotResult before base 8 .total
  let casted := ({loaded with pc := loaded.pc + 1}).set .total (.rational (m : ℚ))
  have slotBits (slot : ℕ) (inside : slot < headerWords) :
      1 + natBits (base + slot) ≤ budget :=
    (Nat.add_le_add_left (PDROC.DataBits.natBits_mono (by omega : base + slot ≤ base + headerWords)) 1).trans addressBits
  have loadRun := (header.loadSlot_execute input 8 .total (by decide) fresh).1
  have loadSafe := PrefixSafe.loadSlot input before base 8 budget .total safe fresh
    (header.live 8 (by decide)) (slotBits 8 (by decide))
    ((PDROC.DataBits.natBits_mono (by omega : before.pc + 3 ≤ before.pc + 7)).trans pcBits)
  have loadedValue : loaded.register .total = .natural m :=
    (header.loadSlot_execute input 8 .total (by decide) fresh).2.trans row
  have castRun : linearExecute input [.natToRat .total .total] loaded = some casted := by
    simp [linearExecute, Instruction.execute, loadedValue, Cell.nat?, casted]
  have castInstruction : Instruction.execute input (.natToRat .total .total) loaded = some casted := by
    simp [Instruction.execute, loadedValue, Cell.nat?, casted]
  have castPC : natBits (loaded.pc + 1) ≤ budget := by
    simpa only [loaded, loadSlotResult, Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc + 4 ≤ before.pc + 7)).trans pcBits)
  have castSafe := PrefixSafe.singleton input (.natToRat .total .total) loaded casted budget
    castInstruction (loadSafe.final loadRun)
    (((loadSafe.final loadRun).withPC (loaded.pc + 1) castPC).set .total (.rational (m : ℚ)) castBits)
  have castFresh : casted.register .fresh = .natural base := by
    simp [casted, loaded, loadSlotResult, State.set, fresh]
  have storeSafe := PrefixSafe.storeSlot input casted base 18 budget .total
    (castSafe.final castRun) castFresh (by decide) (slotBits 18 (by decide))
    (by simpa only [casted, loaded, loadSlotResult, State.set, Nat.add_assoc] using pcBits)
  have tail := PrefixSafe.append input [.natToRat .total .total] (storeSlot 18 .total)
    loaded casted budget castRun castSafe storeSafe
  change PrefixSafe input (loadSlot 8 .total ++ ([.natToRat .total .total] ++ storeSlot 18 .total)) before budget
  exact PrefixSafe.append input (loadSlot 8 .total)
    ([.natToRat .total .total] ++ storeSlot 18 .total) before loaded budget loadRun loadSafe tail

end PDROC.EndpointOperands.Loop
