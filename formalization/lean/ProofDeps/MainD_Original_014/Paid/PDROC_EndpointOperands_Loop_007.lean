module

public import Paid.PDROC_EndpointOperands_Loop_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 750000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver RootD27.Bits
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult)
open PDROC.CalibrationRow.Operand

def pairLoadCode : List Instruction :=
  loadSlot 9 .flag ++ loadSlot 11 .old ++ loadSlot 8 .index ++ loadSlot 0 .total

/-- The four genuine source reads precede all cache-pointer arithmetic.
Their old source cells retain the actual caller B, including arbitrary
cells not used as this row's error/charge in a generic incoming header. -/
theorem pairLoads_safe (input : List Cell) (before : State)
    (base E m budget : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh = .natural base)
    (cache : values 0 = .natural E) (row : values 8 = .natural m)
    (safe : SafeBits before budget)
    (addressBits : 1 + natBits (base + headerWords) ≤ budget)
    (pcBits : natBits (before.pc + 12) ≤ budget) :
    ∃ loaded, linearExecute input pairLoadCode before = some loaded ∧
      PrefixSafe input pairLoadCode before budget ∧ Header loaded base values ∧
      loaded.register .fresh = .natural base ∧ loaded.register .index = .natural m ∧
      loaded.register .total = .natural E ∧ loaded.pc = before.pc + 12 := by
  let first := loadSlotResult before base 9 .flag
  let second := loadSlotResult first base 11 .old
  let third := loadSlotResult second base 8 .index
  let loaded := loadSlotResult third base 0 .total
  have slotBits (slot : ℕ) (inside : slot < headerWords) :
      1 + natBits (base + slot) ≤ budget :=
    (Nat.add_le_add_left (PDROC.DataBits.natBits_mono (by omega : base + slot ≤ base + headerWords)) 1).trans addressBits
  have firstRun := (header.loadSlot_execute input 9 .flag (by decide) fresh).1
  have firstSafe := PrefixSafe.loadSlot input before base 9 budget .flag safe fresh
    (header.live 9 (by decide)) (slotBits 9 (by decide))
    ((PDROC.DataBits.natBits_mono (by omega : before.pc + 3 ≤ before.pc + 12)).trans pcBits)
  have firstFresh : first.register .fresh = .natural base := by
    simp [first, loadSlotResult, fresh]
  have firstHeader : Header first base values := header
  have secondRun := (firstHeader.loadSlot_execute input 11 .old (by decide) firstFresh).1
  have secondSafe := PrefixSafe.loadSlot input first base 11 budget .old
    (firstSafe.final firstRun) firstFresh (firstHeader.live 11 (by decide)) (slotBits 11 (by decide))
    (by simpa only [first, loadSlotResult, Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc + 6 ≤ before.pc + 12)).trans pcBits))
  have secondFresh : second.register .fresh = .natural base := by
    simp [second, first, loadSlotResult, fresh]
  have secondHeader : Header second base values := header
  have thirdRun := (secondHeader.loadSlot_execute input 8 .index (by decide) secondFresh).1
  have thirdSafe := PrefixSafe.loadSlot input second base 8 budget .index
    (secondSafe.final secondRun) secondFresh (secondHeader.live 8 (by decide)) (slotBits 8 (by decide))
    (by simpa only [second, first, loadSlotResult, Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc + 9 ≤ before.pc + 12)).trans pcBits))
  have thirdFresh : third.register .fresh = .natural base := by
    simp [third, second, first, loadSlotResult, fresh]
  have thirdHeader : Header third base values := header
  have loadedRun := (thirdHeader.loadSlot_execute input 0 .total (by decide) thirdFresh).1
  have loadedSafe := PrefixSafe.loadSlot input third base 0 budget .total
    (thirdSafe.final thirdRun) thirdFresh (thirdHeader.live 0 (by decide)) (slotBits 0 (by decide))
    (by simpa only [third, second, first, loadSlotResult, Nat.add_assoc] using pcBits)
  have tail := PrefixSafe.append input (loadSlot 8 .index) (loadSlot 0 .total)
    second third budget thirdRun thirdSafe loadedSafe
  have suffix := PrefixSafe.append input (loadSlot 11 .old)
    (loadSlot 8 .index ++ loadSlot 0 .total) first second budget secondRun secondSafe tail
  have prefixes : PrefixSafe input pairLoadCode before budget :=
    PrefixSafe.append input (loadSlot 9 .flag) (loadSlot 11 .old ++ (loadSlot 8 .index ++ loadSlot 0 .total))
      before first budget firstRun firstSafe suffix
  have run : linearExecute input pairLoadCode before = some loaded := by
    change linearExecute input (loadSlot 9 .flag ++ (loadSlot 11 .old ++ (loadSlot 8 .index ++ loadSlot 0 .total))) before = some loaded
    rw [PDLower.CalibrationCompute.linearExecute_append, firstRun, Option.bind_some]
    change linearExecute input (loadSlot 11 .old ++ (loadSlot 8 .index ++ loadSlot 0 .total)) first = some loaded
    rw [PDLower.CalibrationCompute.linearExecute_append, secondRun, Option.bind_some]
    change linearExecute input (loadSlot 8 .index ++ loadSlot 0 .total) second = some loaded
    rw [PDLower.CalibrationCompute.linearExecute_append, thirdRun, Option.bind_some]
    exact loadedRun
  have loadedIndex : loaded.register .index = .natural m := by
    change third.register .index = .natural m
    exact (secondHeader.loadSlot_execute input 8 .index (by decide) secondFresh).2.trans row
  refine ⟨loaded, run, prefixes, header, ?_, loadedIndex,
    (thirdHeader.loadSlot_execute input 0 .total (by decide) thirdFresh).2.trans cache, ?_⟩
  · simp [loaded, third, second, first, loadSlotResult, fresh]
  · simp [loaded, third, second, first, loadSlotResult, Nat.add_assoc]

end PDROC.EndpointOperands.Loop
