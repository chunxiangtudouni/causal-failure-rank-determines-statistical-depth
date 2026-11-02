module

public import Structure.PA06_A19Prepare_InitialUsed037_Setup
public import Structure.PA06_A19Prepare_PackedView013
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Candidate real88-op used-loop body. The existing72-op packed writer
is embedded in the same containing code. Small read/advance facts do not
assume any post-writer hardware cursor survives: both cursors are reloaded. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareInitialUsed037

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PSTRBuildLower
open AlgorithmClaims.PackedCapacityRAM
open PA17PackedTranslator034 (PackedAccessSafe)

variable {bits : Nat}

theorem readUsed_heap (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom readUsed state).heap = state.heap := rfl
theorem readUsed_address (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom readUsed state).register .address = state.register .address := rfl
theorem readUsed_value (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom readUsed state).register .value = BitVec.ofNat bits
      (rom.semantic.read .input (state.heap (state.register .address + BitVec.ofNat bits cursorSlot)).toNat) := by
  simp [readUsed, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction,
    PhysicalROM.semantic]

theorem readUsed_prefix_heap (rom : PhysicalROM) (state : WordState bits) (count : Nat) :
    (executeOps rom (readUsed.take count) state).heap = state.heap := by
  by_cases hc : count ≤ 4
  · interval_cases count <;> rfl
  · rw [List.take_of_length_le (by rw [readUsed_length]; omega)]
    rfl

theorem advance_heap (slot : Nat) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (advance slot) state).heap = Function.update state.heap
      (state.register .address + BitVec.ofNat bits slot)
      (state.heap (state.register .address + BitVec.ofNat bits slot) + BitVec.ofNat bits 1) := by
  simp [advance, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem advance_address (slot : Nat) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (advance slot) state).register .address = state.register .address := rfl

theorem advance_prefix_heap (slot : Nat) (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) (hc : count ≤ 6) :
    (executeOps rom ((advance slot).take count) state).heap =
      if count < 6 then state.heap else Function.update state.heap
        (state.register .address + BitVec.ofNat bits slot)
        (state.heap (state.register .address + BitVec.ofNat bits slot) + BitVec.ofNat bits 1) := by
  interval_cases count <;> rfl

theorem advance_prefix_address (slot : Nat) (rom : PhysicalROM) (state : WordState bits) (count : Nat) :
    (executeOps rom ((advance slot).take count) state).register .address = state.register .address := by
  by_cases hc : count ≤ 6
  · interval_cases count <;> rfl
  · rw [List.take_of_length_le (by rw [advance_length]; omega)]
    rfl

theorem readUsed_accessSafe (rom : PhysicalROM) (H : Nat) (state : WordState bits)
    (hfit : Fits bits ((state.register .address).toNat + cursorSlot))
    (hroom : (state.register .address).toNat + cursorSlot < H)
    (hrom : (state.heap (state.register .address + BitVec.ofNat bits cursorSlot)).toNat < (rom.words .input).length) :
    PackedAccessSafe H rom readUsed state := by
  intro count hc
  change count < 4 at hc
  interval_cases count
  · trivial
  · trivial
  · change (state.register .address + BitVec.ofNat bits cursorSlot).toNat < H
    rw [PA06A19PrepareBankPacked021.bankWord_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
    exact hroom
  · exact hrom

theorem advance_accessSafe (slot : Nat) (rom : PhysicalROM) (H : Nat) (state : WordState bits)
    (hfit : Fits bits ((state.register .address).toNat + slot))
    (hroom : (state.register .address).toNat + slot < H) :
    PackedAccessSafe H rom (advance slot) state := by
  intro count hc
  change count < 6 at hc
  interval_cases count <;> try exact True.intro
  all_goals
    change (state.register .address + BitVec.ofNat bits slot).toNat < H
    rw [PA06A19PrepareBankPacked021.bankWord_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
    exact hroom

/-- Reuse013's ordinary-update capacity frame for a true relative store.
Only the addressed control word is updated; no new packed ISA is introduced. -/
theorem advance_prefix_capacity (q C slot : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hb : 0 < bits) (hregion : Fits bits (C * CapacityBits.width q))
    (hafter : 4 + packedCapacityWords q C bits ≤ (state.register .address).toNat + slot)
    (hfit : Fits bits ((state.register .address).toNat + slot))
    (count : Nat) (hc : count ≤ 6) (other : Nat) (ho : other < C) :
    unpackHeap q C bits (dataHeap (executeOps rom ((advance slot).take count) state).heap) other =
      unpackHeap q C bits (dataHeap state.heap) other := by
  rw [advance_prefix_heap slot rom state count hc]
  split_ifs with hcount
  · rfl
  · simp only [PA06A19PrepareBankPacked021.bankWord_eq]
    have hh := PA06A19PreparePackedView013.indexStore_capacity_frame q 0 C
      ((state.register .address).toNat + slot) 0
      (state.heap (BitVec.ofNat bits ((state.register .address).toNat + slot)) + BitVec.ofNat bits 1)
      state.heap hb hregion hafter (by simpa only [Nat.sub_self, Nat.add_zero] using hfit) other ho
    simpa only [PA06A19PreparePackedView013.indexStore, Nat.sub_self, Nat.add_zero,
      PA06A19PrepareBankPacked021.bankWord_eq] using hh

theorem advance_prefix_header (q slot : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap)
    (hafter : 4 ≤ (state.register .address).toNat + slot)
    (hfit : Fits bits ((state.register .address).toNat + slot))
    (count : Nat) (hc : count ≤ 6) :
    PA06A19PrepareRuntimePacked016.Header q (executeOps rom ((advance slot).take count) state).heap := by
  rw [advance_prefix_heap slot rom state count hc]
  split_ifs with hcount
  · exact hh
  · simp only [PA06A19PrepareBankPacked021.bankWord_eq]
    exact PA06A19PrepareRuntimePacked016.update_header q _ _ _ hh hafter hfit

theorem body_run (rom : PhysicalROM) (left right : List PackingOp)
    (hcode : WordsFit bits (packingCode (left ++ body ++ right)))
    (hpcCode : Fits bits (5 * (left ++ body ++ right).length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false) :
    packingRun rom (left ++ body ++ right) 88 state = executeOps rom body state := by
  have hh := PSTRWordSegments.straight_segment rom (left ++ body ++ right) body left.length
    (by simp only [List.length_append]; omega) (PA17UniformGenerator035a.segment_index left body right)
    body_straight hcode hpcCode state hpc ha
  simpa only [body_length] using hh

theorem readUsed_initial_bit (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (state : WordState bits) (tool : Fin q)
    (hcursor : (state.heap (state.register .address + BitVec.ofNat bits cursorSlot)).toNat =
      2 + full.length * q + tool.val) :
    (executeOps (controllerInput q full used) readUsed state).register .value =
      BitVec.ofNat bits (bit (decide (tool ∈ used))) := by
  rw [readUsed_value, hcursor, PA06A19PrepareFinalHeader033InitialUsedROM.used_bit_read]

def bodyHeap (q : Nat) (rom : PhysicalROM) (state : WordState bits) : BitVec bits → BitVec bits :=
  let value := BitVec.ofNat bits
    (rom.semantic.read .input (state.heap (state.register .address + BitVec.ofNat bits cursorSlot)).toNat)
  let written := PA06A19PrepareRuntimePacked016.physicalWrite (CapacityBits.width q)
    ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q) value state.heap
  let advanced := Function.update written (state.register .address + BitVec.ofNat bits pointerSlot)
    (written (state.register .address + BitVec.ofNat bits pointerSlot) + BitVec.ofNat bits 1)
  Function.update advanced (state.register .address + BitVec.ofNat bits cursorSlot)
    (advanced (state.register .address + BitVec.ofNat bits cursorSlot) + BitVec.ofNat bits 1)

/-- Exact effect of all88 real body instructions. In particular each
advance reloads the heap produced by the actual preceding writer. -/
theorem body_heap (q C : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 0 < bits)
    (hw : CapacityBits.width q ≤ bits)
    (ha : (PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat < C)
    (hs : Fits bits ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + pointerSlot)
    (hbankFit : Fits bits ((state.register .address).toNat + pointerSlot)) :
    (executeOps rom body state).heap = bodyHeap q rom state := by
  let loaded := executeOps rom readUsed state
  let written := executeOps rom (PA06A19PrepareBankPacked021.safeWrite pointerSlot) loaded
  let advanced := executeOps rom (advance pointerSlot) written
  have hloadedH : loaded.heap = state.heap := readUsed_heap rom state
  have hloadedA : loaded.register .address = state.register .address := readUsed_address rom state
  have hloadedP : PA06A19PrepareBankPacked021.pointer pointerSlot loaded =
      PA06A19PrepareBankPacked021.pointer pointerSlot state := by
    unfold PA06A19PrepareBankPacked021.pointer
    rw [hloadedH, hloadedA]
  have hwriteH := PA06A19PrepareBankPacked021.safeWrite_heap q C pointerSlot rom loaded
    (by rw [hloadedH]; exact hh) hq hb hw (by rw [hloadedP]; exact ha)
    (by rw [hloadedP]; exact hs) (by rw [hloadedP]; exact hf)
    (by rw [hloadedA]; exact hbank) (by rw [hloadedA]; exact hbankFit)
  have hwrittenH : written.heap = PA06A19PrepareRuntimePacked016.physicalWrite (CapacityBits.width q)
      ((PA06A19PrepareBankPacked021.pointer pointerSlot state).toNat * CapacityBits.width q)
      (BitVec.ofNat bits (rom.semantic.read .input
        (state.heap (state.register .address + BitVec.ofNat bits cursorSlot)).toNat)) state.heap := by
    simpa only [hloadedP, hloadedH, loaded, readUsed_value] using hwriteH
  have hwriteA : written.register .address = state.register .address :=
    (PA06A19PrepareBankPacked021.safeWrite_address pointerSlot rom loaded).trans hloadedA
  have hadvanceA : advanced.register .address = state.register .address :=
    (advance_address pointerSlot rom written).trans hwriteA
  have hadvanceH : advanced.heap = Function.update written.heap
      (state.register .address + BitVec.ofNat bits pointerSlot)
      (written.heap (state.register .address + BitVec.ofNat bits pointerSlot) + BitVec.ofNat bits 1) := by
    simpa only [hwriteA] using advance_heap pointerSlot rom written
  have hlast : (executeOps rom (advance cursorSlot) advanced).heap = Function.update advanced.heap
      (state.register .address + BitVec.ofNat bits cursorSlot)
      (advanced.heap (state.register .address + BitVec.ofNat bits cursorSlot) + BitVec.ofNat bits 1) := by
    simpa only [hadvanceA] using advance_heap cursorSlot rom advanced
  simp only [body, executeOps_append]
  change (executeOps rom (advance cursorSlot) advanced).heap = _
  rw [hlast, hadvanceH, hwrittenH]
  rfl

theorem body_address (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom body state).register .address = state.register .address := by
  simp only [body, executeOps_append, advance_address, PA06A19PrepareBankPacked021.safeWrite_address,
    readUsed_address]

end PaperProofs.Structure.LaminarTree.PA06A19PrepareInitialUsed037
