module

public import Structure.PA06_A19Prepare_BankPacked021
public import PaperProofs.Structure.PA17_PackedTranslator_034d
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Candidate prefix transport for the fixed bank-address ABI. It reuses
016's four-store replacement proof and the existing PackedAccessSafe.append;
no second interpreter or new runtime resource premise is introduced. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareBankPacked021

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM PA17PackedTranslator034
open CompactControllerClaims (dataHeap)

variable {bits : Nat}

/-- Real first reload followed by a proof-side 016 address view. -/
def reference (slot : Nat) (rom : PhysicalROM) (state : WordState bits) : WordState bits :=
  withAddress (pointer slot state) (executeOps rom (loadPointer slot) state)

/-- Both three-op reloads are executed. This index only identifies the
already-proved 016 heap phase at the same actual prefix; it is not runtime code. -/
def oldCount (count : Nat) : Nat :=
  if count < 3 then 0 else if count < 34 then count - 3 else if count < 37 then 31 else count - 6

theorem oldCount_le (count : Nat) (hc : count ≤ 72) : oldCount count ≤ 66 := by
  unfold oldCount
  split_ifs <;> omega

/-- The existing fixed direct phase reads only address/value/heap before
its first store. Scratch input registers do not affect ANY prefix heap. -/
theorem directWrite_input_heap (rom : PhysicalROM) (left right : WordState bits)
    (ha : left.register .address = right.register .address)
    (hv : left.register .value = right.register .value) (hh : left.heap = right.heap)
    (count : Nat) (hc : count ≤ 35) :
    (executeOps rom (PA06A19PrepareRuntimePacked016.directWrite.take count) left).heap =
      (executeOps rom (PA06A19PrepareRuntimePacked016.directWrite.take count) right).heap := by
  interval_cases count <;>
    simp +decide only [PA06A19PrepareRuntimePacked016.directWrite, List.take_succ_cons, List.take_zero,
      executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte, ha, hv, hh]

/-- This is the second EXECUTED bank load after clear; old need not have
survived clear. The actual heap frame proves that the reload recovers it. -/
theorem reload_pointer (q C slot : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 0 < bits)
    (hw : CapacityBits.width q ≤ bits) (ha : (pointer slot state).toNat < C)
    (hs : Fits bits ((pointer slot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((pointer slot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + slot)
    (hbankFit : Fits bits ((state.register .address).toNat + slot)) :
    let first := executeOps rom (loadPointer slot) state
    let middle := executeOps rom clear first
    (executeOps rom (loadPointer slot) middle).register .old = pointer slot state := by
  let first := executeOps rom (loadPointer slot) state
  let middle := executeOps rom clear first
  have hmidHeap : middle.heap = PA06A19PrepareRuntimePacked016.physicalClear (CapacityBits.width q)
      ((pointer slot state).toNat * CapacityBits.width q) state.heap :=
    clear_heap q rom first hh hb hw hs hf
  have hmidAddress : middle.register .address = state.register .address :=
    (clear_address rom first).trans (loadPointer_address slot rom state)
  change (executeOps rom (loadPointer slot) middle).register .old = pointer slot state
  rw [loadPointer_old, hmidAddress, hmidHeap, bankWord_eq]
  rw [physicalClear_bank_frame q C _ _ state.heap hq hb ha hbank hbankFit hf]
  exact (congrArg state.heap (bankWord_eq (state.register .address) slot)).symm

theorem safeWrite_prefix_heap_simulation (q C slot : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 0 < bits)
    (hw : CapacityBits.width q ≤ bits) (ha : (pointer slot state).toNat < C)
    (hs : Fits bits ((pointer slot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((pointer slot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + slot)
    (hbankFit : Fits bits ((state.register .address).toNat + slot))
    (count : Nat) (hc : count ≤ 72) :
    (executeOps rom ((safeWrite slot).take count) state).heap =
      (executeOps rom (PA06A19PrepareRuntimePacked016.safeWrite.take (oldCount count)) (reference slot rom state)).heap := by
  let first := executeOps rom (loadPointer slot) state
  let middle := executeOps rom clear first
  let second := executeOps rom (loadPointer slot) middle
  let modeled := executeOps rom PA06A19PrepareRuntimePacked016.clear (reference slot rom state)
  have hm : middle = withAddress (state.register .address) modeled := clear_simulation rom first
  have hmidHeap : middle.heap = modeled.heap := by
    have he := congrArg (fun s : WordState bits => s.heap) hm
    exact he
  have hmidValue : middle.register .value = modeled.register .value := by
    have he := congrArg (fun s : WordState bits => s.register .value) hm
    exact he
  have hsecondOld : second.register .old = pointer slot state :=
    reload_pointer q C slot rom state hh hq hb hw ha hs hf hbank hbankFit
  have hsecondAddress : (withAddress (second.register .old) second).register .address = modeled.register .address := by
    rw [PA06A19PrepareRuntimePacked016.clear_address]
    exact hsecondOld
  have hsecondValue : (withAddress (second.register .old) second).register .value = modeled.register .value :=
    (loadPointer_value slot rom middle).trans hmidValue
  have hsecondHeap : (withAddress (second.register .old) second).heap = modeled.heap := hmidHeap
  by_cases h0 : count < 3
  · rw [oldCount, ite_eq_left h0, List.take_zero, executeOps]
    have hactual : (safeWrite slot).take count = (loadPointer slot).take count := by
      change ((loadPointer slot ++ clear ++ loadPointer slot) ++ directWrite).take count = _
      rw [List.take_append_of_le_length (show count ≤ (loadPointer slot ++ clear ++ loadPointer slot).length by
          simp only [List.length_append, loadPointer_length, clear_length]; omega),
        List.take_append_of_le_length (show count ≤ (loadPointer slot ++ clear).length by
          simp only [List.length_append, loadPointer_length, clear_length]; omega),
        List.take_append_of_le_length (show count ≤ (loadPointer slot).length by rw [loadPointer_length]; omega)]
    calc
      _ = (executeOps rom ((loadPointer slot).take count) state).heap :=
        congrArg (fun code => (executeOps rom code state).heap) hactual
      _ = state.heap := loadPointer_prefix_heap slot rom state count
      _ = (reference slot rom state).heap := rfl
  · rw [oldCount, ite_eq_right h0]
    by_cases h1 : count < 34
    · rw [ite_eq_left h1]
      have hk : count - 3 ≤ clear.length := by rw [clear_length]; omega
      have hactual : (safeWrite slot).take count = loadPointer slot ++ clear.take (count - 3) := by
        change ((loadPointer slot ++ clear ++ loadPointer slot) ++ directWrite).take count = _
        rw [List.take_append_of_le_length (show count ≤ (loadPointer slot ++ clear ++ loadPointer slot).length by
            simp only [List.length_append, loadPointer_length, clear_length]; omega),
          List.take_append_of_le_length (show count ≤ (loadPointer slot ++ clear).length by
            simp only [List.length_append, loadPointer_length, clear_length]; omega),
          List.take_append, List.take_of_length_le (show (loadPointer slot).length ≤ count by rw [loadPointer_length]; omega),
          loadPointer_length]
      have href : PA06A19PrepareRuntimePacked016.safeWrite.take (count - 3) =
          PA06A19PrepareRuntimePacked016.clear.take (count - 3) := by
        change (PA06A19PrepareRuntimePacked016.clear ++ PA06A19PrepareRuntimePacked016.directWrite).take (count - 3) = _
        exact List.take_append_of_le_length (show count - 3 ≤ PA06A19PrepareRuntimePacked016.clear.length by
          simpa only [PA06A19PrepareRuntimePacked016.clear_length, clear_length] using hk)
      rw [hactual, href, executeOps_append]
      have he := congrArg (fun s : WordState bits => s.heap) (clear_prefix_simulation rom first (count - 3) hk)
      exact he
    · rw [ite_eq_right h1]
      by_cases h2 : count < 37
      · rw [ite_eq_left h2]
        have hactual : (safeWrite slot).take count =
            loadPointer slot ++ clear ++ (loadPointer slot).take (count - 34) := by
          change ((loadPointer slot ++ clear ++ loadPointer slot) ++ directWrite).take count = _
          rw [List.take_append_of_le_length (show count ≤ (loadPointer slot ++ clear ++ loadPointer slot).length by
              simp only [List.length_append, loadPointer_length, clear_length]; omega),
            List.take_append, List.take_of_length_le (show (loadPointer slot ++ clear).length ≤ count by
              simp only [List.length_append, loadPointer_length, clear_length]; omega)]
          have hlen : (loadPointer slot ++ clear).length = 34 := rfl
          rw [hlen]
        have htake : PA06A19PrepareRuntimePacked016.clear.take 31 = PA06A19PrepareRuntimePacked016.clear := by
          simpa only [PA06A19PrepareRuntimePacked016.clear_length] using
            (List.take_length (l := PA06A19PrepareRuntimePacked016.clear))
        have href : PA06A19PrepareRuntimePacked016.safeWrite.take 31 = PA06A19PrepareRuntimePacked016.clear := by
          rw [PA06A19PrepareRuntimePacked016.safeWrite,
            List.take_append_of_le_length (show 31 ≤ PA06A19PrepareRuntimePacked016.clear.length from le_rfl)]
          exact htake
        rw [hactual, href]
        calc
          _ = (executeOps rom ((loadPointer slot).take (count - 34)) middle).heap := by
            rw [executeOps_append, executeOps_append]
          _ = middle.heap := loadPointer_prefix_heap slot rom middle (count - 34)
          _ = modeled.heap := hmidHeap
      · rw [ite_eq_right h2]
        have hd : count - 37 ≤ 35 := by omega
        have hactual : (safeWrite slot).take count =
            loadPointer slot ++ clear ++ loadPointer slot ++ directWrite.take (count - 37) := by
          change ((loadPointer slot ++ clear ++ loadPointer slot) ++ directWrite).take count = _
          rw [List.take_append, List.take_of_length_le (show (loadPointer slot ++ clear ++ loadPointer slot).length ≤ count by
            simp only [List.length_append, loadPointer_length, clear_length]; omega)]
          have hlen : (loadPointer slot ++ clear ++ loadPointer slot).length = 37 := rfl
          rw [hlen]
        have htake : PA06A19PrepareRuntimePacked016.clear.take (count - 6) = PA06A19PrepareRuntimePacked016.clear :=
          List.take_of_length_le (show PA06A19PrepareRuntimePacked016.clear.length ≤ count - 6 by
            rw [PA06A19PrepareRuntimePacked016.clear_length]; omega)
        have href : PA06A19PrepareRuntimePacked016.safeWrite.take (count - 6) =
            PA06A19PrepareRuntimePacked016.clear ++ PA06A19PrepareRuntimePacked016.directWrite.take (count - 37) := by
          rw [PA06A19PrepareRuntimePacked016.safeWrite, List.take_append, htake,
            PA06A19PrepareRuntimePacked016.clear_length, show count - 6 - 31 = count - 37 by omega]
        rw [hactual, href, executeOps_append, executeOps_append, executeOps_append, executeOps_append]
        change (executeOps rom (directWrite.take (count - 37)) second).heap =
          (executeOps rom (PA06A19PrepareRuntimePacked016.directWrite.take (count - 37)) modeled).heap
        calc
          _ = (executeOps rom (PA06A19PrepareRuntimePacked016.directWrite.take (count - 37))
              (withAddress (second.register .old) second)).heap := by
            have he := congrArg (fun s : WordState bits => s.heap)
              (directWrite_prefix_simulation rom second (count - 37) hd)
            exact he
          _ = _ := directWrite_input_heap rom (withAddress (second.register .old) second) modeled
            hsecondAddress hsecondValue hsecondHeap (count - 37) hd

theorem safeWrite_prefix_header (q C slot : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 0 < bits)
    (hw : CapacityBits.width q ≤ bits) (ha : (pointer slot state).toNat < C)
    (hs : Fits bits ((pointer slot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((pointer slot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + slot)
    (hbankFit : Fits bits ((state.register .address).toNat + slot))
    (count : Nat) (hc : count ≤ 72) :
    PA06A19PrepareRuntimePacked016.Header q (executeOps rom ((safeWrite slot).take count) state).heap := by
  rw [safeWrite_prefix_heap_simulation q C slot rom state hh hq hb hw ha hs hf hbank hbankFit count hc]
  exact PA06A19PrepareRuntimePacked016.safeWrite_prefix_header q rom (reference slot rom state)
    hh hb hw hs hf (oldCount count) (oldCount_le count hc)

theorem safeWrite_prefix_capacityBounded (q C slot : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 0 < bits)
    (hw : CapacityBits.width q ≤ bits) (ha : (pointer slot state).toNat < C)
    (hs : Fits bits ((pointer slot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((pointer slot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + slot)
    (hbankFit : Fits bits ((state.register .address).toNat + slot))
    (hregion : Fits bits (C * CapacityBits.width q)) (hv : (state.register .value).toNat ≤ q)
    (hbound : CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap state.heap)))
    (count : Nat) (hc : count ≤ 72) :
    CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap (executeOps rom ((safeWrite slot).take count) state).heap)) := by
  rw [safeWrite_prefix_heap_simulation q C slot rom state hh hq hb hw ha hs hf hbank hbankFit count hc]
  exact PA06A19PrepareRuntimePacked016.safeWrite_prefix_capacityBounded q C rom (reference slot rom state)
    hh hb hw hs hf hregion ha hv hbound (oldCount count) (oldCount_le count hc)

theorem safeWrite_prefix_frame (q C slot other : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 0 < bits)
    (hw : CapacityBits.width q ≤ bits) (ha : (pointer slot state).toNat < C)
    (hs : Fits bits ((pointer slot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((pointer slot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + slot)
    (hbankFit : Fits bits ((state.register .address).toNat + slot))
    (hregion : Fits bits (C * CapacityBits.width q)) (hv : (state.register .value).toNat ≤ q)
    (hwhere : (other < C ∧ other ≠ (pointer slot state).toNat) ∨
      (C ≤ other ∧ Fits bits (packedCapacityWords q C bits + (other - C))))
    (count : Nat) (hc : count ≤ 72) :
    unpackHeap q C bits (dataHeap (executeOps rom ((safeWrite slot).take count) state).heap) other =
      unpackHeap q C bits (dataHeap state.heap) other := by
  rw [safeWrite_prefix_heap_simulation q C slot rom state hh hq hb hw ha hs hf hbank hbankFit count hc]
  exact PA06A19PrepareRuntimePacked016.safeWrite_prefix_frame q C other rom (reference slot rom state)
    hh hb hw hs hf hregion ha hv hwhere (oldCount count) (oldCount_le count hc)

theorem clear_access_eq (rom : PhysicalROM) (heapWords : Nat) (state : WordState bits)
    (count : Nat) (hc : count < 31) :
    packingAccessFits rom heapWords (executeOps rom (clear.take count) state) clear[count] =
      packingAccessFits rom heapWords
        (executeOps rom (PA06A19PrepareRuntimePacked016.clear.take count) (withAddress (state.register .old) state))
        PA06A19PrepareRuntimePacked016.clear[count] := by
  rw [clear_prefix_simulation rom state count hc.le]
  interval_cases count <;> rfl

theorem clear_accessSafe (q heapWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hb : 7 ≤ bits)
    (hw : CapacityBits.width q ≤ bits)
    (hs : Fits bits ((state.register .old).toNat * CapacityBits.width q))
    (hf : Fits bits ((state.register .old).toNat * CapacityBits.width q / bits + 4 + 1))
    (hl : (state.register .old).toNat * CapacityBits.width q / bits + 4 + 1 < heapWords) :
    PackedAccessSafe heapWords rom clear state := by
  intro count hc
  rw [clear_access_eq rom heapWords state count hc]
  exact PA06A19PrepareRuntimePacked016.clear_accessFits_executeOps q heapWords rom
    (withAddress (state.register .old) state) hh hb hw hs hf hl count hc

theorem directWrite_access_eq (rom : PhysicalROM) (heapWords : Nat) (state : WordState bits)
    (count : Nat) (hc : count < 35) :
    packingAccessFits rom heapWords (executeOps rom (directWrite.take count) state) directWrite[count] =
      packingAccessFits rom heapWords
        (executeOps rom (PA06A19PrepareRuntimePacked016.directWrite.take count) (withAddress (state.register .old) state))
        PA06A19PrepareRuntimePacked016.directWrite[count] := by
  rw [directWrite_prefix_simulation rom state count hc.le]
  interval_cases count <;> rfl

theorem directWrite_accessSafe (q heapWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hb : 7 ≤ bits)
    (hw : CapacityBits.width q ≤ bits)
    (hs : Fits bits ((state.register .old).toNat * CapacityBits.width q))
    (hf : Fits bits ((state.register .old).toNat * CapacityBits.width q / bits + 4 + 1))
    (hl : (state.register .old).toNat * CapacityBits.width q / bits + 4 + 1 < heapWords) :
    PackedAccessSafe heapWords rom directWrite state := by
  intro count hc
  rw [directWrite_access_eq rom heapWords state count hc]
  exact PA06A19PrepareRuntimePacked016.directWrite_accessFits_executeOps q heapWords rom
    (withAddress (state.register .old) state) hh hb hw hs hf hl count hc

theorem loadPointer_accessSafe (slot heapWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hf : Fits bits ((state.register .address).toNat + slot))
    (hl : (state.register .address).toNat + slot < heapWords) :
    PackedAccessSafe heapWords rom (loadPointer slot) state := by
  intro count hc
  change count < 3 at hc
  interval_cases count <;> try exact True.intro
  change (state.register .address + BitVec.ofNat bits slot).toNat < heapWords
  rw [bankWord_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf]
  exact hl

theorem safeWrite_accessSafe (q C slot heapWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 9 ≤ bits)
    (hw : CapacityBits.width q ≤ bits) (ha : (pointer slot state).toNat < C)
    (hs : Fits bits ((pointer slot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((pointer slot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hl : (pointer slot state).toNat * CapacityBits.width q / bits + 4 + 1 < heapWords)
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + slot)
    (hbankFit : Fits bits ((state.register .address).toNat + slot))
    (hbankH : (state.register .address).toNat + slot < heapWords) :
    PackedAccessSafe heapWords rom (safeWrite slot) state := by
  let first := executeOps rom (loadPointer slot) state
  let middle := executeOps rom clear first
  let second := executeOps rom (loadPointer slot) middle
  have hmidAddress : middle.register .address = state.register .address :=
    (clear_address rom first).trans (loadPointer_address slot rom state)
  have hsecondOld : second.register .old = pointer slot state :=
    reload_pointer q C slot rom state hh hq (by omega) hw ha hs hf hbank hbankFit
  have hmidHeader : PA06A19PrepareRuntimePacked016.Header q middle.heap :=
    clear_header q rom first hh (by omega) hw hs hf
  unfold safeWrite
  apply PackedAccessSafe.append _ _ _ _ _ (loadPointer_accessSafe slot heapWords rom state hbankFit hbankH)
  apply PackedAccessSafe.append _ _ clear _ first (clear_accessSafe q heapWords rom first hh (by omega) hw hs hf hl)
  apply PackedAccessSafe.append _ _ (loadPointer slot) directWrite middle
    (loadPointer_accessSafe slot heapWords rom middle (by rwa [hmidAddress]) (by rwa [hmidAddress]))
  exact directWrite_accessSafe q heapWords rom second hmidHeader (by omega) hw
    (by rwa [hsecondOld]) (by rwa [hsecondOld]) (by rwa [hsecondOld])

theorem safeWrite_run_accessFits (q C slot heapWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 9 ≤ bits)
    (hslot : slot ≤ 511) (hw : CapacityBits.width q ≤ bits) (ha : (pointer slot state).toNat < C)
    (hs : Fits bits ((pointer slot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((pointer slot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hl : (pointer slot state).toNat * CapacityBits.width q / bits + 4 + 1 < heapWords)
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + slot)
    (hbankFit : Fits bits ((state.register .address).toNat + slot))
    (hbankH : (state.register .address).toNat + slot < heapWords)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false)
    (count : Nat) (hc : count < (safeWrite slot).length) :
    packingAccessFits rom heapWords (packingRun rom (safeWrite slot) count state) (safeWrite slot)[count] := by
  rw [packingRun_eq_executeOps_take rom (safeWrite slot) state (safeWrite_straight slot)
    (safeWrite_code_fit slot hslot hb) (safeWrite_pc_fit slot hb) hpc hactive count hc.le]
  exact safeWrite_accessSafe q C slot heapWords rom state hh hq hb hw ha hs hf hl hbank hbankFit hbankH count hc

/-- Exact new Root control-bank placement. This is pure room in the
ORIGINAL A19 8192*D allocation; no old 013 Room bank is reused here. -/
theorem root_control_room (N q t C slot : Nat) (hs : slot ≤ 511) :
    4 + packedCapacityWords q C (indexWidth 32 N q) + 4096 * (N + q + t + 1) + slot <
      4 + packedCapacityWords q C (indexWidth 32 N q) + 8192 * (N + q + t + 1) := by
  omega

theorem root_control_after_lookahead (N q t C slot : Nat) :
    4 + packedCapacityWords q C (indexWidth 32 N q) + 1 ≤
      4 + packedCapacityWords q C (indexWidth 32 N q) + 4096 * (N + q + t + 1) + slot := by
  omega

theorem root_control_fits (N q t C slot : Nat) (hs : slot ≤ 511)
    (hf : Fits (indexWidth 32 N q)
      (4 + packedCapacityWords q C (indexWidth 32 N q) + 8192 * (N + q + t + 1))) :
    Fits (indexWidth 32 N q)
      (4 + packedCapacityWords q C (indexWidth 32 N q) + 4096 * (N + q + t + 1) + slot) :=
  (root_control_room N q t C slot hs).trans hf

theorem safeWrite_run_prefix_capacityBounded (q C slot : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 9 ≤ bits)
    (hslot : slot ≤ 511) (hw : CapacityBits.width q ≤ bits) (ha : (pointer slot state).toNat < C)
    (hs : Fits bits ((pointer slot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((pointer slot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + slot)
    (hbankFit : Fits bits ((state.register .address).toNat + slot))
    (hregion : Fits bits (C * CapacityBits.width q)) (hv : (state.register .value).toNat ≤ q)
    (hbound : CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap state.heap)))
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false)
    (count : Nat) (hc : count ≤ 72) :
    CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap (packingRun rom (safeWrite slot) count state).heap)) := by
  rw [packingRun_eq_executeOps_take rom (safeWrite slot) state (safeWrite_straight slot)
    (safeWrite_code_fit slot hslot hb) (safeWrite_pc_fit slot hb) hpc hactive count (by rwa [safeWrite_length])]
  exact safeWrite_prefix_capacityBounded q C slot rom state hh hq (by omega) hw ha hs hf hbank hbankFit hregion hv hbound count hc

theorem safeWrite_run_prefix_header (q C slot : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 9 ≤ bits)
    (hslot : slot ≤ 511) (hw : CapacityBits.width q ≤ bits) (ha : (pointer slot state).toNat < C)
    (hs : Fits bits ((pointer slot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((pointer slot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + slot)
    (hbankFit : Fits bits ((state.register .address).toNat + slot))
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false)
    (count : Nat) (hc : count ≤ 72) :
    PA06A19PrepareRuntimePacked016.Header q (packingRun rom (safeWrite slot) count state).heap := by
  rw [packingRun_eq_executeOps_take rom (safeWrite slot) state (safeWrite_straight slot)
    (safeWrite_code_fit slot hslot hb) (safeWrite_pc_fit slot hb) hpc hactive count (by rwa [safeWrite_length])]
  exact safeWrite_prefix_header q C slot rom state hh hq (by omega) hw ha hs hf hbank hbankFit count hc

theorem safeWrite_run_prefix_frame (q C slot other : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 9 ≤ bits)
    (hslot : slot ≤ 511) (hw : CapacityBits.width q ≤ bits) (ha : (pointer slot state).toNat < C)
    (hs : Fits bits ((pointer slot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((pointer slot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + slot)
    (hbankFit : Fits bits ((state.register .address).toNat + slot))
    (hregion : Fits bits (C * CapacityBits.width q)) (hv : (state.register .value).toNat ≤ q)
    (hwhere : (other < C ∧ other ≠ (pointer slot state).toNat) ∨
      (C ≤ other ∧ Fits bits (packedCapacityWords q C bits + (other - C))))
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false)
    (count : Nat) (hc : count ≤ 72) :
    unpackHeap q C bits (dataHeap (packingRun rom (safeWrite slot) count state).heap) other =
      unpackHeap q C bits (dataHeap state.heap) other := by
  rw [packingRun_eq_executeOps_take rom (safeWrite slot) state (safeWrite_straight slot)
    (safeWrite_code_fit slot hslot hb) (safeWrite_pc_fit slot hb) hpc hactive count (by rwa [safeWrite_length])]
  exact safeWrite_prefix_frame q C slot other rom state hh hq (by omega) hw ha hs hf hbank hbankFit hregion hv hwhere count hc

theorem safeWrite_run_target (q C slot : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 9 ≤ bits)
    (hslot : slot ≤ 511) (hw : CapacityBits.width q ≤ bits) (ha : (pointer slot state).toNat < C)
    (hs : Fits bits ((pointer slot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((pointer slot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + slot)
    (hbankFit : Fits bits ((state.register .address).toNat + slot)) (hv : (state.register .value).toNat ≤ q)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    unpackHeap q C bits (dataHeap (packingRun rom (safeWrite slot) 72 state).heap) (pointer slot state).toNat =
      (state.register .value).toNat := by
  rw [safeWrite_run_body slot rom state hslot hb hpc hactive,
    safeWrite_heap q C slot rom state hh hq (by omega) hw ha hs hf hbank hbankFit,
    PA06A19PrepareRuntimePacked016.dataHeap_physicalWrite]
  exact unpackHeap_write_target q C _ _ (dataHeap state.heap) (by omega) hw ha
    ((show (pointer slot state).toNat * CapacityBits.width q / bits + 1 ≤
      (pointer slot state).toNat * CapacityBits.width q / bits + 4 + 1 by omega).trans_lt hf)
    (CapacityBits.value_lt_two_pow_width q _ hv)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareBankPacked021
