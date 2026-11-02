module

public import Structure.PSTR_HD_StaticFields_022
import Mathlib.Tactic.IntervalCases

/-! Every actual field-reader access is to the original raw N word or the
same persistent cache. These blocks include full runtime offset formation. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PSTRStaticFields

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine PSTRStaticLayout PSTRStaticHeap
open RawTreePreprocessingClaims

theorem prefix_access {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (field : Fin 9) (position : Nat) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hN : Fits bits full.length) (hp : position < (chunks q full hq)[field.val].length)
    (hi : state.register .index = BitVec.ofNat bits position)
    (hroom : metadataAddress q capWords bits (offset q full field.val + position) < heapWords)
    (count : Nat) (hc : count < (program field).length) :
    packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) ((program field).take count) state) (program field)[count] := by
  have hh : 3 ≤ heapWords := by unfold metadataAddress physicalHeaderWords at hroom; omega
  by_cases h1 : count = 1
  · subst count
    change (BitVec.ofNat bits 0).toNat < heapWords
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    omega
  by_cases h3 : count = 3
  · subst count
    change (BitVec.ofNat bits 2).toNat < heapWords
    exact (Nat.mod_le 2 (2 ^ bits)).trans_lt (by omega)
  by_cases h6 : count = 6
  · subst count
    have hpack := (headers full configuration capWords state.heap rep).2.2.1
    change ((executeOps (callInput q full command) ((program field).take 6) state).register .address).toNat < heapWords
    have hptr : (executeOps (callInput q full command) ((program field).take 6) state).register .address =
        BitVec.ofNat bits (packedCapacityWords q capWords bits) + BitVec.ofNat bits 6 := by
      simp +decide [program, executeOps, packingExecuteOp, wordOp, wordInstruction, hpack]
    rw [hptr, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    apply (Nat.mod_le _ _).trans_lt
    unfold metadataAddress physicalHeaderWords at hroom
    omega
  by_cases h17 : count = 17
  · subst count
    change (BitVec.ofNat bits 0).toNat < (callInput q full command).input.length
    simp [callInput, rawIncidenceROM]
  by_cases h21 : count = 21
  · subst count
    have result := (execute_field full command configuration capWords state field position hb hq rep hN hp hi).2.1
    have hptr : (executeOps (callInput q full command) ((program field).take 21) state).register .address =
        BitVec.ofNat bits (metadataAddress q capWords bits (offset q full field.val + position)) := result
    change ((executeOps (callInput q full command) ((program field).take 21) state).register .address).toNat < heapWords
    rw [hptr, BitVec.toNat_ofNat]
    exact (Nat.mod_le _ _).trans_lt hroom
  change count < 22 at hc
  interval_cases count <;> simp_all +decide [program, packingAccessFits, AccessFits]

theorem containing_run {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp)
    (field : Fin 9) (start : Nat) (hbound : start + (program field).length ≤ containing.length)
    (hcode : ∀ i (hi : i < (program field).length), containing[start + i]'(by omega) = (program field)[i])
    (hwords : WordsFit bits (packingCode containing))
    (hpcfit : Fits bits (5 * containing.length)) (state : WordState bits)
    (hpc : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom containing 22 state = executeOps rom (program field) state := by
  exact PSTRWordSegments.straight_segment rom containing (program field) start hbound hcode
    (program_straight field) hwords hpcfit state hpc ha

theorem standalone_field {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (field : Fin 9) (position : Nat) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hN : Fits bits full.length) (hp : position < (chunks q full hq)[field.val].length)
    (hi : state.register .index = BitVec.ofNat bits position)
    (hpc : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    let result := packingRun (callInput q full command) (program field) 23 state
    result.halted = true ∧ result.register .value = BitVec.ofNat bits (chunks q full hq)[field.val][position] ∧
      result.register .index = state.register .index ∧ result.heap = state.heap := by
  rw [show 23 = (program field).length + 1 from rfl,
    packingRun_executeOps_halt _ _ state (program_straight field) (code_fit field hb) (pc_fit field hb) hpc ha]
  have hr := execute_field full command configuration capWords state field position hb hq rep hN hp hi
  exact ⟨rfl, hr.1, hr.2.2⟩

theorem original_prefix_access {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords indexFactor : Nat) (state : WordState bits)
    (field : Fin 9) (position : Nat) (hb : 8 ≤ bits) (hq : 0 < q) (hl : LaminarSchedule full)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hN : Fits bits full.length) (hp : position < (chunks q full hq)[field.val].length)
    (hi : state.register .index = BitVec.ofNat bits position) (hf : 8 ≤ indexFactor)
    (count : Nat) (hc : count < (program field).length) :
    packingAccessFits (callInput q full command)
      (physicalHeaderWords + packedCapacityWords q capWords bits + indexFactor * (full.length + q + treeSize q full + 1))
      (executeOps (callInput q full command) ((program field).take count) state) (program field)[count] := by
  exact prefix_access full command configuration capWords _ state field position hb hq rep hN hp hi
    (PSTRStaticRead.original_address_room full hq hl capWords indexFactor hf _
      (chunk_in_bounds q full hq field.val position field.isLt hp)) count hc

theorem inline_trace_bound {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom containing 22 state).length ≤ 264 :=
  packingDynamicTrace_length_le rom containing 22 state

end PaperProofs.Structure.LaminarTree.PSTRStaticFields
