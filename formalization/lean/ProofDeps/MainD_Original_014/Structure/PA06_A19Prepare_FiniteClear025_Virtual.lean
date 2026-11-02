module

public import Structure.PA06_A19Prepare_FiniteClear025
public import Structure.PSTR_BuildLower_Relative_008
public import PaperProofs.Structure.PA17_PackedTranslator_034d

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Actual full-width Word execution of025's22-op virtual-register wipe.
The seven source registerSlot cells are CB+32..38. Access proofs compose
the real three-op relativeWrite macro, never expand the whole heap state.
The containing-code PC and runtime bank-room qualifications are ordinary
physical input facts. No RunSafe/all-prefix oracle or fit16 premise is used.
Embedded return remains active; standalone HALT and its real trace are
separate theorems. Concrete preparation of CB remains the caller's code. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareFiniteClear025Virtual

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine
open RawIncidenceLaminarRAM PA06A19PrepareFiniteClear025
open PSTRBuildLower (relativeWrite relativeWrite_length relativeWrite_prefix_base)
open PA17PackedTranslator034 (PackedAccessSafe)

def virtualSlots : List Nat := [32, 33, 34, 35, 36, 37, 38]

theorem clearVirtual_eq : clearVirtual =
    [.base (.base (.constant .value 0))] ++ virtualSlots.flatMap relativeWrite := rfl

private theorem relativeWrite_base {bits : Nat} (rom : PhysicalROM) (offset : Nat) (state : WordState bits) :
    (executeOps rom (relativeWrite offset) state).register .address = state.register .address := by
  have h := relativeWrite_prefix_base rom offset state (relativeWrite offset).length
  simpa only [List.take_length] using h

theorem writes_prefix_base {bits : Nat} (rom : PhysicalROM) (slots : List Nat)
    (state : WordState bits) (count : Nat) :
    (executeOps rom ((slots.flatMap relativeWrite).take count) state).register .address = state.register .address := by
  induction slots generalizing state count with
  | nil => simp only [List.flatMap_nil, List.take_nil, executeOps]
  | cons offset rest ih =>
    change (executeOps rom ((relativeWrite offset ++ rest.flatMap relativeWrite).take count) state).register .address = _
    by_cases hfirst : count ≤ (relativeWrite offset).length
    · rw [List.take_append_of_le_length hfirst]
      exact relativeWrite_prefix_base rom offset state count
    · rw [List.take_append, List.take_of_length_le (by omega), executeOps_append]
      exact (ih (executeOps rom (relativeWrite offset) state) _).trans (relativeWrite_base rom offset state)

theorem clearVirtual_prefix_base {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (count : Nat) :
    (executeOps rom (clearVirtual.take count) state).register .address = state.register .address := by
  cases count with
  | zero => rfl
  | succ count =>
    let seeded := packingExecuteOp rom (.base (.base (.constant .value 0))) state
    change (executeOps rom ((virtualSlots.flatMap relativeWrite).take count) seeded).register .address = _
    exact writes_prefix_base rom virtualSlots seeded count

private theorem bank_add_toNat {bits : Nat} (state : WordState bits) (offset : Nat)
    (hfit : Fits bits ((state.register .address).toNat + offset)) :
    (state.register .address + BitVec.ofNat bits offset).toNat = (state.register .address).toNat + offset := by
  have hoff : Fits bits offset := lt_of_le_of_lt (by omega) hfit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff, Nat.mod_eq_of_lt hfit]

theorem relativeWrite_accessSafe {bits : Nat} (rom : PhysicalROM) (heapWords offset : Nat)
    (state : WordState bits) (hfit : Fits bits ((state.register .address).toNat + offset))
    (hroom : (state.register .address).toNat + offset < heapWords) :
    PackedAccessSafe heapWords rom (relativeWrite offset) state := by
  intro count hc
  change count < 3 at hc
  interval_cases count <;> try exact True.intro
  change (state.register .address + BitVec.ofNat bits offset).toNat < heapWords
  rw [bank_add_toNat state offset hfit]
  exact hroom

theorem writes_accessSafe {bits : Nat} (rom : PhysicalROM) (heapWords : Nat) (slots : List Nat)
    (state : WordState bits)
    (bounds : ∀ offset ∈ slots, Fits bits ((state.register .address).toNat + offset) ∧
      (state.register .address).toNat + offset < heapWords) :
    PackedAccessSafe heapWords rom (slots.flatMap relativeWrite) state := by
  induction slots generalizing state with
  | nil => exact PackedAccessSafe.nil heapWords rom state
  | cons offset rest ih =>
    change PackedAccessSafe heapWords rom (relativeWrite offset ++ rest.flatMap relativeWrite) state
    apply PackedAccessSafe.append heapWords rom _ _ state
      (relativeWrite_accessSafe rom heapWords offset state (bounds offset List.mem_cons_self).1
        (bounds offset List.mem_cons_self).2)
    apply ih
    intro other hother
    rw [relativeWrite_base rom offset state]
    exact bounds other (List.mem_cons_of_mem offset hother)

/-- Actual bank addresses fit and lie below the allocation; no virtual
register values or incoming heap contents are qualifications. -/
theorem clearVirtual_accessSafe {bits : Nat} (rom : PhysicalROM) (heapWords : Nat) (state : WordState bits)
    (hfit : Fits bits ((state.register .address).toNat + 38))
    (hroom : (state.register .address).toNat + 39 ≤ heapWords) :
    PackedAccessSafe heapWords rom clearVirtual state := by
  rw [clearVirtual_eq]
  apply PackedAccessSafe.append heapWords rom _ _ state
  · intro count hc
    have hz : count = 0 := by change count < 1 at hc; omega
    subst count
    trivial
  · apply writes_accessSafe
    intro offset hslot
    have hle : offset ≤ 38 := by
      simp only [virtualSlots, List.mem_cons, List.not_mem_nil, or_false] at hslot
      omega
    change Fits bits ((state.register .address).toNat + offset) ∧ (state.register .address).toNat + offset < heapWords
    exact ⟨lt_of_le_of_lt (by omega) hfit, by omega⟩

theorem clearVirtual_code_fit {bits : Nat} (h38 : Fits bits 38) :
    WordsFit bits (packingCode clearVirtual) := by
  intro value hvalue
  simp [clearVirtual, packingCode, PackingOp.encode, Op.encodeWords,
    Instruction.encodeWords, Register.word, haltWords] at hvalue
  dsimp only [Fits] at *
  omega

theorem clearVirtual_code_fit_of_bank {bits : Nat} (before : WordState bits)
    (hfit : Fits bits ((before.register .address).toNat + 38)) :
    WordsFit bits (packingCode clearVirtual) :=
  clearVirtual_code_fit (lt_of_le_of_lt (by omega) hfit)

/-- All seven ORIGINAL source register slots receive actual physical zero.
The source bank address is runtime CB, not a different table/layout type. -/
theorem source_registers_zero {bits : Nat} (rom : PhysicalROM) (before : WordState bits) (reg : Register) :
    (executeOps rom clearVirtual before).heap
      (before.register .address + BitVec.ofNat bits (PSTRBuildLower.registerSlot reg)) = 0 := by
  exact clearVirtual_zero rom before _ (PSTRBuildLower.registerSlot_bounds reg).1
    (PSTRBuildLower.registerSlot_bounds reg).2

section Embedded

variable {bits : Nat} (rom : PhysicalROM) (heapWords : Nat) (left right : List PackingOp)
  (before : WordState bits)
  (hcode : WordsFit bits (packingCode (left ++ clearVirtual ++ right)))
  (hpcCode : Fits bits (5 * (left ++ clearVirtual ++ right).length))
  (hpc : before.pc = BitVec.ofNat bits (5 * left.length)) (ha : before.halted = false)

include hcode hpcCode hpc ha

theorem body_prefix (count : Nat) (hc : count ≤ 22) :
    packingRun rom (left ++ clearVirtual ++ right) count before = executeOps rom (clearVirtual.take count) before := by
  have hlen : (clearVirtual.take count).length = count :=
    List.length_take_of_le (by rw [clearVirtual_length]; exact hc)
  conv_lhs => rw [← hlen]
  apply PSTRWordSegments.straight_segment rom (left ++ clearVirtual ++ right) (clearVirtual.take count) left.length
    (by simp only [List.length_append, clearVirtual_length, hlen]; omega) ?_ ?_ hcode hpcCode before hpc ha
  · intro position hp
    have hpos : position < clearVirtual.length := by rw [hlen] at hp; rw [clearVirtual_length]; omega
    simpa only [List.getElem_take] using PA17UniformGenerator035a.segment_index left clearVirtual right position hpos
  · intro op hop
    exact clearVirtual_straight op (List.mem_of_mem_take hop)

theorem body_prefix_safe
    (hfit : Fits bits ((before.register .address).toNat + 38))
    (hroom : (before.register .address).toNat + 39 ≤ heapWords)
    (count : Nat) (hc : count < 22) :
    let code := left ++ clearVirtual ++ right
    let actual := packingRun rom code count before
    actual.halted = false ∧ actual.register .address = before.register .address ∧
      actual.pc.toNat = 5 * (left.length + count) ∧ actual.pc.toNat + 4 < (packingCode code).length ∧
      PackingOp.decode (fetch code actual) = some (clearVirtual[count]'(by rw [clearVirtual_length]; exact hc)) ∧
      packingAccessFits rom heapWords actual (clearVirtual[count]'(by rw [clearVirtual_length]; exact hc)) := by
  let code := left ++ clearVirtual ++ right
  have run := body_prefix rom left right before hcode hpcCode hpc ha count hc.le
  have prefixStraight : StraightProgram (clearVirtual.take count) :=
    fun op hop => clearVirtual_straight op (List.mem_of_mem_take hop)
  have pcWord : (executeOps rom (clearVirtual.take count) before).pc.toNat = 5 * (left.length + count) := by
    rw [executeOps_pc rom _ before prefixStraight, hpc, List.length_take_of_le
      (by rw [clearVirtual_length]; exact hc.le), BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    have number : 5 * left.length + 5 * count = 5 * (left.length + count) := by omega
    rw [number]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (by
      simp only [List.length_append, clearVirtual_length]
      omega) hpcCode)
  dsimp only
  rw [run]
  refine ⟨(executeOps_halted rom _ before).trans ha, clearVirtual_prefix_base rom before count, pcWord, ?_, ?_, ?_⟩
  · rw [pcWord, packingCode_length]
    simp only [List.length_append, clearVirtual_length]
    omega
  · change PackingOp.decode (physicalFetch bits (packingCode code)
      (executeOps rom (clearVirtual.take count) before).pc.toNat) = _
    rw [pcWord, physicalFetch_eq _ _ _ hcode]
    change PackingOp.decode (natFetch code (5 * (left.length + count))) = _
    rw [natFetch_body code (left.length + count) (by
      dsimp only [code]; simp only [List.length_append, clearVirtual_length]; omega), decode_encode]
    exact congrArg some (PA17UniformGenerator035a.segment_index left clearVirtual right count
      (by rw [clearVirtual_length]; exact hc))
  · exact clearVirtual_accessSafe rom heapWords before hfit hroom count (by rw [clearVirtual_length]; exact hc)

theorem body_run : packingRun rom (left ++ clearVirtual ++ right) 22 before = executeOps rom clearVirtual before := by
  rw [body_prefix rom left right before hcode hpcCode hpc ha 22 le_rfl]
  rw [← clearVirtual_length, List.take_length]

theorem body_zero (reg : Register) :
    (packingRun rom (left ++ clearVirtual ++ right) 22 before).heap
      (before.register .address + BitVec.ofNat bits (PSTRBuildLower.registerSlot reg)) = 0 := by
  rw [body_run rom left right before hcode hpcCode hpc ha]
  exact source_registers_zero rom before reg

theorem body_frame (point : BitVec bits)
    (outside : ∀ slot ∈ virtualSlots, point ≠ before.register .address + BitVec.ofNat bits slot) :
    (packingRun rom (left ++ clearVirtual ++ right) 22 before).heap point = before.heap point := by
  rw [body_run rom left right before hcode hpcCode hpc ha]
  exact clearVirtual_frame rom before point outside

end Embedded

/-- Standalone exact HALT, keeping arbitrary incoming full-width registers
and the runtime bank pointer; no PC reset is performed by the code. -/
theorem standalone_halt {bits : Nat} (rom : PhysicalROM) (before : WordState bits)
    (hcode : WordsFit bits (packingCode clearVirtual)) (hpcFit : Fits bits 110)
    (hpc : before.pc = BitVec.ofNat bits 0) (ha : before.halted = false) :
    packingRun rom clearVirtual 23 before = { executeOps rom clearVirtual before with halted := true } := by
  simpa only [clearVirtual_length] using packingRun_executeOps_halt rom clearVirtual before clearVirtual_straight
    hcode (by simpa only [clearVirtual_length] using hpcFit) hpc ha

theorem standalone_trace {bits : Nat} (rom : PhysicalROM) (before : WordState bits)
    (hcode : WordsFit bits (packingCode clearVirtual)) (hpcFit : Fits bits 110)
    (hpc : before.pc = BitVec.ofNat bits 0) (ha : before.halted = false) :
    packingDynamicTrace rom clearVirtual 23 before = packingTrace clearVirtual := by
  simpa only [clearVirtual_length] using packingDynamicTrace_eq_packingTrace rom clearVirtual before clearVirtual_straight
    hcode (by simpa only [clearVirtual_length] using hpcFit) hpc ha

theorem standalone_trace_bound {bits : Nat} (rom : PhysicalROM) (before : WordState bits) :
    (packingDynamicTrace rom clearVirtual 23 before).length ≤ 276 :=
  packingDynamicTrace_length_le rom clearVirtual 23 before

end PaperProofs.Structure.LaminarTree.PA06A19PrepareFiniteClear025Virtual
