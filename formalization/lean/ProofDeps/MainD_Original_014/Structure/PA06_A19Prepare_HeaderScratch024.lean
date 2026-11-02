module

public import Structure.PA06_A19Prepare_RuntimePacked016
public import PaperProofs.Structure.PA17_PackedTranslator_034d
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Uncompiled candidate: fixed actual save/restore of the five low-cache
words touched by the dimension expression stack. Only 9..13 are scratch;
64..68 are restored. This block does not reset PC, supply dimensions, or
claim preservation of the whole low heap. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareHeaderScratch024

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM PA17PackedTranslator034

variable {bits : Nat}

def copyWord (source target : Nat) : List PackingOp :=
  [.base (.base (.constant .index source)),
   .base (.base (.loadHeap .total .index)),
   .base (.base (.constant .index target)),
   .base (.base (.storeHeap .index .total))]

def save : List PackingOp := copyWord 64 9 ++ copyWord 65 10 ++ copyWord 66 11 ++ copyWord 67 12 ++ copyWord 68 13

def restore : List PackingOp := copyWord 9 64 ++ copyWord 10 65 ++ copyWord 11 66 ++ copyWord 12 67 ++ copyWord 13 68

theorem save_length : save.length = 20 := rfl
theorem restore_length : restore.length = 20 := rfl
theorem save_events_length : (save.flatMap PackingOp.events).length = 190 := rfl
theorem restore_events_length : (restore.flatMap PackingOp.events).length = 190 := rfl

theorem copyWord_heap (source target : Nat) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (copyWord source target) state).heap =
      Function.update state.heap (BitVec.ofNat bits target) (state.heap (BitVec.ofNat bits source)) := rfl

theorem copyWord_address (source target : Nat) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (copyWord source target) state).register .address = state.register .address := rfl

theorem small_fits (hb : 7 ≤ bits) (value : Nat) (hv : value ≤ 68) : Fits bits value := by
  have hp : 2 ^ 7 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hb
  change value < 2 ^ bits
  omega

theorem small_toNat (hb : 7 ≤ bits) (value : Nat) (hv : value ≤ 68) :
    (BitVec.ofNat bits value).toNat = value := Nat.mod_eq_of_lt (small_fits hb value hv)

theorem small_word_eq (hb : 7 ≤ bits) (left right : Nat) (hl : left ≤ 68) (hr : right ≤ 68) :
    BitVec.ofNat bits left = BitVec.ofNat bits right ↔ left = right :=
  ofNat_injective_of_fit left right (small_fits hb left hl) (small_fits hb right hr)

theorem word_ne_small (hb : 7 ≤ bits) (address : BitVec bits) (value : Nat) (hv : value ≤ 68)
    (hne : address.toNat ≠ value) : address ≠ BitVec.ofNat bits value := by
  intro heq
  apply hne
  exact (congrArg BitVec.toNat heq).trans (small_toNat hb value hv)

theorem save_heap (hb : 7 ≤ bits) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom save state).heap =
      Function.update (Function.update (Function.update (Function.update (Function.update state.heap
        (BitVec.ofNat bits 9) (state.heap (BitVec.ofNat bits 64)))
        (BitVec.ofNat bits 10) (state.heap (BitVec.ofNat bits 65)))
        (BitVec.ofNat bits 11) (state.heap (BitVec.ofNat bits 66)))
        (BitVec.ofNat bits 12) (state.heap (BitVec.ofNat bits 67)))
        (BitVec.ofNat bits 13) (state.heap (BitVec.ofNat bits 68)) := by
  simp only [save, executeOps_append, copyWord_heap]
  simp +decide only [Function.update_apply, small_word_eq hb, ↓reduceIte]

theorem restore_heap (hb : 7 ≤ bits) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom restore state).heap =
      Function.update (Function.update (Function.update (Function.update (Function.update state.heap
        (BitVec.ofNat bits 64) (state.heap (BitVec.ofNat bits 9)))
        (BitVec.ofNat bits 65) (state.heap (BitVec.ofNat bits 10)))
        (BitVec.ofNat bits 66) (state.heap (BitVec.ofNat bits 11)))
        (BitVec.ofNat bits 67) (state.heap (BitVec.ofNat bits 12)))
        (BitVec.ofNat bits 68) (state.heap (BitVec.ofNat bits 13)) := by
  simp only [restore, executeOps_append, copyWord_heap]
  simp +decide only [Function.update_apply, small_word_eq hb, ↓reduceIte]

theorem save_value (hb : 7 ≤ bits) (rom : PhysicalROM) (state : WordState bits) (index : Nat) (hi : index < 5) :
    (executeOps rom save state).heap (BitVec.ofNat bits (9 + index)) = state.heap (BitVec.ofNat bits (64 + index)) := by
  rw [save_heap hb rom state]
  interval_cases index <;> simp +decide only [Function.update_apply, small_word_eq hb, ↓reduceIte]

theorem restore_value (hb : 7 ≤ bits) (rom : PhysicalROM) (state : WordState bits) (index : Nat) (hi : index < 5) :
    (executeOps rom restore state).heap (BitVec.ofNat bits (64 + index)) = state.heap (BitVec.ofNat bits (9 + index)) := by
  rw [restore_heap hb rom state]
  interval_cases index <;> simp +decide only [Function.update_apply, small_word_eq hb, ↓reduceIte]

theorem save_cache_frame (hb : 7 ≤ bits) (rom : PhysicalROM) (state : WordState bits)
    (address : BitVec bits) (ha : 16 ≤ address.toNat) :
    (executeOps rom save state).heap address = state.heap address := by
  rw [save_heap hb rom state]
  simp only [Function.update_of_ne (word_ne_small hb address 9 (by decide) (by omega)),
    Function.update_of_ne (word_ne_small hb address 10 (by decide) (by omega)),
    Function.update_of_ne (word_ne_small hb address 11 (by decide) (by omega)),
    Function.update_of_ne (word_ne_small hb address 12 (by decide) (by omega)),
    Function.update_of_ne (word_ne_small hb address 13 (by decide) (by omega))]

theorem restore_cache_frame (hb : 7 ≤ bits) (rom : PhysicalROM) (state : WordState bits)
    (address : BitVec bits) (ha : address.toNat < 64 ∨ 69 ≤ address.toNat) :
    (executeOps rom restore state).heap address = state.heap address := by
  rw [restore_heap hb rom state]
  simp only [Function.update_of_ne (word_ne_small hb address 64 (by decide) (by omega)),
    Function.update_of_ne (word_ne_small hb address 65 (by decide) (by omega)),
    Function.update_of_ne (word_ne_small hb address 66 (by decide) (by omega)),
    Function.update_of_ne (word_ne_small hb address 67 (by decide) (by omega)),
    Function.update_of_ne (word_ne_small hb address 68 (by decide) (by omega))]

/-- Internal middle-state composition: a real header computation must prove
its low-save cells and non-stack cache frame. No Header is assumed about
an original caller and no execution or performance theorem is a premise. -/
theorem restored_cache (hb : 7 ≤ bits) (rom : PhysicalROM) (original middle : WordState bits)
    (hsaved : ∀ index < 5, middle.heap (BitVec.ofNat bits (9 + index)) =
      (executeOps rom save original).heap (BitVec.ofNat bits (9 + index)))
    (hframe : ∀ address : BitVec bits, 16 ≤ address.toNat →
      (address.toNat < 64 ∨ 69 ≤ address.toNat) → middle.heap address =
        (executeOps rom save original).heap address) :
    ∀ address : BitVec bits, 16 ≤ address.toNat →
      (executeOps rom restore middle).heap address = original.heap address := by
  intro address ha
  by_cases hstack : 64 ≤ address.toNat ∧ address.toNat < 69
  · let index := address.toNat - 64
    have hi : index < 5 := by dsimp only [index]; omega
    have heq : address = BitVec.ofNat bits (64 + index) := by
      have hn : 64 + index = address.toNat := by dsimp only [index]; omega
      rw [hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [heq, restore_value hb rom middle index hi, hsaved index hi, save_value hb rom original index hi]
  · have hout : address.toNat < 64 ∨ 69 ≤ address.toNat := by omega
    rw [restore_cache_frame hb rom middle address hout, hframe address ha hout,
      save_cache_frame hb rom original address ha]

theorem restore_header (hb : 7 ≤ bits) (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) :
    PA06A19PrepareRuntimePacked016.Header q (executeOps rom restore state).heap := by
  constructor
  · rw [restore_cache_frame hb rom state (BitVec.ofNat bits 0) (Or.inl (by rw [small_toNat hb 0 (by decide)]; decide))]; exact hh.width
  · rw [restore_cache_frame hb rom state (BitVec.ofNat bits 1) (Or.inl (by rw [small_toNat hb 1 (by decide)]; decide))]; exact hh.mask
  · rw [restore_cache_frame hb rom state (BitVec.ofNat bits 2) (Or.inl (by rw [small_toNat hb 2 (by decide)]; decide))]; exact hh.ones
  · rw [restore_cache_frame hb rom state (BitVec.ofNat bits 3) (Or.inl (by rw [small_toNat hb 3 (by decide)]; decide))]; exact hh.wordBits

theorem copyWord_accessSafe (hb : 7 ≤ bits) (source target heapWords : Nat)
    (hs : source ≤ 68) (ht : target ≤ 68) (hheap : 69 ≤ heapWords)
    (rom : PhysicalROM) (state : WordState bits) : PackedAccessSafe heapWords rom (copyWord source target) state := by
  intro count hc
  change count < 4 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide only [copyWord, List.take_succ_cons, List.take_zero, List.getElem_cons_succ,
    List.getElem_cons_zero, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, packingAccessFits, AccessFits]
  · rw [small_toNat hb source hs]; omega
  · rw [small_toNat hb target ht]; omega

theorem save_accessSafe (hb : 7 ≤ bits) (heapWords : Nat) (hheap : 69 ≤ heapWords)
    (rom : PhysicalROM) (state : WordState bits) : PackedAccessSafe heapWords rom save state := by
  unfold save
  apply PackedAccessSafe.append _ _ (copyWord 64 9) _ _
    (copyWord_accessSafe hb 64 9 heapWords (by decide) (by decide) hheap rom _)
  apply PackedAccessSafe.append _ _ (copyWord 65 10) _ _
    (copyWord_accessSafe hb 65 10 heapWords (by decide) (by decide) hheap rom _)
  apply PackedAccessSafe.append _ _ (copyWord 66 11) _ _
    (copyWord_accessSafe hb 66 11 heapWords (by decide) (by decide) hheap rom _)
  apply PackedAccessSafe.append _ _ (copyWord 67 12) _ _
    (copyWord_accessSafe hb 67 12 heapWords (by decide) (by decide) hheap rom _)
  exact copyWord_accessSafe hb 68 13 heapWords (by decide) (by decide) hheap rom _

theorem restore_accessSafe (hb : 7 ≤ bits) (heapWords : Nat) (hheap : 69 ≤ heapWords)
    (rom : PhysicalROM) (state : WordState bits) : PackedAccessSafe heapWords rom restore state := by
  unfold restore
  apply PackedAccessSafe.append _ _ (copyWord 9 64) _ _
    (copyWord_accessSafe hb 9 64 heapWords (by decide) (by decide) hheap rom _)
  apply PackedAccessSafe.append _ _ (copyWord 10 65) _ _
    (copyWord_accessSafe hb 10 65 heapWords (by decide) (by decide) hheap rom _)
  apply PackedAccessSafe.append _ _ (copyWord 11 66) _ _
    (copyWord_accessSafe hb 11 66 heapWords (by decide) (by decide) hheap rom _)
  apply PackedAccessSafe.append _ _ (copyWord 12 67) _ _
    (copyWord_accessSafe hb 12 67 heapWords (by decide) (by decide) hheap rom _)
  exact copyWord_accessSafe hb 13 68 heapWords (by decide) (by decide) hheap rom _

theorem save_address (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom save state).register .address = state.register .address := by
  simp only [save, executeOps_append, copyWord_address]

theorem save_straight : StraightProgram save := by
  simp [StraightProgram, save, copyWord, StraightOp]

theorem save_code_fit (hb : 7 ≤ bits) : WordsFit bits (packingCode save) := by
  have hp : 2 ^ 7 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hb
  intro value hv
  simp [packingCode, save, copyWord, PackingOp.encode, Op.encodeWords,
    Instruction.encodeWords, PackingPrimitive.word, Register.word, haltWords] at hv
  simp only [Fits]
  omega

theorem save_pc_fit (hb : 7 ≤ bits) : Fits bits (5 * save.length) := by
  have hp : 2 ^ 7 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hb
  rw [save_length]
  change 100 < 2 ^ bits
  omega

theorem save_run_body (rom : PhysicalROM) (state : WordState bits)
    (hb : 7 ≤ bits) (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    packingRun rom save 20 state = executeOps rom save state := by
  rw [show 20 = save.length from rfl,
    packingRun_eq_executeOps_take rom save state save_straight (save_code_fit hb)
      (save_pc_fit hb) hp ha _ le_rfl, List.take_length]

theorem save_run_access (heapWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hb : 7 ≤ bits) (hheap : 69 ≤ heapWords)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false)
    (count : Nat) (hc : count < save.length) :
    packingAccessFits rom heapWords (packingRun rom save count state) save[count] := by
  rw [packingRun_eq_executeOps_take rom save state save_straight (save_code_fit hb)
    (save_pc_fit hb) hp ha count hc.le]
  exact save_accessSafe hb heapWords hheap rom state count hc

theorem restore_address (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom restore state).register .address = state.register .address := by
  simp only [restore, executeOps_append, copyWord_address]

theorem restore_straight : StraightProgram restore := by
  simp [StraightProgram, restore, copyWord, StraightOp]

theorem restore_code_fit (hb : 7 ≤ bits) : WordsFit bits (packingCode restore) := by
  have hp : 2 ^ 7 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hb
  intro value hv
  simp [packingCode, restore, copyWord, PackingOp.encode, Op.encodeWords,
    Instruction.encodeWords, PackingPrimitive.word, Register.word, haltWords] at hv
  simp only [Fits]
  omega

theorem restore_pc_fit (hb : 7 ≤ bits) : Fits bits (5 * restore.length) := by
  have hp : 2 ^ 7 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hb
  rw [restore_length]
  change 100 < 2 ^ bits
  omega

theorem restore_run_body (rom : PhysicalROM) (state : WordState bits)
    (hb : 7 ≤ bits) (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    packingRun rom restore 20 state = executeOps rom restore state := by
  rw [show 20 = restore.length from rfl,
    packingRun_eq_executeOps_take rom restore state restore_straight (restore_code_fit hb)
      (restore_pc_fit hb) hp ha _ le_rfl, List.take_length]

theorem restore_run_access (heapWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hb : 7 ≤ bits) (hheap : 69 ≤ heapWords)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false)
    (count : Nat) (hc : count < restore.length) :
    packingAccessFits rom heapWords (packingRun rom restore count state) restore[count] := by
  rw [packingRun_eq_executeOps_take rom restore state restore_straight (restore_code_fit hb)
    (restore_pc_fit hb) hp ha count hc.le]
  exact restore_accessSafe hb heapWords hheap rom state count hc

end PaperProofs.Structure.LaminarTree.PA06A19PrepareHeaderScratch024
