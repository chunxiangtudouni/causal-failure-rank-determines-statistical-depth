module

public import Structure.PA06_A19Prepare_RuntimePacked016_Write
public import PaperProofs.Structure.PA17_PackedTemplates_046e
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Uncompiled candidate for the fixed control-bank ABI. Hardware.address
is preserved; each packed phase reads its scalar pointer from old. The
writer reloads that pointer from actual bank storage before BOTH phases.
Only the fixed existing ISA is used. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareBankPacked021

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM
open CompactControllerClaims (dataHeap)


variable {bits : Nat}

/-- A proof-side input view only; runtime never changes hardware.address
through this function. The port executes its explicit fixed code below. -/
def withAddress (address : BitVec bits) (state : WordState bits) : WordState bits :=
  { state with register := Function.update state.register .address address }

/-- A static substitution in fixed source, with no data-dependent code.
Only the third opcode's multiply source changes from address to old. -/
def read : List PackingOp := PA06A19PrepareRuntimePacked016.read.take 2 ++
  [.arithmetic .multiply .old .old .total] ++ PA06A19PrepareRuntimePacked016.read.drop 3

def clear : List PackingOp := PA06A19PrepareRuntimePacked016.clear.take 2 ++
  [.arithmetic .multiply .old .old .total] ++ PA06A19PrepareRuntimePacked016.clear.drop 3

def directWrite : List PackingOp := PA06A19PrepareRuntimePacked016.directWrite.take 2 ++
  [.arithmetic .multiply .old .old .total] ++ PA06A19PrepareRuntimePacked016.directWrite.drop 3

/-- slot is a compile-time small control-bank offset, not an input dimension. -/
def loadPointer (slot : Nat) : List PackingOp :=
  [.base (.base (.constant .index slot)),
   .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .old .index))]

def safeWrite (slot : Nat) : List PackingOp :=
  loadPointer slot ++ clear ++ loadPointer slot ++ directWrite

theorem read_length : read.length = 21 := rfl
theorem clear_length : clear.length = 31 := rfl
theorem directWrite_length : directWrite.length = 35 := rfl
theorem loadPointer_length (slot : Nat) : (loadPointer slot).length = 3 := rfl
theorem safeWrite_length (slot : Nat) : (safeWrite slot).length = 72 := rfl
theorem safeWrite_code_length (slot : Nat) : (packingCode (safeWrite slot)).length = 365 := rfl
theorem read_trace_length : (packingTrace read).length = 222 := rfl
theorem safeWrite_trace_length (slot : Nat) : (packingTrace (safeWrite slot)).length = 744 := rfl

/-- A small semantic composition lemma for the actual suffix. Every
opcode premise below is discharged from the concrete existing phase;
there is no new interpreter, runtime input, or assumed implementation. -/
private theorem executeOps_bank_commute (rom : PhysicalROM) (code : List PackingOp)
    (base : BitVec bits) (state : WordState bits)
    (hcomm : ∀ op ∈ code, ∀ start : WordState bits,
      packingExecuteOp rom op (withAddress base start) =
        withAddress base (packingExecuteOp rom op start)) :
    executeOps rom code (withAddress base state) =
      withAddress base (executeOps rom code state) := by
  induction code generalizing state with
  | nil => rfl
  | cons op later ih =>
    have hl : ∀ entry ∈ later, ∀ start : WordState bits,
        packingExecuteOp rom entry (withAddress base start) =
          withAddress base (packingExecuteOp rom entry start) :=
      fun entry he start => hcomm entry (List.mem_cons_of_mem op he) start
    rw [executeOps, hcomm op List.mem_cons_self state]
    exact ih _ hl

private theorem read_suffix_commute (rom : PhysicalROM) (base : BitVec bits)
    (state : WordState bits) (op : PackingOp)
    (ho : op ∈ PA06A19PrepareRuntimePacked016.read.drop 3) :
    packingExecuteOp rom op (withAddress base state) =
      withAddress base (packingExecuteOp rom op state) := by
  simp only [PA06A19PrepareRuntimePacked016.read, List.drop_succ_cons, List.drop_zero,
    List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply wordState_ext
  all_goals first | rfl | (funext register; cases register <;> rfl)

private theorem clear_suffix_commute (rom : PhysicalROM) (base : BitVec bits)
    (state : WordState bits) (op : PackingOp)
    (ho : op ∈ PA06A19PrepareRuntimePacked016.clear.drop 3) :
    packingExecuteOp rom op (withAddress base state) =
      withAddress base (packingExecuteOp rom op state) := by
  simp only [PA06A19PrepareRuntimePacked016.clear, List.drop_succ_cons, List.drop_zero,
    List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply wordState_ext
  all_goals first | rfl | (funext register; cases register <;> rfl)

private theorem directWrite_suffix_commute (rom : PhysicalROM) (base : BitVec bits)
    (state : WordState bits) (op : PackingOp)
    (ho : op ∈ PA06A19PrepareRuntimePacked016.directWrite.drop 3) :
    packingExecuteOp rom op (withAddress base state) =
      withAddress base (packingExecuteOp rom op state) := by
  simp only [PA06A19PrepareRuntimePacked016.directWrite, List.drop_succ_cons, List.drop_zero,
    List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply wordState_ext
  all_goals first | rfl | (funext register; cases register <;> rfl)

/-- Pure state simulation of the actual fixed phase; no execution or
performance conclusion is an input. The only difference is the preserved
physical bank base in address. -/
theorem read_prefix_simulation (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) (hc : count ≤ 21) :
    executeOps rom (read.take count) state =
      withAddress (state.register .address)
        (executeOps rom (PA06A19PrepareRuntimePacked016.read.take count) (withAddress (state.register .old) state)) := by
  have hsmall (number : Nat) (hn : number ≤ 3) :
      executeOps rom (read.take number) state =
        withAddress (state.register .address)
          (executeOps rom (PA06A19PrepareRuntimePacked016.read.take number)
            (withAddress (state.register .old) state)) := by
    interval_cases number <;> apply wordState_ext
    all_goals first | rfl | (funext register; cases register <;> rfl)
  by_cases hthree : count ≤ 3
  · exact hsmall count hthree
  · have heq : count = 3 + (count - 3) := by omega
    have hdrop : read.drop 3 = PA06A19PrepareRuntimePacked016.read.drop 3 := rfl
    have hp : read.take count = read.take 3 ++
        (PA06A19PrepareRuntimePacked016.read.drop 3).take (count - 3) := by
      conv_lhs => rw [heq, List.take_add, hdrop]
    have hr : PA06A19PrepareRuntimePacked016.read.take count =
        PA06A19PrepareRuntimePacked016.read.take 3 ++
          (PA06A19PrepareRuntimePacked016.read.drop 3).take (count - 3) := by
      conv_lhs => rw [heq, List.take_add]
    rw [hp, hr, executeOps_append, executeOps_append, hsmall 3 le_rfl]
    exact executeOps_bank_commute rom _ (state.register .address) _
      (fun op ho start => read_suffix_commute rom _ start op (List.mem_of_mem_take ho))

theorem read_simulation (rom : PhysicalROM) (state : WordState bits) :
    executeOps rom read state = withAddress (state.register .address)
      (executeOps rom PA06A19PrepareRuntimePacked016.read (withAddress (state.register .old) state)) := by
  have hp : read.take 21 = read := by
    simpa only [read_length] using (List.take_length (l := read))
  have hr : PA06A19PrepareRuntimePacked016.read.take 21 = PA06A19PrepareRuntimePacked016.read := by
    simpa only [PA06A19PrepareRuntimePacked016.read_length] using (List.take_length (l := PA06A19PrepareRuntimePacked016.read))
  simpa only [hp, hr] using read_prefix_simulation rom state 21 le_rfl

theorem read_address (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom read state).register .address = state.register .address := rfl

/-- Pure state simulation of the actual fixed phase; no execution or
performance conclusion is an input. The only difference is the preserved
physical bank base in address. -/
theorem clear_prefix_simulation (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) (hc : count ≤ 31) :
    executeOps rom (clear.take count) state =
      withAddress (state.register .address)
        (executeOps rom (PA06A19PrepareRuntimePacked016.clear.take count) (withAddress (state.register .old) state)) := by
  have hsmall (number : Nat) (hn : number ≤ 3) :
      executeOps rom (clear.take number) state =
        withAddress (state.register .address)
          (executeOps rom (PA06A19PrepareRuntimePacked016.clear.take number)
            (withAddress (state.register .old) state)) := by
    interval_cases number <;> apply wordState_ext
    all_goals first | rfl | (funext register; cases register <;> rfl)
  by_cases hthree : count ≤ 3
  · exact hsmall count hthree
  · have heq : count = 3 + (count - 3) := by omega
    have hdrop : clear.drop 3 = PA06A19PrepareRuntimePacked016.clear.drop 3 := rfl
    have hp : clear.take count = clear.take 3 ++
        (PA06A19PrepareRuntimePacked016.clear.drop 3).take (count - 3) := by
      conv_lhs => rw [heq, List.take_add, hdrop]
    have hr : PA06A19PrepareRuntimePacked016.clear.take count =
        PA06A19PrepareRuntimePacked016.clear.take 3 ++
          (PA06A19PrepareRuntimePacked016.clear.drop 3).take (count - 3) := by
      conv_lhs => rw [heq, List.take_add]
    rw [hp, hr, executeOps_append, executeOps_append, hsmall 3 le_rfl]
    exact executeOps_bank_commute rom _ (state.register .address) _
      (fun op ho start => clear_suffix_commute rom _ start op (List.mem_of_mem_take ho))

theorem clear_simulation (rom : PhysicalROM) (state : WordState bits) :
    executeOps rom clear state = withAddress (state.register .address)
      (executeOps rom PA06A19PrepareRuntimePacked016.clear (withAddress (state.register .old) state)) := by
  have hp : clear.take 31 = clear := by
    simpa only [clear_length] using (List.take_length (l := clear))
  have hr : PA06A19PrepareRuntimePacked016.clear.take 31 = PA06A19PrepareRuntimePacked016.clear := by
    simpa only [PA06A19PrepareRuntimePacked016.clear_length] using (List.take_length (l := PA06A19PrepareRuntimePacked016.clear))
  simpa only [hp, hr] using clear_prefix_simulation rom state 31 le_rfl

theorem clear_address (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom clear state).register .address = state.register .address := rfl

/-- Pure state simulation of the actual fixed phase; no execution or
performance conclusion is an input. The only difference is the preserved
physical bank base in address. -/
theorem directWrite_prefix_simulation (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) (hc : count ≤ 35) :
    executeOps rom (directWrite.take count) state =
      withAddress (state.register .address)
        (executeOps rom (PA06A19PrepareRuntimePacked016.directWrite.take count) (withAddress (state.register .old) state)) := by
  have hsmall (number : Nat) (hn : number ≤ 3) :
      executeOps rom (directWrite.take number) state =
        withAddress (state.register .address)
          (executeOps rom (PA06A19PrepareRuntimePacked016.directWrite.take number)
            (withAddress (state.register .old) state)) := by
    interval_cases number <;> apply wordState_ext
    all_goals first | rfl | (funext register; cases register <;> rfl)
  by_cases hthree : count ≤ 3
  · exact hsmall count hthree
  · have heq : count = 3 + (count - 3) := by omega
    have hdrop : directWrite.drop 3 = PA06A19PrepareRuntimePacked016.directWrite.drop 3 := rfl
    have hp : directWrite.take count = directWrite.take 3 ++
        (PA06A19PrepareRuntimePacked016.directWrite.drop 3).take (count - 3) := by
      conv_lhs => rw [heq, List.take_add, hdrop]
    have hr : PA06A19PrepareRuntimePacked016.directWrite.take count =
        PA06A19PrepareRuntimePacked016.directWrite.take 3 ++
          (PA06A19PrepareRuntimePacked016.directWrite.drop 3).take (count - 3) := by
      conv_lhs => rw [heq, List.take_add]
    rw [hp, hr, executeOps_append, executeOps_append, hsmall 3 le_rfl]
    exact executeOps_bank_commute rom _ (state.register .address) _
      (fun op ho start => directWrite_suffix_commute rom _ start op (List.mem_of_mem_take ho))

theorem directWrite_simulation (rom : PhysicalROM) (state : WordState bits) :
    executeOps rom directWrite state = withAddress (state.register .address)
      (executeOps rom PA06A19PrepareRuntimePacked016.directWrite (withAddress (state.register .old) state)) := by
  have hp : directWrite.take 35 = directWrite := by
    simpa only [directWrite_length] using (List.take_length (l := directWrite))
  have hr : PA06A19PrepareRuntimePacked016.directWrite.take 35 = PA06A19PrepareRuntimePacked016.directWrite := by
    simpa only [PA06A19PrepareRuntimePacked016.directWrite_length] using (List.take_length (l := PA06A19PrepareRuntimePacked016.directWrite))
  simpa only [hp, hr] using directWrite_prefix_simulation rom state 35 le_rfl

theorem directWrite_address (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom directWrite state).register .address = state.register .address := rfl

theorem loadPointer_heap (slot : Nat) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (loadPointer slot) state).heap = state.heap := rfl

theorem loadPointer_address (slot : Nat) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (loadPointer slot) state).register .address = state.register .address := rfl

theorem loadPointer_value (slot : Nat) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (loadPointer slot) state).register .value = state.register .value := rfl

theorem loadPointer_old (slot : Nat) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (loadPointer slot) state).register .old =
      state.heap (state.register .address + BitVec.ofNat bits slot) := rfl

theorem loadPointer_prefix_heap (slot : Nat) (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) : (executeOps rom ((loadPointer slot).take count) state).heap = state.heap := by
  apply executeOps_heap_of_no_store
  intro op ho
  have hn : ∀ instruction ∈ loadPointer slot, HeapPreservingOp instruction := by
    simp [loadPointer, HeapPreservingOp]
  exact hn op (List.mem_of_mem_take ho)

theorem bankWord_eq (base : BitVec bits) (slot : Nat) :
    base + BitVec.ofNat bits slot = BitVec.ofNat bits (base.toNat + slot) := by
  rw [← BitVec.ofNat_add_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem read_decodes (q C : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits)
    (hs : Fits bits ((state.register .old).toNat * CapacityBits.width q))
    (ha : (state.register .old).toNat < C) :
    ((executeOps rom read state).register .value).toNat =
      unpackHeap q C bits (dataHeap state.heap) (state.register .old).toNat := by
  rw [read_simulation]
  change ((executeOps rom PA06A19PrepareRuntimePacked016.read (withAddress (state.register .old) state)).register .value).toNat = _
  exact PA06A19PrepareRuntimePacked016.read_decodes q C rom _ hh hb hw hs ha

theorem clear_heap (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits)
    (hs : Fits bits ((state.register .old).toNat * CapacityBits.width q))
    (hf : Fits bits ((state.register .old).toNat * CapacityBits.width q / bits + 4 + 1)) :
    (executeOps rom clear state).heap =
      PA06A19PrepareRuntimePacked016.physicalClear (CapacityBits.width q) ((state.register .old).toNat * CapacityBits.width q) state.heap := by
  rw [clear_simulation]
  exact PA06A19PrepareRuntimePacked016.clear_heap q rom (withAddress (state.register .old) state) hh hb hw hs hf

theorem clear_header (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits)
    (hs : Fits bits ((state.register .old).toNat * CapacityBits.width q))
    (hf : Fits bits ((state.register .old).toNat * CapacityBits.width q / bits + 4 + 1)) :
    PA06A19PrepareRuntimePacked016.Header q (executeOps rom clear state).heap := by
  rw [clear_heap q rom state hh hb hw hs hf]
  exact PA06A19PrepareRuntimePacked016.physicalClear_header q _ _ _ hh hf

theorem directWrite_heap (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits)
    (hs : Fits bits ((state.register .old).toNat * CapacityBits.width q))
    (hf : Fits bits ((state.register .old).toNat * CapacityBits.width q / bits + 4 + 1)) :
    (executeOps rom directWrite state).heap =
      PA06A19PrepareRuntimePacked016.physicalWrite (CapacityBits.width q) ((state.register .old).toNat * CapacityBits.width q)
        (state.register .value) state.heap := by
  rw [directWrite_simulation]
  exact PA06A19PrepareRuntimePacked016.directWrite_heap q rom (withAddress (state.register .old) state) hh hb hw hs hf

/-- The bank is strictly after the packed one-word lookahead. All address
inequalities are made into actual Word inequalities using Fits. -/
theorem physicalClear_bank_frame (q C a physical : Nat) (heap : BitVec bits → BitVec bits)
    (hq : 0 < q) (hb : 0 < bits) (ha : a < C)
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ physical)
    (hbankFit : Fits bits physical)
    (hnext : Fits bits (a * CapacityBits.width q / bits + 4 + 1)) :
    PA06A19PrepareRuntimePacked016.physicalClear (CapacityBits.width q) (a * CapacityBits.width q) heap
      (BitVec.ofNat bits physical) = heap (BitVec.ofNat bits physical) := by
  have hwpos := PA17PackedTemplates046.width_pos q hq
  have hd : a * CapacityBits.width q / bits < packedCapacityWords q C bits := by
    apply (Nat.div_lt_iff_lt_mul hb).mpr
    exact (Nat.mul_lt_mul_of_pos_right ha hwpos).trans_le (packedCapacityWords_mul_bits q C hb)
  have hbefore : a * CapacityBits.width q / bits + 4 + 1 < physical := by omega
  have hlo : Fits bits (a * CapacityBits.width q / bits + 4) :=
    (Nat.le_succ _).trans_lt hnext
  have hneHigh : BitVec.ofNat bits physical ≠ BitVec.ofNat bits (a * CapacityBits.width q / bits + 4 + 1) :=
    (ofNat_injective_of_fit _ _ hbankFit hnext).not.mpr (Nat.ne_of_gt hbefore)
  have hneLow : BitVec.ofNat bits physical ≠ BitVec.ofNat bits (a * CapacityBits.width q / bits + 4) :=
    (ofNat_injective_of_fit _ _ hbankFit hlo).not.mpr (Nat.ne_of_gt ((Nat.lt_succ_self _).trans hbefore))
  simp only [PA06A19PrepareRuntimePacked016.physicalClear, PA06A19PrepareRuntimePacked016.physicalClearLow,
    Function.update_of_ne hneHigh, Function.update_of_ne hneLow]

/-- Exact actual scalar pointer loaded from the original bank before a call. -/
def pointer (slot : Nat) (state : WordState bits) : BitVec bits :=
  state.heap (state.register .address + BitVec.ofNat bits slot)

/-- Repeated replacement through two REAL bank reloads. In particular no
claim that clear preserved old is used: only the proved actual bank frame
allows the second executed load to recover the same stored pointer. -/
theorem safeWrite_heap (q C slot : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 0 < bits)
    (hw : CapacityBits.width q ≤ bits)
    (ha : (pointer slot state).toNat < C)
    (hs : Fits bits ((pointer slot state).toNat * CapacityBits.width q))
    (hf : Fits bits ((pointer slot state).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + slot)
    (hbankFit : Fits bits ((state.register .address).toNat + slot)) :
    (executeOps rom (safeWrite slot) state).heap =
      PA06A19PrepareRuntimePacked016.physicalWrite (CapacityBits.width q) ((pointer slot state).toNat * CapacityBits.width q)
        (state.register .value) state.heap := by
  let first := executeOps rom (loadPointer slot) state
  let middle := executeOps rom clear first
  let second := executeOps rom (loadPointer slot) middle
  have hfirstOld : first.register .old = pointer slot state := rfl
  have hmidHeap : middle.heap = PA06A19PrepareRuntimePacked016.physicalClear (CapacityBits.width q)
      ((pointer slot state).toNat * CapacityBits.width q) state.heap := by
    exact clear_heap q rom first hh hb hw hs hf
  have hmidHeader : PA06A19PrepareRuntimePacked016.Header q middle.heap := clear_header q rom first hh hb hw hs hf
  have hmidAddress : middle.register .address = state.register .address := by
    exact (clear_address rom first).trans (loadPointer_address slot rom state)
  have hmidValue : middle.register .value = state.register .value := by
    dsimp only [middle]
    rw [clear_simulation]
    exact (PA06A19PrepareRuntimePacked016.clear_value rom (withAddress (first.register .old) first)).trans (loadPointer_value slot rom state)
  have hbankFrame : middle.heap (state.register .address + BitVec.ofNat bits slot) =
      state.heap (state.register .address + BitVec.ofNat bits slot) := by
    rw [hmidHeap, bankWord_eq]
    exact physicalClear_bank_frame q C _ _ state.heap hq hb ha hbank hbankFit hf
  have hsecondOld : second.register .old = pointer slot state := by
    dsimp only [second]
    rw [loadPointer_old, hmidAddress, hbankFrame]
    rfl
  have hsecondHeap : second.heap = middle.heap := rfl
  have hsecondValue : second.register .value = state.register .value :=
    (loadPointer_value slot rom middle).trans hmidValue
  change (executeOps rom (loadPointer slot ++ clear ++ loadPointer slot ++ directWrite) state).heap = _
  rw [executeOps_append, executeOps_append, executeOps_append]
  change (executeOps rom directWrite second).heap = _
  rw [directWrite_heap q rom second hmidHeader hb hw (by rwa [hsecondOld]) (by rwa [hsecondOld]),
    hsecondOld, hsecondValue, hsecondHeap, hmidHeap,
    PA06A19PrepareRuntimePacked016.physicalWrite_clear _ _ _ _ hf]

theorem read_straight : StraightProgram read := by
  simp [StraightProgram, read, PA06A19PrepareRuntimePacked016.read, StraightOp]

theorem read_code_fit (hb : 7 ≤ bits) : WordsFit bits (packingCode read) := by
  have hp : 2 ^ 7 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hb
  intro value hv
  simp [packingCode, read, PA06A19PrepareRuntimePacked016.read, PackingOp.encode,
    Op.encodeWords, Instruction.encodeWords, PackingPrimitive.word, Register.word, haltWords] at hv
  simp only [Fits]
  omega

theorem read_pc_fit (hb : 7 ≤ bits) : Fits bits (5 * read.length) :=
  PA06A19PrepareRuntimePacked016.read_pc_fit hb

theorem read_access_eq (rom : PhysicalROM) (heapWords : Nat) (state : WordState bits)
    (count : Nat) (hc : count < 21) :
    packingAccessFits rom heapWords (executeOps rom (read.take count) state) read[count] =
      packingAccessFits rom heapWords
        (executeOps rom (PA06A19PrepareRuntimePacked016.read.take count) (withAddress (state.register .old) state))
        PA06A19PrepareRuntimePacked016.read[count] := by
  rw [read_prefix_simulation rom state count hc.le]
  interval_cases count <;> rfl

theorem read_accessFits (q heapWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hb : 7 ≤ bits)
    (hw : CapacityBits.width q ≤ bits)
    (hs : Fits bits ((state.register .old).toNat * CapacityBits.width q))
    (hf : Fits bits (4 + ((state.register .old).toNat * CapacityBits.width q / bits + 1)))
    (hl : 4 + ((state.register .old).toNat * CapacityBits.width q / bits + 1) < heapWords)
    (hpc : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false)
    (count : Nat) (hc : count < read.length) :
    packingAccessFits rom heapWords (packingRun rom read count state) read[count] := by
  rw [packingRun_eq_executeOps_take rom read state read_straight (read_code_fit hb)
    (read_pc_fit hb) hpc ha count hc.le, read_access_eq rom heapWords state count hc]
  have hold := PA06A19PrepareRuntimePacked016.read_accessFits q heapWords rom
    (withAddress (state.register .old) state) hh hb hw hs hf hl hpc ha count hc
  rw [packingRun_eq_executeOps_take rom PA06A19PrepareRuntimePacked016.read
    (withAddress (state.register .old) state)
    PA06A19PrepareRuntimePacked016.read_straight (PA06A19PrepareRuntimePacked016.read_code_fit hb)
    (PA06A19PrepareRuntimePacked016.read_pc_fit hb) hpc ha count hc.le] at hold
  exact hold

theorem read_run_body (rom : PhysicalROM) (state : WordState bits)
    (hb : 7 ≤ bits) (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    packingRun rom read 21 state = executeOps rom read state := by
  rw [show 21 = read.length from rfl,
    packingRun_eq_executeOps_take rom read state read_straight (read_code_fit hb)
      (read_pc_fit hb) hp ha _ le_rfl, List.take_length]

theorem read_run_decodes (q C : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hb : 7 ≤ bits)
    (hw : CapacityBits.width q ≤ bits)
    (hs : Fits bits ((state.register .old).toNat * CapacityBits.width q))
    (haddress : (state.register .old).toNat < C)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    ((packingRun rom read 21 state).register .value).toNat =
      unpackHeap q C bits (dataHeap state.heap) (state.register .old).toNat := by
  rw [read_run_body rom state hb hp ha]
  exact read_decodes q C rom state hh (by omega) hw hs haddress

theorem read_run_halt (rom : PhysicalROM) (state : WordState bits)
    (hb : 7 ≤ bits) (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    packingRun rom read 22 state = { executeOps rom read state with halted := true } :=
  packingRun_executeOps_halt rom read state read_straight (read_code_fit hb) (read_pc_fit hb) hp ha

theorem safeWrite_straight (slot : Nat) : StraightProgram (safeWrite slot) := by
  simp [StraightProgram, safeWrite, loadPointer, clear, directWrite,
    PA06A19PrepareRuntimePacked016.clear, PA06A19PrepareRuntimePacked016.directWrite, StraightOp]

theorem safeWrite_code_fit (slot : Nat) (hs : slot ≤ 511) (hb : 9 ≤ bits) :
    WordsFit bits (packingCode (safeWrite slot)) := by
  have hp : 2 ^ 9 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hb
  intro value hv
  simp [packingCode, safeWrite, loadPointer, clear, directWrite,
    PA06A19PrepareRuntimePacked016.clear, PA06A19PrepareRuntimePacked016.directWrite,
    PackingOp.encode, Op.encodeWords, Instruction.encodeWords, PackingPrimitive.word, Register.word, haltWords] at hv
  simp only [Fits]
  omega

theorem safeWrite_pc_fit (slot : Nat) (hb : 9 ≤ bits) : Fits bits (5 * (safeWrite slot).length) := by
  have hp : 2 ^ 9 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hb
  rw [safeWrite_length]
  change 360 < 2 ^ bits
  omega

theorem safeWrite_address (slot : Nat) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (safeWrite slot) state).register .address = state.register .address := rfl

theorem safeWrite_value (slot : Nat) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (safeWrite slot) state).register .value = state.register .value := rfl

theorem safeWrite_run_body (slot : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hs : slot ≤ 511) (hb : 9 ≤ bits) (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    packingRun rom (safeWrite slot) 72 state = executeOps rom (safeWrite slot) state := by
  rw [show 72 = (safeWrite slot).length from rfl,
    packingRun_eq_executeOps_take rom (safeWrite slot) state (safeWrite_straight slot) (safeWrite_code_fit slot hs hb)
      (safeWrite_pc_fit slot hb) hp ha _ le_rfl, List.take_length]

theorem safeWrite_run_halt (slot : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hs : slot ≤ 511) (hb : 9 ≤ bits) (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    packingRun rom (safeWrite slot) 73 state = { executeOps rom (safeWrite slot) state with halted := true } :=
  packingRun_executeOps_halt rom (safeWrite slot) state (safeWrite_straight slot)
    (safeWrite_code_fit slot hs hb) (safeWrite_pc_fit slot hb) hp ha

theorem safeWrite_dynamicTrace_length (slot : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hs : slot ≤ 511) (hb : 9 ≤ bits) (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    (packingDynamicTrace rom (safeWrite slot) 73 state).length = 744 := by
  rw [show 73 = (safeWrite slot).length + 1 from rfl,
    packingDynamicTrace_eq_packingTrace rom (safeWrite slot) state (safeWrite_straight slot)
      (safeWrite_code_fit slot hs hb) (safeWrite_pc_fit slot hb) hp ha, safeWrite_trace_length]

end PaperProofs.Structure.LaminarTree.PA06A19PrepareBankPacked021
