module

public import PaperProofs.Structure.AlgorithmClaims

/-!
Actual encoded execution interfaces for the fixed physical ISA used by A06
and A17. The natural-state interpreter is a proof view of the same ordinary
instructions and branches. It does not add a set, tree, packed-read or rank
primitive. Physical execution is linked through the original fetched words.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PackingMachine

open IndexedRAM IndexedClosureRAM AlgorithmClaims

theorem decode_encode (op : PackingOp) : PackingOp.decode op.encode = some op := by
  cases op with
  | base op =>
    have htag : op.encodeWords[0] < 9 := by
      cases op with
      | base instruction => cases instruction <;> simp [Instruction.encodeWords, Op.encodeWords]
      | subtract target left right => simp [Op.encodeWords]
    have hnot : op.encodeWords[0] ≠ 15 := by omega
    simp only [PackingOp.encode, PackingOp.decode, hnot, ite_false,
      not_le_of_gt htag, Op.decodeWords_encodeWords, Option.map_some]
  | arithmetic operation target left right =>
    cases operation <;> simp [PackingOp.encode, PackingOp.decode, PackingPrimitive.word,
      PackingPrimitive.fromWord, Register.fromWord_word]
  | jumpIfZero condition target =>
    simp [PackingOp.encode, PackingOp.decode, Register.fromWord_word]

theorem decode_halt : PackingOp.decode haltWords = none := rfl

def bodyWords (program : List PackingOp) : List Nat :=
  program.flatMap (fun op => op.encode.toArray.toList)

theorem bodyWords_length (program : List PackingOp) : (bodyWords program).length = 5 * program.length := by
  simp only [bodyWords, List.length_flatMap, Array.length_toList, Vector.size_toArray,
    List.map_const', List.sum_replicate, Nat.nsmul_eq_mul]
  omega

theorem packingCode_length (program : List PackingOp) : (packingCode program).length = 5 * program.length + 5 := by
  change (bodyWords program ++ haltWords.toArray.toList).length = _
  rw [List.length_append, bodyWords_length]
  rfl

theorem bodyWords_fetch (program : List PackingOp) (index position : Nat)
    (hindex : index < program.length) (hposition : position < 5) :
    (bodyWords program).getD (5 * index + position) 0 =
      ((program[index]'hindex).encode.toArray.toList).getD position 0 := by
  induction program generalizing index with
  | nil => simp only [List.length_nil] at hindex; omega
  | cons op later ih =>
    have hhead : op.encode.toArray.toList.length = 5 := by
      simp only [Array.length_toList, Vector.size_toArray]
    cases index with
    | zero =>
      simp only [bodyWords, List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      exact List.getD_append _ _ _ _ (hhead.symm ▸ hposition)
    | succ index =>
      have htail : index < later.length := Nat.lt_of_succ_lt_succ hindex
      have hlarge : op.encode.toArray.toList.length ≤ 5 * (index + 1) + position := by omega
      simp only [bodyWords, List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getD_append_right _ _ _ _ hlarge, hhead]
      have hsub : 5 * (index + 1) + position - 5 = 5 * index + position := by omega
      rw [hsub]
      exact ih index htail

def natFetch (program : List PackingOp) (pc : Nat) : Vector Nat 5 :=
  fetchWords (packingCode program) pc

theorem natFetch_body (program : List PackingOp) (index : Nat) (hindex : index < program.length) :
    natFetch program (5 * index) = (program[index]'hindex).encode := by
  apply Vector.ext
  intro position hposition
  change (Vector.ofFn _).get ⟨position, hposition⟩ = (program[index]'hindex).encode.get ⟨position, hposition⟩
  rw [cache_get_ofFn]
  change (bodyWords program ++ haltWords.toArray.toList).getD (5 * index + position) 0 = _
  rw [List.getD_append _ _ _ _ (by rw [bodyWords_length]; omega),
    bodyWords_fetch program index position hindex hposition,
    List.getD_eq_getElem _ 0 (by simpa only [Array.length_toList, Vector.size_toArray] using hposition)]
  rfl

theorem natFetch_halt (program : List PackingOp) :
    natFetch program (5 * program.length) = haltWords := by
  apply Vector.ext
  intro position hposition
  change (Vector.ofFn _).get ⟨position, hposition⟩ = haltWords.get ⟨position, hposition⟩
  rw [cache_get_ofFn]
  change (bodyWords program ++ haltWords.toArray.toList).getD (5 * program.length + position) 0 = _
  rw [List.getD_append_right _ _ _ _ (by rw [bodyWords_length]; omega), bodyWords_length,
    Nat.add_sub_cancel_left, List.getD_eq_getElem _ 0 (by
      simpa only [Array.length_toList, Vector.size_toArray] using hposition)]
  rfl

structure NatState where
  register : Register → Nat
  heap : Nat → Nat
  pc : Nat
  halted : Bool

def NatState.toWord (bits : Nat) (state : NatState) : WordState bits :=
  ⟨fun reg => BitVec.ofNat bits (state.register reg),
    fun address => BitVec.ofNat bits (state.heap address.toNat),
    BitVec.ofNat bits state.pc, state.halted⟩

def natArithmetic (operation : PackingPrimitive) (left right : Nat) : Nat :=
  match operation with
  | .multiply => left * right
  | .divide => left / right
  | .bitAnd => Nat.land left right
  | .bitOr => Nat.lor left right
  | .shiftLeft => Nat.shiftLeft left right
  | .shiftRight => Nat.shiftRight left right

def natExecuteOp (rom : PhysicalROM) : PackingOp → NatState → NatState
  | .base op, state =>
    let after := op.execute rom.semantic ⟨state.register, state.heap, state.pc⟩
    ⟨after.register, after.heap, after.pc, state.halted⟩
  | .arithmetic operation target left right, state =>
    { state with
      register := Function.update state.register target
          (natArithmetic operation (state.register left) (state.register right))
      pc := state.pc + 5 }
  | .jumpIfZero condition target, state =>
    { state with pc := if state.register condition = 0 then state.register target else state.pc + 5 }

def natStep (rom : PhysicalROM) (program : List PackingOp) (state : NatState) : NatState :=
  if state.halted then state else
    match PackingOp.decode (natFetch program state.pc) with
    | none => { state with halted := true }
    | some op => natExecuteOp rom op state

def natRun (rom : PhysicalROM) (program : List PackingOp) : Nat → NatState → NatState
  | 0, state => state
  | count + 1, state => natRun rom program count (natStep rom program state)

theorem natRun_add (rom : PhysicalROM) (program : List PackingOp) (left right : Nat) (state : NatState) :
    natRun rom program (left + right) state = natRun rom program right (natRun rom program left state) := by
  induction left generalizing state with
  | zero => simp only [Nat.zero_add, natRun]
  | succ left ih =>
    rw [Nat.succ_add]
    change natRun rom program (left + right) (natStep rom program state) = _
    exact ih _

theorem natRun_succ (rom : PhysicalROM) (program : List PackingOp) (count : Nat) (state : NatState) :
    natRun rom program (count + 1) state = natStep rom program (natRun rom program count state) := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => exact ih _

theorem natStep_of_index (rom : PhysicalROM) (program : List PackingOp) (state : NatState)
    (index : Nat) (hindex : index < program.length)
    (hpc : state.pc = 5 * index) (hactive : state.halted = false) :
    natStep rom program state = natExecuteOp rom (program[index]'hindex) state := by
  simp only [natStep, hactive, Bool.false_eq_true, ite_false, hpc,
    natFetch_body program index hindex, decode_encode]

theorem natStep_halt (rom : PhysicalROM) (program : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * program.length) (hactive : state.halted = false) :
    natStep rom program state = { state with halted := true } := by
  simp only [natStep, hactive, Bool.false_eq_true, ite_false, hpc, natFetch_halt, decode_halt]

def physicalFetch (bits : Nat) (code : List Nat) (pc : Nat) : Vector Nat 5 :=
  Vector.ofFn (fun position =>
    (((code.map (BitVec.ofNat bits)).getD (pc + position.val) (BitVec.ofNat bits 0))).toNat)

theorem getD_map_ofNat (bits : Nat) (code : List Nat) (index : Nat) (hfit : WordsFit bits code) :
    (((code.map (BitVec.ofNat bits)).getD index (BitVec.ofNat bits 0))).toNat = code.getD index 0 := by
  induction code generalizing index with
  | nil => simp
  | cons word later ih =>
    cases index with
    | zero =>
      simpa only [List.map_cons, List.getD_cons_zero, BitVec.toNat_ofNat] using
        Nat.mod_eq_of_lt (hfit word List.mem_cons_self)
    | succ index =>
      simp only [List.map_cons, List.getD_cons_succ]
      exact ih index (fun value hv => hfit value (List.mem_cons_of_mem _ hv))

theorem physicalFetch_eq (bits : Nat) (code : List Nat) (pc : Nat) (hfit : WordsFit bits code) :
    physicalFetch bits code pc = fetchWords code pc := by
  apply Vector.ext
  intro position hposition
  change (Vector.ofFn _).get ⟨position, hposition⟩ = (Vector.ofFn _).get ⟨position, hposition⟩
  rw [cache_get_ofFn, cache_get_ofFn]
  exact getD_map_ofNat bits code (pc + position) hfit

theorem packingStep_of_index {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (state : WordState bits) (index : Nat) (hindex : index < program.length)
    (hfit : WordsFit bits (packingCode program)) (hpc : state.pc.toNat = 5 * index)
    (hactive : state.halted = false) :
    packingStep rom ((packingCode program).map (BitVec.ofNat bits)) state =
      packingExecuteOp rom (program[index]'hindex) state := by
  change (if state.halted then state else
    match PackingOp.decode (physicalFetch bits (packingCode program) state.pc.toNat) with
    | none => { state with halted := true }
    | some op => packingExecuteOp rom op state) = _
  rw [physicalFetch_eq bits (packingCode program) state.pc.toNat hfit, hpc]
  change (if state.halted then state else
    match PackingOp.decode (natFetch program (5 * index)) with
    | none => { state with halted := true }
    | some op => packingExecuteOp rom op state) = _
  simp only [hactive, Bool.false_eq_true, ite_false, natFetch_body program index hindex, decode_encode]

theorem packingStep_halt {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (state : WordState bits) (hfit : WordsFit bits (packingCode program))
    (hpc : state.pc.toNat = 5 * program.length) (hactive : state.halted = false) :
    packingStep rom ((packingCode program).map (BitVec.ofNat bits)) state = { state with halted := true } := by
  change (if state.halted then state else
    match PackingOp.decode (physicalFetch bits (packingCode program) state.pc.toNat) with
    | none => { state with halted := true }
    | some op => packingExecuteOp rom op state) = _
  rw [physicalFetch_eq bits (packingCode program) state.pc.toNat hfit, hpc]
  change (if state.halted then state else
    match PackingOp.decode (natFetch program (5 * program.length)) with
    | none => { state with halted := true }
    | some op => packingExecuteOp rom op state) = _
  simp only [hactive, Bool.false_eq_true, ite_false, natFetch_halt, decode_halt]

def executeOps {bits : Nat} (rom : PhysicalROM) : List PackingOp → WordState bits → WordState bits
  | [], state => state
  | op :: later, state => executeOps rom later (packingExecuteOp rom op state)

theorem executeOps_append {bits : Nat} (rom : PhysicalROM) (left right : List PackingOp)
    (state : WordState bits) :
    executeOps rom (left ++ right) state = executeOps rom right (executeOps rom left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons op later ih => exact ih _

theorem packingExecuteOp_halted {bits : Nat} (rom : PhysicalROM) (op : PackingOp)
    (state : WordState bits) : (packingExecuteOp rom op state).halted = state.halted := by
  cases op with
  | base op => cases op with
    | base instruction => cases instruction <;> rfl
    | subtract target left right => rfl
  | arithmetic operation target left right => rfl
  | jumpIfZero condition target => rfl

theorem executeOps_halted {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (state : WordState bits) : (executeOps rom program state).halted = state.halted := by
  induction program generalizing state with
  | nil => rfl
  | cons op later ih => rw [executeOps, ih, packingExecuteOp_halted]

def StraightOp : PackingOp → Prop
  | .jumpIfZero _ _ => False
  | _ => True

def StraightProgram (program : List PackingOp) : Prop := ∀ op ∈ program, StraightOp op

theorem packingExecuteOp_pc {bits : Nat} (rom : PhysicalROM) (op : PackingOp)
    (state : WordState bits) (hstraight : StraightOp op) :
    (packingExecuteOp rom op state).pc = state.pc + BitVec.ofNat bits 5 := by
  cases op with
  | base op => cases op with
    | base instruction => cases instruction <;> rfl
    | subtract target left right => rfl
  | arithmetic operation target left right => rfl
  | jumpIfZero condition target => cases hstraight

theorem executeOps_pc {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (state : WordState bits) (hstraight : StraightProgram program) :
    (executeOps rom program state).pc = state.pc + BitVec.ofNat bits (5 * program.length) := by
  induction program generalizing state with
  | nil => simp only [executeOps, List.length_nil, Nat.mul_zero, BitVec.add_zero]
  | cons op later ih =>
    have ho := hstraight op List.mem_cons_self
    have hl : StraightProgram later := fun entry he => hstraight entry (List.mem_cons_of_mem _ he)
    rw [executeOps, ih _ hl, packingExecuteOp_pc rom op state ho, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
    congr 1
    congr 1
    simp only [List.length_cons]
    omega

theorem packingRun_succ {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (count : Nat) (state : WordState bits) :
    packingRun rom program (count + 1) state =
      packingStep rom ((packingCode program).map (BitVec.ofNat bits)) (packingRun rom program count state) := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => exact ih _

theorem packingRun_eq_executeOps_take {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (state : WordState bits) (hstraight : StraightProgram program)
    (hfit : WordsFit bits (packingCode program)) (hpcfit : Fits bits (5 * program.length))
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false)
    (count : Nat) (hcount : count ≤ program.length) :
    packingRun rom program count state = executeOps rom (program.take count) state := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have hlt : count < program.length := by omega
    rw [packingRun_succ, ih (by omega)]
    have hprefix : StraightProgram (program.take count) := by
      intro op ho
      exact hstraight op (List.mem_of_mem_take ho)
    have hprefixPc : (executeOps rom (program.take count) state).pc.toNat = 5 * count := by
      rw [executeOps_pc rom (program.take count) state hprefix, hpc, BitVec.zero_add,
        List.length_take_of_le (by omega), BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (lt_of_le_of_lt (by omega) hpcfit)
    rw [packingStep_of_index rom program _ count hlt hfit hprefixPc
      (by rw [executeOps_halted, hactive]), List.take_succ_eq_append_getElem hlt,
      executeOps_append]
    rfl

theorem packingRun_executeOps_halt {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (state : WordState bits) (hstraight : StraightProgram program)
    (hfit : WordsFit bits (packingCode program)) (hpcfit : Fits bits (5 * program.length))
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    packingRun rom program (program.length + 1) state =
      { executeOps rom program state with halted := true } := by
  rw [packingRun_succ, packingRun_eq_executeOps_take rom program state hstraight hfit hpcfit hpc hactive
    program.length le_rfl, List.take_length]
  apply packingStep_halt rom program _ hfit
  · rw [executeOps_pc rom program state hstraight, hpc, BitVec.zero_add, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hpcfit
  · rw [executeOps_halted, hactive]

end PaperProofs.Structure.LaminarTree.PackingMachine
