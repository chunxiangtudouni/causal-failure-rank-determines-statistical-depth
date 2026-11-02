module

public import PaperProofs.Structure.PA17_PackedTranslator_034a
public import PaperProofs.Structure.PackedCapacityRAM

/-! Actual straight packed translation. Logical registers live in seven
ordinary index words. Both physical heap paths are safe before selection;
capacity writes use the real clear-then-write 50-instruction program. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17PackedTranslator034

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM

def physicalSpillBase (q bits capWords indexWords : Nat) : Nat := packedCapacityWords q capWords bits + indexWords

def loadReg (spillBase : Nat) (source target : Register) : List PackingOp :=
  [.base (.base (.constant .total (spillBase + source.word))), .base (.base (.loadHeap target .total))]

def saveReg (spillBase : Nat) (target : Register) : List PackingOp :=
  [.base (.base (.constant .total (spillBase + target.word))), .base (.base (.storeHeap .total .value))]

def physicalWipe (spillBase : Nat) : List PackingOp := (wipe spillBase).map PackingOp.base

def restoredRegisters : List Register := [.address, .index, .value, .old, .fresh]

def restore (spillBase : Nat) : List PackingOp :=
  restoredRegisters.flatMap (fun register => loadReg spillBase register register)

def capAddress (capWords spillBase : Nat) (pointer : Register) : List PackingOp :=
  loadReg spillBase pointer .address ++
    [.base (.base (.constant .total capWords)), .base (.subtract .flag .total .address),
     .base (.base (.constant .fresh 0)), .base (.base (.select .address .flag .address .fresh))]

def indexAddress (q bits capWords spillBase : Nat) (pointer : Register) : List PackingOp :=
  loadReg spillBase pointer .address ++
    [.base (.base (.constant .total capWords)), .base (.subtract .fresh .address .total),
     .base (.base (.constant .old (packedCapacityWords q capWords bits))),
     .base (.base (.add .index .old .fresh))]

def readMacro (q bits capWords spillBase : Nat) (target pointer : Register) : List PackingOp :=
  capAddress capWords spillBase pointer ++ readProgram q bits ++
    indexAddress q bits capWords spillBase pointer ++
    [.base (.base (.loadHeap .fresh .index)), .base (.base (.select .value .flag .value .fresh))] ++
    saveReg spillBase target

def writeMacro (q bits capWords spillBase : Nat) (pointer source : Register) : List PackingOp :=
  capAddress capWords spillBase pointer ++ readProgram q bits ++
    loadReg spillBase source .fresh ++ [.base (.base (.select .value .flag .fresh .value))] ++
    safeWriteProgram q bits ++ indexAddress q bits capWords spillBase pointer ++
    [.base (.subtract .flag .total .address), .base (.base (.loadHeap .old .index))] ++
    loadReg spillBase source .fresh ++
    [.base (.base (.select .value .flag .old .fresh)), .base (.base (.storeHeap .index .value))]

def translateOp (q bits capWords spillBase : Nat) : Op → List PackingOp
  | .base (.constant target value) => [.base (.base (.constant .value value))] ++ saveReg spillBase target
  | .base (.add target left right) => loadReg spillBase left .old ++ loadReg spillBase right .fresh ++
      [.base (.base (.add .value .old .fresh))] ++ saveReg spillBase target
  | .base (.minimum target left right) => loadReg spillBase left .old ++ loadReg spillBase right .fresh ++
      [.base (.base (.minimum .value .old .fresh))] ++ saveReg spillBase target
  | .base (.select target condition whenTrue whenFalse) => loadReg spillBase condition .flag ++
      loadReg spillBase whenTrue .old ++ loadReg spillBase whenFalse .fresh ++
      [.base (.base (.select .value .flag .old .fresh))] ++ saveReg spillBase target
  | .base (.loadROM region target pointer) => loadReg spillBase pointer .index ++
      [.base (.base (.loadROM region .value .index))] ++ saveReg spillBase target
  | .base (.loadHeap target pointer) => readMacro q bits capWords spillBase target pointer
  | .base (.storeHeap pointer source) => writeMacro q bits capWords spillBase pointer source
  | .subtract target left right => loadReg spillBase left .old ++ loadReg spillBase right .fresh ++
      [.base (.subtract .value .old .fresh)] ++ saveReg spillBase target

def packedProgram (q bits capWords indexWords : Nat) (body : List Op) : List PackingOp :=
  let spillBase := physicalSpillBase q bits capWords indexWords
  physicalWipe spillBase ++ body.flatMap (translateOp q bits capWords spillBase) ++
    restore spillBase ++ physicalWipe spillBase

theorem register_word_lt (register : Register) : register.word < spillWords := by cases register <;> decide

theorem loadReg_length (spillBase : Nat) (source target : Register) : (loadReg spillBase source target).length = 2 := rfl

theorem saveReg_length (spillBase : Nat) (target : Register) : (saveReg spillBase target).length = 2 := rfl

theorem physicalWipe_length (spillBase : Nat) : (physicalWipe spillBase).length = 16 := rfl

theorem restore_length (spillBase : Nat) : (restore spillBase).length = 10 := rfl

theorem capAddress_length (capWords spillBase : Nat) (pointer : Register) : (capAddress capWords spillBase pointer).length = 6 := rfl

theorem indexAddress_length (q bits capWords spillBase : Nat) (pointer : Register) :
    (indexAddress q bits capWords spillBase pointer).length = 6 := rfl

theorem readMacro_length (q bits capWords spillBase : Nat) (target pointer : Register) :
    (readMacro q bits capWords spillBase target pointer).length = 32 := rfl

theorem writeMacro_length (q bits capWords spillBase : Nat) (pointer source : Register) :
    (writeMacro q bits capWords spillBase pointer source).length = 87 := rfl

theorem translateOp_length_le (q bits capWords spillBase : Nat) (op : Op) :
    (translateOp q bits capWords spillBase op).length ≤ 87 := by
  cases op with
  | base instruction => cases instruction <;> simp [translateOp, loadReg, saveReg, readMacro_length, writeMacro_length]
  | subtract _ _ _ => simp [translateOp, loadReg, saveReg]

theorem packedProgram_length_le (q bits capWords indexWords : Nat) (body : List Op) :
    (packedProgram q bits capWords indexWords body).length ≤ 87 * body.length + 42 := by
  have hbody : (body.flatMap (translateOp q bits capWords (physicalSpillBase q bits capWords indexWords))).length ≤ 87 * body.length := by
    induction body with
    | nil => simp
    | cons op later ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have hh := translateOp_length_le q bits capWords (physicalSpillBase q bits capWords indexWords) op
      omega
  simp only [packedProgram, List.length_append, physicalWipe_length, restore_length]
  omega

theorem straight_append (left right : List PackingOp) :
    StraightProgram (left ++ right) ↔ StraightProgram left ∧ StraightProgram right := by
  constructor
  · intro h
    exact ⟨fun op ho => h op (List.mem_append.mpr (Or.inl ho)),
      fun op ho => h op (List.mem_append.mpr (Or.inr ho))⟩
  · rintro ⟨hl, hr⟩ op ho
    rcases List.mem_append.mp ho with ho | ho
    · exact hl op ho
    · exact hr op ho

theorem loadReg_straight (spillBase : Nat) (source target : Register) : StraightProgram (loadReg spillBase source target) := by
  simp [StraightProgram, loadReg, StraightOp]

theorem saveReg_straight (spillBase : Nat) (target : Register) : StraightProgram (saveReg spillBase target) := by
  simp [StraightProgram, saveReg, StraightOp]

theorem physicalWipe_straight (spillBase : Nat) : StraightProgram (physicalWipe spillBase) := by
  intro op ho
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp ho
  trivial

theorem restore_straight (spillBase : Nat) : StraightProgram (restore spillBase) := by
  intro op ho
  obtain ⟨register, _, hop⟩ := List.mem_flatMap.mp ho
  exact loadReg_straight spillBase register register op hop

theorem capAddress_straight (capWords spillBase : Nat) (pointer : Register) : StraightProgram (capAddress capWords spillBase pointer) := by
  simp only [capAddress, straight_append]
  exact ⟨loadReg_straight _ _ _, by simp [StraightProgram, StraightOp]⟩

theorem indexAddress_straight (q bits capWords spillBase : Nat) (pointer : Register) :
    StraightProgram (indexAddress q bits capWords spillBase pointer) := by
  simp only [indexAddress, straight_append]
  exact ⟨loadReg_straight _ _ _, by simp [StraightProgram, StraightOp]⟩

theorem readMacro_straight (q bits capWords spillBase : Nat) (target pointer : Register) :
    StraightProgram (readMacro q bits capWords spillBase target pointer) := by
  simp only [readMacro, straight_append]
  exact ⟨⟨⟨⟨capAddress_straight _ _ _, readProgram_straight _ _⟩,
    indexAddress_straight _ _ _ _ _⟩, by simp [StraightProgram, StraightOp]⟩, saveReg_straight _ _⟩

theorem writeMacro_straight (q bits capWords spillBase : Nat) (pointer source : Register) :
    StraightProgram (writeMacro q bits capWords spillBase pointer source) := by
  simp only [writeMacro, straight_append]
  repeat' constructor
  all_goals first
    | exact capAddress_straight _ _ _
    | exact readProgram_straight _ _
    | exact loadReg_straight _ _ _
    | exact safeWriteProgram_straight _ _
    | exact indexAddress_straight _ _ _ _ _
    | simp [StraightProgram, StraightOp]

theorem translateOp_straight (q bits capWords spillBase : Nat) (op : Op) :
    StraightProgram (translateOp q bits capWords spillBase op) := by
  cases op with
  | base instruction =>
    cases instruction <;> first
      | exact readMacro_straight _ _ _ _ _ _
      | exact writeMacro_straight _ _ _ _ _ _
      | simp [translateOp, loadReg, saveReg, StraightProgram, StraightOp]
  | subtract _ _ _ => simp [translateOp, loadReg, saveReg, StraightProgram, StraightOp]

theorem packedProgram_straight (q bits capWords indexWords : Nat) (body : List Op) :
    StraightProgram (packedProgram q bits capWords indexWords body) := by
  simp only [packedProgram, straight_append]
  refine ⟨⟨⟨physicalWipe_straight _, ?_⟩, restore_straight _⟩, physicalWipe_straight _⟩
  intro op ho
  obtain ⟨entry, _, hop⟩ := List.mem_flatMap.mp ho
  exact translateOp_straight _ _ _ _ entry op hop

theorem packingTrace_length_le (program : List PackingOp) : (packingTrace program).length ≤ 12 * program.length + 6 := by
  have hflat : (program.flatMap PackingOp.events).length ≤ 12 * program.length := by
    induction program with
    | nil => simp
    | cons op later ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have hh := packingOp_events_length_le op
      omega
  simp only [packingTrace, List.length_append, List.length_map, haltTrace_length]
  omega

theorem packedProgram_cost_le (q bits capWords indexWords spillBase : Nat) (body : List Op) :
    (packingCode (packedProgram q bits capWords indexWords body)).length +
      (packingTrace (packedProgram q bits capWords indexWords body)).length + 8 ≤
        512 * ((haltingWords (logicalProgram spillBase body)).length +
          (trace (logicalProgram spillBase body) ++ haltTrace).length + 8) := by
  have hl := packedProgram_length_le q bits capWords indexWords body
  have ht := packingTrace_length_le (packedProgram q bits capWords indexWords body)
  rw [packingCode_length, haltingWords_length, logicalProgram_length]
  omega

theorem packedPhysicalWords_bitBound (q capWords indexWords bits : Nat) :
    (packedCapacityWords q capWords bits + indexWords) * bits ≤
      capWords * CapacityBits.width q + (indexWords + 1) * bits := by
  have hd := Nat.div_mul_le_self (capWords * CapacityBits.width q + bits - 1) bits
  unfold packedCapacityWords
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
  omega

theorem loadReg_value {bits : Nat} (spillBase : Nat) (source target : Register) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (loadReg spillBase source target) state).register target = state.heap (BitVec.ofNat bits (spillBase + source.word)) := by
  simp [loadReg, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem loadReg_heap {bits : Nat} (spillBase : Nat) (source target : Register) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (loadReg spillBase source target) state).heap = state.heap := rfl

theorem saveReg_heap {bits : Nat} (spillBase : Nat) (target : Register) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (saveReg spillBase target) state).heap =
      Function.update state.heap (BitVec.ofNat bits (spillBase + target.word)) (state.register .value) := rfl

theorem loadReg_register_frame {bits : Nat} (spillBase : Nat) (source target : Register)
    (rom : PhysicalROM) (state : WordState bits) (register : Register)
    (htotal : register ≠ .total) (htarget : register ≠ target) :
    (executeOps rom (loadReg spillBase source target) state).register register = state.register register := by
  simp [loadReg, executeOps, packingExecuteOp, wordOp, wordInstruction, htotal, htarget]

theorem saveReg_register_frame {bits : Nat} (spillBase : Nat) (target : Register)
    (rom : PhysicalROM) (state : WordState bits) (register : Register) (htotal : register ≠ .total) :
    (executeOps rom (saveReg spillBase target) state).register register = state.register register := by
  simp [saveReg, executeOps, packingExecuteOp, wordOp, wordInstruction, htotal]

theorem capAddress_heap {bits : Nat} (capWords spillBase : Nat) (pointer : Register) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (capAddress capWords spillBase pointer) state).heap = state.heap := rfl

theorem capAddress_flag {bits : Nat} (capWords spillBase : Nat) (pointer : Register) (rom : PhysicalROM) (state : WordState bits)
    (hcap : Fits bits capWords) :
    (executeOps rom (capAddress capWords spillBase pointer) state).register .flag =
      BitVec.ofNat bits (capWords - (state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat) := by
  simp [capAddress, loadReg, executeOps, packingExecuteOp, wordOp, wordInstruction, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap]

theorem capAddress_address {bits : Nat} (capWords spillBase : Nat) (pointer : Register) (rom : PhysicalROM) (state : WordState bits)
    (hcap : Fits bits capWords) :
    (executeOps rom (capAddress capWords spillBase pointer) state).register .address =
      if (state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat < capWords then
        state.heap (BitVec.ofNat bits (spillBase + pointer.word)) else BitVec.ofNat bits 0 := by
  have hsub : capWords - (state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat < 2 ^ bits :=
    (Nat.sub_le _ _).trans_lt hcap
  by_cases ha : (state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat < capWords
  · have hne : capWords - (state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat ≠ 0 := by omega
    simp [capAddress, loadReg, executeOps, packingExecuteOp, wordOp, wordInstruction,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap, Nat.mod_eq_of_lt hsub, ha, hne]
  · have hz : capWords - (state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat = 0 := by omega
    simp [capAddress, loadReg, executeOps, packingExecuteOp, wordOp, wordInstruction,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap, ha, hz]

theorem indexAddress_heap {bits : Nat} (q capWords spillBase : Nat) (pointer : Register) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (indexAddress q bits capWords spillBase pointer) state).heap = state.heap := rfl

theorem indexAddress_index {bits : Nat} (q capWords spillBase : Nat) (pointer : Register) (rom : PhysicalROM) (state : WordState bits)
    (hcap : Fits bits capWords) :
    (executeOps rom (indexAddress q bits capWords spillBase pointer) state).register .index =
      BitVec.ofNat bits (packedCapacityWords q capWords bits +
        ((state.heap (BitVec.ofNat bits (spillBase + pointer.word))).toNat - capWords)) := by
  simp [indexAddress, loadReg, executeOps, packingExecuteOp, wordOp, wordInstruction,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap, BitVec.ofNat_add_ofNat]

theorem indexAddress_address {bits : Nat} (q capWords spillBase : Nat) (pointer : Register) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (indexAddress q bits capWords spillBase pointer) state).register .address =
      state.heap (BitVec.ofNat bits (spillBase + pointer.word)) := rfl

theorem indexAddress_total {bits : Nat} (q capWords spillBase : Nat) (pointer : Register) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (indexAddress q bits capWords spillBase pointer) state).register .total = BitVec.ofNat bits capWords := rfl

theorem indexAddress_flag {bits : Nat} (q capWords spillBase : Nat) (pointer : Register) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (indexAddress q bits capWords spillBase pointer) state).register .flag = state.register .flag := rfl

theorem indexAddress_value {bits : Nat} (q capWords spillBase : Nat) (pointer : Register) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (indexAddress q bits capWords spillBase pointer) state).register .value = state.register .value := rfl

theorem readProgram_flag {bits : Nat} (q : Nat) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (readProgram q bits) state).register .flag = state.register .flag := rfl

theorem readProgram_address {bits : Nat} (q : Nat) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (readProgram q bits) state).register .address = state.register .address := rfl

theorem safeWriteProgram_address {bits : Nat} (q : Nat) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (safeWriteProgram q bits) state).register .address = state.register .address := rfl

theorem safeWriteProgram_value {bits : Nat} (q : Nat) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (safeWriteProgram q bits) state).register .value = state.register .value := rfl

theorem restore_heap {bits : Nat} (spillBase : Nat) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (restore spillBase) state).heap = state.heap := rfl

theorem restore_register {bits : Nat} (spillBase : Nat) (rom : PhysicalROM) (state : WordState bits)
    (register : Register) (hflag : register ≠ .flag) (htotal : register ≠ .total) :
    (executeOps rom (restore spillBase) state).register register = state.heap (BitVec.ofNat bits (spillBase + register.word)) := by
  cases register <;> first | rfl | contradiction

theorem physicalWipe_register {bits : Nat} (spillBase : Nat) (rom : PhysicalROM) (state : WordState bits) (register : Register) :
    (executeOps rom (physicalWipe spillBase) state).register register =
      if register = .flag ∨ register = .total then BitVec.ofNat bits 0 else state.register register := by
  cases register <;> rfl

theorem restore_physicalWipe_register {bits : Nat} (spillBase : Nat) (rom : PhysicalROM) (state : WordState bits) (register : Register) :
    (executeOps rom (restore spillBase ++ physicalWipe spillBase) state).register register =
      if register = .flag ∨ register = .total then BitVec.ofNat bits 0 else
        state.heap (BitVec.ofNat bits (spillBase + register.word)) := by
  rw [executeOps_append, physicalWipe_register]
  split_ifs with heq
  · rfl
  · push Not at heq
    exact restore_register spillBase rom state register heq.1 heq.2

theorem index_update_capacity {bits : Nat} (q capWords physicalAddress : Nat)
    (value : BitVec bits) (heap : BitVec bits → BitVec bits)
    (hbits : 0 < bits) (hregion : Fits bits (capWords * CapacityBits.width q))
    (haddress : packedCapacityWords q capWords bits ≤ physicalAddress) (hphysical : Fits bits physicalAddress)
    (address : Nat) (ha : address < capWords) :
    unpackHeap q capWords bits (Function.update heap (BitVec.ofNat bits physicalAddress) value) address =
      unpackHeap q capWords bits heap address := by
  rw [unpackHeap, unpackHeap, ite_eq_left ha, ite_eq_left ha]
  congr 1
  apply congrArg List.ofFn
  funext position
  dsimp only
  have hm := Nat.mul_le_mul_right (CapacityBits.width q) (show address + 1 ≤ capWords by omega)
  rw [Nat.add_mul, Nat.one_mul] at hm
  have hoffset : address * CapacityBits.width q + position.val < capWords * CapacityBits.width q := by have := position.isLt; omega
  have hword : (address * CapacityBits.width q + position.val) / bits < packedCapacityWords q capWords bits := by
    apply (Nat.div_lt_iff_lt_mul hbits).mpr
    exact hoffset.trans_le (packedCapacityWords_mul_bits q capWords hbits)
  have hfit : Fits bits ((address * CapacityBits.width q + position.val) / bits) :=
    (Nat.div_le_self _ _).trans_lt (hoffset.trans hregion)
  rw [Function.update_of_ne ((ofNat_injective_of_fit _ _ hfit hphysical).not.mpr (by omega))]

end PaperProofs.Structure.LaminarTree.PA17PackedTranslator034
