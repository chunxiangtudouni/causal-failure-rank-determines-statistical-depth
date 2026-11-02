module

public import PaperProofs.Structure.PackingMachine

/-! Charged events of the actual fetched execution, including encoded HALT.
Straight-line instruction counts are connected to the dynamic physical trace;
branching clients also obtain a bound per actual interpreter step. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PackingMachine

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def stepEvents {bits : Nat} (_rom : PhysicalROM) (program : List PackingOp) (state : WordState bits) :
    List (Sum Event PackingPrimitive) :=
  if state.halted then [] else
    match PackingOp.decode (physicalFetch bits (packingCode program) state.pc.toNat) with
    | none => haltTrace.map Sum.inl
    | some op => op.events

theorem dynamicTrace_of_halted {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (count : Nat) (state : WordState bits) (hhalted : state.halted = true) :
    packingDynamicTrace rom program count state = [] := by
  cases count with
  | zero => rfl
  | succ count => simp only [packingDynamicTrace, hhalted, ite_true]

theorem dynamicTrace_succ {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (count : Nat) (state : WordState bits) :
    packingDynamicTrace rom program (count + 1) state = stepEvents rom program state ++
      packingDynamicTrace rom program count
        (packingStep rom ((packingCode program).map (BitVec.ofNat bits)) state) := by
  cases hh : state.halted
  · cases hd : PackingOp.decode (physicalFetch bits (packingCode program) state.pc.toNat) with
    | none =>
      have hs : packingStep rom ((packingCode program).map (BitVec.ofNat bits)) state =
          { state with halted := true } := by
        change (if state.halted then state else
          match PackingOp.decode (physicalFetch bits (packingCode program) state.pc.toNat) with
          | none => { state with halted := true }
          | some op => packingExecuteOp rom op state) = _
        simp only [hh, Bool.false_eq_true, ite_false, hd]
      rw [hs, dynamicTrace_of_halted rom program count _ rfl, List.append_nil]
      change (if state.halted then [] else
        match PackingOp.decode (physicalFetch bits (packingCode program) state.pc.toNat) with
        | none => haltTrace.map Sum.inl
        | some op => op.events ++ packingDynamicTrace rom program count (packingExecuteOp rom op state)) = _
      simp only [hh, Bool.false_eq_true, ite_false, hd, stepEvents]
    | some op =>
      change (if state.halted then [] else
        match PackingOp.decode (physicalFetch bits (packingCode program) state.pc.toNat) with
        | none => haltTrace.map Sum.inl
        | some op => op.events ++ packingDynamicTrace rom program count (packingExecuteOp rom op state)) = _
      change _ = stepEvents rom program state ++ packingDynamicTrace rom program count
        (if state.halted then state else
          match PackingOp.decode (physicalFetch bits (packingCode program) state.pc.toNat) with
          | none => { state with halted := true }
          | some op => packingExecuteOp rom op state)
      simp only [hh, Bool.false_eq_true, ite_false, hd, stepEvents]
  · rw [dynamicTrace_of_halted rom program (count + 1) state hh]
    simp only [stepEvents, hh, ite_true, List.nil_append]
    simp only [packingStep, hh, ite_true]
    apply (dynamicTrace_of_halted rom program count state hh).symm

theorem dynamicTrace_add {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (left right : Nat) (state : WordState bits) :
    packingDynamicTrace rom program (left + right) state = packingDynamicTrace rom program left state ++
      packingDynamicTrace rom program right (packingRun rom program left state) := by
  induction left generalizing state with
  | zero => simp only [Nat.zero_add, packingDynamicTrace, packingRun, List.nil_append]
  | succ left ih =>
    rw [Nat.succ_add, dynamicTrace_succ, dynamicTrace_succ, List.append_assoc]
    exact congrArg (stepEvents rom program state ++ ·) (ih _)

theorem dynamicTrace_succ_right {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (count : Nat) (state : WordState bits) :
    packingDynamicTrace rom program (count + 1) state = packingDynamicTrace rom program count state ++
      stepEvents rom program (packingRun rom program count state) := by
  rw [dynamicTrace_add, dynamicTrace_succ]
  simp only [packingDynamicTrace, List.append_nil]

theorem stepEvents_of_index {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (state : WordState bits) (index : Nat) (hindex : index < program.length)
    (hfit : WordsFit bits (packingCode program)) (hpc : state.pc.toNat = 5 * index)
    (hactive : state.halted = false) :
    stepEvents rom program state = (program[index]'hindex).events := by
  simp only [stepEvents, hactive, Bool.false_eq_true, ite_false]
  rw [physicalFetch_eq bits (packingCode program) state.pc.toNat hfit, hpc]
  change (match PackingOp.decode (natFetch program (5 * index)) with
    | none => haltTrace.map Sum.inl
    | some op => op.events) = _
  rw [natFetch_body program index hindex, decode_encode]

theorem stepEvents_halt {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (state : WordState bits) (hfit : WordsFit bits (packingCode program))
    (hpc : state.pc.toNat = 5 * program.length) (hactive : state.halted = false) :
    stepEvents rom program state = haltTrace.map Sum.inl := by
  simp only [stepEvents, hactive, Bool.false_eq_true, ite_false]
  rw [physicalFetch_eq bits (packingCode program) state.pc.toNat hfit, hpc]
  change (match PackingOp.decode (natFetch program (5 * program.length)) with
    | none => haltTrace.map Sum.inl
    | some op => op.events) = _
  rw [natFetch_halt, decode_halt]

theorem dynamicTrace_prefix {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (state : WordState bits) (hstraight : StraightProgram program)
    (hfit : WordsFit bits (packingCode program)) (hpcfit : Fits bits (5 * program.length))
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false)
    (count : Nat) (hcount : count ≤ program.length) :
    packingDynamicTrace rom program count state = (program.take count).flatMap PackingOp.events := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have hlt : count < program.length := by omega
    rw [dynamicTrace_succ_right, ih (by omega),
      packingRun_eq_executeOps_take rom program state hstraight hfit hpcfit hpc hactive count (by omega)]
    have hpref : StraightProgram (program.take count) :=
      fun op ho => hstraight op (List.mem_of_mem_take ho)
    have hp : (executeOps rom (program.take count) state).pc.toNat = 5 * count := by
      rw [executeOps_pc rom (program.take count) state hpref, hpc, BitVec.zero_add,
        List.length_take_of_le (by omega), BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (lt_of_le_of_lt (by omega) hpcfit)
    rw [stepEvents_of_index rom program _ count hlt hfit hp (by rw [executeOps_halted, hactive]),
      List.take_succ_eq_append_getElem hlt, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem packingDynamicTrace_eq_packingTrace {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (state : WordState bits) (hstraight : StraightProgram program)
    (hfit : WordsFit bits (packingCode program)) (hpcfit : Fits bits (5 * program.length))
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    packingDynamicTrace rom program (program.length + 1) state = packingTrace program := by
  rw [dynamicTrace_succ_right,
    dynamicTrace_prefix rom program state hstraight hfit hpcfit hpc hactive program.length le_rfl,
    List.take_length,
    packingRun_eq_executeOps_take rom program state hstraight hfit hpcfit hpc hactive program.length le_rfl,
    List.take_length]
  have hp : (executeOps rom program state).pc.toNat = 5 * program.length := by
    rw [executeOps_pc rom program state hstraight, hpc, BitVec.zero_add, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hpcfit
  rw [stepEvents_halt rom program _ hfit hp (by rw [executeOps_halted, hactive])]
  rfl

theorem packingOp_events_length_le (op : PackingOp) : op.events.length ≤ 12 := by
  cases op with
  | base op =>
    cases op with
    | base instruction =>
      cases instruction <;> simp [PackingOp.events, Op.trace, Instruction.trace, Instruction.operations]
    | subtract target left right => simp [PackingOp.events, Op.trace]
  | arithmetic operation target left right => simp [PackingOp.events]
  | jumpIfZero condition target => simp [PackingOp.events]

theorem stepEvents_length_le {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (state : WordState bits) : (stepEvents rom program state).length ≤ 12 := by
  unfold stepEvents
  split_ifs
  · simp only [List.length_nil, zero_le]
  · split
    · rw [List.length_map, haltTrace_length]
      decide
    · exact packingOp_events_length_le _

theorem packingDynamicTrace_length_le {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (count : Nat) (state : WordState bits) :
    (packingDynamicTrace rom program count state).length ≤ 12 * count := by
  induction count generalizing state with
  | zero => simp only [packingDynamicTrace, List.length_nil, Nat.mul_zero, le_refl]
  | succ count ih =>
    rw [dynamicTrace_succ, List.length_append]
    have hs := stepEvents_length_le rom program state
    have ht := ih (packingStep rom ((packingCode program).map (BitVec.ofNat bits)) state)
    omega

end PaperProofs.Structure.LaminarTree.PackingMachine
