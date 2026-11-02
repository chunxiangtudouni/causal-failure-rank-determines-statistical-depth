module

public import PaperProofs.Structure.PackingMachine

/-!
No-overflow transport from the natural proof view to the original physical
word machine. The safety hypotheses are exact prefix numeric bounds to be
proved for the constructed algorithms, not additional paper assumptions.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PackingMachine

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def RegistersFit (bits : Nat) (state : NatState) : Prop :=
  ∀ register, Fits bits (state.register register)

theorem toWord_register_toNat (bits : Nat) (state : NatState) (hfit : RegistersFit bits state)
    (register : Register) : ((state.toWord bits).register register).toNat = state.register register :=
  Nat.mod_eq_of_lt (hfit register)

theorem map_update_register (bits : Nat) (registers : Register → Nat) (target : Register) (value : Nat) :
    (fun register => BitVec.ofNat bits (Function.update registers target value register)) =
      Function.update (fun register => BitVec.ofNat bits (registers register)) target (BitVec.ofNat bits value) := by
  funext register
  by_cases heq : register = target <;> simp [heq]

theorem map_update_heap (bits : Nat) (heap : Nat → Nat) (pointer value : Nat)
    (hpointer : Fits bits pointer) :
    (fun address : BitVec bits => BitVec.ofNat bits (Function.update heap pointer value address.toNat)) =
      Function.update (fun address : BitVec bits => BitVec.ofNat bits (heap address.toNat))
        (BitVec.ofNat bits pointer) (BitVec.ofNat bits value) := by
  funext address
  have hp : (BitVec.ofNat bits pointer).toNat = pointer := Nat.mod_eq_of_lt hpointer
  by_cases heq : address = BitVec.ofNat bits pointer
  · subst address
    simp only [hp, Function.update_self]
  · have hne : address.toNat ≠ pointer := by
      intro hh
      apply heq
      exact BitVec.eq_of_toNat_eq (hh.trans hp.symm)
    rw [Function.update_of_ne hne, Function.update_of_ne heq]

theorem wordState_ext {bits : Nat} {left right : WordState bits}
    (hregister : left.register = right.register) (hheap : left.heap = right.heap)
    (hpc : left.pc = right.pc) (hhalted : left.halted = right.halted) : left = right := by
  cases left
  cases right
  simp only at hregister hheap hpc hhalted
  subst_vars
  rfl

theorem natExecuteOp_toWord {bits : Nat} (rom : PhysicalROM) (op : PackingOp) (state : NatState)
    (hfit : RegistersFit bits state) :
    packingExecuteOp rom op (state.toWord bits) = (natExecuteOp rom op state).toWord bits := by
  have hr (register : Register) : (BitVec.ofNat bits (state.register register)).toNat = state.register register :=
    Nat.mod_eq_of_lt (hfit register)
  cases op with
  | base op =>
    cases op with
    | base instruction =>
      cases instruction with
      | constant target value =>
        apply wordState_ext
        · exact (map_update_register bits state.register target value).symm
        · rfl
        · exact (BitVec.ofNat_add state.pc 5).symm
        · rfl
      | add target left right =>
        apply wordState_ext
        · simpa only [packingExecuteOp, wordOp, wordInstruction, NatState.toWord, natExecuteOp,
            Op.execute, Instruction.execute, BitVec.ofNat_add] using
            (map_update_register bits state.register target (state.register left + state.register right)).symm
        · rfl
        · exact (BitVec.ofNat_add state.pc 5).symm
        · rfl
      | minimum target left right =>
        apply wordState_ext
        · simp only [packingExecuteOp, wordOp, wordInstruction, NatState.toWord, natExecuteOp,
            Op.execute, Instruction.execute, hr]
          funext register
          by_cases heq : register = target
          · subst register
            simp only [Function.update_self]
            split_ifs with h
            · rw [min_eq_left h]
            · rw [min_eq_right (Nat.le_of_not_ge h)]
          · simp only [Function.update_of_ne heq]
        · rfl
        · exact (BitVec.ofNat_add state.pc 5).symm
        · rfl
      | select target condition whenTrue whenFalse =>
        apply wordState_ext
        · simp only [packingExecuteOp, wordOp, wordInstruction, NatState.toWord, natExecuteOp,
            Op.execute, Instruction.execute, hr]
          split_ifs <;> exact (map_update_register bits state.register target _).symm
        · rfl
        · exact (BitVec.ofNat_add state.pc 5).symm
        · rfl
      | loadROM region target pointer =>
        apply wordState_ext
        · simpa only [packingExecuteOp, wordOp, wordInstruction, NatState.toWord, natExecuteOp,
            Op.execute, Instruction.execute, PhysicalROM.semantic, hr] using
            (map_update_register bits state.register target ((rom.words region).getD (state.register pointer) 0)).symm
        · rfl
        · exact (BitVec.ofNat_add state.pc 5).symm
        · rfl
      | loadHeap target pointer =>
        apply wordState_ext
        · simpa only [packingExecuteOp, wordOp, wordInstruction, NatState.toWord, natExecuteOp,
            Op.execute, Instruction.execute, hr] using
            (map_update_register bits state.register target (state.heap (state.register pointer))).symm
        · rfl
        · exact (BitVec.ofNat_add state.pc 5).symm
        · rfl
      | storeHeap pointer source =>
        apply wordState_ext
        · rfl
        · simpa only [packingExecuteOp, wordOp, wordInstruction, NatState.toWord, natExecuteOp,
            Op.execute, Instruction.execute, hr] using
            (map_update_heap bits state.heap (state.register pointer) (state.register source) (hfit pointer)).symm
        · exact (BitVec.ofNat_add state.pc 5).symm
        · rfl
    | subtract target left right =>
      apply wordState_ext
      · simpa only [packingExecuteOp, wordOp, NatState.toWord, natExecuteOp,
          Op.execute, hr] using
          (map_update_register bits state.register target (state.register left - state.register right)).symm
      · rfl
      · exact (BitVec.ofNat_add state.pc 5).symm
      · rfl
  | arithmetic operation target left right =>
    apply wordState_ext
    · cases operation <;>
        simp only [packingExecuteOp, packingArithmetic, NatState.toWord, natExecuteOp, natArithmetic, hr] <;>
        exact (map_update_register bits state.register target _).symm
    · rfl
    · exact (BitVec.ofNat_add state.pc 5).symm
    · rfl
  | jumpIfZero condition target =>
    apply wordState_ext
    · rfl
    · rfl
    · simp only [packingExecuteOp, NatState.toWord, natExecuteOp, hr]
      split_ifs
      · rfl
      · exact (BitVec.ofNat_add state.pc 5).symm
    · rfl

theorem natStep_toWord {bits : Nat} (rom : PhysicalROM) (program : List PackingOp) (state : NatState)
    (hfit : RegistersFit bits state) (hpc : Fits bits state.pc)
    (hcode : WordsFit bits (packingCode program)) :
    packingStep rom ((packingCode program).map (BitVec.ofNat bits)) (state.toWord bits) =
      (natStep rom program state).toWord bits := by
  have hpc' : (BitVec.ofNat bits state.pc).toNat = state.pc := Nat.mod_eq_of_lt hpc
  change (if state.halted then state.toWord bits else
    match PackingOp.decode (physicalFetch bits (packingCode program) (BitVec.ofNat bits state.pc).toNat) with
    | none => { state.toWord bits with halted := true }
    | some op => packingExecuteOp rom op (state.toWord bits)) = _
  rw [hpc', physicalFetch_eq bits (packingCode program) state.pc hcode]
  change (if state.halted then state.toWord bits else
    match PackingOp.decode (natFetch program state.pc) with
    | none => { state.toWord bits with halted := true }
    | some op => packingExecuteOp rom op (state.toWord bits)) = _
  cases hh : state.halted
  · cases hd : PackingOp.decode (natFetch program state.pc) with
    | none => simp only [natStep, hh, Bool.false_eq_true, ite_false, hd]; rfl
    | some op =>
      simp only [natStep, hh, Bool.false_eq_true, ite_false, hd]
      exact natExecuteOp_toWord rom op state hfit
  · simp only [natStep, hh, ite_true]

theorem natRun_toWord {bits : Nat} (rom : PhysicalROM) (program : List PackingOp) (state : NatState)
    (count : Nat) (hcode : WordsFit bits (packingCode program))
    (hfit : ∀ k < count, RegistersFit bits (natRun rom program k state) ∧
      Fits bits (natRun rom program k state).pc) :
    packingRun rom program count (state.toWord bits) = (natRun rom program count state).toWord bits := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [packingRun_succ, ih (fun k hk => hfit k (by omega)), natRun_succ]
    exact natStep_toWord rom program _ (hfit count (by omega)).1 (hfit count (by omega)).2 hcode

end PaperProofs.Structure.LaminarTree.PackingMachine
