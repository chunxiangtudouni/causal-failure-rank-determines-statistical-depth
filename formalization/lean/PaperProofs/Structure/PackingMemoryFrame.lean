module

public import PaperProofs.Structure.PackingMachine
public import PaperProofs.Structure.RawTreePreprocessingClaims

/-! Actual machine access bounds imply a memory frame outside the allocated
workspace. This is used when composing the raw checker with tree output;
it does not grant a fresh zero workspace or silently reset physical memory. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PackingMachine

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def GuardedAccess {bits : Nat} (heapWords : Nat) (rom : PhysicalROM)
    (program : List PackingOp) (state : WordState bits) : Prop :=
  state.halted = false →
    match PackingOp.decode (physicalFetch bits (packingCode program) state.pc.toNat) with
    | none => True
    | some op => packingAccessFits rom heapWords state op

theorem packingExecuteOp_heap_frame {bits : Nat} (rom : PhysicalROM) (heapWords : Nat)
    (op : PackingOp) (state : WordState bits) (haccess : packingAccessFits rom heapWords state op)
    (address : BitVec bits) (haddress : heapWords ≤ address.toNat) :
    (packingExecuteOp rom op state).heap address = state.heap address := by
  cases op with
  | base op =>
    cases op with
    | base instruction =>
      cases instruction with
      | storeHeap pointer source =>
        have hp : (state.register pointer).toNat < heapWords := haccess
        have hne : address ≠ state.register pointer := by
          intro heq
          rw [heq] at haddress
          omega
        change Function.update state.heap (state.register pointer) (state.register source) address = _
        exact Function.update_of_ne hne _ _
      | constant target value => rfl
      | add target left right => rfl
      | minimum target left right => rfl
      | select target condition whenTrue whenFalse => rfl
      | loadROM region target pointer => rfl
      | loadHeap target pointer => rfl
    | subtract target left right => rfl
  | arithmetic operation target left right => rfl
  | jumpIfZero condition target => rfl

theorem packingStep_heap_frame {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (heapWords : Nat) (state : WordState bits) (haccess : GuardedAccess heapWords rom program state)
    (address : BitVec bits) (haddress : heapWords ≤ address.toNat) :
    (packingStep rom ((packingCode program).map (BitVec.ofNat bits)) state).heap address = state.heap address := by
  change (if state.halted then state else
    match PackingOp.decode (physicalFetch bits (packingCode program) state.pc.toNat) with
    | none => { state with halted := true }
    | some op => packingExecuteOp rom op state).heap address = _
  cases hh : state.halted
  · have hs := haccess hh
    cases hd : PackingOp.decode (physicalFetch bits (packingCode program) state.pc.toNat) with
    | none => simp only [Bool.false_eq_true, ite_false]
    | some op =>
      rw [hd] at hs
      simp only [Bool.false_eq_true, ite_false]
      exact packingExecuteOp_heap_frame rom heapWords op state hs address haddress
  · simp only [ite_true]

theorem packingRun_heap_frame {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (heapWords count : Nat) (state : WordState bits)
    (haccess : ∀ k < count, GuardedAccess heapWords rom program (packingRun rom program k state))
    (address : BitVec bits) (haddress : heapWords ≤ address.toNat) :
    (packingRun rom program count state).heap address = state.heap address := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [packingRun_succ]
    exact (packingStep_heap_frame rom program heapWords _ (haccess count (by omega)) address haddress).trans
      (ih (fun k hk => haccess k (by omega)))

theorem dynamicRunCorrect_heap_frame {bits : Nat} (heapWords : Nat) (rom : PhysicalROM)
    (program : List PackingOp) (steps : Nat) (heap : BitVec bits → BitVec bits)
    (hcorrect : RawTreePreprocessingClaims.DynamicRunCorrect heapWords rom program steps heap)
    (address : BitVec bits) (haddress : heapWords ≤ address.toNat) :
    (packingRun rom program steps (packingInitial heap)).heap address = heap address := by
  apply packingRun_heap_frame rom program heapWords steps (packingInitial heap) ?_ address haddress
  intro k hk hactive
  have hs := (hcorrect.2.2.2.2 k hk).2.2
  change (match PackingOp.decode
    (RawTreePreprocessingClaims.fetch program (packingRun rom program k (packingInitial heap))) with
    | none => True
    | some op => packingAccessFits rom heapWords (packingRun rom program k (packingInitial heap)) op)
  cases hd : PackingOp.decode
      (RawTreePreprocessingClaims.fetch program (packingRun rom program k (packingInitial heap))) with
  | none => trivial
  | some op =>
    rw [hd] at hs
    exact hs

end PaperProofs.Structure.LaminarTree.PackingMachine
