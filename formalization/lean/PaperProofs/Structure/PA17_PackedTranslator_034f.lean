module

public import PaperProofs.Structure.PA17_PackedTranslator_034e

/-! Saved-register representation and ordinary-instruction translation.
Real virtual-register writes preserve every original logical heap word,
including arbitrary index words; the extra seven slots are explicit. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17PackedTranslator034

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM

def savedRegisters {bits : Nat} (spillBase : Nat) (heap : BitVec bits → BitVec bits) (register : Register) : BitVec bits :=
  heap (BitVec.ofNat bits (spillBase + register.word))

def virtualState {bits : Nat} (spillBase : Nat) (state : WordState bits) : WordState bits :=
  { state with register := savedRegisters spillBase state.heap }

def NonHeapOp : Op → Prop
  | .base (.loadHeap _ _) | .base (.storeHeap _ _) => False
  | _ => True

def opTarget : Op → Register
  | .base (.constant target _) | .base (.add target _ _) | .base (.minimum target _ _)
  | .base (.select target _ _ _) | .base (.loadROM _ target _) | .base (.loadHeap target _)
  | .subtract target _ _ => target
  | .base (.storeHeap _ _) => .flag

theorem register_word_injective : Function.Injective Register.word := by
  intro left right heq
  have hh := congrArg Register.fromWord heq
  simpa only [Register.fromWord_word, Option.some.injEq] using hh

theorem spill_slot_fits {bits : Nat} (spillBase : Nat) (hfoot : Fits bits (spillBase + spillWords))
    (register : Register) : Fits bits (spillBase + register.word) := by
  have hw := register_word_lt register
  exact (Nat.add_lt_add_left hw spillBase).trans hfoot

theorem savedRegisters_update {bits : Nat} (spillBase : Nat) (heap : BitVec bits → BitVec bits)
    (target : Register) (value : BitVec bits) (hfoot : Fits bits (spillBase + spillWords)) :
    savedRegisters spillBase (Function.update heap (BitVec.ofNat bits (spillBase + target.word)) value) =
      Function.update (savedRegisters spillBase heap) target value := by
  funext register
  change (Function.update heap (BitVec.ofNat bits (spillBase + target.word)) value)
    (BitVec.ofNat bits (spillBase + register.word)) =
      (Function.update (savedRegisters spillBase heap) target value) register
  by_cases heq : register = target
  · subst register; simp
  · have hnat : spillBase + register.word ≠ spillBase + target.word := by
      intro hh
      exact heq (register_word_injective (Nat.add_left_cancel hh))
    rw [Function.update_of_ne ((ofNat_injective_of_fit _ _ (spill_slot_fits spillBase hfoot register)
      (spill_slot_fits spillBase hfoot target)).not.mpr hnat), Function.update_of_ne heq]
    rfl

theorem spill_update_old_heap {bits : Nat} (q capWords indexWords spillBase : Nat)
    (heap : BitVec bits → BitVec bits) (target : Register) (value : BitVec bits)
    (hbits : 0 < bits) (hbase : spillBase = packedCapacityWords q capWords bits + indexWords)
    (hfoot : Fits bits (spillBase + spillWords)) (hregion : Fits bits (capWords * CapacityBits.width q))
    (address : Nat) (ha : address < capWords + indexWords) :
    unpackHeap q capWords bits (Function.update heap (BitVec.ofNat bits (spillBase + target.word)) value) address =
      unpackHeap q capWords bits heap address := by
  have htarget := spill_slot_fits spillBase hfoot target
  by_cases hcap : address < capWords
  · exact index_update_capacity q capWords (spillBase + target.word) value heap hbits hregion (by omega) htarget address hcap
  · have hi : packedCapacityWords q capWords bits + (address - capWords) < spillBase := by omega
    have hifit : Fits bits (packedCapacityWords q capWords bits + (address - capWords)) := by
      have hs : spillBase < spillBase + spillWords := by simp [spillWords]
      exact hi.trans (hs.trans hfoot)
    simp only [unpackHeap, hcap, ite_false]
    rw [Function.update_of_ne ((ofNat_injective_of_fit _ _ hifit htarget).not.mpr (by omega))]

theorem saveReg_savedRegisters {bits : Nat} (spillBase : Nat) (target : Register)
    (rom : PhysicalROM) (state : WordState bits) (hfoot : Fits bits (spillBase + spillWords)) :
    savedRegisters spillBase (executeOps rom (saveReg spillBase target) state).heap =
      Function.update (savedRegisters spillBase state.heap) target (state.register .value) := by
  rw [saveReg_heap]
  exact savedRegisters_update spillBase state.heap target (state.register .value) hfoot

theorem saveReg_old_heap {bits : Nat} (q capWords indexWords spillBase : Nat) (target : Register)
    (rom : PhysicalROM) (state : WordState bits) (hbits : 0 < bits)
    (hbase : spillBase = packedCapacityWords q capWords bits + indexWords)
    (hfoot : Fits bits (spillBase + spillWords)) (hregion : Fits bits (capWords * CapacityBits.width q))
    (address : Nat) (ha : address < capWords + indexWords) :
    unpackHeap q capWords bits (executeOps rom (saveReg spillBase target) state).heap address =
      unpackHeap q capWords bits state.heap address := by
  rw [saveReg_heap]
  exact spill_update_old_heap q capWords indexWords spillBase state.heap target _ hbits hbase hfoot hregion address ha

theorem translateOp_nonheap_heap {bits : Nat} (q capWords spillBase : Nat) (op : Op)
    (hn : NonHeapOp op) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (translateOp q bits capWords spillBase op) state).heap =
      Function.update state.heap (BitVec.ofNat bits (spillBase + (opTarget op).word))
        ((wordOp rom op (virtualState spillBase state)).register (opTarget op)) := by
  cases op with
  | base instruction =>
    cases instruction <;>
      simp_all [NonHeapOp, opTarget, translateOp, loadReg, saveReg, executeOps,
        packingExecuteOp, wordOp, wordInstruction, virtualState, savedRegisters]
    all_goals rfl
  | subtract _ _ _ =>
    simp [opTarget, translateOp, loadReg, saveReg, executeOps, packingExecuteOp,
      wordOp, wordInstruction, virtualState, savedRegisters]

theorem wordOp_nonheap_register {bits : Nat} (spillBase : Nat) (op : Op) (hn : NonHeapOp op)
    (rom : PhysicalROM) (state : WordState bits) :
    (wordOp rom op (virtualState spillBase state)).register =
      Function.update (savedRegisters spillBase state.heap) (opTarget op)
        ((wordOp rom op (virtualState spillBase state)).register (opTarget op)) := by
  cases op with
  | base instruction =>
    cases instruction <;> simp_all [NonHeapOp, opTarget, wordOp, wordInstruction, virtualState]
  | subtract _ _ _ => simp [opTarget, wordOp, virtualState]

theorem wordOp_nonheap_register_congr {bits : Nat} (op : Op) (hn : NonHeapOp op)
    (rom : PhysicalROM) (left right : WordState bits) (hregister : left.register = right.register) :
    (wordOp rom op left).register = (wordOp rom op right).register := by
  rcases left with ⟨lr, lh, lp, la⟩
  rcases right with ⟨rr, rh, rp, ra⟩
  dsimp only at hregister
  subst rr
  cases op with
  | base instruction =>
    cases instruction with
    | constant _ _ => rfl
    | add _ _ _ => rfl
    | minimum _ _ _ => rfl
    | select _ _ _ _ => rfl
    | loadROM _ _ _ => rfl
    | loadHeap _ _ => cases hn
    | storeHeap _ _ => cases hn
  | subtract _ _ _ => rfl

theorem translateOp_nonheap_savedRegisters {bits : Nat} (q capWords spillBase : Nat) (op : Op)
    (hn : NonHeapOp op) (rom : PhysicalROM) (state : WordState bits) (hfoot : Fits bits (spillBase + spillWords)) :
    savedRegisters spillBase (executeOps rom (translateOp q bits capWords spillBase op) state).heap =
      (wordOp rom op (virtualState spillBase state)).register := by
  rw [translateOp_nonheap_heap q capWords spillBase op hn rom state, savedRegisters_update _ _ _ _ hfoot]
  exact (wordOp_nonheap_register spillBase op hn rom state).symm

theorem translateOp_nonheap_old_heap {bits : Nat} (q capWords indexWords spillBase : Nat) (op : Op)
    (hn : NonHeapOp op) (rom : PhysicalROM) (state : WordState bits) (hbits : 0 < bits)
    (hbase : spillBase = packedCapacityWords q capWords bits + indexWords)
    (hfoot : Fits bits (spillBase + spillWords)) (hregion : Fits bits (capWords * CapacityBits.width q))
    (address : Nat) (ha : address < capWords + indexWords) :
    unpackHeap q capWords bits (executeOps rom (translateOp q bits capWords spillBase op) state).heap address =
      unpackHeap q capWords bits state.heap address := by
  rw [translateOp_nonheap_heap q capWords spillBase op hn rom state]
  exact spill_update_old_heap q capWords indexWords spillBase state.heap _ _ hbits hbase hfoot hregion address ha

theorem translateOp_nonheap_take_heap {bits : Nat} (q capWords spillBase : Nat) (op : Op)
    (hn : NonHeapOp op) (rom : PhysicalROM) (state : WordState bits) (count : Nat)
    (hc : count ≤ (translateOp q bits capWords spillBase op).length) :
    (executeOps rom ((translateOp q bits capWords spillBase op).take count) state).heap =
      if count < (translateOp q bits capWords spillBase op).length then state.heap else
        (executeOps rom (translateOp q bits capWords spillBase op) state).heap := by
  cases op with
  | base instruction =>
    cases instruction with
    | constant target value => change count ≤ 3 at hc; interval_cases count <;> rfl
    | add target left right => change count ≤ 7 at hc; interval_cases count <;> rfl
    | minimum target left right => change count ≤ 7 at hc; interval_cases count <;> rfl
    | select target condition whenTrue whenFalse => change count ≤ 9 at hc; interval_cases count <;> rfl
    | loadROM region target pointer => change count ≤ 5 at hc; interval_cases count <;> rfl
    | loadHeap target pointer => cases hn
    | storeHeap pointer source => cases hn
  | subtract target left right => change count ≤ 7 at hc; interval_cases count <;> rfl

theorem translateOp_nonheap_prefix_old_heap {bits : Nat} (q capWords indexWords spillBase : Nat) (op : Op)
    (hn : NonHeapOp op) (rom : PhysicalROM) (state : WordState bits) (hbits : 0 < bits)
    (hbase : spillBase = packedCapacityWords q capWords bits + indexWords)
    (hfoot : Fits bits (spillBase + spillWords)) (hregion : Fits bits (capWords * CapacityBits.width q))
    (count : Nat) (hc : count ≤ (translateOp q bits capWords spillBase op).length)
    (address : Nat) (ha : address < capWords + indexWords) :
    unpackHeap q capWords bits (executeOps rom ((translateOp q bits capWords spillBase op).take count) state).heap address =
      unpackHeap q capWords bits state.heap address := by
  rw [translateOp_nonheap_take_heap q capWords spillBase op hn rom state count hc]
  split_ifs
  · rfl
  · exact translateOp_nonheap_old_heap q capWords indexWords spillBase op hn rom state hbits hbase hfoot hregion address ha

theorem readMacro_savedRegisters {bits : Nat} (q capWords spillBase : Nat) (target pointer : Register)
    (rom : PhysicalROM) (state : WordState bits) (hfoot : Fits bits (spillBase + spillWords)) :
    savedRegisters spillBase (executeOps rom (readMacro q bits capWords spillBase target pointer) state).heap =
      Function.update (savedRegisters spillBase state.heap) target
        ((executeOps rom (readMacro q bits capWords spillBase target pointer) state).register .value) := by
  rw [readMacro_heap]
  exact savedRegisters_update spillBase state.heap target _ hfoot

theorem readMacro_prefix_old_heap {bits : Nat} (q capWords indexWords spillBase : Nat) (target pointer : Register)
    (rom : PhysicalROM) (state : WordState bits) (hbits : 0 < bits)
    (hbase : spillBase = packedCapacityWords q capWords bits + indexWords)
    (hfoot : Fits bits (spillBase + spillWords)) (hregion : Fits bits (capWords * CapacityBits.width q))
    (count : Nat) (hc : count ≤ (readMacro q bits capWords spillBase target pointer).length)
    (address : Nat) (ha : address < capWords + indexWords) :
    unpackHeap q capWords bits (executeOps rom ((readMacro q bits capWords spillBase target pointer).take count) state).heap address =
      unpackHeap q capWords bits state.heap address := by
  rw [readMacro_take_heap q capWords spillBase target pointer rom state count hc]
  split_ifs
  · rfl
  · rw [readMacro_heap]
    exact spill_update_old_heap q capWords indexWords spillBase state.heap target _ hbits hbase hfoot hregion address ha

end PaperProofs.Structure.LaminarTree.PA17PackedTranslator034
