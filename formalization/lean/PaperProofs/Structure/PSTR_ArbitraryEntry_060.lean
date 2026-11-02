module

public import PaperProofs.Structure.PSTR_BootstrapSlices_057

/-! A real jump back to pc0 may enter with arbitrary payload registers.
The first14 actual fetched instructions overwrite every register. Equality
after that real prefix justifies reuse of the original entry proof; it is
not a reset instruction or a helper restart performed by the machine. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRArbitraryEntry

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

def entryLead : List PackingOp :=
  PSTRLiveHeader.program ++ PSTRRuntimeWidth.initCode ++ PSTRWidthKernel.testLeadAt 8

theorem entryLead_length : entryLead.length = 14 := rfl

theorem entryLead_straight : StraightProgram entryLead := by
  simp [entryLead, PSTRLiveHeader.program, PSTRRuntimeWidth.initCode, PSTRWidthKernel.testLeadAt,
    StraightProgram, StraightOp]

theorem entry_index_bound (whole : List PackingOp) (hbound : 14 ≤ whole.length)
    (i : Nat) (hi : i < entryLead.length) : i < whole.length := by
  rw [entryLead_length] at hi
  omega

structure Contains (whole : List PackingOp) : Prop where
  bound : 14 ≤ whole.length
  code : ∀ i (hi : i < entryLead.length), whole[i]'(entry_index_bound whole bound i hi) = entryLead[i]

theorem of_bootstrap (whole : List PackingOp) (hc : PSTRBootstrapSlices.Contains whole) : Contains whole := by
  refine ⟨by have hb := hc.bound; omega, ?_⟩
  intro i hi
  have hh := hc.code i (by rw [PSTRCountBootstrapCode.program_length]; rw [entryLead_length] at hi; omega)
  have he : PSTRCountBootstrapCode.program[i]'(by rw [PSTRCountBootstrapCode.program_length]; rw [entryLead_length] at hi; omega) =
      entryLead[i] := by
    change i < 14 at hi
    interval_cases i <;> rfl
  exact hh.trans he

theorem state_ext {bits : Nat} (left right : WordState bits)
    (hr : left.register = right.register) (hh : left.heap = right.heap)
    (hp : left.pc = right.pc) (ha : left.halted = right.halted) : left = right := by
  cases left with
  | mk lr lh lp la =>
    cases right with
    | mk rr rh rp ra =>
      dsimp only at hr hh hp ha
      cases hr
      cases hh
      cases hp
      cases ha
      rfl

set_option maxHeartbeats 1000000 in
theorem entry_registers {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom entryLead state).register =
      (executeOps rom entryLead (packingInitial state.heap)).register := by
  funext register
  cases register <;>
    simp +decide only [entryLead, PSTRLiveHeader.program, PSTRRuntimeWidth.initCode,
      PSTRWidthKernel.testLeadAt, List.cons_append, List.nil_append, executeOps,
      packingExecuteOp, wordOp, wordInstruction, packingArithmetic, packingInitial,
      Function.update_apply, ↓reduceIte]

theorem entry_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom entryLead state).heap = state.heap := by
  have ht (current : WordState bits) :
      (executeOps rom (PSTRWidthKernel.testLeadAt 8) current).heap = current.heap := rfl
  rw [entryLead, executeOps_append, executeOps_append, ht, PSTRWidthKernel.init_heap,
    PSTRLiveHeader.execute_heap]

theorem execute_entry {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    executeOps rom entryLead state = executeOps rom entryLead (packingInitial state.heap) := by
  apply state_ext _ _ (entry_registers rom state)
  · rw [entry_heap, entry_heap]
    rfl
  · rw [executeOps_pc rom entryLead state entryLead_straight,
      executeOps_pc rom entryLead (packingInitial state.heap) entryLead_straight, hp]
    rfl
  · rw [executeOps_halted, executeOps_halted, ha]
    rfl

theorem fetched_entry {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (hc : Contains whole) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    packingRun rom whole 14 state = executeOps rom entryLead state := by
  apply PSTRWordSegments.straight_segment rom whole entryLead 0
    (by have hb := hc.bound; rw [entryLead_length]; omega) ?_ entryLead_straight hw hpcfit state hp ha
  intro i hi
  simpa only [Nat.zero_add] using hc.code i hi

theorem run_from_arbitrary {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (hc : Contains whole) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false)
    (steps : Nat) (hsteps : 14 ≤ steps) :
    packingRun rom whole steps state = packingRun rom whole steps (packingInitial state.heap) := by
  have he : packingRun rom whole 14 state = packingRun rom whole 14 (packingInitial state.heap) :=
    (fetched_entry rom whole hc hw hpcfit state hp ha).trans
      ((execute_entry rom state hp ha).trans (fetched_entry rom whole hc hw hpcfit (packingInitial state.heap) rfl rfl).symm)
  rw [show steps = 14 + (steps - 14) by omega, PSTRWordSegments.run_add, PSTRWordSegments.run_add, he]

end PaperProofs.Structure.LaminarTree.PSTRArbitraryEntry
