module

public import Structure.PSTR_BuildLower_LoadData_064

/-! One compositional proof object for an ACTUAL fetched read-port run.
Concrete constructors must prove its run/value/heap/PC fields from the fixed
backend. It is not an original caller premise or a whole-builder oracle. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

structure ReadExit {bits : Nat} (rom : PhysicalROM) (left block right : List PackingOp)
    (state : WordState bits) (value limit : Nat) where
  steps : Nat
  bounded : steps ≤ limit
  value : (packingRun rom (left ++ block ++ right) steps state).register .value = BitVec.ofNat bits value
  heap : (packingRun rom (left ++ block ++ right) steps state).heap = state.heap
  address : (packingRun rom (left ++ block ++ right) steps state).register .address = state.register .address
  pc : (packingRun rom (left ++ block ++ right) steps state).pc = BitVec.ofNat bits (5 * (left.length + block.length))
  active : (packingRun rom (left ++ block ++ right) steps state).halted = false

theorem read_then_write_data (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (target : Register) (value limit : Nat) (logical : State) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (left block right : List PackingOp)
    (port : ReadExit physical left block (relativeWrite (registerOffset target) ++ right) state value limit)
    (hcode : WordsFit (bits q full) (packingCode (left ++ block ++ relativeWrite (registerOffset target) ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ block ++ relativeWrite (registerOffset target) ++ right).length)) :
    let after := packingRun physical (left ++ block ++ relativeWrite (registerOffset target) ++ right) (port.steps + 3) state
    port.steps + 3 ≤ limit + 3 ∧ Prepared q full (loaded logical target value) after ∧ RuntimeData.Data q full after.heap ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + block.length + 3)) ∧ after.halted = false ∧
      ∀ offset ≤ 512, offset ≠ registerOffset target →
        after.heap (BitVec.ofNat _ (controlBase q full + offset)) = state.heap (BitVec.ofNat _ (controlBase q full + offset)) := by
  let code := left ++ block ++ relativeWrite (registerOffset target) ++ right
  let middle := packingRun physical code port.steps state
  have middleHeap : middle.heap = state.heap := by
    simpa only [middle, code, List.append_assoc] using port.heap
  have middleBase : middle.register .address = state.register .address := by
    simpa only [middle, code, List.append_assoc] using port.address
  have middleValue : middle.register .value = BitVec.ofNat _ value := by
    simpa only [middle, code, List.append_assoc] using port.value
  have middlePC : middle.pc = BitVec.ofNat _ (5 * (left ++ block).length) := by
    simpa only [middle, code, List.append_assoc, List.length_append] using port.pc
  have middleActive : middle.halted = false := by
    simpa only [middle, code, List.append_assoc] using port.active
  have middleRep : Prepared q full logical middle := by
    refine ⟨middleBase.trans hrep.address, ?_, ?_⟩
    · rw [middleHeap]
      exact hrep.registers
    · rw [middleHeap]
      exact hrep.heap
  have middleData : RuntimeData.Data q full middle.heap := by rw [middleHeap]; exact data
  have final := finish_load_data q full hq physical target value logical middle middleRep middleData middleValue
    (left ++ block) right middlePC middleActive hcode hpcfit
  have whole : packingRun physical code (port.steps + 3) state = packingRun physical code 3 middle :=
    PSTRWordSegments.run_add physical code port.steps 3 state
  dsimp only at final ⊢
  rw [whole]
  refine ⟨Nat.add_le_add_right port.bounded 3, final.1, final.2.1, ?_, final.2.2.2.1, ?_⟩
  · simpa only [List.length_append] using final.2.2.1
  · intro offset ho hn
    exact (final.2.2.2.2 offset ho hn).trans (congrFun middleHeap _)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
