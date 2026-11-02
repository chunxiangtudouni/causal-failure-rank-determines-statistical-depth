module

public import Structure.PSTR_BuildLower_LoadResources_101
public import Structure.PSTR_BuildLower_ConcreteReadExits_067

/-! An actual readonly port and its real VM writeback have ONE count for
source/data simulation, full NEW-C capacity and every high-cache word. The
ReadExit object is constructed by the concrete frozen ports, not supplied by
the original caller. No endpoint heap equality is promoted to a prefix fact. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem read_then_write_end_resources (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (target : Register) (value limit : Nat) (logical : State) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (bounded : GlobalCapacity.Bounded q full state.heap) (left block right : List PackingOp)
    (port : ReadExit physical left block (relativeWrite (registerOffset target) ++ right) state value limit)
    (hcode : WordsFit (bits q full) (packingCode (left ++ block ++ relativeWrite (registerOffset target) ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ block ++ relativeWrite (registerOffset target) ++ right).length)) :
    let after := packingRun physical (left ++ block ++ relativeWrite (registerOffset target) ++ right) (port.steps + 3) state
    port.steps + 3 ≤ limit + 3 ∧ Prepared q full (loaded logical target value) after ∧ RuntimeData.Data q full after.heap ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + block.length + 3)) ∧ after.halted = false ∧
      (∀ offset ≤ 512, offset ≠ registerOffset target → after.heap (BitVec.ofNat _ (controlBase q full + offset)) =
        state.heap (BitVec.ofNat _ (controlBase q full + offset))) ∧
      GlobalCapacity.Bounded q full after.heap ∧ ResourceTrace.CacheFrame q full state.heap after.heap := by
  let code := left ++ block ++ relativeWrite (registerOffset target) ++ right
  let middle := packingRun physical code port.steps state
  have middleHeap : middle.heap = state.heap := by simpa only [middle, code, List.append_assoc] using port.heap
  have middleBase : middle.register .address = state.register .address := by simpa only [middle, code, List.append_assoc] using port.address
  have middleValue : middle.register .value = BitVec.ofNat _ value := by simpa only [middle, code, List.append_assoc] using port.value
  have middlePC : middle.pc = BitVec.ofNat _ (5 * (left ++ block).length) := by
    simpa only [middle, code, List.append_assoc, List.length_append] using port.pc
  have middleActive : middle.halted = false := by simpa only [middle, code, List.append_assoc] using port.active
  have middleRep : Prepared q full logical middle := by
    refine ⟨middleBase.trans hrep.address, ?_, ?_⟩
    · rw [middleHeap]
      exact hrep.registers
    · rw [middleHeap]
      exact hrep.heap
  have middleData : RuntimeData.Data q full middle.heap := by rw [middleHeap]; exact data
  have middleBounded : GlobalCapacity.Bounded q full middle.heap := by rw [middleHeap]; exact bounded
  have final := finish_load_resources q full hq physical target value logical middle middleRep middleData middleBounded middleValue
    (left ++ block) right middlePC middleActive hcode hpcfit
  have whole : packingRun physical code (port.steps + 3) state = packingRun physical code 3 middle :=
    PSTRWordSegments.run_add physical code port.steps 3 state
  dsimp only at final ⊢
  rw [whole]
  refine ⟨Nat.add_le_add_right port.bounded 3, final.1, final.2.1, ?_, final.2.2.2.1, ?_,
    (final.2.2.2.2.2 3 le_rfl).1, ?_⟩
  · calc
      _ = BitVec.ofNat _ (5 * ((left ++ block).length + 3)) := final.2.2.1
      _ = BitVec.ofNat _ (5 * (left.length + block.length + 3)) := by rw [List.length_append]
  · intro offset ho hn
    exact (final.2.2.2.2.1 offset ho hn).trans (congrFun middleHeap _)
  · intro point hp hf
    exact ((final.2.2.2.2.2 3 le_rfl).2 point hp hf).trans (congrFun middleHeap _)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
