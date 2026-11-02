module

public import Structure.PSTR_BuildLower_ReadPrefixExit_130
public import Structure.PSTR_BuildLower_ReadEndResources_103
public import Structure.PSTR_BuildLower_InlineAccess_120

/-! EXISTING actual read endpoint and genuine prefix certificates share the
same steps, followed by the REAL three VM-store instructions. Source output,
every-clock Cnew/cache and actual access all use that identical count/run. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem read_then_write_prefix_resources (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (target : Register) (value limit : Nat) (logical : State) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (bounded : GlobalCapacity.Bounded q full state.heap) (left block right : List PackingOp)
    (port : ReadPrefixExit (allocated q full) physical left block (relativeWrite (registerOffset target) ++ right) state value limit)
    (hcode : WordsFit (bits q full) (packingCode (left ++ block ++ relativeWrite (registerOffset target) ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ block ++ relativeWrite (registerOffset target) ++ right).length)) :
    let whole := left ++ block ++ relativeWrite (registerOffset target) ++ right
    let after := packingRun physical whole (port.steps + 3) state
    port.steps + 3 ≤ limit + 3 ∧ Prepared q full (loaded logical target value) after ∧ RuntimeData.Data q full after.heap ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + block.length + 3)) ∧ after.halted = false ∧
      (∀ offset ≤ 512, offset ≠ registerOffset target → after.heap (BitVec.ofNat _ (controlBase q full + offset)) =
        state.heap (BitVec.ofNat _ (controlBase q full + offset))) ∧
      ResourceTrace.Keeps q full physical whole state (port.steps + 3) ∧
      TraceAccess.Safe (allocated q full) physical whole state (port.steps + 3) := by
  let whole := left ++ block ++ relativeWrite (registerOffset target) ++ right
  let middle := packingRun physical whole port.steps state
  have endpoint := read_then_write_end_resources q full hq physical target value limit logical state hrep data bounded
    left block right port.toReadExit hcode hpcfit
  have frontKeeps : ResourceTrace.Keeps q full physical whole state port.steps := by
    simpa only [whole, List.append_assoc] using port.keeps q full physical left block _ state value limit bounded
  have frontSafe : TraceAccess.Safe (allocated q full) physical whole state port.steps := by
    simpa only [whole, List.append_assoc] using port.safe
  have middleBase : middle.register .address = BitVec.ofNat _ (controlBase q full) := by
    have hb : middle.register .address = state.register .address := by
      simpa only [middle, whole, List.append_assoc] using port.address
    exact hb.trans hrep.address
  have middleBounded : GlobalCapacity.Bounded q full middle.heap := (frontKeeps port.steps le_rfl).1
  have middlePC : middle.pc = BitVec.ofNat _ (5 * (left ++ block).length) := by
    simpa only [middle, whole, List.append_assoc, List.length_append] using port.pc
  have middleActive : middle.halted = false := by
    simpa only [middle, whole, List.append_assoc] using port.active
  have slots := registerSlot_bounds target
  change 32 ≤ registerOffset target ∧ registerOffset target < 39 at slots
  have backKeeps := ResourceTrace.bank_actual_keeps q full hq physical (relativeWrite (registerOffset target)) 32 39
    (by decide) (by decide) (ViewFrame.relativeWrite_range physical (registerOffset target) 32 39 slots.1 slots.2)
    (relativeWrite_straight _) middle middleBase middleBounded (left ++ block) right middlePC middleActive hcode hpcfit
  rw [relativeWrite_length] at backKeeps
  have primitive := BankAccess.write_safe physical (registerOffset target) (allocated q full) middle
    (BankAccess.point_room q full hq middle middleBase (registerOffset target) (by omega))
  have backSafe := TraceAccess.straight physical (left ++ block) (relativeWrite (registerOffset target)) right
    (allocated q full) middle (relativeWrite_straight _) primitive middlePC middleActive hcode hpcfit
  rw [relativeWrite_length] at backSafe
  refine ⟨endpoint.1, endpoint.2.1, endpoint.2.2.1, endpoint.2.2.2.1, endpoint.2.2.2.2.1, endpoint.2.2.2.2.2.1, ?_, ?_⟩
  · exact ResourceTrace.keeps_add q full physical whole state port.steps 3 frontKeeps backKeeps
  · exact TraceAccess.add (allocated q full) physical whole state port.steps 3 frontSafe backSafe

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
