module

public import Structure.PSTR_BuildLower_ResourceTrace_094
public import Structure.PSTR_BuildLower_LoadData_064

/-! A proved readonly actual trace transports both physical invariants;
the real three-instruction VM writeback then carries them at the SAME count
as source/data simulation. Concrete readonly ports must supply their true
prefix heap equality, not an original-caller frame or answer oracle. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ResourceTrace
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem of_readonly (q : Nat) (full : List (Finset (Fin q))) (physical : PhysicalROM)
    (whole : List PackingOp) (state : WordState (bits q full)) (count : Nat)
    (bounded : GlobalCapacity.Bounded q full state.heap)
    (frame : ∀ clock ≤ count, (packingRun physical whole clock state).heap = state.heap) :
    Keeps q full physical whole state count := by
  intro clock hc
  rw [frame clock hc]
  exact ⟨bounded, CacheFrame.refl q full state.heap⟩

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ResourceTrace

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem finish_load_resources (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (target : Register) (value : Nat) (logical : State) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (bounded : GlobalCapacity.Bounded q full state.heap) (hvalue : state.register .value = BitVec.ofNat _ value)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ relativeWrite (registerOffset target) ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ relativeWrite (registerOffset target) ++ right).length)) :
    let after := packingRun physical (left ++ relativeWrite (registerOffset target) ++ right) 3 state
    Prepared q full (loaded logical target value) after ∧ RuntimeData.Data q full after.heap ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + 3)) ∧ after.halted = false ∧
      (∀ offset ≤ 512, offset ≠ registerOffset target → after.heap (BitVec.ofNat _ (controlBase q full + offset)) =
        state.heap (BitVec.ofNat _ (controlBase q full + offset))) ∧
      ResourceTrace.Keeps q full physical (left ++ relativeWrite (registerOffset target) ++ right) state 3 := by
  have actual := finish_load_data q full hq physical target value logical state hrep data hvalue left right hpc ha hcode hpcfit
  have hlo := (registerSlot_bounds target).1
  have hhi := (registerSlot_bounds target).2
  change 32 ≤ registerOffset target at hlo
  change registerOffset target < 39 at hhi
  have keeps := ResourceTrace.bank_actual_keeps q full hq physical (relativeWrite (registerOffset target)) 32 39
    (by decide) (by decide) (ViewFrame.relativeWrite_range physical (registerOffset target) 32 39 hlo hhi)
    (relativeWrite_straight _) state hrep.address bounded left right hpc ha hcode hpcfit
  rw [relativeWrite_length] at keeps
  exact ⟨actual.1, actual.2.1, actual.2.2.1, actual.2.2.2.1, actual.2.2.2.2, keeps⟩

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
