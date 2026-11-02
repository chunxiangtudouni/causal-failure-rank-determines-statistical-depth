module
public import RootL01_PHCompat_Assembly004
public import RootL01_PHCompat_PStatic005

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace RootL01.PHCompat.Public
open PaperProofs.Structure.LaminarTree
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open RawTreePreprocessingClaims PA17A19RuntimeEntry020 PSTRHeadsRuntime
open PaperProofs.Common.Native.CompactPrice

open Assembly

/-- Original P correctness and original H correctness on exactly the heap P produced.
The Bool VM consumer must separately pay its real ROM switch and register-reset path. -/
theorem actual_original_prepared_query {q : Nat} (full : List (Finset (Fin q)))
    (laminar : LaminarSchedule full) (used : Finset (Fin q)) :
    ∃ prepSteps headSteps : Nat,
      DynamicRunCorrect (allocatedWords full) (controllerInput q full used)
        Preparation.program prepSteps (fun _ => BitVec.ofNat (wordBits full) 0) ∧
      totalCost (allocatedWords full) (controllerInput q full used) Preparation.program prepSteps
        (fun _ => BitVec.ofNat (wordBits full) 0) ≤
        Preparation.constant * preprocessingWork full.length q (treeSize q full) ∧
      headSteps ≤ (full.length+1)*(PSTRUniformQuery.budget full+101) ∧
      DynamicRunCorrect (allocatedWords full) (callInput q full .query)
        PSTRUniformHeads.program headSteps (preparedHeap full used prepSteps) ∧
      callCost q full PSTRUniformHeads.program .query headSteps (preparedHeap full used prepSteps) ≤
        30000 * headWork q full ∧
      (let after := packingRun (callInput q full .query) PSTRUniformHeads.program headSteps
          (packingInitial (preparedHeap full used prepSteps));
        HeapRepresents q full (capacity full) ⟨full.length,used,false⟩ after.heap ∧
        (after.register .index).toNat+(headWords q full used).length≤allocatedWords full ∧
        heapWordsAt after.heap (after.register .index).toNat (headWords q full used).length=headWords q full used) := by
  exact Assembly.actual_original_prepared_query full laminar used

theorem fixed_program_certificate (N q : Nat) :
    WordsFit (indexWidth 32 N q) (packingCode Preparation.program) ∧
      Fits (indexWidth 32 N q) (5*Preparation.program.length) :=
  Preparation.selected_certificate N q

theorem constant_positive : 0<Preparation.constant := Preparation.constant_pos

end RootL01.PHCompat.Public
