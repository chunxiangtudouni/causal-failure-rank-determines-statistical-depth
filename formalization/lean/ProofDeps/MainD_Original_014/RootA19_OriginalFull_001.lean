module

public import PaperProofs.Structure.CompactControllerClaims
import Structure.PA06_A19Prepare_AllQFinal089_Expanded
import RootA19_ImportIsolationProbe_Consumer_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

@[expose] public section
open PaperProofs.Structure.LaminarTree
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims

namespace RootA19.OriginalFull

universe u

private theorem actual_raw :
∃ (Cpre : Nat) (P : List PackingOp),
  ∀ (q : Nat) (full : List (Finset (Fin q))), LaminarSchedule full →
  ∀ used : Finset (Fin q),
  let N := full.length
  let t := treeSize q full
  let bits := indexWidth 32 N q
  let capWords := capacityWords 8192 N q t
  let heapWords := physicalHeaderWords + packedCapacityWords q capWords bits +
    8192 * (N + q + t + 1)
  let empty : BitVec bits → BitVec bits := fun _ => BitVec.ofNat bits 0
  let source := controllerInput q full used
  ∃ steps : Nat,
    DynamicRunCorrect heapWords source P steps empty ∧
    totalCost heapWords source P steps empty ≤ Cpre * preprocessingWork N q t ∧
    HeapRepresents q full capWords ⟨0, used, false⟩
      (packingRun source P steps (packingInitial empty)).heap := by
  obtain ⟨Cpre, P, _positive, rawP⟩ :=
    PA06A19PrepareAllQFinal089Expanded.fixed_raw_implementation
  refine ⟨Cpre, P, ?_⟩
  simpa only [CompactControllerClaims.physicalHeaderWords] using rawP

theorem fullClaims : CompactControllerClaims.FullClaims.{u} :=
  RootA19.ImportIsolationProbe.Consumer.conditional_fullClaims actual_raw

theorem machineControllerClaims : CompactControllerClaims.MachineControllerClaims :=
  fullClaims.{0}.2.2.2.1

end RootA19.OriginalFull
