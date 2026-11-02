module

public import PaperProofs.Structure.CompactControllerClaims
import Structure.PA06_A19Prepare_AllQPositive087_Run

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

@[expose] public section
open PaperProofs.Structure.LaminarTree
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims

namespace RootA19.ImportIsolationProbe.Raw

def RawExists : Prop :=
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
      (packingRun source P steps (packingInitial empty)).heap

theorem transport (raw : RawExists) : RawExists := raw

private theorem unused_private_identity (p : Prop) : p → p := fun h => h

end RootA19.ImportIsolationProbe.Raw
