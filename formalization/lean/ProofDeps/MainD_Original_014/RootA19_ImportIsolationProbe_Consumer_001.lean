module

public import PaperProofs.Structure.RawTreePreprocessingA06Closure
public import PaperProofs.Structure.PA17_FullGivenTree_049
public import PaperProofs.Structure.PSTR_Callback_001
import RootA19_ImportIsolationProbe_Machine_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

@[expose] public section
open PaperProofs.Structure.LaminarTree
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims

namespace RootA19.ImportIsolationProbe.Consumer

universe u

theorem conditional_fullClaims (raw :
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
      (packingRun source P steps (packingInitial empty)).heap) : CompactControllerClaims.FullClaims.{u} :=
  ⟨RawTreePreprocessingA06Closure.fullClaims,
    PA17FullGivenTree049.fullGivenTreeClaims, PSTRCallback.callbackClaims,
    RootA19.ImportIsolationProbe.Machine.from_raw raw, PSTRCallback.nativeCallbackClaims⟩

end RootA19.ImportIsolationProbe.Consumer
