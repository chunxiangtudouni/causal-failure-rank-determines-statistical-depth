module

public import PaperProofs.Structure.CompactControllerClaims
import RootA19_ImportIsolationProbe_Raw_001
import Structure.PSTR_LiveControllerStage_141

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

@[expose] public section
open PaperProofs.Structure.LaminarTree
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims

namespace RootA19.ImportIsolationProbe.Machine

theorem from_raw (raw :
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
      (packingRun source P steps (packingInitial empty)).heap) : MachineControllerClaims := by
  have neutral : RootA19.ImportIsolationProbe.Raw.RawExists :=
    RootA19.ImportIsolationProbe.Raw.transport raw
  obtain ⟨Cpre, P, rawP⟩ := neutral
  have stageRaw : PSTRLiveControllerStage.RawPreprocessorObligation Cpre P := by
    simpa only [PSTRLiveControllerStage.RawPreprocessorObligation,
      PA17A19RuntimeEntry020.wordBits, PA17A19RuntimeEntry020.capacity,
      PA17A19RuntimeEntry020.allocatedWords] using rawP
  exact PSTRLiveControllerStage.machine_of_actual_preprocessor
    Cpre P PSTRLiveControllerCode.program rfl stageRaw

end RootA19.ImportIsolationProbe.Machine
