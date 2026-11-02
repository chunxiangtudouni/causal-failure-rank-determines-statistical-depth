module

public import Structure.PSTR_LiveControllerPrefix_137
public import Structure.PSTR_LiveControllerHalt_134
public import Structure.PSTR_LiveControllerUpdate_136

/-! Compose the SAME actual pref clock with a concrete update+return.
The original all-command theorem must construct the update from136. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace PaperProofs.Structure.LaminarTree.PSTRLiveController

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PA17A19RuntimeEntry020 PSTRWordSegments

theorem active_after_update {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (command : Command) (heap : BitVec (wordBits full) → BitVec (wordBits full)) (steps count : Nat)
    (upper : steps ≤ PSTRUniformQuery.budget full + 18) (countBound : count ≤ 102)
    (pref : PrefixPost full configuration command heap steps)
    (update : PSTRLiveControllerUpdate.UpdatePost full configuration (capacity full) command
      PSTRLiveControllerCode.program count 1514 (allocatedWords full)
      (packingRun (callInput q full command) PSTRLiveControllerCode.program steps (packingInitial heap))) :
    ∃ total ≤ PSTRUniformQuery.budget full + 123, ActiveCall full configuration command heap total := by
  let program := PSTRLiveControllerCode.program
  let rom := callInput q full command
  let initial := packingInitial heap
  let before := packingRun rom program steps initial
  have runFinal : packingRun rom program (steps + (count + 3)) initial = packingRun rom program (count + 3) before := by
    rw [run_add]
  refine ⟨steps + (count + 3), by omega, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [PSTRLiveControllerCode.program_length, runFinal]
    exact update.pc
  · rw [runFinal]
    exact update.active
  · rw [runFinal]
    exact update.represented
  · intro cursor
    rw [runFinal]
    exact PSTRLiveControllerUpdate.UpdatePost.reply full configuration (capacity full) command program count 1514 (allocatedWords full) before update
      (callback q full ⟨configuration.stage, cursor⟩ configuration.used) (pref.reply cursor)
  · intro clock hc
    by_cases early : clock ≤ steps
    · exact pref.capacityBound clock early
    · rw [show clock = steps + (clock - steps) by omega, run_add]
      exact update.capacity (clock - steps) (by omega)
  · intro clock hc address ha positive
    by_cases early : clock ≤ steps
    · exact pref.table clock early address ha positive
    · rw [show clock = steps + (clock - steps) by omega, run_add]
      exact (update.table (clock - steps) (by omega) address ha).trans
        (pref.table steps le_rfl address ha positive)
  · intro clock hc
    by_cases early : clock < steps
    · exact pref.safe clock early
    · rw [show clock = steps + (clock - steps) by omega, run_add]
      exact update.safe (clock - steps) (by omega)

end PaperProofs.Structure.LaminarTree.PSTRLiveController
