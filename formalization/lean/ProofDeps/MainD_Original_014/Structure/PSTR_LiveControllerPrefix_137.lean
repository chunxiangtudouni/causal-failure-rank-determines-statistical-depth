module

public import Structure.PSTR_LiveControllerBody_133
public import Structure.PSTR_LiveControllerCode_129
public import Structure.PSTR_LiveDispatchComplete_131

/-! One original ALL-command body+dispatcher prefix of the SAME1514 code.
All data and prefix properties share the same existential clock. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace PaperProofs.Structure.LaminarTree.PSTRLiveController

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open RawTreePreprocessingClaims PA17A19RuntimeEntry020 PSTRCountKernel PSTRWordSegments

structure PrefixPost {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (command : Command) (heap : BitVec (wordBits full) → BitVec (wordBits full)) (steps : Nat) : Prop where
  active : (packingRun (callInput q full command) PSTRLiveControllerCode.program steps (packingInitial heap)).halted = false
  pc : (packingRun (callInput q full command) PSTRLiveControllerCode.program steps (packingInitial heap)).pc =
    BitVec.ofNat (wordBits full) (5 * PSTRLiveDispatch.destination q command 1371 1494 1505 1514
      ((packingRun (callInput q full command) PSTRLiveControllerCode.program steps (packingInitial heap)).register .index).toNat)
  represented : HeapRepresents q full (capacity full)
    (if q = 0 then nextConfiguration q full configuration command else configuration)
    (packingRun (callInput q full command) PSTRLiveControllerCode.program steps (packingInitial heap)).heap
  reply : ∀ cursor : configuration.stage < full.length + 1,
    ReplyCorrect q (callback q full ⟨configuration.stage, cursor⟩ configuration.used)
      (replyState q (capacity full) (packingRun (callInput q full command) PSTRLiveControllerCode.program steps (packingInitial heap)))
  width : 0 < q → (packingRun (callInput q full command) PSTRLiveControllerCode.program steps (packingInitial heap)).heap
    (BitVec.ofNat (wordBits full) (PSTRCountWorkspace.base q full (capacity full) (wordBits full) + 12)) =
      BitVec.ofNat (wordBits full) (CapacityBits.width q)
  capacityBound : ∀ clock ≤ steps, CapacityPrefixBounded q (capacity full)
    (logicalHeap q (capacity full) (packingRun (callInput q full command) PSTRLiveControllerCode.program clock (packingInitial heap)).heap)
  table : ∀ clock ≤ steps, ∀ address < tableWords full.length q (treeSize q full), 0 < q →
    logicalHeap q (capacity full) (packingRun (callInput q full command) PSTRLiveControllerCode.program clock (packingInitial heap)).heap address =
      logicalHeap q (capacity full) heap address
  safe : ∀ clock < steps, AtSafe (callInput q full command) PSTRLiveControllerCode.program (allocatedWords full)
    (packingRun (callInput q full command) PSTRLiveControllerCode.program clock (packingInitial heap))

theorem actual_prefix {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (command : Command) (allowed : Allowed full configuration command) (hl : LaminarSchedule full)
    (heap : BitVec (wordBits full) → BitVec (wordBits full))
    (rep : HeapRepresents q full (capacity full) configuration heap) :
    ∃ steps ≤ PSTRUniformQuery.budget full + 18, PrefixPost full configuration command heap steps := by
  let program := PSTRLiveControllerCode.program
  let rom := callInput q full command
  let initial := packingInitial heap
  have hw := PSTRLiveControllerCode.program_words full.length q
  have hpc := PSTRLiveControllerCode.program_pc full.length q
  obtain ⟨bodySteps, upper, body⟩ := PSTRLiveControllerBody.actual_body full configuration command allowed hl program
    PSTRLiveControllerCode.body_contains hw hpc
    (by rw [PSTRLiveControllerCode.program_length]; decide) PSTRLiveControllerCode.literal initial rfl rfl rep
  let before := packingRun rom program bodySteps initial
  let d := PSTRLiveDispatch.duration q command
  have dispatch := PSTRLiveDispatch.actual_dispatch full command program 1371 1494 1505 1514
    (allocatedWords full) before PSTRLiveControllerCode.dispatch_block hw hpc body.pc body.active
  have runFinal : packingRun rom program (bodySteps + d) initial = packingRun rom program d before := by rw [run_add]
  have hd : d ≤ 18 := dispatch.steps
  have index : (packingRun rom program d before).register .index = before.register .index :=
    (dispatch.execution.reply d le_rfl).2.2.2
  refine ⟨bodySteps + d, by omega, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [runFinal]
    exact dispatch.execution.active
  · rw [runFinal, index]
    exact dispatch.pc
  · rw [runFinal, dispatch.execution.heap d le_rfl]
    exact body.represented
  · intro cursor
    rw [runFinal]
    exact PSTRRepairHeap.replyCorrect_of_registers (capacity full) before _ (dispatch.execution.reply d le_rfl)
      (callback q full ⟨configuration.stage, cursor⟩ configuration.used) (body.reply cursor)
  · intro hpositive
    rw [runFinal, dispatch.execution.heap d le_rfl]
    exact body.width hpositive
  · intro clock hc
    by_cases hb : clock ≤ bodySteps
    · exact body.capacity clock hb
    · rw [show clock = bodySteps + (clock - bodySteps) by omega, run_add]
      rw [dispatch.execution.heap (clock - bodySteps) (show clock - bodySteps ≤ d by omega)]
      exact body.capacity bodySteps le_rfl
  · intro clock hc address ha positive
    by_cases hb : clock ≤ bodySteps
    · exact body.table clock hb address ha positive
    · rw [show clock = bodySteps + (clock - bodySteps) by omega, run_add]
      rw [dispatch.execution.heap (clock - bodySteps) (show clock - bodySteps ≤ d by omega)]
      exact body.table bodySteps le_rfl address ha positive
  · intro clock hc
    by_cases hb : clock < bodySteps
    · exact body.safe clock hb
    · rw [show clock = bodySteps + (clock - bodySteps) by omega, run_add]
      exact dispatch.execution.safe (clock - bodySteps) (show clock - bodySteps < d by omega)

end PaperProofs.Structure.LaminarTree.PSTRLiveController
