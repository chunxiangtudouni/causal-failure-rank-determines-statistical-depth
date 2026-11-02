module

public import Structure.PSTR_LiveControllerRoom_132

/-! The real final HALT transports ONE concrete active live-call witness
to the original CallClaims. Constructing that witness for every command
is the remaining declaration-composition theorem, not an assumed oracle. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRLiveController

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open RawTreePreprocessingClaims AlgorithmClaims.PackedCapacityRAM PA17A19RuntimeEntry020 PSTRCountKernel

structure ActiveCall {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (command : Command) (heap : BitVec (wordBits full) → BitVec (wordBits full)) (steps : Nat) : Prop where
  pc : (packingRun (callInput q full command) PSTRLiveControllerCode.program steps (packingInitial heap)).pc =
    BitVec.ofNat (wordBits full) (5 * PSTRLiveControllerCode.program.length)
  active : (packingRun (callInput q full command) PSTRLiveControllerCode.program steps (packingInitial heap)).halted = false
  represented : HeapRepresents q full (capacity full) (nextConfiguration q full configuration command)
    (packingRun (callInput q full command) PSTRLiveControllerCode.program steps (packingInitial heap)).heap
  reply : ∀ cursor : configuration.stage < full.length + 1,
    ReplyCorrect q (callback q full ⟨configuration.stage, cursor⟩ configuration.used)
      (replyState q (capacity full) (packingRun (callInput q full command) PSTRLiveControllerCode.program steps (packingInitial heap)))
  capacityBound : ∀ clock ≤ steps, CapacityPrefixBounded q (capacity full)
    (logicalHeap q (capacity full) (packingRun (callInput q full command) PSTRLiveControllerCode.program clock (packingInitial heap)).heap)
  table : ∀ clock ≤ steps, ∀ address < tableWords full.length q (treeSize q full), 0 < q →
    logicalHeap q (capacity full) (packingRun (callInput q full command) PSTRLiveControllerCode.program clock (packingInitial heap)).heap address =
      logicalHeap q (capacity full) heap address
  safe : ∀ clock < steps, AtSafe (callInput q full command) PSTRLiveControllerCode.program (allocatedWords full)
    (packingRun (callInput q full command) PSTRLiveControllerCode.program clock (packingInitial heap))

theorem callClaims_of_active {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (command : Command) (heap : BitVec (wordBits full) → BitVec (wordBits full)) (steps : Nat)
    (upper : steps ≤ PSTRUniformQuery.budget full + 123)
    (post : ActiveCall full configuration command heap steps) :
    CallClaims 32768 q full (capacity full) (allocatedWords full)
      PSTRLiveControllerCode.program configuration command (steps + 1) heap := by
  let rom := callInput q full command
  let program := PSTRLiveControllerCode.program
  let before := packingRun rom program steps (packingInitial heap)
  have hw := PSTRLiveControllerCode.program_words full.length q
  have hpc := PSTRLiveControllerCode.program_pc full.length q
  have halt := PSTRCountKernel.halt_at_exit rom program steps (packingInitial heap) hw hpc post.active post.pc
  have heap_eq : (packingRun rom program (steps + 1) (packingInitial heap)).heap = before.heap := by
    have h := congrArg (fun state : WordState (wordBits full) => state.heap) halt
    exact h
  have dynamic : DynamicRunCorrect (allocatedWords full) rom program (steps + 1) heap := by
    refine ⟨hw, ?_, PSTRLiveControllerRoom.footprint_fit full command, congrArg WordState.halted halt, ?_⟩
    · have hb : 32 ≤ wordBits full := PSTROriginalCountRoom.word_lower full.length q
      exact PSTRLiveHeaderSafety.input_fit full command (by omega)
        (PSTROriginalCountRoom.raw_rooms full.length q).1
        (PSTROriginalCountRoom.dimension_rooms full).2.2.2.2
    · intro clock hc
      by_cases hs : clock < steps
      · obtain ⟨active, pc, op, decoded, access⟩ := post.safe clock hs
        exact ⟨active, pc, by rw [decoded]; exact access⟩
      · have he : clock = steps := by omega
        subst clock
        exact PSTRCountAllocation.terminal_access rom program _ before hw hpc post.pc post.active
  refine ⟨dynamic, PSTRLiveControllerRoom.call_cost_bound full command (steps + 1) heap (by omega), ?_, ?_, ?_, ?_⟩
  · rw [heap_eq]
    exact post.represented
  · intro address ha positive
    rw [heap_eq]
    exact post.table steps le_rfl address ha positive
  · intro clock hc _positive
    by_cases hs : clock ≤ steps
    · exact post.capacityBound clock hs
    · have he : clock = steps + 1 := by omega
      subst clock
      rw [heap_eq]
      exact post.capacityBound steps le_rfl
  · intro cursor
    rw [halt]
    exact post.reply cursor

end PaperProofs.Structure.LaminarTree.PSTRLiveController
