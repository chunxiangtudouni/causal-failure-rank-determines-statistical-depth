module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordCache

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Fetched-prefix safety for the actual22/15-op adjacency setup blocks
and the already defined nine-op copy. These are concrete assembly helpers;
their numeric premises are discharged by WordAdjacency's original-layout
factory, rather than added to the original preprocessor's caller. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035l PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023 (RunFacts highCacheEnd)

theorem initializeAdjacency_prefix_address (rom : PhysicalROM) (state : NatState)
    (count : Nat) (hc : count ≤ 22) :
    (runOps rom (initializeAdjacency.take count) state).register .address = state.register .address := by
  interval_cases count <;> rfl

theorem setupDegreeChildren_prefix_address (rom : PhysicalROM) (state : NatState)
    (count : Nat) (hc : count ≤ 15) :
    (runOps rom (setupDegreeChildren.take count) state).register .address = state.register .address := by
  interval_cases count <;> rfl

theorem initializeAdjacency_runFacts (rom : PhysicalROM) (B H CB P M t : Nat)
    (left right : List PackingOp) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hM : state.heap (CB + 528) = M) (ht : state.heap (CB + 2) = t)
    (hbase : state.heap (CB + 6) = 4 + P) (htM : t ≤ M)
    (hlayout : CB = 4 + P + 4096 * (M + t))
    (hroom : highCacheEnd CB M < H) (hH : H ≤ B)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    RunFacts B H rom (left ++ adjacencyProgramAt left.length ++ right) 22 state := by
  let suffix := copyProgramAt (left.length + 22) ++ setupDegreeChildren ++
    copyProgramAt (left.length + 46) ++ right
  have numeric := initializeAdjacency_numeric rom B H CB P M t state
    hr hCB hM ht hbase htM hlayout hroom hH
  have safe := straight_segment_safe rom B H left initializeAdjacency suffix
    initializeAdjacency_noJump state hpc ha numeric
  refine ⟨?_, ?_⟩
  · simpa only [adjacencyProgramAt, suffix, List.append_assoc, initializeAdjacency_length] using safe
  · intro count hc
    have hprefix := straight_prefix_run rom left initializeAdjacency suffix
      initializeAdjacency_noJump state hpc ha count (by rw [initializeAdjacency_length]; exact hc)
    have hprefix' : natRun rom (left ++ adjacencyProgramAt left.length ++ right) count state =
        runOps rom (initializeAdjacency.take count) state := by
      simpa only [adjacencyProgramAt, suffix, List.append_assoc] using hprefix
    rw [hprefix']
    exact initializeAdjacency_prefix_address rom state count hc

theorem setupDegreeChildren_runFacts (rom : PhysicalROM) (B H CB M t : Nat)
    (left right : List PackingOp) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hM : state.heap (CB + 528) = M) (ht : state.heap (CB + 2) = t) (htM : t ≤ M)
    (hroom : highCacheEnd CB M < H) (hH : H ≤ B)
    (hpc : state.pc = 5 * (left.length + 31)) (ha : state.halted = false) :
    RunFacts B H rom (left ++ adjacencyProgramAt left.length ++ right) 15 state := by
  let lead := left ++ initializeAdjacency ++ copyProgramAt (left.length + 22)
  have leadLength : lead.length = left.length + 31 := by
    simp only [lead, List.length_append, initializeAdjacency_length, copyProgramAt_length]
  have numeric := setupDegreeChildren_numeric rom B H CB M t state hr hCB hM ht htM hroom hH
  have safe := straight_segment_safe rom B H lead setupDegreeChildren
    (copyProgramAt (left.length + 46) ++ right) setupDegreeChildren_noJump state
    (by rw [leadLength]; exact hpc) ha numeric
  refine ⟨?_, ?_⟩
  · simpa only [lead, adjacencyProgramAt, List.append_assoc, setupDegreeChildren_length] using safe
  · intro count hc
    have hprefix := straight_prefix_run rom lead setupDegreeChildren
      (copyProgramAt (left.length + 46) ++ right) setupDegreeChildren_noJump state
      (by rw [leadLength]; exact hpc) ha count (by rw [setupDegreeChildren_length]; exact hc)
    have hprefix' : natRun rom (left ++ adjacencyProgramAt left.length ++ right) count state =
        runOps rom (setupDegreeChildren.take count) state := by
      simpa only [lead, adjacencyProgramAt, List.append_assoc] using hprefix
    rw [hprefix']
    exact setupDegreeChildren_prefix_address rom state count hc

/-- Start the actual copy from its genuine register values. The source
words here are original cache cells; no output list or execution oracle is
an input. WordAdjacency derives these bounds from023's actual OutputData. -/
theorem copy_runFacts (rom : PhysicalROM) (B H : Nat) (left right : List PackingOp)
    (CB source target length : Nat) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hs : state.register .index = source) (ht : state.register .old = target)
    (hn : state.register .total = length) (hfresh : state.register .fresh = 1)
    (hflag : state.register .flag = 0) (hd : target + length ≤ source)
    (hsource : source + length ≤ H) (htarget : target + length ≤ H) (hH : H ≤ B)
    (hwords : ∀ position < length, state.heap (source + position) ≤ B)
    (hcodePC : 5 * (left ++ copyProgramAt left.length ++ right).length ≤ B) :
    RunFacts B H rom (left ++ copyProgramAt left.length ++ right) (9 * length + 2) state := by
  have initial : CopyInv CB source target state.heap 0 length state := by
    refine ⟨hCB, by simpa only [Nat.add_zero] using hs,
      by simpa only [Nat.add_zero] using ht, hn, hfresh, hflag, ?_⟩
    funext address
    simp [PA06A19PrepareControlBank017.relocatedHeap]
  exact copy_loop_safe rom B H left right CB source target length state.heap hd hsource htarget hH
    hwords hcodePC length 0 state (by omega) hpc ha hr initial

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
