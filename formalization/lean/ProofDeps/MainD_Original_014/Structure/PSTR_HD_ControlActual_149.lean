module

public import Structure.PSTR_HD_ControlEffects_148

/-! Actual containing-program controller-only8/6 at original w32/F8192.
All four reply registers survive every prefix from arbitrary registers.
No width slot, selected-tool value, scratch input, reset or HALT is needed. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRReplyControls
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM PSTRReplySpill PSTRCountKernel PSTRWordSegments PSTRSelectedError

structure ControlPost {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (command : Command) (ops whole : List PackingOp) (start heapWords : Nat) (state : WordState bits) : Prop where
  pc : (packingRun (callInput q full command) whole ops.length state).pc = BitVec.ofNat bits (5 * (start + ops.length))
  active : (packingRun (callInput q full command) whole ops.length state).halted = false
  represented : HeapRepresents q full capWords (nextConfiguration q full configuration command)
    (packingRun (callInput q full command) whole ops.length state).heap
  registers : ∀ clock ≤ ops.length, ReplyRegisters state (packingRun (callInput q full command) whole clock state)
  effects : ∀ clock ≤ ops.length, HeapEffects full capWords state.heap (packingRun (callInput q full command) whole clock state).heap
  safe : ∀ clock < ops.length, AtSafe (callInput q full command) whole heapWords (packingRun (callInput q full command) whole clock state)
  trace : (packingDynamicTrace (callInput q full command) whole ops.length state).length ≤ 12 * ops.length

theorem ControlPost.reply {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (command : Command) (ops whole : List PackingOp) (start heapWords : Nat) (state : WordState bits)
    (post : ControlPost full configuration capWords command ops whole start heapWords state)
    (answer : IndexedQuery.Reply q) (before : ReplyCorrect q answer (replyState q capWords state))
    (clock : Nat) (hc : clock ≤ ops.length) :
    ReplyCorrect q answer (replyState q capWords (packingRun (callInput q full command) whole clock state)) :=
  PSTRRepairHeap.replyCorrect_of_registers capWords state _ (post.registers clock hc) answer before

theorem actual_controls {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (command : Command) (ops whole : List PackingOp) (start heapWords : Nat) (state : WordState bits)
    (straight : StraightProgram ops) (block : PSTROuterCountCode.BlockAt whole start ops)
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (represented : HeapRepresents q full capWords (nextConfiguration q full configuration command)
      (executeOps (callInput q full command) ops state).heap)
    (registers : ∀ clock ≤ ops.length, ReplyRegisters state (executeOps (callInput q full command) (ops.take clock) state))
    (effects : ∀ clock ≤ ops.length, HeapEffects full capWords state.heap (executeOps (callInput q full command) (ops.take clock) state).heap)
    (access : ∀ clock (hc : clock < ops.length), packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) (ops.take clock) state) ops[clock]) :
    ControlPost full configuration capWords command ops whole start heapWords state := by
  let rom := callInput q full command
  have run := straight_segment rom whole ops start block.1 block.2 straight hwords hpcfit state hp ha
  have prefixes : PrefixOK rom heapWords (fun _ => False) ops state := ⟨access, by intro _ _ _ _ h; exact False.elim h⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, packingDynamicTrace_length_le rom whole ops.length state⟩
  · rw [run, executeOps_pc rom ops state straight, hp, BitVec.ofNat_add_ofNat]
    congr 1
    omega
  · rw [run, executeOps_halted]
    exact ha
  · rw [run]
    exact represented
  · intro clock hc
    rw [fetched_prefix rom whole ops start block.1 block.2 straight hwords hpcfit state hp ha clock hc]
    exact registers clock hc
  · intro clock hc
    rw [fetched_prefix rom whole ops start block.1 block.2 straight hwords hpcfit state hp ha clock hc]
    exact effects clock hc
  · intro clock hc
    exact (straight_prefix_safe rom whole ops heapWords start (fun _ => False) block.1 block.2 straight
      hwords hpcfit state hp ha prefixes clock hc).1

theorem original_targets {q : Nat} (full : List (Finset (Fin q))) (hq : 0 < q) (laminar : LaminarSchedule full) :
    let bits := indexWidth 32 full.length q
    let capWords := capacityWords 8192 full.length q (treeSize q full)
    Fits bits (5 + packedCapacityWords q capWords bits) ∧ 5 + packedCapacityWords q capWords bits < PSTRCountAllocation.allocation full := by
  dsimp only
  have room := original_rooms full hq laminar
  constructor
  · have h := Rooms.metadata full _ _ room hq 1 (by omega)
    convert h using 1
    omega
  · unfold PSTRCountAllocation.allocation physicalHeaderWords
    omega

theorem static_rooms {q : Nat} (full : List (Finset (Fin q))) (whole : List PackingOp)
    (length : whole.length ≤ 8192) (literal : ∀ value ∈ packingCode whole, value < 65536) :
    WordsFit (indexWidth 32 full.length q) (packingCode whole) ∧ Fits (indexWidth 32 full.length q) (5 * whole.length) := by
  have hpow : 2 ^ 32 ≤ 2 ^ indexWidth 32 full.length q :=
    Nat.pow_le_pow_right (by decide) (PSTROriginalCountRoom.word_lower full.length q)
  have hbound : Fits (indexWidth 32 full.length q) 65536 := by unfold Fits; omega
  exact ⟨fun value hv => (literal value hv).trans hbound, (show 5 * whole.length ≤ 65536 by omega).trans_lt hbound⟩

theorem actual_correct_original {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (whole : List PackingOp) (start : Nat) (state : WordState (indexWidth 32 full.length q))
    (hq : 0 < q) (laminar : LaminarSchedule full) (allowed : Allowed full configuration .correct)
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration state.heap)
    (block : PSTROuterCountCode.BlockAt whole start correctProgram)
    (length : whole.length ≤ 8192) (literal : ∀ value ∈ packingCode whole, value < 65536)
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) (5 * start)) (ha : state.halted = false) :
    ControlPost full configuration (capacityWords 8192 full.length q (treeSize q full)) .correct correctProgram whole start
      (PSTRCountAllocation.allocation full) state := by
  have room := original_rooms full hq laminar
  have targets := original_targets full hq laminar
  have code := static_rooms full whole length literal
  let packed := packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)
  have fit4 : Fits (indexWidth 32 full.length q) (4 + packed) :=
    (show 4 + packed ≤ 5 + packed by omega).trans_lt targets.1
  have heap4 : 4 + packed < PSTRCountAllocation.allocation full := by have h := targets.2; omega
  exact actual_controls full configuration _ .correct correctProgram whole start _ state correct_straight block code.1 code.2 hp ha
    (correct_represents full configuration _ state hq room allowed rep)
    (correct_prefix_registers (callInput q full .correct) state)
    (correct_prefix_effects full configuration _ state hq room rep)
    (correct_access (callInput q full .correct) _ _ state rep.2.2.1 fit4 heap4)

theorem actual_fail_original {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (whole : List PackingOp) (start : Nat) (state : WordState (indexWidth 32 full.length q))
    (hq : 0 < q) (laminar : LaminarSchedule full) (allowed : Allowed full configuration .error)
    (choose : (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used).tool = none)
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration state.heap)
    (block : PSTROuterCountCode.BlockAt whole start failProgram)
    (length : whole.length ≤ 8192) (literal : ∀ value ∈ packingCode whole, value < 65536)
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) (5 * start)) (ha : state.halted = false) :
    ControlPost full configuration (capacityWords 8192 full.length q (treeSize q full)) .error failProgram whole start
      (PSTRCountAllocation.allocation full) state := by
  have room := original_rooms full hq laminar
  have targets := original_targets full hq laminar
  have code := static_rooms full whole length literal
  exact actual_controls full configuration _ .error failProgram whole start _ state fail_straight block code.1 code.2 hp ha
    (fail_represents full configuration _ state hq room allowed choose rep)
    (fail_prefix_registers (callInput q full .error) state)
    (fail_prefix_effects full configuration _ state hq room rep)
    (fail_access (callInput q full .error) _ _ state rep.2.2.1 targets.1 targets.2)

theorem charged_cost {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (command : Command) (ops whole : List PackingOp) (start heapWords : Nat) (state : WordState bits)
    (post : ControlPost full configuration capWords command ops whole start heapWords state) :
    1 + (packingCode whole).length + 8 + (packingDynamicTrace (callInput q full command) whole ops.length state).length ≤
      5 * whole.length + 14 + 12 * ops.length := by
  have h := post.trace
  rw [packingCode_length]
  omega

end PaperProofs.Structure.LaminarTree.PSTRReplyControls
