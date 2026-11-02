module

public import Structure.PSTR_HD_ControlActual_149
public import Structure.PSTR_QueryReturn_111

/-! Actual update followed by its genuine three-instruction containing-code
return. Only the final reply registers are promised: selected-error102
temporarily spills them. No standalone HALT or reset is used. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRLiveControllerUpdate
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine
open PSTRWordSegments PSTRCountKernel PSTRReplySpill PSTRCountControl

structure UpdateCore {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (command : Command) (whole : List PackingOp) (start count heapWords : Nat)
    (state : WordState bits) : Prop where
  pc : (packingRun (callInput q full command) whole count state).pc = BitVec.ofNat bits (5 * (start + count))
  active : (packingRun (callInput q full command) whole count state).halted = false
  represented : HeapRepresents q full capWords (nextConfiguration q full configuration command)
    (packingRun (callInput q full command) whole count state).heap
  registers : ReplyRegisters state (packingRun (callInput q full command) whole count state)
  capacity : ∀ clock ≤ count, CapacityPrefixBounded q capWords
    (logicalHeap q capWords (packingRun (callInput q full command) whole clock state).heap)
  table : ∀ clock ≤ count, ∀ address < tableWords full.length q (treeSize q full),
    logicalHeap q capWords (packingRun (callInput q full command) whole clock state).heap address =
      logicalHeap q capWords state.heap address
  safe : ∀ clock < count, AtSafe (callInput q full command) whole heapWords
    (packingRun (callInput q full command) whole clock state)

structure UpdatePost {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (command : Command) (whole : List PackingOp) (count target heapWords : Nat)
    (state : WordState bits) : Prop where
  pc : (packingRun (callInput q full command) whole (count + 3) state).pc = BitVec.ofNat bits (5 * target)
  active : (packingRun (callInput q full command) whole (count + 3) state).halted = false
  represented : HeapRepresents q full capWords (nextConfiguration q full configuration command)
    (packingRun (callInput q full command) whole (count + 3) state).heap
  registers : ReplyRegisters state (packingRun (callInput q full command) whole (count + 3) state)
  capacity : ∀ clock ≤ count + 3, CapacityPrefixBounded q capWords
    (logicalHeap q capWords (packingRun (callInput q full command) whole clock state).heap)
  table : ∀ clock ≤ count + 3, ∀ address < tableWords full.length q (treeSize q full),
    logicalHeap q capWords (packingRun (callInput q full command) whole clock state).heap address =
      logicalHeap q capWords state.heap address
  safe : ∀ clock < count + 3, AtSafe (callInput q full command) whole heapWords
    (packingRun (callInput q full command) whole clock state)
  trace : (packingDynamicTrace (callInput q full command) whole (count + 3) state).length ≤ 12 * (count + 3)

theorem UpdatePost.reply {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (command : Command) (whole : List PackingOp) (count target heapWords : Nat)
    (state : WordState bits) (post : UpdatePost full configuration capWords command whole count target heapWords state)
    (answer : IndexedQuery.Reply q) (before : ReplyCorrect q answer (replyState q capWords state)) :
    ReplyCorrect q answer (replyState q capWords (packingRun (callInput q full command) whole (count + 3) state)) :=
  PSTRRepairHeap.replyCorrect_of_registers capWords state _ post.registers answer before

theorem actual_return_after_update {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (command : Command) (whole : List PackingOp) (start count target heapWords : Nat)
    (state : WordState bits) (head : UpdateCore full configuration capWords command whole start count heapWords state)
    (back : PSTROuterCountCode.BlockAt whole (start + count) (backBlock target))
    (hw : WordsFit bits (packingCode whole)) (hpc : Fits bits (5 * whole.length)) :
    UpdatePost full configuration capWords command whole count target heapWords state := by
  let rom := callInput q full command
  let middle := packingRun rom whole count state
  have returned := PSTRQueryReturn.actual_return rom whole (start + count) target back hw hpc middle head.pc head.active
  have run : packingRun rom whole (count + 3) state = packingRun rom whole 3 middle := run_add rom whole count 3 state
  have split (clock : Nat) (hc : count ≤ clock) :
      packingRun rom whole clock state = packingRun rom whole (clock - count) middle := by
    rw [← run_add]
    congr 1
    omega
  have returnHeap (clock : Nat) (hc : clock ≤ 3) :
      (packingRun rom whole clock middle).heap = middle.heap :=
    PSTRQueryReturn.prefix_heap rom whole (start + count) target back hw hpc middle head.pc head.active clock hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, packingDynamicTrace_length_le rom whole (count + 3) state⟩
  · rw [run]
    exact returned.1
  · rw [run]
    exact returned.2.1
  · rw [run, returned.2.2.1]
    exact head.represented
  · rw [run]
    exact ⟨returned.2.2.2.1.trans head.registers.1,
      returned.2.2.2.2.1.trans head.registers.2.1,
      returned.2.2.2.2.2.1.trans head.registers.2.2.1,
      returned.2.2.2.2.2.2.trans head.registers.2.2.2⟩
  · intro clock hc
    by_cases early : clock ≤ count
    · exact head.capacity clock early
    · rw [split clock (by omega), returnHeap _ (by omega)]
      exact head.capacity count le_rfl
  · intro clock hc address ha
    by_cases early : clock ≤ count
    · exact head.table clock early address ha
    · rw [split clock (by omega), returnHeap _ (by omega)]
      exact head.table count le_rfl address ha
  · intro clock hc
    by_cases early : clock < count
    · exact head.safe clock early
    · rw [split clock (by omega)]
      exact PSTRQueryReturn.actual_safe rom whole (start + count) target heapWords back hw hpc middle head.pc head.active _ (by omega)

theorem core_of_controls {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (command : Command) (ops whole : List PackingOp) (start heapWords : Nat)
    (state : WordState bits) (head : PSTRReplyControls.ControlPost full configuration capWords command ops whole start heapWords state) :
    UpdateCore full configuration capWords command whole start ops.length heapWords state :=
  ⟨head.pc, head.active, head.represented, head.registers ops.length le_rfl,
    fun clock hc => (head.effects clock hc).capacity,
    fun clock hc => (head.effects clock hc).table, head.safe⟩

theorem core_of_selected {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (whole : List PackingOp) (start heapWords : Nat) (state : WordState bits)
    (head : PSTRSelectedError.SelectedPost full configuration capWords whole start heapWords state) :
    UpdateCore full configuration capWords .error whole start 102 heapWords state :=
  ⟨head.pc, head.active, head.represented, head.registers, head.capacity, head.table, head.safe⟩

theorem actual_correct {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (whole : List PackingOp) (start target : Nat) (state : WordState (indexWidth 32 full.length q))
    (hq : 0 < q) (laminar : LaminarSchedule full) (allowed : Allowed full configuration .correct)
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration state.heap)
    (block : PSTROuterCountCode.BlockAt whole start PSTRReplyControls.correctProgram)
    (back : PSTROuterCountCode.BlockAt whole (start + 8) (backBlock target))
    (length : whole.length ≤ 8192) (literal : ∀ value ∈ packingCode whole, value < 65536)
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) (5 * start)) (ha : state.halted = false) :
    UpdatePost full configuration (capacityWords 8192 full.length q (treeSize q full)) .correct whole 8 target
      (PSTRCountAllocation.allocation full) state := by
  have head := PSTRReplyControls.actual_correct_original full configuration whole start state hq laminar allowed rep block length literal hp ha
  have core := core_of_controls full configuration _ .correct PSTRReplyControls.correctProgram whole start _ state head
  have code := PSTRReplyControls.static_rooms full whole length literal
  exact actual_return_after_update full configuration _ .correct whole start 8 target _ state core back code.1 code.2

theorem actual_fail {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (whole : List PackingOp) (start target : Nat) (state : WordState (indexWidth 32 full.length q))
    (hq : 0 < q) (laminar : LaminarSchedule full) (allowed : Allowed full configuration .error)
    (choose : (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used).tool = none)
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration state.heap)
    (block : PSTROuterCountCode.BlockAt whole start PSTRReplyControls.failProgram)
    (back : PSTROuterCountCode.BlockAt whole (start + 6) (backBlock target))
    (length : whole.length ≤ 8192) (literal : ∀ value ∈ packingCode whole, value < 65536)
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) (5 * start)) (ha : state.halted = false) :
    UpdatePost full configuration (capacityWords 8192 full.length q (treeSize q full)) .error whole 6 target
      (PSTRCountAllocation.allocation full) state := by
  have head := PSTRReplyControls.actual_fail_original full configuration whole start state hq laminar allowed choose rep block length literal hp ha
  have core := core_of_controls full configuration _ .error PSTRReplyControls.failProgram whole start _ state head
  have code := PSTRReplyControls.static_rooms full whole length literal
  exact actual_return_after_update full configuration _ .error whole start 6 target _ state core back code.1 code.2

theorem actual_selected {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (whole : List PackingOp) (start target : Nat) (state : WordState (indexWidth 32 full.length q)) (tool : Fin q)
    (hq : 0 < q) (laminar : LaminarSchedule full) (allowed : Allowed full configuration .error)
    (choose : (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used).tool = some tool)
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration state.heap)
    (reply : ReplyCorrect q (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used)
      (replyState q (capacityWords 8192 full.length q (treeSize q full)) state))
    (savedWidth : state.heap (BitVec.ofNat (indexWidth 32 full.length q)
      (PSTRCountWorkspace.base q full (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q) + 12)) =
        BitVec.ofNat (indexWidth 32 full.length q) (CapacityBits.width q))
    (block : PSTROuterCountCode.BlockAt whole start PSTRSelectedError.program)
    (back : PSTROuterCountCode.BlockAt whole (start + 102) (backBlock target))
    (length : whole.length ≤ 8192) (literal : ∀ value ∈ packingCode whole, value < 65536)
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) (5 * start)) (ha : state.halted = false) :
    UpdatePost full configuration (capacityWords 8192 full.length q (treeSize q full)) .error whole 102 target
      (PSTRCountAllocation.allocation full) state := by
  have head := PSTRSelectedError.actual_selected_original full configuration whole start state tool hq laminar allowed choose rep reply savedWidth block length literal hp ha
  have core := core_of_selected full configuration _ whole start _ state head
  have code := PSTRReplyControls.static_rooms full whole length literal
  exact actual_return_after_update full configuration _ .error whole start 102 target _ state core back code.1 code.2

theorem charged_cost {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (command : Command) (whole : List PackingOp) (count target heapWords : Nat)
    (state : WordState bits) (post : UpdatePost full configuration capWords command whole count target heapWords state) :
    1 + (packingCode whole).length + 8 + (packingDynamicTrace (callInput q full command) whole (count + 3) state).length ≤
      5 * whole.length + 14 + 12 * (count + 3) := by
  have h := post.trace
  rw [packingCode_length]
  omega

end PaperProofs.Structure.LaminarTree.PSTRLiveControllerUpdate
