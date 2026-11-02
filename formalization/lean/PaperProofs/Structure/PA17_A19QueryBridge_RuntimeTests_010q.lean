module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_010p
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Control_015g
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Control_015o

/-! One actual budget body. Its only ghost heap is original logicalHeap q C;
physical frames use physical W/H. BudgetPhases are deterministic actual run
states, never supplied transition, flag, or prefix-safety oracles. -/

@[expose] public section
set_option maxRecDepth 28000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def BudgetFrame {bits q : Nat} (full : List (Finset (Fin q))) (capWords budget : Nat)
    (old fresh : BitVec bits → BitVec bits) : Prop :=
  let header := PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)
  ∀ address, (∀ offset, 8 ≤ offset → offset ≤ 14 → address ≠ BitVec.ofNat bits (header + offset)) →
    address ≠ BitVec.ofNat bits (header + 16 + budget) →
    address ≠ BitVec.ofNat bits (header + 16 + (q + 2) + budget) → fresh address = old address

theorem BudgetFrame.refl {bits q : Nat} (full : List (Finset (Fin q))) (capWords budget : Nat)
    (heap : BitVec bits → BitVec bits) : BudgetFrame full capWords budget heap heap := fun _ _ _ _ => rfl

theorem BudgetFrame.trans {bits q : Nat} {full : List (Finset (Fin q))} {capWords budget : Nat}
    {old middle fresh : BitVec bits → BitVec bits}
    (hm : BudgetFrame full capWords budget old middle) (hf : BudgetFrame full capWords budget middle fresh) :
    BudgetFrame full capWords budget old fresh :=
  fun address hs hg hb => (hf address hs hg hb).trans (hm address hs hg hb)

theorem BudgetFrame.slot {bits q : Nat} (full : List (Finset (Fin q))) (capWords budget offset : Nat)
    (heap : BitVec bits → BitVec bits) (value : BitVec bits) (h8 : 8 ≤ offset) (h14 : offset ≤ 14) :
    BudgetFrame full capWords budget heap (Function.update heap
      (BitVec.ofNat bits (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
        (treeSize q full) + offset)) value) := by
  intro address hs _ _
  rw [Function.update_of_ne (hs offset h8 h14)]

theorem BudgetFrame.good {bits q : Nat} (full : List (Finset (Fin q))) (capWords budget : Nat)
    (heap : BitVec bits → BitVec bits) (value : BitVec bits) :
    BudgetFrame full capWords budget heap (Function.update heap
      (BitVec.ofNat bits (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
        (treeSize q full) + 16 + budget)) value) := by
  intro address _ hg _
  rw [Function.update_of_ne hg]

theorem BudgetFrame.bad {bits q : Nat} (full : List (Finset (Fin q))) (capWords budget : Nat)
    (heap : BitVec bits → BitVec bits) (value : BitVec bits) :
    BudgetFrame full capWords budget heap (Function.update heap
      (BitVec.ofNat bits (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
        (treeSize q full) + 16 + (q + 2) + budget)) value) := by
  intro address _ _ hb
  rw [Function.update_of_ne hb]

theorem BudgetFrame.leading {bits q : Nat} {full : List (Finset (Fin q))} {capWords budget : Nat}
    {old fresh : BitVec bits → BitVec bits} (hframe : BudgetFrame full capWords budget old fresh)
    (hend : Fits bits (PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q))
    (hb : budget < q + 2) :
    ∀ physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 8,
      fresh (BitVec.ofNat bits physical) = old (BitVec.ofNat bits physical) := by
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace (treeSize q full)
  let endpoint := PSTRQueryLayout.endpoint workspace (treeSize q full) q
  intro physical hp
  have h8 : header + 8 < endpoint := scratch_lt_endpoint workspace (treeSize q full) q 8 (by decide)
  have hpf : Fits bits physical := (hp.trans h8).trans hend
  have hne (target : Nat) (ht : target < endpoint) (hpt : physical < target) :
      BitVec.ofNat bits physical ≠ BitVec.ofNat bits target := by
    intro heq
    have hn := (ofNat_injective_of_fit physical target hpf (ht.trans hend)).mp heq
    omega
  apply hframe
  · intro offset ho hlo
    exact hne _ (scratch_lt_endpoint workspace (treeSize q full) q offset (by omega)) (by omega)
  · exact hne _ (good_lt_endpoint workspace (treeSize q full) q budget hb) (by omega)
  · exact hne _ (bad_lt_endpoint workspace (treeSize q full) q budget hb) (by omega)

theorem BudgetFrame.high {bits q : Nat} {full : List (Finset (Fin q))} {capWords budget : Nat}
    {old fresh : BitVec bits → BitVec bits} (hframe : BudgetFrame full capWords budget old fresh)
    (hend : Fits bits (PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q))
    (hb : budget < q + 2) :
    HighFrame (PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q) old fresh := by
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  intro physical hp hge
  apply hframe
  · intro offset _ hlo
    exact high_address_ne _ _ physical hend (scratch_lt_endpoint workspace (treeSize q full) q offset (by omega)) hp hge
  · exact high_address_ne _ _ physical hend (good_lt_endpoint workspace (treeSize q full) q budget hb) hp hge
  · exact high_address_ne _ _ physical hend (bad_lt_endpoint workspace (treeSize q full) q budget hb) hp hge

theorem BudgetFrame.logical {bits q : Nat} {full : List (Finset (Fin q))} {capWords budget : Nat}
    {old fresh : BitVec bits → BitVec bits} (hframe : BudgetFrame full capWords budget old fresh)
    (hb : 0 < bits) (hq : 0 < q) (hs : Fits bits (4 + capWords * CapacityBits.width q))
    (hend : Fits bits (PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q))
    (hbudget : budget < q + 2) :
    ∀ logical < PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + 8,
      logicalHeap q capWords fresh logical = logicalHeap q capWords old logical := by
  have hh : PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 16 ≤
      PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q := by
    unfold PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags
    omega
  exact logical_leading_frame full capWords (treeSize q full) old fresh hb hq hs (hh.trans_lt hend)
    (hframe.leading hend hbudget)

def budgetBlockClock (size : Nat) : Nat := 86 + nodeClock size + 26 + ancestorClock size + 16

theorem budgetBlockClock_eq (size : Nat) : budgetBlockClock size = 138 + 215 * size := by
  unfold budgetBlockClock nodeClock ancestorClock
  omega

structure BudgetPhases (bits : Nat) where
  entry : WordState bits
  nodes : WordState bits
  initialized : WordState bits
  ancestors : WordState bits
  finished : WordState bits

def budgetPhases {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (size : Nat)
    (state : WordState bits) : BudgetPhases bits :=
  let entry := packingRun rom containing 86 state
  let nodes := packingRun rom containing (nodeClock size) entry
  let initialized := packingRun rom containing 26 nodes
  let ancestors := packingRun rom containing (ancestorClock size) initialized
  let finished := packingRun rom containing 16 ancestors
  ⟨entry, nodes, initialized, ancestors, finished⟩

theorem budgetPhases_finished {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp)
    (size : Nat) (state : WordState bits) :
    (budgetPhases rom containing size state).finished =
      packingRun rom containing (budgetBlockClock size) state := by
  unfold budgetPhases budgetBlockClock
  rw [run_add rom containing (86 + nodeClock size + 26 + ancestorClock size) 16 state,
    run_add rom containing (86 + nodeClock size + 26) (ancestorClock size) state,
    run_add rom containing (86 + nodeClock size) 26 state,
    run_add rom containing 86 (nodeClock size) state]

structure BudgetCoreReady {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords pc : Nat) (state : WordState bits) : Prop where
  rep : HeapRepresents q full capWords configuration state.heap
  width : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
    BitVec.ofNat bits (CapacityBits.width q)
  mask : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 13)) =
    lowMask bits (CapacityBits.width q)
  header : state.register .address = BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))
  pc_eq : state.pc = BitVec.ofNat bits (5 * pc)
  active : state.halted = false

theorem BudgetCoreReady.after_frame {bits q : Nat} {full : List (Finset (Fin q))}
    {configuration : Configuration q} {capWords budget oldPC newPC : Nat} {before after : WordState bits}
    (ready : BudgetCoreReady full configuration capWords oldPC before)
    (frame : BudgetFrame full capWords budget before.heap after.heap)
    (hb : 0 < bits) (hq : 0 < q)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q))
    (hend : Fits bits (PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q))
    (hbudget : budget < q + 2)
    (hh : after.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)))
    (hp : after.pc = BitVec.ofNat bits (5 * newPC)) (ha : after.halted = false) :
    BudgetCoreReady full configuration capWords newPC after := by
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace (treeSize q full)
  have hroom : Fits bits (header + 16) := (show header + 16 ≤ PSTRQueryLayout.endpoint workspace (treeSize q full) q by
    unfold PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags
    omega).trans_lt hend
  have hcache (offset : Nat) (ho : offset ≤ 13) : workspace + offset < header + 8 := by
    unfold header PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
    omega
  have hleading := frame.leading hend hbudget
  exact ⟨represents_of_leading_frame full configuration capWords before.heap after.heap hb hq
      ready.rep bitmap hs hroom hleading,
    (hleading _ (hcache 12 (by decide))).trans ready.width,
    (hleading _ (hcache 13 (by decide))).trans ready.mask, hh, hp, ha⟩

theorem word_tag_bit {bits : Nat} (tag : Nat) :
    BitVec.ofNat bits (if tag = 0 then 0 else 1) = BitVec.ofNat bits (bit (decide (tag ≠ 0))) := by
  by_cases hz : tag = 0 <;> simp [hz, bit]

theorem word_gate_bit {bits : Nat} (flag : Bool) (encoded : Nat) :
    (if encoded = 0 then BitVec.ofNat bits 0 else BitVec.ofNat bits (bit flag)) =
      BitVec.ofNat bits (bit (flag && decide (encoded ≠ 0))) := by
  by_cases hz : encoded = 0 <;> simp [hz, bit]

structure BudgetBlockPost {bits q : Nat} (full : List (Finset (Fin q)))
    (capWords rowBase budget encoded origin : Nat) (before after : WordState bits) : Prop where
  active : after.halted = false
  pc : after.pc = BitVec.ofNat bits (5 * (origin + 7))
  header : after.register .address = BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))
  counter : after.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 8)) = BitVec.ofNat bits budget
  good : after.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 16 + budget)) =
    BitVec.ofNat bits (bit (rawGood (logicalHeap q capWords before.heap)
      (rowBase + budget * (treeSize q full + 1))
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords)) (treeSize q full)))
  bad : after.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 16 + (q + 2) + budget)) =
    BitVec.ofNat bits (bit (rawBad (logicalHeap q capWords before.heap)
      (rowBase + budget * (treeSize q full + 1))
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords))
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full)) (treeSize q full) encoded))
  «outside» : BudgetFrame full capWords budget before.heap after.heap
  leading : ∀ physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 8, after.heap (BitVec.ofNat bits physical) = before.heap (BitVec.ofNat bits physical)
  high : HighFrame (PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q)
    before.heap after.heap

structure BudgetPhasesReady {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords rowBase budget encoded origin : Nat) (before : WordState bits) (phases : BudgetPhases bits) : Prop where
  entry_core : BudgetCoreReady full configuration capWords (origin + 98) phases.entry
  entry_frame : BudgetFrame full capWords budget before.heap phases.entry.heap
  entry_budget : phases.entry.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 8)) = BitVec.ofNat bits budget
  entry_counter : phases.entry.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 9)) = BitVec.ofNat bits (treeSize q full)
  entry_row : phases.entry.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 13)) =
    BitVec.ofNat bits (rowBase + budget * (treeSize q full + 1))
  node_post : NodeLoopPost full capWords (rowBase + budget * (treeSize q full + 1))
    (treeSize q full) origin phases.entry phases.nodes
  nodes_core : BudgetCoreReady full configuration capWords (origin + 196) phases.nodes
  nodes_frame : BudgetFrame full capWords budget before.heap phases.nodes.heap
  nodes_budget : phases.nodes.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 8)) = BitVec.ofNat bits budget
  initialized_core : BudgetCoreReady full configuration capWords (origin + 222) phases.initialized
  initialized_frame : BudgetFrame full capWords budget before.heap phases.initialized.heap
  initialized_counter : phases.initialized.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 12)) = BitVec.ofNat bits (treeSize q full)
  initialized_node : phases.initialized.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 11)) = BitVec.ofNat bits encoded
  initialized_row : phases.initialized.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 13)) =
    BitVec.ofNat bits (rowBase + budget * (treeSize q full + 1))
  initialized_budget : phases.initialized.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 8)) = BitVec.ofNat bits budget
  initialized_parents : ∀ e ≤ treeSize q full, logicalHeap q capWords phases.initialized.heap
    (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + e) ≤ treeSize q full
  ancestor_post : AncestorLoopPost full capWords (rowBase + budget * (treeSize q full + 1))
    (treeSize q full) encoded origin phases.initialized phases.ancestors
  ancestors_core : BudgetCoreReady full configuration capWords (origin + 339) phases.ancestors
  ancestors_frame : BudgetFrame full capWords budget before.heap phases.ancestors.heap
  ancestors_budget : phases.ancestors.heap (BitVec.ofNat bits
    (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 8)) = BitVec.ofNat bits budget
  finished_core : BudgetCoreReady full configuration capWords (origin + 7) phases.finished
  post : BudgetBlockPost full capWords rowBase budget encoded origin before phases.finished

theorem actual_budget_phases {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords rowBase budget encoded : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (hendpoint_alloc : PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) q ≤ heapWords)
    (hwidth : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 13)) =
      lowMask bits (CapacityBits.width q))
    (hh : state.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)))
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 12))) (ha : state.halted = false)
    (htotal : state.register .total = BitVec.ofNat bits (budget + 1))
    (hrowPointer : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))) = BitVec.ofNat bits rowBase)
    (hnodePointer : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 1)) = BitVec.ofNat bits encoded)
    (hbudget : budget < q + 2) (hencoded : encoded ≤ treeSize q full)
    (hrowExtent : rowBase + (q + 2) * (treeSize q full + 1) ≤ capWords)
    (hparents : ∀ e ≤ treeSize q full, logicalHeap q capWords state.heap
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + e) ≤ treeSize q full) :
    BudgetPhasesReady full configuration capWords rowBase budget encoded origin state
      (budgetPhases (callInput q full command) containing (treeSize q full) state) := by
  let rom := callInput q full command
  let size := treeSize q full
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace size
  let endpoint := PSTRQueryLayout.endpoint workspace size q
  let entryBase := rowBase + budget * (size + 1)
  let logicalCounts := PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords)
  let logicalParents := PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) size
  let phases := budgetPhases rom containing size state
  let good := rawGood (logicalHeap q capWords state.heap) entryBase logicalCounts size
  let bad := rawBad (logicalHeap q capWords state.heap) entryBase logicalCounts logicalParents size encoded
  let tagFlag := BitVec.ofNat bits (if logicalHeap q capWords state.heap entryBase = 0 then 0 else 1)
  have hend : Fits bits endpoint := hendpoint_alloc.trans_lt hf
  have hgap : header + 16 < endpoint := by
    unfold endpoint PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags
    omega
  have hroom : Fits bits (header + 16) := hgap.trans hend
  have halloc : header + 16 < heapWords := hgap.trans_le hendpoint_alloc
  have hrowRoom : entryBase + (size + 1) ≤ capWords := by
    have hm := Nat.mul_le_mul_right (size + 1) (show budget + 1 ≤ q + 2 by omega)
    unfold entryBase
    nlinarith
  have hscalar : entryBase < capWords := by omega
  have hheader : Fits bits header := (Nat.le_add_right header 16).trans_lt hroom
  have hsize : Fits bits size := (show size ≤ header by
    unfold header PSTRQueryLayout.header; omega).trans_lt hheader
  have henc : Fits bits encoded := (show encoded ≤ header by
    unfold header PSTRQueryLayout.header; omega).trans_lt hheader
  have hsizeWord : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size := by
    apply BitVec.eq_of_toNat_eq
    rw [rep.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsize]
  have hslotNe (left right : Nat) (hl : left ≤ 16) (hr : right ≤ 16) (hne : left ≠ right) :
      BitVec.ofNat bits (header + left) ≠ BitVec.ofNat bits (header + right) := by
    intro heq
    exact hne ((slots_eq_iff header left right hroom hl hr).mp heq)
  have hscratch (offset : Nat) (ho : offset < 16) : header + offset < endpoint :=
    scratch_lt_endpoint workspace size q offset ho
  have hgoodBound : header + 16 + budget < endpoint := good_lt_endpoint workspace size q budget hbudget
  have hbadBound : header + 16 + (q + 2) + budget < endpoint := bad_lt_endpoint workspace size q budget hbudget
  have hpointNe (left right : Nat) (hl : left < endpoint) (hr : right < endpoint) (hne : left ≠ right) :
      BitVec.ofNat bits left ≠ BitVec.ofNat bits right := by
    intro heq
    exact hne ((ofNat_injective_of_fit left right (hl.trans hend) (hr.trans hend)).mp heq)
  have initialCore : BudgetCoreReady full configuration capWords (origin + 12) state :=
    ⟨rep, hwidth, hmask, hh, hp, ha⟩
  have hi := actual_budgetInit_end em rom state hp ha
  have hm := budgetInit_result full command configuration capWords heapWords rowBase budget state
    hb hq hw rep bitmap hs hf halloc hwidth hmask hh htotal hrowPointer hscalar
  have hEntryEq : phases.entry = executeOps rom budgetInit state := hi.1
  have hEntryHeap : phases.entry.heap = Function.update
      (Function.update
        (Function.update
          (Function.update state.heap (BitVec.ofNat bits (header + 8)) (BitVec.ofNat bits budget))
          (BitVec.ofNat bits (header + 13)) (BitVec.ofNat bits entryBase))
        (BitVec.ofNat bits (header + 10)) tagFlag)
      (BitVec.ofNat bits (header + 9)) (BitVec.ofNat bits size) := by
    rw [hEntryEq]
    exact hm.1
  have hEntryFrame : BudgetFrame full capWords budget state.heap phases.entry.heap := by
    rw [hEntryHeap]
    exact (((BudgetFrame.slot full capWords budget 8 state.heap _ (by decide) (by decide)).trans
      (BudgetFrame.slot full capWords budget 13 _ _ (by decide) (by decide))).trans
      (BudgetFrame.slot full capWords budget 10 _ _ (by decide) (by decide))).trans
      (BudgetFrame.slot full capWords budget 9 _ _ (by decide) (by decide))
  have hEntryHeader : phases.entry.register .address = BitVec.ofNat bits header := by
    rw [hEntryEq]
    exact hm.2
  have entryCore := initialCore.after_frame hEntryFrame (by omega) hq bitmap hs hend hbudget
    hEntryHeader hi.2.1 hi.2.2
  have hEntryBudget : phases.entry.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget := by
    rw [hEntryHeap, Function.update_of_ne (hslotNe 8 9 (by decide) (by decide) (by decide)),
      Function.update_of_ne (hslotNe 8 10 (by decide) (by decide) (by decide)),
      Function.update_of_ne (hslotNe 8 13 (by decide) (by decide) (by decide)), Function.update_self]
  have hEntryCounter : phases.entry.heap (BitVec.ofNat bits (header + 9)) = BitVec.ofNat bits size := by
    rw [hEntryHeap, Function.update_self]
  have hEntryRow : phases.entry.heap (BitVec.ofNat bits (header + 13)) = BitVec.ofNat bits entryBase := by
    rw [hEntryHeap, Function.update_of_ne (hslotNe 13 9 (by decide) (by decide) (by decide)),
      Function.update_of_ne (hslotNe 13 10 (by decide) (by decide) (by decide)), Function.update_self]
  have hTag := logical_scalar_of_leading_frame full capWords entryBase state.heap phases.entry.heap
    (by omega) hq hs hroom (hEntryFrame.leading hend hbudget) hscalar
  have hEntryFlagOld : phases.entry.heap (BitVec.ofNat bits (header + 10)) =
      BitVec.ofNat bits (bit (decide (logicalHeap q capWords state.heap entryBase ≠ 0))) := by
    rw [hEntryHeap, Function.update_of_ne (hslotNe 10 9 (by decide) (by decide) (by decide)), Function.update_self]
    exact word_tag_bit _
  have hEntryFlag : phases.entry.heap (BitVec.ofNat bits (header + 10)) =
      BitVec.ofNat bits (bit (decide (logicalHeap q capWords phases.entry.heap entryBase ≠ 0))) := by
    rw [hTag]
    exact hEntryFlagOld
  have hn := actual_nodeLoop em full command configuration capWords heapWords entryBase size phases.entry
    hb hq hw entryCore.rep bitmap hs hf halloc hend entryCore.width entryCore.mask entryCore.header
    entryCore.pc_eq entryCore.active hEntryCounter hEntryRow (by rfl) hrowRoom
  have hNodeRelative : BudgetFrame full capWords budget phases.entry.heap phases.nodes.heap := by
    intro address hp' _ _
    exact hn.«outside» address (hp' 9 (by decide) (by decide)) (hp' 10 (by decide) (by decide))
  have hNodeFrame := hEntryFrame.trans hNodeRelative
  have nodesCore := initialCore.after_frame hNodeFrame (by omega) hq bitmap hs hend hbudget hn.header hn.pc hn.active
  have hNodeBudget : phases.nodes.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget :=
    hn.budget.trans hEntryBudget
  have hNodeRow : phases.nodes.heap (BitVec.ofNat bits (header + 13)) = BitVec.ofNat bits entryBase := hn.entry.trans hEntryRow
  have hNodeMask : phases.nodes.heap (BitVec.ofNat bits (header + 10)) =
      wordMask (acceptPrefix (logicalHeap q capWords phases.entry.heap) entryBase logicalCounts size)
        (phases.entry.heap (BitVec.ofNat bits (header + 10))) := hn.flag
  have hNodeGoodLocal : phases.nodes.heap (BitVec.ofNat bits (header + 10)) =
      BitVec.ofNat bits (bit (rawGood (logicalHeap q capWords phases.entry.heap) entryBase logicalCounts size)) := by
    rw [hNodeMask, hEntryFlag, wordMask_bit]
    rfl
  have hNodeGood : phases.nodes.heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits (bit good) := by
    rw [hNodeGoodLocal, rawGood_of_leading_frame full capWords entryBase state.heap phases.entry.heap
      (by omega) hq hs hroom (hEntryFrame.leading hend hbudget) hrowRoom]
  have hNodeStage : phases.nodes.heap (BitVec.ofNat bits (header + 1)) = BitVec.ofNat bits encoded :=
    ((hNodeFrame.leading hend hbudget) _ (by change header + 1 < header + 8; omega)).trans hnodePointer
  have hNodeSize : phases.nodes.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size :=
    ((hNodeFrame.leading hend hbudget) _ (by omega)).trans hsizeWord
  have hac := actual_acceptFinish_result em rom header budget phases.nodes hroom (hgoodBound.trans hend)
    nodesCore.header hNodeBudget nodesCore.pc_eq nodesCore.active
  have hAcceptHeap : phases.initialized.heap = Function.update
      (Function.update
        (Function.update
          (Function.update phases.nodes.heap (BitVec.ofNat bits (header + 16 + budget))
            (phases.nodes.heap (BitVec.ofNat bits (header + 10))))
          (BitVec.ofNat bits (header + 11)) (phases.nodes.heap (BitVec.ofNat bits (header + 1))))
        (BitVec.ofNat bits (header + 14))
        (if (phases.nodes.heap (BitVec.ofNat bits (header + 1))).toNat = 0 then BitVec.ofNat bits 0
          else phases.nodes.heap (BitVec.ofNat bits (header + 10))))
      (BitVec.ofNat bits (header + 12)) (phases.nodes.heap (BitVec.ofNat bits 0)) := hac.1
  have hAcceptRelative : BudgetFrame full capWords budget phases.nodes.heap phases.initialized.heap := by
    rw [hAcceptHeap]
    exact (((BudgetFrame.good full capWords budget phases.nodes.heap _).trans
      (BudgetFrame.slot full capWords budget 11 _ _ (by decide) (by decide))).trans
      (BudgetFrame.slot full capWords budget 14 _ _ (by decide) (by decide))).trans
      (BudgetFrame.slot full capWords budget 12 _ _ (by decide) (by decide))
  have hAcceptFrame := hNodeFrame.trans hAcceptRelative
  have initializedCore := initialCore.after_frame hAcceptFrame (by omega) hq bitmap hs hend hbudget
    hac.2.1 hac.2.2.1 hac.2.2.2
  have hInitializedParents : ∀ e ≤ size, logicalHeap q capWords phases.initialized.heap (logicalParents + e) ≤ size := by
    intro e he'
    rw [hAcceptFrame.logical (by omega) hq hs hend hbudget _ (by
      unfold logicalParents PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
      omega)]
    exact hparents e he'
  have hslots := actual_acceptFinish_slots em rom header budget encoded size entryBase good phases.nodes
    hroom (hgoodBound.trans hend) henc nodesCore.header nodesCore.pc_eq nodesCore.active
    hNodeBudget hNodeStage hNodeGood hNodeRow hNodeSize
  have hGoodAeq : rawGood (logicalHeap q capWords phases.initialized.heap) entryBase logicalCounts size = good :=
    rawGood_of_leading_frame full capWords entryBase state.heap phases.initialized.heap
      (by omega) hq hs hroom (hAcceptFrame.leading hend hbudget) hrowRoom
  have hInitializedFlag : phases.initialized.heap (BitVec.ofNat bits (header + 14)) =
      BitVec.ofNat bits (bit (rawGood (logicalHeap q capWords phases.initialized.heap) entryBase logicalCounts size &&
        decide (encoded ≠ 0))) := by
    rw [hGoodAeq]
    exact hslots.flag
  have han := actual_ancestorLoop em full command configuration capWords heapWords entryBase size encoded phases.initialized
    hb hq hw initializedCore.rep bitmap hs hf halloc hend initializedCore.width initializedCore.mask
    initializedCore.header initializedCore.pc_eq initializedCore.active hslots.fuel hslots.row hslots.node
    (by rfl) hencoded hrowRoom hInitializedParents
  have hAncestorOutside : ∀ address,
      address ≠ BitVec.ofNat bits (header + 11) → address ≠ BitVec.ofNat bits (header + 12) →
      address ≠ BitVec.ofNat bits (header + 14) → phases.ancestors.heap address = phases.initialized.heap address := han.«outside»
  have hAncestorMask : phases.ancestors.heap (BitVec.ofNat bits (header + 14)) =
      wordMask (chainPrefix (logicalHeap q capWords phases.initialized.heap) entryBase logicalCounts logicalParents size encoded)
        (phases.initialized.heap (BitVec.ofNat bits (header + 14))) := han.flag
  have hAncestorRelative : BudgetFrame full capWords budget phases.initialized.heap phases.ancestors.heap := by
    intro address hprotected _ _
    exact hAncestorOutside address (hprotected 11 (by decide) (by decide))
      (hprotected 12 (by decide) (by decide)) (hprotected 14 (by decide) (by decide))
  have hAncestorFrame := hAcceptFrame.trans hAncestorRelative
  have ancestorsCore := initialCore.after_frame hAncestorFrame (by omega) hq bitmap hs hend hbudget
    han.header han.pc han.active
  have hAncestorBudget : phases.ancestors.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget :=
    (hAncestorOutside _ (hslotNe 8 11 (by decide) (by decide) (by decide))
      (hslotNe 8 12 (by decide) (by decide) (by decide))
      (hslotNe 8 14 (by decide) (by decide) (by decide))).trans hslots.budget
  have hAncestorGood : phases.ancestors.heap (BitVec.ofNat bits (header + 16 + budget)) = BitVec.ofNat bits (bit good) :=
    (hAncestorOutside _ (hpointNe _ _ hgoodBound (hscratch 11 (by decide)) (by omega))
      (hpointNe _ _ hgoodBound (hscratch 12 (by decide)) (by omega))
      (hpointNe _ _ hgoodBound (hscratch 14 (by decide)) (by omega))).trans hslots.good
  have hAncestorBadLocal : phases.ancestors.heap (BitVec.ofNat bits (header + 14)) =
      BitVec.ofNat bits (bit (rawBad (logicalHeap q capWords phases.initialized.heap) entryBase logicalCounts logicalParents size encoded)) := by
    rw [hAncestorMask, hInitializedFlag, wordMask_bit]
    rfl
  have hAncestorBad : phases.ancestors.heap (BitVec.ofNat bits (header + 14)) = BitVec.ofNat bits (bit bad) := by
    rw [hAncestorBadLocal, rawBad_of_leading_frame full capWords entryBase encoded state.heap phases.initialized.heap
      (by omega) hq hs hroom (hAcceptFrame.leading hend hbudget) hrowRoom hencoded hparents]
  have hqraw : (rom.words .input).getD 1 0 = q := by rfl
  have h1 : Fits bits 1 := (show 1 ≤ header + 16 by omega).trans_lt hroom
  have hfooter := actual_budgetFooter_result em rom header q budget phases.ancestors h1 hqraw ancestorsCore.header
    hAncestorBudget ancestorsCore.pc_eq ancestorsCore.active
  have hFooterHeap : phases.finished.heap = Function.update phases.ancestors.heap
      (BitVec.ofNat bits (header + 16 + (q + 2) + budget))
      (phases.ancestors.heap (BitVec.ofNat bits (header + 14))) := hfooter.1
  have hFooterRelative : BudgetFrame full capWords budget phases.ancestors.heap phases.finished.heap := by
    rw [hFooterHeap]
    exact BudgetFrame.bad full capWords budget phases.ancestors.heap _
  have hFinishedFrame := hAncestorFrame.trans hFooterRelative
  have finishedCore := initialCore.after_frame hFinishedFrame (by omega) hq bitmap hs hend hbudget
    hfooter.2.1 hfooter.2.2.1 hfooter.2.2.2
  have hFinishedBudget : phases.finished.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget := by
    rw [hFooterHeap, Function.update_of_ne (hpointNe _ _ (hscratch 8 (by decide)) hbadBound (by omega))]
    exact hAncestorBudget
  have hFinishedGood : phases.finished.heap (BitVec.ofNat bits (header + 16 + budget)) = BitVec.ofNat bits (bit good) := by
    rw [hFooterHeap, Function.update_of_ne (hpointNe _ _ hgoodBound hbadBound (by omega))]
    exact hAncestorGood
  have hFinishedBad : phases.finished.heap (BitVec.ofNat bits (header + 16 + (q + 2) + budget)) = BitVec.ofNat bits (bit bad) := by
    rw [hFooterHeap, Function.update_self]
    exact hAncestorBad
  have post : BudgetBlockPost full capWords rowBase budget encoded origin state phases.finished :=
    ⟨finishedCore.active, finishedCore.pc_eq, finishedCore.header, hFinishedBudget, hFinishedGood,
      hFinishedBad, hFinishedFrame, hFinishedFrame.leading hend hbudget, hFinishedFrame.high hend hbudget⟩
  exact {
    entry_core := entryCore
    entry_frame := hEntryFrame
    entry_budget := hEntryBudget
    entry_counter := hEntryCounter
    entry_row := hEntryRow
    node_post := hn
    nodes_core := nodesCore
    nodes_frame := hNodeFrame
    nodes_budget := hNodeBudget
    initialized_core := initializedCore
    initialized_frame := hAcceptFrame
    initialized_counter := hslots.fuel
    initialized_node := hslots.node
    initialized_row := hslots.row
    initialized_budget := hslots.budget
    initialized_parents := hInitializedParents
    ancestor_post := han
    ancestors_core := ancestorsCore
    ancestors_frame := hAncestorFrame
    ancestors_budget := hAncestorBudget
    finished_core := finishedCore
    post := post }

theorem actual_budget_block {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords rowBase budget encoded : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (hendpoint_alloc : PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) q ≤ heapWords)
    (hwidth : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 13)) =
      lowMask bits (CapacityBits.width q))
    (hh : state.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)))
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 12))) (ha : state.halted = false)
    (htotal : state.register .total = BitVec.ofNat bits (budget + 1))
    (hrowPointer : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))) = BitVec.ofNat bits rowBase)
    (hnodePointer : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 1)) = BitVec.ofNat bits encoded)
    (hbudget : budget < q + 2) (hencoded : encoded ≤ treeSize q full)
    (hrowExtent : rowBase + (q + 2) * (treeSize q full + 1) ≤ capWords)
    (hparents : ∀ e ≤ treeSize q full, logicalHeap q capWords state.heap
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) (treeSize q full) + e) ≤ treeSize q full) :
    BudgetBlockPost full capWords rowBase budget encoded origin state
      (packingRun (callInput q full command) containing (budgetBlockClock (treeSize q full)) state) := by
  have ready := actual_budget_phases em full command configuration capWords heapWords rowBase budget encoded state
    hb hq hw rep bitmap hs hf hendpoint_alloc hwidth hmask hh hp ha htotal hrowPointer hnodePointer
    hbudget hencoded hrowExtent hparents
  have post := ready.post
  rw [budgetPhases_finished] at post
  exact post

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
