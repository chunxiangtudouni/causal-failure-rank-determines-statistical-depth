module

public import PaperProofs.Structure.PSTR_HD_CountInvariant_035

/-! Actual fetched loop control for one node. The test examines the real
stored D/k words; one real114step iteration updates the physical accumulator
and counter and jumps back to the encoded loop address while still active. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine PSTRWordSegments PSTRCountWorkspace PSTRStaticLayout

structure ReadyLoop {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords countsBase offset origin : Nat) (node : (prepareNormalization q full).indexed.NodeId)
    (initial : WordState bits) (count : Nat) (state : WordState bits) : Prop where
  data : LoopData full configuration capWords countsBase offset node initial count state
  pc : state.pc = BitVec.ofNat bits (5 * (origin + 121))

theorem same_heap_data {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords countsBase offset count : Nat) (node : (prepareNormalization q full).indexed.NodeId)
    (initial old fresh : WordState bits)
    (data : LoopData full configuration capWords countsBase offset node initial count old)
    (hh : fresh.heap = old.heap) (ha : fresh.halted = false) :
    LoopData full configuration capWords countsBase offset node initial count fresh := by
  exact ⟨by rw [hh]; exact data.rep, by rw [hh]; exact data.slots,
    by rw [hh]; exact data.array, by rw [hh]; exact data.outside, data.counter, ha⟩

theorem body_control {bits : Nat} (rom : PhysicalROM) (origin : Nat) (state : WordState bits) :
    (executeOps rom (bodyLead origin) state).register .flag = BitVec.ofNat bits 0 ∧
      (executeOps rom (bodyLead origin) state).register .total = BitVec.ofNat bits (5 * (origin + 121)) := by
  exact ⟨rfl, rfl⟩

theorem kernel_index_bound (containing : List PackingOp) (origin : Nat)
    (hbound : origin + (programAt origin).length ≤ containing.length)
    (index : Nat) (hi : index < (programAt origin).length) :
    origin + index < containing.length := by
  omega

section Fetch

variable {bits q : Nat} (full : List (Finset (Fin q))) (command : Command) (configuration : Configuration q)
    (capWords countsBase offset origin : Nat) (node : (prepareNormalization q full).indexed.NodeId)
    (initial : WordState bits) (containing : List PackingOp)
    (hbound : origin + (programAt origin).length ≤ containing.length)
    (hcode : ∀ i (hi : i < (programAt origin).length),
      containing[origin + i]'(kernel_index_bound containing origin hbound i hi) = (programAt origin)[i])
    (hwords : WordsFit bits (packingCode containing)) (hpcfit : Fits bits (5 * containing.length))
    (hb : 8 ≤ bits) (hq : 0 < q) (hN : Fits bits full.length)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hw : Fits bits (base q full capWords bits + 7))
    (hbase : base q full capWords bits + 16 ≤ countsBase)
    (hfit : Fits bits (countsBase + (prepareNormalization q full).indexed.nodes.size))
    (hbreg : initial.register .old = BitVec.ofNat bits countsBase)
    (horeg : initial.register .fresh = BitVec.ofNat bits offset)
    (hoff : offset + ((prepareNormalization q full).indexed.children.get node).size ≤ edgeCount q full)

include hbound hcode hwords hpcfit hb hq hN bitmap hr hw hbase hfit

theorem fetched_setup_ready
    (rep : HeapRepresents q full capWords configuration initial.heap)
    (hi : initial.register .index = BitVec.ofNat bits node.val)
    (hp : initial.pc = BitVec.ofNat bits (5 * origin)) (ha : initial.halted = false) :
    ReadyLoop full configuration capWords countsBase offset origin node initial 0
      (packingRun (callInput q full command) containing 121 initial) := by
  rw [fetched_setup (callInput q full command) containing origin hbound hcode hwords hpcfit initial hp ha]
  constructor
  · exact setup_data full command configuration capWords countsBase offset node initial hb hq rep hN hi bitmap hr hw hbase hfit ha
  · rw [executeOps_pc _ setup initial setup_straight, hp, setup_length, BitVec.ofNat_add_ofNat]
    congr 1

omit hN bitmap hr hw hbase hfit

theorem fetched_test_state (count : Nat) (state : WordState bits)
    (ready : ReadyLoop full configuration capWords countsBase offset origin node initial count state) :
    let result := packingRun (callInput q full command) containing 28 state
    LoopData full configuration capWords countsBase offset node initial count result ∧
      result.pc = if count = ((prepareNormalization q full).indexed.children.get node).size then
        BitVec.ofNat bits (5 * (origin + 235)) else BitVec.ofNat bits (5 * (origin + 149)) := by
  dsimp only
  let rom := callInput q full command
  let degree := ((prepareNormalization q full).indexed.children.get node).size
  let tested := executeOps rom (testLead origin) state
  have hd := degree_fits full configuration capWords state.heap node hq ready.data.rep
  have hk : Fits bits count := ready.data.counter.trans_lt hd
  have h4 : state.heap (BitVec.ofNat bits (base q full capWords bits + 4)) = BitVec.ofNat bits degree := by
    simpa only [slotValue] using ready.data.slots 4 (by decide)
  have h6 : state.heap (BitVec.ofNat bits (base q full capWords bits + 6)) = BitVec.ofNat bits count := by
    simpa only [slotValue] using ready.data.slots 6 (by decide)
  have ht := execute_test full command configuration capWords origin degree count state hb hq ready.data.rep hd hk h4 h6
  have hz : (tested.register .flag).toNat = 0 ↔ count = degree := by
    rw [ht.1]
    exact test_remaining_zero degree count ready.data.counter hd
  have hp : tested.pc = BitVec.ofNat bits (5 * (origin + 148)) := by
    rw [executeOps_pc rom (testLead origin) state (testLead_straight origin), ready.pc,
      testLead_length, BitVec.ofNat_add_ofNat]
    congr 1
  rw [fetched_test rom containing origin hbound hcode hwords hpcfit state ready.pc ready.data.active]
  constructor
  · exact same_heap_data full configuration capWords countsBase offset count node initial state _ ready.data ht.2.2.1
      (by rw [packingExecuteOp_halted, ht.2.2.2, ready.data.active])
  · change (packingExecuteOp rom (.jumpIfZero .flag .total) tested).pc = _
    by_cases he : count = degree
    · rw [ite_eq_left he]
      calc
        _ = tested.register .total := by simp [packingExecuteOp, hz.mpr he]
        _ = _ := ht.2.1
    · rw [ite_eq_right he]
      have hn : ¬ (tested.register .flag).toNat = 0 := fun h => he (hz.mp h)
      calc
        _ = tested.pc + BitVec.ofNat bits 5 := by simp [packingExecuteOp, hn]
        _ = BitVec.ofNat bits (5 * (origin + 148) + 5) := by rw [hp, BitVec.ofNat_add_ofNat]
        _ = _ := congrArg (BitVec.ofNat bits) (by omega)

include hN bitmap hr hw hbase hfit hbreg horeg hoff

theorem fetched_iteration (count : Nat) (state : WordState bits)
    (hc : count < ((prepareNormalization q full).indexed.children.get node).size)
    (ready : ReadyLoop full configuration capWords countsBase offset origin node initial count state) :
    ReadyLoop full configuration capWords countsBase offset origin node initial (count + 1)
      (packingRun (callInput q full command) containing 114 state) := by
  let rom := callInput q full command
  let tested := packingRun rom containing 28 state
  have ht := fetched_test_state full command configuration capWords countsBase offset origin node initial
    containing hbound hcode hwords hpcfit hb hq count state ready
  have htp : tested.pc = BitVec.ofNat bits (5 * (origin + 149)) := by
    rw [ht.2, ite_eq_right (by omega)]
  have hd := body_data full command configuration capWords countsBase offset origin count node initial tested
    hb hq hN bitmap hr hw hbase hfit hbreg horeg hoff hc ht.1
  have controls := body_control rom origin tested
  rw [show 114 = 28 + 86 from rfl, run_add,
    fetched_body rom containing origin hbound hcode hwords hpcfit tested htp ht.1.active]
  constructor
  · exact same_heap_data full configuration capWords countsBase offset (count + 1) node initial _ _ hd rfl
      (by rw [packingExecuteOp_halted]; exact hd.active)
  · simp only [packingExecuteOp, controls.1, BitVec.toNat_ofNat, Nat.zero_mod, ite_true, controls.2]

theorem fetched_iterations (count iterations : Nat) (state : WordState bits)
    (hcount : count + iterations ≤ ((prepareNormalization q full).indexed.children.get node).size)
    (ready : ReadyLoop full configuration capWords countsBase offset origin node initial count state) :
    ReadyLoop full configuration capWords countsBase offset origin node initial (count + iterations)
      (packingRun (callInput q full command) containing (114 * iterations) state) := by
  induction iterations with
  | zero => exact ready
  | succ iterations ih =>
    have hi := ih (by omega)
    have hs := fetched_iteration full command configuration capWords countsBase offset origin node initial
      containing hbound hcode hwords hpcfit hb hq hN bitmap hr hw hbase hfit hbreg horeg hoff
      (count + iterations) (packingRun (callInput q full command) containing (114 * iterations) state) (by omega) hi
    rw [Nat.mul_succ, run_add]
    simpa only [Nat.add_assoc] using hs

end Fetch

end PaperProofs.Structure.LaminarTree.PSTRCountKernel
