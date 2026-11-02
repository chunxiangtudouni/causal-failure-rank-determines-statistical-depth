module

public import PaperProofs.Structure.PSTR_HD_CountFetchSafe_046

/-! Every clock of the actual dynamic child loop has an in-bounds decoded
instruction, real memory access, and the original heap/caller frame. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine PSTRWordSegments PSTRCountWorkspace PSTRStaticLayout

theorem loopData_frame {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords countsBase offset count : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (initial state : WordState bits)
    (data : LoopData full configuration capWords countsBase offset node initial count state) :
    HeapFrame (nodeProtected (base q full capWords bits) countsBase node.val) initial.heap state.heap := by
  intro physical hf hp
  exact data.outside physical hf hp.1

theorem active_node_prefix {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords countsBase offset origin heapWords : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (initial : WordState bits) (containing : List PackingOp)
    (hbound : origin + (programAt origin).length ≤ containing.length)
    (hcode : ∀ i (hi : i < (programAt origin).length), containing[origin + i]'(kernel_index_bound containing origin hbound i hi) = (programAt origin)[i])
    (hwords : WordsFit bits (packingCode containing)) (hpcfit : Fits bits (5 * containing.length))
    (hb : 8 ≤ bits) (hq : 0 < q) (hN : Fits bits full.length)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hw : Fits bits (base q full capWords bits + 7))
    (hbase : base q full capWords bits + 16 ≤ countsBase)
    (hfit : Fits bits (countsBase + (prepareNormalization q full).indexed.nodes.size))
    (hroom : base q full capWords bits + 7 < heapWords)
    (hcounts : countsBase + (prepareNormalization q full).indexed.nodes.size ≤ heapWords)
    (hbreg : initial.register .old = BitVec.ofNat bits countsBase)
    (horeg : initial.register .fresh = BitVec.ofNat bits offset)
    (hireg : initial.register .index = BitVec.ofNat bits node.val)
    (hoff : offset + ((prepareNormalization q full).indexed.children.get node).size ≤ edgeCount q full)
    (rep : HeapRepresents q full capWords configuration initial.heap)
    (hp : initial.pc = BitVec.ofNat bits (5 * origin)) (ha : initial.halted = false)
    (clock : Nat) (hc : clock < activeSteps ((prepareNormalization q full).indexed.children.get node).size) :
    let result := packingRun (callInput q full command) containing clock initial
    AtSafe (callInput q full command) containing heapWords result ∧
      HeapFrame (nodeProtected (base q full capWords bits) countsBase node.val) initial.heap result.heap ∧
      HeapRepresents q full capWords configuration result.heap := by
  dsimp only
  let rom := callInput q full command
  let degree := ((prepareNormalization q full).indexed.children.get node).size
  let region := nodeProtected (base q full capWords bits) countsBase node.val
  have hs := fetched_setup_ready full command configuration capWords countsBase offset origin node initial
    containing hbound hcode hwords hpcfit hb hq hN bitmap hr hw hbase hfit rep hireg hp ha
  have ready (count : Nat) (hcount : count ≤ degree) :
      ReadyLoop full configuration capWords countsBase offset origin node initial count
        (packingRun rom containing (121 + 114 * count) initial) := by
    rw [run_add]
    have hi := fetched_iterations full command configuration capWords countsBase offset origin node initial
      containing hbound hcode hwords hpcfit hb hq hN bitmap hr hw hbase hfit hbreg horeg hoff
      0 count (packingRun rom containing 121 initial) (by omega) hs
    simpa only [Nat.zero_add] using hi
  have conclude (state : WordState bits) (safe : AtSafe rom containing heapWords state)
      (frame : HeapFrame region initial.heap state.heap) :
      AtSafe rom containing heapWords state ∧ HeapFrame region initial.heap state.heap ∧
        HeapRepresents q full capWords configuration state.heap :=
    ⟨safe, frame, frame_represents full configuration capWords countsBase node.val initial.heap state.heap
      (by omega) hq rep bitmap hr hw hbase frame⟩
  rcases phase_partition degree clock hc with hstart | ⟨count, rest, hcount, hrest, heq⟩ | ⟨rest, hrest, heq⟩
  · have p := setup_prefixOK full command configuration capWords countsBase heapWords node initial
      hb hq rep hN hireg bitmap hr hw hroom
    have s := setup_fetch_safe rom containing origin heapWords region hbound hcode hwords hpcfit initial hp ha p clock hstart
    exact conclude _ s.1 s.2
  · let state := packingRun rom containing (121 + 114 * count) initial
    have rd := ready count hcount.le
    by_cases ht : rest < 28
    · have p := testLead_prefixOK full command configuration capWords countsBase node.val heapWords origin state hb hq rd.data.rep hroom
      have s := test_fetch_safe rom containing origin heapWords region hbound hcode hwords hpcfit state rd.pc rd.data.active p rest ht
      rw [heq, run_add]
      exact conclude _ s.1 (heapFrame_trans region initial.heap state.heap _
        (loopData_frame full configuration capWords countsBase offset count node initial state rd.data) s.2)
    · let tested := packingRun rom containing 28 state
      have t := fetched_test_state full command configuration capWords countsBase offset origin node initial
        containing hbound hcode hwords hpcfit hb hq count state rd
      have tp : tested.pc = BitVec.ofNat bits (5 * (origin + 149)) := by rw [t.2, ite_eq_right (by omega)]
      have p := bodyLead_prefixOK full command configuration capWords countsBase offset count heapWords origin node initial tested
        hb hq hN hw hroom hcounts hbreg horeg hoff hcount t.1
      have s := body_fetch_safe rom containing origin heapWords region hbound hcode hwords hpcfit tested tp t.1.active p (rest - 28) (by omega)
      rw [heq, show 121 + 114 * count + rest = (121 + 114 * count) + (28 + (rest - 28)) by omega, run_add, run_add]
      exact conclude _ s.1 (heapFrame_trans region initial.heap tested.heap _
        (loopData_frame full configuration capWords countsBase offset count node initial tested t.1) s.2)
  · let state := packingRun rom containing (121 + 114 * degree) initial
    have rd := ready degree le_rfl
    by_cases ht : rest < 28
    · have p := testLead_prefixOK full command configuration capWords countsBase node.val heapWords origin state hb hq rd.data.rep hroom
      have s := test_fetch_safe rom containing origin heapWords region hbound hcode hwords hpcfit state rd.pc rd.data.active p rest ht
      rw [heq, run_add]
      exact conclude _ s.1 (heapFrame_trans region initial.heap state.heap _
        (loopData_frame full configuration capWords countsBase offset degree node initial state rd.data) s.2)
    · let tested := packingRun rom containing 28 state
      have t := fetched_test_state full command configuration capWords countsBase offset origin node initial
        containing hbound hcode hwords hpcfit hb hq degree state rd
      have tp : tested.pc = BitVec.ofNat bits (5 * (origin + 235)) := by rw [t.2, ite_eq_left rfl]
      have nf : Fits bits (countsBase + node.val) :=
        (show countsBase + node.val ≤ countsBase + (prepareNormalization q full).indexed.nodes.size by have hn := node.isLt; omega).trans_lt hfit
      have p := footer_prefixOK full command configuration capWords countsBase offset degree heapWords node initial tested hb hq nf hroom
        (by have hn := node.isLt; omega) hbreg hireg t.1
      have s := footer_fetch_safe rom containing origin heapWords region hbound hcode hwords hpcfit tested tp t.1.active p (rest - 28) (by omega)
      rw [heq, show 121 + 114 * degree + rest = (121 + 114 * degree) + (28 + (rest - 28)) by omega, run_add, run_add]
      exact conclude _ s.1 (heapFrame_trans region initial.heap tested.heap _
        (loopData_frame full configuration capWords countsBase offset degree node initial tested t.1) s.2)

end PaperProofs.Structure.LaminarTree.PSTRCountKernel
