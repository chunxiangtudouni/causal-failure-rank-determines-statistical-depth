module
public import Structure.PA17_A19QueryBridge_RuntimeTests_Safety_018e
public import Structure.PA17_A19QueryBridge_RuntimeTests_Control_015r

/-! Safety of one actually executed budget block. All five phase entry
facts come from the frozen concrete budget producer, rather than caller
certificates for an unexecuted phase. -/
@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSafety018
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PA17A19RuntimeTests010

theorem actual_budgetBlock_safe {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords rowBase budget encoded : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (hendpoint_alloc : PSTRQueryLayout.endpoint (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) q ≤ heapWords)
    (ready : OuterBodyEntry full configuration capWords rowBase encoded origin budget state)
    (count : Nat) (hcut : count < budgetBlockClock (treeSize q full)) :
    StepSafe (callInput q full command) containing heapWords
      (packingRun (callInput q full command) containing count state) := by
  let rom := callInput q full command
  let size := treeSize q full
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace size
  let endpoint := PSTRQueryLayout.endpoint workspace size q
  let entryBase := rowBase + budget * (size + 1)
  let phases := budgetPhases rom containing size state
  have hheaderEnd : header + 16 < endpoint := by
    unfold endpoint PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags
    omega
  have halloc : header + 16 < heapWords := hheaderEnd.trans_le hendpoint_alloc
  have hrow : entryBase + (size + 1) ≤ capWords := by
    have hm := Nat.mul_le_mul_right (size + 1) (show budget + 1 ≤ q + 2 by have := ready.budget_bound; omega)
    have he := ready.row_extent
    dsimp only [entryBase, size] at *
    nlinarith
  have hscalar : entryBase < capWords := by omega
  have produced := actual_budget_phases em full command configuration capWords heapWords rowBase budget encoded state
    hb hq hw ready.core.rep bitmap hs hf hendpoint_alloc ready.core.width ready.core.mask ready.core.header
    ready.core.pc_eq ready.core.active ready.counter ready.row_pointer ready.node_pointer ready.budget_bound
    ready.encoded_bound ready.row_extent ready.parents
  have hgood : header + 16 + budget < heapWords := by
    have h := good_lt_endpoint workspace size q budget ready.budget_bound
    change header + 16 + budget < endpoint at h
    exact h.trans_le hendpoint_alloc
  have hbad : header + q + 18 + budget < heapWords := by
    have h := bad_lt_endpoint workspace size q budget ready.budget_bound
    change header + 16 + (q + 2) + budget < endpoint at h
    rw [show header + q + 18 + budget = header + 16 + (q + 2) + budget by omega]
    exact h.trans_le hendpoint_alloc
  have h1 : Fits bits 1 := by
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
    change 1 < 2 ^ bits
    omega
  have hinput : 1 < rom.input.length := by
    change 1 < (([full.length, q] ++ incidence full) ++ [command.word]).length
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hqraw : (rom.words .input).getD 1 0 = q := rfl
  have tail (entry : WordState bits) (first cut : Nat) (hle : first ≤ cut) :
      packingRun rom containing cut entry =
        packingRun rom containing (cut - first) (packingRun rom containing first entry) := by
    conv_lhs => rw [show cut = first + (cut - first) by omega]
    exact run_add rom containing first (cut - first) entry
  by_cases hinit : count < 86
  · exact budgetInit_safe em full command configuration capWords heapWords rowBase budget state hb hq hw
      bitmap hs hf halloc ready.core ready.counter ready.row_pointer hscalar count hinit
  · have hfront : packingRun rom containing count state =
        packingRun rom containing (count - 86) phases.entry := tail state 86 count (by omega)
    rw [hfront]
    by_cases hnodes : count - 86 < nodeClock size
    · exact actual_nodeLoop_safe em full command configuration capWords heapWords entryBase size phases.entry
        hb hq hw bitmap hs hf halloc produced.entry_core produced.entry_counter produced.entry_row
        (by omega) hrow (count - 86) hnodes
    · have hnodesRun : packingRun rom containing (count - 86) phases.entry =
          packingRun rom containing (count - 86 - nodeClock size) phases.nodes :=
        tail phases.entry (nodeClock size) (count - 86) (by omega)
      rw [hnodesRun]
      by_cases hfinish : count - 86 - nodeClock size < 26
      · exact acceptFinish_safe em rom header budget heapWords phases.nodes produced.nodes_core.header
          produced.nodes_core.pc_eq produced.nodes_core.active produced.nodes_budget hgood
          (count - 86 - nodeClock size) hfinish
      · have hfinishRun : packingRun rom containing (count - 86 - nodeClock size) phases.nodes =
            packingRun rom containing (count - 86 - nodeClock size - 26) phases.initialized :=
          tail phases.nodes 26 (count - 86 - nodeClock size) (by omega)
        rw [hfinishRun]
        by_cases hancestors : count - 86 - nodeClock size - 26 < ancestorClock size
        · exact actual_ancestorLoop_safe em full command configuration capWords heapWords entryBase size encoded phases.initialized
            hb hq hw bitmap hs hf halloc produced.initialized_core produced.initialized_counter produced.initialized_row
            produced.initialized_node (by omega) ready.encoded_bound hrow produced.initialized_parents
            (count - 86 - nodeClock size - 26) hancestors
        · have hancestorRun : packingRun rom containing (count - 86 - nodeClock size - 26) phases.initialized =
              packingRun rom containing (count - 86 - nodeClock size - 26 - ancestorClock size) phases.ancestors :=
            tail phases.initialized (ancestorClock size) (count - 86 - nodeClock size - 26) (by omega)
          rw [hancestorRun]
          apply budgetFooter_safe em rom header q budget heapWords phases.ancestors h1 hinput hqraw
            produced.ancestors_core.header produced.ancestors_core.pc_eq produced.ancestors_core.active
            produced.ancestors_budget hbad (count - 86 - nodeClock size - 26 - ancestorClock size)
          unfold budgetBlockClock at hcut
          dsimp only [size] at *
          omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSafety018
