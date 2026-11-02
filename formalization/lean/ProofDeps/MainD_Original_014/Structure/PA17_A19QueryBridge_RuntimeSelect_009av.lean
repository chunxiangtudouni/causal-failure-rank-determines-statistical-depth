module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009au

/-! Every actual clock of a descent round preserves the original leading
heap and HD's exclusive suffix; only H13 and actual node/tool slots store. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3200000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem descReady_frame {bits q origin capWords heapWords header base counts parents size remaining : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : DescReady full configuration origin capWords header base counts parents size (remaining + 1) state)
    (clock : Nat) (hc : clock ≤ 91) (physical : Nat) (hfit : Fits bits physical)
    (hprotect : physical < header + 13 ∨ endpoint header q size ≤ physical) :
    (packingRun (callInput q full command) containing clock state).heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  let rom := callInput q full command
  let tested := executeOps rom (descendTest origin) state
  by_cases htest : clock ≤ 5
  · have hb : origin + (descendTest origin).length ≤ containing.length := by
      have hh := em.bound; rw [descendTest_length, descendProgramAt_length] at *; omega
    rw [PA17A19RuntimeRanks008.last_prefix rom containing (descendTestLead origin) (.jumpIfZero .total .old) origin hb
      (desc_test_code em) (descendTestLead_straight origin) em.words em.pcfit state ready.pc ready.active clock
      (by rw [descendTestLead_length]; omega)]
    exact WordPrefixFrame.noStore rom (descendTest origin) state _ (descendTest_noStore origin) clock
      (by rw [descendTest_length]; omega)
  · have ht := descendTest_result rom origin header (remaining + 1) state (ready.bound.trans_lt layout.sizeFits)
      ready.address ready.pc ready.fuel
    have hp : tested.pc = BitVec.ofNat bits (5 * (origin + 5)) := by
      simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] using ht.1
    have hn : BitVec.ofNat bits physical ≠ BitVec.ofNat bits (nodeSlot header q size) := by
      apply (ofNat_injective_of_fit _ _ hfit
        ((show nodeSlot header q size ≤ endpoint header q size by unfold nodeSlot endpoint; omega).trans_lt layout.endpointFits)).not.mpr
      rcases hprotect with hlo | hhi <;> dsimp only [nodeSlot, endpoint, childBase] at * <;> omega
    have htool : BitVec.ofNat bits physical ≠ BitVec.ofNat bits (toolSlot header q size) := by
      apply (ofNat_injective_of_fit _ _ hfit
        ((show toolSlot header q size ≤ endpoint header q size by unfold toolSlot endpoint; omega).trans_lt layout.endpointFits)).not.mpr
      rcases hprotect with hlo | hhi <;> dsimp only [toolSlot, endpoint, childBase] at * <;> omega
    have hf : BitVec.ofNat bits physical ≠ BitVec.ofNat bits (header + 13) := by
      apply (ofNat_injective_of_fit _ _ hfit (layout.headerFits 13 (by decide))).not.mpr
      rcases hprotect with hlo | hhi <;> dsimp only [endpoint, childBase] at * <;> omega
    have hframe := descendBody_prefixFrame layout command configuration origin tested
      (by rw [ht.2.2]; exact ready.data.represents) ht.2.1
      (by rw [ht.2.2]; exact ready.nodePointer) (by rw [ht.2.2]; exact ready.toolPointer)
      (by rw [ht.2.2]; exact ready.nodeBound) _ hn htool hf
    have hb : origin + 5 + (descendBody origin).length ≤ containing.length := by
      have hh := em.bound; rw [descendBody_length, descendProgramAt_length] at *; omega
    rw [show clock = 5 + (clock - 5) by omega, run_add, fetched_desc_test em rom state ready.pc ready.active,
      PA17A19RuntimeRanks008.last_prefix rom containing (descendBodyLead origin) (.jumpIfZero .flag .old) (origin + 5) hb
        (desc_body_code em) (descendBodyLead_straight origin) em.words em.pcfit tested hp
        (by rw [executeOps_halted, ready.active]) (clock - 5) (by rw [descendBodyLead_length]; omega)]
    exact (hframe (clock - 5) (by rw [descendBody_length]; omega)).trans (congrFun ht.2.2 _)

theorem descReady_iterations_frame {bits q origin capWords heapWords header base counts parents size remaining iterations : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : DescReady full configuration origin capWords header base counts parents size (remaining + iterations) state)
    (physical : Nat) (hfit : Fits bits physical)
    (hprotect : physical < header + 13 ∨ endpoint header q size ≤ physical) :
    (packingRun (callInput q full command) containing (91 * iterations) state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  induction iterations generalizing state with
  | zero => rfl
  | succ iterations ih =>
    have rd : DescReady full configuration origin capWords header base counts parents size ((remaining + iterations) + 1) state := by
      simpa only [Nat.add_assoc] using ready
    have next := descReady_step em layout command configuration state rd
    rw [show 91 * (iterations + 1) = 91 + 91 * iterations by omega, run_add]
    exact (ih _ next).trans (descReady_frame em layout command configuration state rd 91 le_rfl physical hfit hprotect)

theorem actual_desc_loop_frame {bits q origin capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : DescReady full configuration origin capWords header base counts parents size size state)
    (clock : Nat) (hc : clock ≤ 91 * size + 5) (physical : Nat) (hfit : Fits bits physical)
    (hprotect : physical < header + 13 ∨ endpoint header q size ≤ physical) :
    (packingRun (callInput q full command) containing clock state).heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  let rom := callInput q full command
  by_cases hloop : clock < 91 * size
  · let iterations := clock / 91
    let localClock := clock % 91
    let remaining := size - iterations
    have hi : iterations < size := by dsimp only [iterations]; omega
    have hlocal : localClock < 91 := by dsimp only [localClock]; omega
    have hrem : 0 < remaining := by dsimp only [remaining]; omega
    have hsum : remaining + iterations = size := by dsimp only [remaining]; omega
    have r0 : DescReady full configuration origin capWords header base counts parents size (remaining + iterations) state := by
      rw [hsum]
      exact ready
    have ri := descReady_iterations em layout command configuration state r0
    have rf := descReady_iterations_frame em layout command configuration state r0 physical hfit hprotect
    have rpositive : DescReady full configuration origin capWords header base counts parents size (remaining - 1 + 1)
        (packingRun rom containing (91 * iterations) state) := by
      rw [Nat.sub_add_cancel (show 1 ≤ remaining by omega)]
      exact ri
    rw [show clock = 91 * iterations + localClock by dsimp only [iterations, localClock]; omega, run_add]
    exact (descReady_frame em layout command configuration _ rpositive localClock hlocal.le physical hfit hprotect).trans rf
  · let looped := packingRun rom containing (91 * size) state
    have r0 : DescReady full configuration origin capWords header base counts parents size (0 + size) state := by
      simpa only [Nat.zero_add] using ready
    have hend : DescReady full configuration origin capWords header base counts parents size 0 looped :=
      descReady_iterations em layout command configuration state r0
    have hf := descReady_iterations_frame em layout command configuration state r0 physical hfit hprotect
    have hbound : origin + (descendTest origin).length ≤ containing.length := by
      have hh := em.bound; rw [descendTest_length, descendProgramAt_length] at *; omega
    rw [show clock = 91 * size + (clock - 91 * size) by omega, run_add,
      PA17A19RuntimeRanks008.last_prefix rom containing (descendTestLead origin) (.jumpIfZero .total .old) origin hbound
        (desc_test_code em) (descendTestLead_straight origin) em.words em.pcfit looped hend.pc hend.active (clock - 91 * size)
        (by rw [descendTestLead_length]; omega)]
    exact (WordPrefixFrame.noStore rom (descendTest origin) looped _ (descendTest_noStore origin)
      (clock - 91 * size) (by rw [descendTest_length]; omega)).trans hf

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

