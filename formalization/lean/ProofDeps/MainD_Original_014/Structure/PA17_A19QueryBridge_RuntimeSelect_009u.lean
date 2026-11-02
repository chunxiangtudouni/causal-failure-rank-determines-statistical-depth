module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009t

/-! Complete reverse-loop physical frames. Every actual prefix preserves the
original leading region and HD's entire exclusive suffix. Source parent
bounds and original packed representation are carried by the proved Ready
invariant, rather than supplied as a trace or per-iteration safety oracle. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem reverseReady_frame {bits q origin capWords heapWords header base counts parents size remaining : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : ReverseReady full configuration origin capWords header base counts parents size (remaining + 1) state)
    (clock : Nat) (hc : clock ≤ 105) (physical : Nat) (hfit : Fits bits physical)
    (hprotect : physical < header + 8 ∨ endpoint header q size ≤ physical) :
    (packingRun (callInput q full command) containing clock state).heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  let rom := callInput q full command
  let tested := executeOps rom (reverseTest origin) state
  have hn : Fits bits (remaining + 1) := ready.bound.trans_lt layout.sizeFits
  by_cases htest : clock ≤ 5
  · have hbound : origin + (reverseTest origin).length ≤ containing.length := by
      have hh := em.bound; rw [reverseTest_length, reverseProgramAt_length] at *; omega
    rw [PA17A19RuntimeRanks008.last_prefix rom containing (reverseTestLead origin) (.jumpIfZero .total .old) origin hbound
      (reverse_test_code em) (reverseTestLead_straight origin) em.words em.pcfit state ready.pc ready.active clock
      (by rw [reverseTestLead_length]; omega)]
    exact WordPrefixFrame.noStore rom (reverseTest origin) state _ (reverseTest_noStore origin) clock
      (by rwa [reverseTest_length])
  · let parent := (state.heap (BitVec.ofNat bits (parents + (remaining + 1)))).toNat
    have hpBound : parent ≤ size := ready.data.parentBound remaining (by have hh := ready.bound; omega)
    have ht := reverseTest_result rom origin header (remaining + 1) state hn ready.address ready.pc ready.counter
    have hpc : tested.pc = BitVec.ofNat bits (5 * (origin + 5)) := by
      simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] using ht.1
    have hrep : HeapRepresents q full capWords configuration tested.heap := by rw [ht.2.2]; exact ready.data.represents
    have hneH : BitVec.ofNat bits physical ≠ BitVec.ofNat bits (header + 8) := by
      apply (ofNat_injective_of_fit _ _ hfit (layout.headerFits 8 (by decide))).not.mpr
      rcases hprotect with hlow | hhigh
      · omega
      · unfold endpoint childBase at hhigh
        omega
    have hneC : BitVec.ofNat bits physical ≠ BitVec.ofNat bits (childBase header q + parent) := by
      apply (ofNat_injective_of_fit _ _ hfit ((Nat.le_succ _).trans_lt (layout.targetFits parent hpBound))).not.mpr
      rcases hprotect with hlow | hhigh
      · unfold childBase
        omega
      · unfold endpoint at hhigh
        omega
    have hparentWord : state.heap (BitVec.ofNat bits (parents + (remaining + 1))) = BitVec.ofNat bits parent := by
      simp only [parent, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hframe := reverseBody_prefixFrame full command configuration capWords heapWords origin header base (childBase header q)
      counts parents remaining parent tested layout.bits8 layout.positive layout.width hrep layout.capacityFits layout.heapFits
      layout.header_eq (by have hh := layout.headerAllocated; omega)
      (by rw [ht.2.2]; exact ready.data.width) (by rw [ht.2.2]; exact ready.data.mask) layout.oneFits hn (BitVec.isLt _)
      ((show base + remaining ≤ base + size by have hh := ready.bound; omega).trans_lt layout.payloadFits)
      (by have hh := layout.payloadBound; have hb := ready.bound; omega) ht.2.1
      (by rw [ht.2.2]; exact ready.counter) (by rw [ht.2.2]; exact ready.data.payload)
      (by rw [ht.2.2]; exact ready.data.candidates) (by rw [ht.2.2]; exact ready.data.countsBase)
      (by rw [ht.2.2]; exact ready.data.parentsBase) (by rw [ht.2.2]; exact hparentWord) _ hneH hneC
    have hbound : origin + 5 + (reverseBody origin).length ≤ containing.length := by
      have hh := em.bound; rw [reverseBody_length, reverseProgramAt_length] at *; omega
    rw [show clock = 5 + (clock - 5) by omega, run_add, fetched_reverse_test em rom state ready.pc ready.active,
      PA17A19RuntimeRanks008.last_prefix rom containing (reverseBodyLead origin) (.jumpIfZero .flag .old) (origin + 5) hbound
        (reverse_body_code em) (reverseBodyLead_straight origin) em.words em.pcfit tested hpc
        (by rw [executeOps_halted, ready.active]) (clock - 5) (by rw [reverseBodyLead_length]; omega)]
    exact (hframe (clock - 5) (by rw [reverseBody_length]; omega)).trans (congrFun ht.2.2 _)

theorem reverseReady_iterations_frame {bits q origin capWords heapWords header base counts parents size remaining iterations : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : ReverseReady full configuration origin capWords header base counts parents size (remaining + iterations) state)
    (physical : Nat) (hfit : Fits bits physical)
    (hprotect : physical < header + 8 ∨ endpoint header q size ≤ physical) :
    (packingRun (callInput q full command) containing (105 * iterations) state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  induction iterations generalizing state with
  | zero => rfl
  | succ iterations ih =>
    have rd : ReverseReady full configuration origin capWords header base counts parents size ((remaining + iterations) + 1) state := by
      simpa only [Nat.add_assoc] using ready
    have next := reverseReady_step em layout command configuration state rd
    rw [show 105 * (iterations + 1) = 105 + 105 * iterations by omega, run_add]
    exact (ih _ next).trans (reverseReady_frame em layout command configuration state rd 105 le_rfl physical hfit hprotect)

theorem actual_reverse_loop_frame {bits q origin capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : ReverseReady full configuration origin capWords header base counts parents size size state)
    (clock : Nat) (hc : clock ≤ 105 * size + 5) (physical : Nat) (hfit : Fits bits physical)
    (hprotect : physical < header + 8 ∨ endpoint header q size ≤ physical) :
    (packingRun (callInput q full command) containing clock state).heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  let rom := callInput q full command
  by_cases hloop : clock < 105 * size
  · let iterations := clock / 105
    let localClock := clock % 105
    let remaining := size - iterations
    have hi : iterations < size := by dsimp only [iterations]; omega
    have hlocal : localClock < 105 := by dsimp only [localClock]; omega
    have hrem : 0 < remaining := by dsimp only [remaining]; omega
    have hsum : remaining + iterations = size := by dsimp only [remaining]; omega
    have r0 : ReverseReady full configuration origin capWords header base counts parents size (remaining + iterations) state := by
      rw [hsum]
      exact ready
    have ri := reverseReady_iterations em layout command configuration state r0
    have rf := reverseReady_iterations_frame em layout command configuration state r0 physical hfit hprotect
    have rpositive : ReverseReady full configuration origin capWords header base counts parents size (remaining - 1 + 1)
        (packingRun rom containing (105 * iterations) state) := by
      rw [Nat.sub_add_cancel (show 1 ≤ remaining by omega)]
      exact ri
    rw [show clock = 105 * iterations + localClock by dsimp only [iterations, localClock]; omega, run_add]
    exact (reverseReady_frame em layout command configuration _ rpositive localClock hlocal.le physical hfit hprotect).trans rf
  · let looped := packingRun rom containing (105 * size) state
    have r0 : ReverseReady full configuration origin capWords header base counts parents size (0 + size) state := by
      simpa only [Nat.zero_add] using ready
    have hend : ReverseReady full configuration origin capWords header base counts parents size 0 looped :=
      reverseReady_iterations em layout command configuration state r0
    have hf := reverseReady_iterations_frame em layout command configuration state r0 physical hfit hprotect
    have hbound : origin + (reverseTest origin).length ≤ containing.length := by
      have hh := em.bound; rw [reverseTest_length, reverseProgramAt_length] at *; omega
    rw [show clock = 105 * size + (clock - 105 * size) by omega, run_add,
      PA17A19RuntimeRanks008.last_prefix rom containing (reverseTestLead origin) (.jumpIfZero .total .old) origin hbound
        (reverse_test_code em) (reverseTestLead_straight origin) em.words em.pcfit looped hend.pc hend.active (clock - 105 * size)
        (by rw [reverseTestLead_length]; omega)]
    exact (WordPrefixFrame.noStore rom (reverseTest origin) looped _ (reverseTest_noStore origin)
      (clock - 105 * size) (by rw [reverseTest_length]; omega)).trans hf

theorem actual_reverse_loop_represents {bits q origin capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : ReverseReady full configuration origin capWords header base counts parents size size state)
    (clock : Nat) (hc : clock ≤ 105 * size + 5) :
    HeapRepresents q full capWords configuration (packingRun (callInput q full command) containing clock state).heap := by
  apply PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords (header + 8) state.heap _
    (by have hb := layout.bits8; omega) layout.positive ready.data.represents layout.bitmap layout.capacityFits
    (by simpa only [Nat.add_assoc, Nat.reduceAdd] using layout.headerFits 11 (by decide)) layout.metadata_le
  intro physical hphysical
  exact actual_reverse_loop_frame em layout command configuration state ready clock hc physical
    ((show physical ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt layout.endpointFits) (.inl hphysical)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
