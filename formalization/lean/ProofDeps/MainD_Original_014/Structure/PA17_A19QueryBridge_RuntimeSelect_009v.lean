module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009u

/-! Actual whole-loop physical fetch, decode, finite PC and AccessFits.
These follow from the loop's proved internal data invariant and the real
fixed phases, rather than being assumed as an entry prefix-safety oracle. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def DecodedAt {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (heapWords : Nat) (state : WordState bits) : Prop :=
  state.halted = false ∧ Fits bits (state.pc.toNat + 4) ∧
    state.pc.toNat + 4 < (packingCode containing).length ∧
    ∃ op, PackingOp.decode (physicalFetch bits (packingCode containing) state.pc.toNat) = some op ∧
      packingAccessFits rom heapWords state op

theorem decoded_of_phase {bits : Nat} (rom : PhysicalROM) (containing block : List PackingOp) (start heapWords : Nat)
    (hbound : start + block.length ≤ containing.length)
    (hcode : ∀ i (hi : i < block.length), containing[start + i]'(by omega) = block[i])
    (hw : WordsFit bits (packingCode containing)) (hpcf : Fits bits (5 * containing.length))
    (state : WordState bits) (ha : state.halted = false) (clock : Nat) (hc : clock < block.length)
    (hrun : packingRun rom containing clock state = executeOps rom (block.take clock) state)
    (hp : (executeOps rom (block.take clock) state).pc = BitVec.ofNat bits (5 * (start + clock)))
    (haccess : packingAccessFits rom heapWords (executeOps rom (block.take clock) state) block[clock]) :
    DecodedAt rom containing heapWords (packingRun rom containing clock state) := by
  have hi : start + clock < containing.length := by omega
  have hpNat : (executeOps rom (block.take clock) state).pc.toNat = 5 * (start + clock) := by
    rw [hp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt ((Nat.mul_le_mul_left 5 hi.le).trans_lt hpcf)
  have hsmall : 5 * (start + clock) + 4 < 5 * containing.length := by omega
  rw [hrun]
  refine ⟨by rw [executeOps_halted, ha], ?_, ?_, block[clock], ?_, haccess⟩
  · rw [hpNat]
    exact hsmall.trans hpcf
  · rw [hpNat, packingCode_length]
    omega
  · rw [hpNat, physicalFetch_eq bits (packingCode containing) _ hw]
    change PackingOp.decode (natFetch containing (5 * (start + clock))) = some block[clock]
    rw [natFetch_body containing (start + clock) hi, hcode clock hc, decode_encode]

theorem reverse_test_decoded {bits origin : Nat} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing) (rom : PhysicalROM) (header heapWords : Nat) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header) (halloc : header + 8 < heapWords)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (clock : Nat) (hc : clock < 5) : DecodedAt rom containing heapWords (packingRun rom containing clock state) := by
  have hbound : origin + (reverseTest origin).length ≤ containing.length := by
    have hh := em.bound; rw [reverseTest_length, reverseProgramAt_length] at *; omega
  have hcl : clock < (reverseTest origin).length := by rwa [reverseTest_length]
  refine decoded_of_phase rom containing (reverseTest origin) origin heapWords hbound (reverse_test_code em) em.words em.pcfit
    state ha clock hcl
    (PA17A19RuntimeRanks008.last_prefix rom containing (reverseTestLead origin) (.jumpIfZero .total .old) origin hbound
      (reverse_test_code em) (reverseTestLead_straight origin) em.words em.pcfit state hp ha clock (by rw [reverseTestLead_length]; omega))
    ?_ (reverseTest_access rom origin header heapWords state hh halloc clock hcl)
  rw [reverseTest, List.take_append_of_le_length (show clock ≤ (reverseTestLead origin).length by rw [reverseTestLead_length]; omega)]
  exact PA17A19RuntimeRanks008.prefix_pc rom (reverseTestLead origin) origin (reverseTestLead_straight origin) state hp clock
    (by rw [reverseTestLead_length]; omega)

theorem reverseReady_decoded {bits q origin capWords heapWords header base counts parents size remaining : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : ReverseReady full configuration origin capWords header base counts parents size (remaining + 1) state)
    (clock : Nat) (hc : clock < 105) :
    DecodedAt (callInput q full command) containing heapWords (packingRun (callInput q full command) containing clock state) := by
  let rom := callInput q full command
  by_cases htest : clock < 5
  · exact reverse_test_decoded em rom header heapWords state ready.address (by have hh := layout.headerAllocated; omega)
      ready.pc ready.active clock htest
  · let tested := executeOps rom (reverseTest origin) state
    let parent := (state.heap (BitVec.ofNat bits (parents + (remaining + 1)))).toNat
    have hrem : remaining < size := by have hh := ready.bound; omega
    have hn : Fits bits (remaining + 1) := ready.bound.trans_lt layout.sizeFits
    have hparent : parent ≤ size := ready.data.parentBound remaining hrem
    have hparentWord : state.heap (BitVec.ofNat bits (parents + (remaining + 1))) = BitVec.ofNat bits parent := by
      simp only [parent, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have ht := reverseTest_result rom origin header (remaining + 1) state hn ready.address ready.pc ready.counter
    have hpc : tested.pc = BitVec.ofNat bits (5 * (origin + 5)) := by
      simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] using ht.1
    have ha : tested.halted = false := by rw [executeOps_halted, ready.active]
    have hrep : HeapRepresents q full capWords configuration tested.heap := by rw [ht.2.2]; exact ready.data.represents
    have haccess := reverseBody_access full command configuration capWords heapWords origin header base (childBase header q)
      counts parents remaining parent tested layout.bits8 layout.positive layout.width hrep layout.capacityFits layout.heapFits
      layout.header_eq layout.headerAllocated
      (by rw [ht.2.2]; exact ready.data.width) (by rw [ht.2.2]; exact ready.data.mask) layout.oneFits hn
      ((show base + remaining ≤ base + size by omega).trans_lt layout.payloadFits)
      (by have hh := layout.payloadBound; omega) ht.2.1
      (by rw [ht.2.2]; exact ready.counter) (by rw [ht.2.2]; exact ready.data.payload)
      (by rw [ht.2.2]; exact ready.data.candidates) (by rw [ht.2.2]; exact ready.data.countsBase)
      (by rw [ht.2.2]; exact ready.data.parentsBase) (by rw [ht.2.2]; exact hparentWord)
      (by have hh := layout.countsEnd; have he := layout.headerAllocated; omega)
      (by have hh := layout.parentsEnd; have he := layout.headerAllocated; omega)
      (by have he := layout.allocated; unfold endpoint at he; omega)
    have hbound : origin + 5 + (reverseBody origin).length ≤ containing.length := by
      have hh := em.bound; rw [reverseBody_length, reverseProgramAt_length] at *; omega
    rw [show clock = 5 + (clock - 5) by omega, run_add, fetched_reverse_test em rom state ready.pc ready.active]
    refine decoded_of_phase rom containing (reverseBody origin) (origin + 5) heapWords hbound (reverse_body_code em) em.words em.pcfit
      tested ha (clock - 5) (by rw [reverseBody_length]; omega)
      (PA17A19RuntimeRanks008.last_prefix rom containing (reverseBodyLead origin) (.jumpIfZero .flag .old) (origin + 5) hbound
        (reverse_body_code em) (reverseBodyLead_straight origin) em.words em.pcfit tested hpc ha (clock - 5)
        (by rw [reverseBodyLead_length]; omega)) ?_ (haccess (clock - 5) (by rw [reverseBody_length]; omega))
    rw [reverseBody, List.take_append_of_le_length (show clock - 5 ≤ (reverseBodyLead origin).length by rw [reverseBodyLead_length]; omega)]
    exact PA17A19RuntimeRanks008.prefix_pc rom (reverseBodyLead origin) (origin + 5) (reverseBodyLead_straight origin) tested hpc (clock - 5)
      (by rw [reverseBodyLead_length]; omega)

theorem actual_reverse_loop_decoded {bits q origin capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : ReverseReady full configuration origin capWords header base counts parents size size state)
    (clock : Nat) (hc : clock < 105 * size + 5) :
    DecodedAt (callInput q full command) containing heapWords (packingRun (callInput q full command) containing clock state) := by
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
    have rpositive : ReverseReady full configuration origin capWords header base counts parents size (remaining - 1 + 1)
        (packingRun rom containing (105 * iterations) state) := by
      rw [Nat.sub_add_cancel (show 1 ≤ remaining by omega)]
      exact ri
    rw [show clock = 105 * iterations + localClock by dsimp only [iterations, localClock]; omega, run_add]
    exact reverseReady_decoded em layout command configuration _ rpositive localClock hlocal
  · let looped := packingRun rom containing (105 * size) state
    have r0 : ReverseReady full configuration origin capWords header base counts parents size (0 + size) state := by
      simpa only [Nat.zero_add] using ready
    have hend : ReverseReady full configuration origin capWords header base counts parents size 0 looped :=
      reverseReady_iterations em layout command configuration state r0
    rw [show clock = 105 * size + (clock - 105 * size) by omega, run_add]
    exact reverse_test_decoded em rom header heapWords looped hend.address (by have hh := layout.headerAllocated; omega)
      hend.pc hend.active (clock - 105 * size) (by omega)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
