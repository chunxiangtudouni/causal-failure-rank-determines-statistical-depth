module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009av

/-! Descent actual-clock fetch/decode/PC/AccessFits. No run certificate or
all-prefix NumericSafe is an entry input: the real fixed body and its proved
runtime invariant provide every current operation's access facts. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem desc_test_decoded {bits q origin capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (rom : PhysicalROM) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (clock : Nat) (hc : clock < 5) : DecodedAt rom containing heapWords (packingRun rom containing clock state) := by
  have hb : origin + (descendTest origin).length ≤ containing.length := by
    have hh := em.bound; rw [descendTest_length, descendProgramAt_length] at *; omega
  have hcl : clock < (descendTest origin).length := by rwa [descendTest_length]
  refine decoded_of_phase rom containing (descendTest origin) origin heapWords hb (desc_test_code em) em.words em.pcfit
    state ha clock hcl
    (PA17A19RuntimeRanks008.last_prefix rom containing (descendTestLead origin) (.jumpIfZero .total .old) origin hb
      (desc_test_code em) (descendTestLead_straight origin) em.words em.pcfit state hp ha clock (by rw [descendTestLead_length]; omega))
    ?_ (descendTest_access layout rom origin state hh clock hcl)
  rw [descendTest, List.take_append_of_le_length (show clock ≤ (descendTestLead origin).length by rw [descendTestLead_length]; omega)]
  exact PA17A19RuntimeRanks008.prefix_pc rom (descendTestLead origin) origin (descendTestLead_straight origin) state hp clock
    (by rw [descendTestLead_length]; omega)

theorem descReady_decoded {bits q origin capWords heapWords header base counts parents size remaining : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : DescReady full configuration origin capWords header base counts parents size (remaining + 1) state)
    (clock : Nat) (hc : clock < 91) :
    DecodedAt (callInput q full command) containing heapWords (packingRun (callInput q full command) containing clock state) := by
  let rom := callInput q full command
  by_cases htest : clock < 5
  · exact desc_test_decoded em layout rom state ready.address ready.pc ready.active clock htest
  · let tested := executeOps rom (descendTest origin) state
    have ht := descendTest_result rom origin header (remaining + 1) state (ready.bound.trans_lt layout.sizeFits)
      ready.address ready.pc ready.fuel
    have hp : tested.pc = BitVec.ofNat bits (5 * (origin + 5)) := by
      simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] using ht.1
    have ha : tested.halted = false := by rw [executeOps_halted, ready.active]
    have hb : origin + 5 + (descendBody origin).length ≤ containing.length := by
      have hh := em.bound; rw [descendBody_length, descendProgramAt_length] at *; omega
    have haccess := descendBody_access layout command configuration origin tested
      (by rw [ht.2.2]; exact ready.data.represents) ht.2.1
      (by rw [ht.2.2]; exact ready.nodePointer) (by rw [ht.2.2]; exact ready.toolPointer)
      (by rw [ht.2.2]; exact ready.data.candidates) (by rw [ht.2.2]; exact ready.nodeBound)
    rw [show clock = 5 + (clock - 5) by omega, run_add, fetched_desc_test em rom state ready.pc ready.active]
    refine decoded_of_phase rom containing (descendBody origin) (origin + 5) heapWords hb (desc_body_code em) em.words em.pcfit
      tested ha (clock - 5) (by rw [descendBody_length]; omega)
      (PA17A19RuntimeRanks008.last_prefix rom containing (descendBodyLead origin) (.jumpIfZero .flag .old) (origin + 5) hb
        (desc_body_code em) (descendBodyLead_straight origin) em.words em.pcfit tested hp ha (clock - 5)
        (by rw [descendBodyLead_length]; omega)) ?_ (haccess (clock - 5) (by rw [descendBody_length]; omega))
    rw [descendBody, List.take_append_of_le_length (show clock - 5 ≤ (descendBodyLead origin).length by rw [descendBodyLead_length]; omega)]
    exact PA17A19RuntimeRanks008.prefix_pc rom (descendBodyLead origin) (origin + 5) (descendBodyLead_straight origin)
      tested hp (clock - 5) (by rw [descendBodyLead_length]; omega)

theorem actual_desc_loop_decoded {bits q origin capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : DescReady full configuration origin capWords header base counts parents size size state)
    (clock : Nat) (hc : clock < 91 * size + 5) :
    DecodedAt (callInput q full command) containing heapWords (packingRun (callInput q full command) containing clock state) := by
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
    have rpositive : DescReady full configuration origin capWords header base counts parents size (remaining - 1 + 1)
        (packingRun rom containing (91 * iterations) state) := by
      rw [Nat.sub_add_cancel (show 1 ≤ remaining by omega)]
      exact ri
    rw [show clock = 91 * iterations + localClock by dsimp only [iterations, localClock]; omega, run_add]
    exact descReady_decoded em layout command configuration _ rpositive localClock hlocal
  · let looped := packingRun rom containing (91 * size) state
    have r0 : DescReady full configuration origin capWords header base counts parents size (0 + size) state := by
      simpa only [Nat.zero_add] using ready
    have hend : DescReady full configuration origin capWords header base counts parents size 0 looped :=
      descReady_iterations em layout command configuration state r0
    rw [show clock = 91 * size + (clock - 91 * size) by omega, run_add]
    exact desc_test_decoded em layout rom looped hend.address
      hend.pc hend.active (clock - 91 * size) (by omega)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009


