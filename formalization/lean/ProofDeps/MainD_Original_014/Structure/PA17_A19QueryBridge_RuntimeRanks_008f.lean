module

public import Structure.PA17_A19QueryBridge_RuntimeRanks_008e

/-! Every real fetched instruction in each fixed phase is decoded, allocated
and frame preserving. The loop/global composition consumes these proved
certificates; the public kernel receives only ordinary layout/data facts. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeRanks008

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments

def Point {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (heapWords header : Nat)
    (state : WordState bits) : Prop :=
  state.halted = false ∧ ∃ index : Nat, ∃ hi : index < containing.length,
    state.pc.toNat = 5 * index ∧
    physicalFetch bits (packingCode containing) state.pc.toNat = containing[index].encode ∧
    packingAccessFits rom heapWords state containing[index] ∧
    ∀ address, Protected header address →
      (packingExecuteOp rom containing[index] state).heap address = state.heap address

theorem straight_prefix {bits : Nat} (rom : PhysicalROM) (containing block : List PackingOp) (start : Nat)
    (hbound : start + block.length ≤ containing.length)
    (hcode : ∀ i (hi : i < block.length), containing[start + i]'(by omega) = block[i])
    (hs : StraightProgram block) (hw : WordsFit bits (packingCode containing)) (hpcf : Fits bits (5 * containing.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ block.length) :
    packingRun rom containing count state = executeOps rom (block.take count) state := by
  have hl : (block.take count).length = count := List.length_take_of_le hc
  conv_lhs => rw [← hl]
  apply straight_segment rom containing (block.take count) start (by omega) ?_ ?_ hw hpcf state hp ha
  · intro i hi
    have hh : i < block.length := by rw [hl] at hi; omega
    simpa only [List.getElem_take] using hcode i hh
  · intro op ho
    exact hs op (List.mem_of_mem_take ho)

theorem last_prefix {bits : Nat} (rom : PhysicalROM) (containing lead : List PackingOp) (last : PackingOp) (start : Nat)
    (hbound : start + (lead ++ [last]).length ≤ containing.length)
    (hcode : ∀ i (hi : i < (lead ++ [last]).length), containing[start + i]'(by omega) = (lead ++ [last])[i])
    (hs : StraightProgram lead) (hw : WordsFit bits (packingCode containing)) (hpcf : Fits bits (5 * containing.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ lead.length + 1) :
    packingRun rom containing count state = executeOps rom ((lead ++ [last]).take count) state := by
  apply segment_prefix rom containing lead last start (by simpa only [List.length_append, List.length_singleton, Nat.add_assoc] using hbound)
    ?_ ?_ hs hw hpcf state hp ha count hc
  · intro i hi
    have hh := hcode i (by simp only [List.length_append, List.length_singleton]; omega)
    simpa only [List.getElem_append_left hi] using hh
  · have hh := hcode lead.length (by simp only [List.length_append, List.length_singleton]; omega)
    simpa only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero] using hh

theorem prefix_pc {bits : Nat} (rom : PhysicalROM) (block : List PackingOp) (start : Nat)
    (hs : StraightProgram block) (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start))
    (count : Nat) (hc : count ≤ block.length) :
    (executeOps rom (block.take count) state).pc = BitVec.ofNat bits (5 * (start + count)) := by
  rw [executeOps_pc rom (block.take count) state (by intro op ho; exact hs op (List.mem_of_mem_take ho)), hp,
    List.length_take_of_le hc, BitVec.ofNat_add_ofNat]
  congr 1
  omega

theorem point_of_phase {bits : Nat} (rom : PhysicalROM) (containing block : List PackingOp)
    (start heapWords header : Nat) (hbound : start + block.length ≤ containing.length)
    (hcode : ∀ i (hi : i < block.length), containing[start + i]'(by omega) = block[i])
    (hw : WordsFit bits (packingCode containing)) (hpcf : Fits bits (5 * containing.length))
    (state : WordState bits) (ha : state.halted = false) (count : Nat) (hc : count < block.length)
    (hrun : packingRun rom containing count state = executeOps rom (block.take count) state)
    (hp : (executeOps rom (block.take count) state).pc = BitVec.ofNat bits (5 * (start + count)))
    (haccess : packingAccessFits rom heapWords (executeOps rom (block.take count) state) block[count])
    (hframe : ∀ address, Protected header address →
      (packingExecuteOp rom block[count] (executeOps rom (block.take count) state)).heap address =
        (executeOps rom (block.take count) state).heap address) :
    Point rom containing heapWords header (packingRun rom containing count state) := by
  have hi : start + count < containing.length := by omega
  have hpNat : (executeOps rom (block.take count) state).pc.toNat = 5 * (start + count) := by
    rw [hp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt ((Nat.mul_le_mul_left 5 hi.le).trans_lt hpcf)
  rw [hrun]
  refine ⟨by rw [executeOps_halted, ha], start + count, hi, hpNat, ?_, ?_, ?_⟩
  · rw [hpNat, physicalFetch_eq bits (packingCode containing) _ hw]
    change natFetch containing (5 * (start + count)) = containing[start + count].encode
    exact natFetch_body containing (start + count) hi
  · rw [hcode count hc]
    exact haccess
  · rw [hcode count hc]
    exact hframe

theorem setup_point {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (rom : PhysicalROM) (heapWords header : Nat) (state : WordState bits)
    (h1 : Fits bits 1) (hinput : 1 < rom.input.length)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (count : Nat) (hc : count < 8) : Point rom containing heapWords header (packingRun rom containing count state) := by
  have hb : origin + setup.length ≤ containing.length := by have hh := em.bound; rw [programAt_length, setup_length] at *; omega
  have hcount : count < setup.length := by rwa [setup_length]
  apply point_of_phase rom containing setup origin heapWords header hb (setup_code em) em.words em.pcfit state ha count hcount
    (straight_prefix rom containing setup origin hb (setup_code em) setup_straight em.words em.pcfit state hp ha count hcount.le)
    (prefix_pc rom setup origin setup_straight state hp count hcount.le)
    (setup_access rom heapWords state h1 hinput count hcount)
  intro address _
  exact congrFun (preserving_step_heap rom setup[count] _ (setup_noStore _ (List.getElem_mem hcount))) address

theorem test_point {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (rom : PhysicalROM) (heapWords header : Nat) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 8))) (ha : state.halted = false)
    (count : Nat) (hc : count < 2) : Point rom containing heapWords header (packingRun rom containing count state) := by
  have hb : origin + 8 + (testBlock origin).length ≤ containing.length := by have hh := em.bound; rw [programAt_length, testBlock_length] at *; omega
  have hcount : count < (testBlock origin).length := by rwa [testBlock_length]
  refine point_of_phase rom containing (testBlock origin) (origin + 8) heapWords header hb (test_code em) em.words em.pcfit state ha count hcount
    (last_prefix rom containing (testLead origin) (.jumpIfZero .index .old) (origin + 8) hb (test_code em)
      (testLead_straight origin) em.words em.pcfit state hp ha count (by rw [testLead_length]; omega))
    ?_ (test_access rom origin heapWords state count hcount) ?_
  · rw [testBlock, List.take_append_of_le_length (show count ≤ (testLead origin).length by rw [testLead_length]; omega)]
    exact prefix_pc rom (testLead origin) (origin + 8) (testLead_straight origin) state hp count (by rw [testLead_length]; omega)
  · intro address _
    exact congrFun (preserving_step_heap rom (testBlock origin)[count] _ (test_noStore origin _ (List.getElem_mem hcount))) address

theorem body_point {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (rom : PhysicalROM) (q header remaining heapWords : Nat) (state : WordState bits)
    (hroom : Fits bits (header + 16 + 2 * (q + 2))) (halloc : header + 16 + 2 * (q + 2) ≤ heapWords)
    (hr : remaining < q + 2) (hh : state.register .address = BitVec.ofNat bits header)
    (hi : state.register .index = BitVec.ofNat bits (remaining + 1)) (hq : state.register .total = BitVec.ofNat bits (q + 2))
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 10))) (ha : state.halted = false)
    (count : Nat) (hc : count < 13) : Point rom containing heapWords header (packingRun rom containing count state) := by
  have hb : origin + 10 + (bodyBlock origin).length ≤ containing.length := by have hh := em.bound; rw [programAt_length, bodyBlock_length] at *; omega
  have hcount : count < (bodyBlock origin).length := by rwa [bodyBlock_length]
  refine point_of_phase rom containing (bodyBlock origin) (origin + 10) heapWords header hb (body_code em) em.words em.pcfit state ha count hcount
    (last_prefix rom containing (bodyLead origin) (.jumpIfZero .flag .old) (origin + 10) hb (body_code em)
      (bodyLead_straight origin) em.words em.pcfit state hp ha count (by rw [bodyLead_length]; omega))
    ?_ (body_access rom origin q header remaining heapWords state hroom halloc hr hh hi hq count hcount) ?_
  · rw [bodyBlock, List.take_append_of_le_length (show count ≤ (bodyLead origin).length by rw [bodyLead_length]; omega)]
    exact prefix_pc rom (bodyLead origin) (origin + 10) (bodyLead_straight origin) state hp count (by rw [bodyLead_length]; omega)
  · intro address _
    exact congrFun (preserving_step_heap rom (bodyBlock origin)[count] _ (body_noStore origin _ (List.getElem_mem hcount))) address

theorem footer_point {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (rom : PhysicalROM) (header heapWords : Nat) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header) (halloc : header + 8 ≤ heapWords)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 23))) (ha : state.halted = false)
    (count : Nat) (hc : count < 28) : Point rom containing heapWords header (packingRun rom containing count state) := by
  have hb : origin + 23 + footer.length ≤ containing.length := by have hh := em.bound; rw [programAt_length, footer_length] at *; omega
  have hcount : count < footer.length := by rwa [footer_length]
  exact point_of_phase rom containing footer (origin + 23) heapWords header hb (footer_code em) em.words em.pcfit state ha count hcount
    (straight_prefix rom containing footer (origin + 23) hb (footer_code em) footer_straight em.words em.pcfit state hp ha count hcount.le)
    (prefix_pc rom footer (origin + 23) footer_straight state hp count hcount.le)
    (footer_access rom header heapWords state hh halloc count hcount)
    (fun address hprotected => footer_step_frame rom header state hh address hprotected count hcount)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeRanks008
