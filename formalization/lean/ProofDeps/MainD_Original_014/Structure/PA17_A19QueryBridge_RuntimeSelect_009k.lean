module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009j

/-! Real fetched embedding of the fixed reverse-parent scan. This module
does not pretend the scalar reader preserves any unpromised register.
The body really executes 9+58+24+9 operations before its actual backedge. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

def reverseBodyLead (origin : Nat) : List PackingOp :=
  payloadRead ++ PA17A19RuntimeRead007.cachedProgram ++ pushProgram ++ reverseFootLead origin

def reverseBody (origin : Nat) : List PackingOp := reverseBodyLead origin ++ [.jumpIfZero .flag .old]

theorem reverseBodyLead_length (origin : Nat) : (reverseBodyLead origin).length = 99 := rfl
theorem reverseBody_length (origin : Nat) : (reverseBody origin).length = 100 := rfl

theorem reverseBodyLead_straight (origin : Nat) : StraightProgram (reverseBodyLead origin) := by
  intro op ho
  simp only [reverseBodyLead, List.mem_append] at ho
  rcases ho with ((ho | ho) | ho) | ho
  · exact payloadRead_straight op ho
  · exact PA17A19RuntimeRead007.cachedProgram_straight op ho
  · exact pushProgram_straight op ho
  · exact reverseFootLead_straight origin op ho

theorem reverseProgramAt_eq (origin : Nat) : reverseProgramAt origin = reverseTest origin ++ reverseBody origin := by
  simp only [reverseProgramAt, reverseBody, reverseBodyLead, reverseFoot, List.append_assoc]

structure ReverseEmbedded (bits origin : Nat) (containing : List PackingOp) : Prop where
  bound : origin + (reverseProgramAt origin).length ≤ containing.length
  code : ∀ i (hi : i < (reverseProgramAt origin).length),
    containing[origin + i]'(by omega) = (reverseProgramAt origin)[i]
  words : WordsFit bits (packingCode containing)
  pcfit : Fits bits (5 * containing.length)

theorem reverse_phase_code {bits origin : Nat} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing)
    (before block after : List PackingOp) (heq : reverseProgramAt origin = before ++ block ++ after) :
    ∀ i (hi : i < block.length), containing[(origin + before.length) + i]'(by
      have hl := congrArg List.length heq
      have hb := em.bound
      simp only [List.length_append] at hl
      omega) = block[i] := by
  intro i hi
  have hl := congrArg List.length heq
  simp only [List.length_append] at hl
  have hc := em.code (before.length + i) (by omega)
  have hm : (reverseProgramAt origin)[before.length + i]'(by omega) = block[i] := by
    simpa only [heq] using PA17A19RuntimeRanks008.middle_get before block after i hi
  simpa only [Nat.add_assoc] using hc.trans hm

theorem reverse_test_code {bits origin : Nat} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing) :
    ∀ i (hi : i < (reverseTest origin).length), containing[origin + i]'(by
      have hb := em.bound; rw [reverseTest_length] at hi; rw [reverseProgramAt_length] at hb; omega) = (reverseTest origin)[i] := by
  have he : reverseProgramAt origin = [] ++ reverseTest origin ++ reverseBody origin := by
    simp only [List.nil_append, reverseProgramAt_eq]
  simpa only [List.length_nil, Nat.add_zero] using reverse_phase_code em [] (reverseTest origin) _ he

theorem reverse_body_code {bits origin : Nat} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing) :
    ∀ i (hi : i < (reverseBody origin).length), containing[(origin + 5) + i]'(by
      have hb := em.bound; rw [reverseBody_length] at hi; rw [reverseProgramAt_length] at hb; omega) = (reverseBody origin)[i] := by
  have he : reverseProgramAt origin = reverseTest origin ++ reverseBody origin ++ [] := by
    simp only [List.append_nil, reverseProgramAt_eq]
  simpa only [reverseTest_length] using reverse_phase_code em (reverseTest origin) (reverseBody origin) [] he

theorem fetched_reverse_test {bits origin : Nat} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    packingRun rom containing 5 state = executeOps rom (reverseTest origin) state := by
  rw [show 5 = (reverseTestLead origin).length + 1 from rfl,
    segment_last rom containing (reverseTestLead origin) (.jumpIfZero .total .old) origin
      (by have hb := em.bound; rw [reverseTestLead_length, reverseProgramAt_length] at *; omega) ?_ ?_
      (reverseTestLead_straight origin) em.words em.pcfit state hp ha,
    reverseTest, executeOps_append]
  · rfl
  · intro i hi
    have hc := reverse_test_code em i (by rw [reverseTestLead_length] at hi; rw [reverseTest_length]; omega)
    change i < 4 at hi
    interval_cases i <;> exact hc
  · exact reverse_test_code em 4 (by rw [reverseTest_length]; decide)

theorem fetched_reverse_body {bits origin : Nat} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 5))) (ha : state.halted = false) :
    packingRun rom containing 100 state = executeOps rom (reverseBody origin) state := by
  rw [show 100 = (reverseBodyLead origin).length + 1 from rfl,
    segment_last rom containing (reverseBodyLead origin) (.jumpIfZero .flag .old) (origin + 5)
      (by have hb := em.bound; rw [reverseBodyLead_length, reverseProgramAt_length] at *; omega) ?_ ?_
      (reverseBodyLead_straight origin) em.words em.pcfit state hp ha,
    reverseBody, executeOps_append]
  · rfl
  · intro i hi
    have hc := reverse_body_code em i (by rw [reverseBodyLead_length] at hi; rw [reverseBody_length]; omega)
    simpa only [reverseBody, List.getElem_append_left hi] using hc
  · exact reverse_body_code em 99 (by rw [reverseBody_length]; decide)

theorem reverseFoot_pc {bits : Nat} (rom : PhysicalROM) (origin : Nat) (state : WordState bits) :
    (executeOps rom (reverseFoot origin) state).pc = BitVec.ofNat bits (5 * origin) := by
  simp +decide [reverseFoot, reverseFootLead, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem reverseBody_pc {bits : Nat} (rom : PhysicalROM) (origin : Nat) (state : WordState bits) :
    (executeOps rom (reverseBody origin) state).pc = BitVec.ofNat bits (5 * origin) := by
  have he : reverseBody origin = payloadRead ++ PA17A19RuntimeRead007.cachedProgram ++ pushProgram ++ reverseFoot origin := by
    simp only [reverseBody, reverseBodyLead, reverseFoot, List.append_assoc]
  rw [he, executeOps_append]
  exact reverseFoot_pc rom origin _

theorem fetched_reverse_iteration {bits origin : Nat} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing) (rom : PhysicalROM) (header remaining : Nat) (state : WordState bits)
    (hr : Fits bits (remaining + 1)) (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (hnode : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits (remaining + 1)) :
    let after := packingRun rom containing 105 state
    after = executeOps rom (reverseBody origin) (executeOps rom (reverseTest origin) state) ∧
      after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * origin) := by
  have ht := reverseTest_result rom origin header (remaining + 1) state hr hh hp hnode
  have hbody : (executeOps rom (reverseTest origin) state).pc = BitVec.ofNat bits (5 * (origin + 5)) := by
    simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false] using ht.1
  have hrun : packingRun rom containing 105 state = executeOps rom (reverseBody origin) (executeOps rom (reverseTest origin) state) := by
    rw [show 105 = 5 + 100 from rfl, run_add, fetched_reverse_test em rom state hp ha]
    exact fetched_reverse_body em rom _ hbody (by rw [executeOps_halted, ha])
  dsimp only
  refine ⟨hrun, ?_, ?_⟩
  · rw [hrun, executeOps_halted, executeOps_halted, ha]
  · rw [hrun, reverseBody_pc]

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
