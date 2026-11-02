module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009a

/-! The fixed clear loop is embedded at its actual containing-code PC.
There is no helper HALT, PC reset, or dimension-dependent instruction list. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

structure ClearEmbedded (bits origin : Nat) (containing : List PackingOp) : Prop where
  bound : origin + (clearProgramAt origin).length ≤ containing.length
  code : ∀ i (hi : i < (clearProgramAt origin).length),
    containing[origin + i]'(by omega) = (clearProgramAt origin)[i]
  words : WordsFit bits (packingCode containing)
  pcfit : Fits bits (5 * containing.length)

theorem clear_phase_code {bits origin : Nat} {containing : List PackingOp}
    (em : ClearEmbedded bits origin containing)
    (before block after : List PackingOp) (heq : clearProgramAt origin = before ++ block ++ after) :
    ∀ i (hi : i < block.length), containing[(origin + before.length) + i]'(by
      have hl := congrArg List.length heq
      have hb := em.bound
      simp only [List.length_append] at hl
      omega) = block[i] := by
  intro i hi
  have hl := congrArg List.length heq
  simp only [List.length_append] at hl
  have hc := em.code (before.length + i) (by omega)
  have hm : (clearProgramAt origin)[before.length + i]'(by omega) = block[i] := by
    simpa only [heq] using PA17A19RuntimeRanks008.middle_get before block after i hi
  simpa only [Nat.add_assoc] using hc.trans hm

theorem clear_setup_code {bits origin : Nat} {containing : List PackingOp}
    (em : ClearEmbedded bits origin containing) :
    ∀ i (hi : i < clearSetup.length), containing[origin + i]'(by
      have hb := em.bound; rw [clearSetup_length] at hi; rw [clearProgramAt_length] at hb; omega) = clearSetup[i] := by
  have he : clearProgramAt origin = [] ++ clearSetup ++ (clearTest origin ++ clearBody origin) := by
    simp only [clearProgramAt, List.nil_append, List.append_assoc]
  simpa only [List.length_nil, Nat.add_zero] using clear_phase_code em [] clearSetup _ he

theorem clear_test_code {bits origin : Nat} {containing : List PackingOp}
    (em : ClearEmbedded bits origin containing) :
    ∀ i (hi : i < (clearTest origin).length), containing[(origin + 14) + i]'(by
      have hb := em.bound; rw [clearTest_length] at hi; rw [clearProgramAt_length] at hb; omega) = (clearTest origin)[i] := by
  have he : clearProgramAt origin = clearSetup ++ clearTest origin ++ clearBody origin := rfl
  simpa only [clearSetup_length] using clear_phase_code em clearSetup (clearTest origin) _ he

theorem clear_body_code {bits origin : Nat} {containing : List PackingOp}
    (em : ClearEmbedded bits origin containing) :
    ∀ i (hi : i < (clearBody origin).length), containing[(origin + 16) + i]'(by
      have hb := em.bound; rw [clearBody_length] at hi; rw [clearProgramAt_length] at hb; omega) = (clearBody origin)[i] := by
  have he : clearProgramAt origin = (clearSetup ++ clearTest origin) ++ clearBody origin ++ [] := by
    simp only [clearProgramAt, List.append_nil]
  simpa only [List.length_append, clearSetup_length, clearTest_length] using
    clear_phase_code em (clearSetup ++ clearTest origin) (clearBody origin) [] he

theorem fetched_clear_setup {bits origin : Nat} {containing : List PackingOp}
    (em : ClearEmbedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    packingRun rom containing 14 state = executeOps rom clearSetup state := by
  simpa only [clearSetup_length] using straight_segment rom containing clearSetup origin
    (by have hb := em.bound; rw [clearSetup_length, clearProgramAt_length] at *; omega)
    (clear_setup_code em) clearSetup_straight em.words em.pcfit state hp ha

theorem fetched_clear_test {bits origin : Nat} {containing : List PackingOp}
    (em : ClearEmbedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 14))) (ha : state.halted = false) :
    packingRun rom containing 2 state = executeOps rom (clearTest origin) state := by
  rw [show 2 = (clearTestLead origin).length + 1 from rfl,
    segment_last rom containing (clearTestLead origin) (.jumpIfZero .total .old) (origin + 14)
      (by have hb := em.bound; rw [clearTestLead_length, clearProgramAt_length] at *; omega) ?_ ?_
      (clearTestLead_straight origin) em.words em.pcfit state hp ha,
    clearTest, executeOps_append]
  · rfl
  · intro i hi
    have hc := clear_test_code em i (by rw [clearTestLead_length] at hi; rw [clearTest_length]; omega)
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst i
    exact hc
  · exact clear_test_code em 1 (by rw [clearTest_length]; decide)

theorem fetched_clear_body {bits origin : Nat} {containing : List PackingOp}
    (em : ClearEmbedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 16))) (ha : state.halted = false) :
    packingRun rom containing 5 state = executeOps rom (clearBody origin) state := by
  rw [show 5 = (clearBodyLead origin).length + 1 from rfl,
    segment_last rom containing (clearBodyLead origin) (.jumpIfZero .value .old) (origin + 16)
      (by have hb := em.bound; rw [clearBodyLead_length, clearProgramAt_length] at *; omega) ?_ ?_
      (clearBodyLead_straight origin) em.words em.pcfit state hp ha,
    clearBody, executeOps_append]
  · rfl
  · intro i hi
    have hc := clear_body_code em i (by rw [clearBodyLead_length] at hi; rw [clearBody_length]; omega)
    change i < 4 at hi
    interval_cases i <;> exact hc
  · exact clear_body_code em 4 (by rw [clearBody_length]; decide)

theorem clear_test_register {bits : Nat} (rom : PhysicalROM) (origin : Nat) (state : WordState bits)
    (register : Register) (hne : register ≠ .old) :
    (executeOps rom (clearTest origin) state).register register = state.register register := by
  cases register <;> try rfl
  exact False.elim (hne rfl)

theorem clear_test_result {bits : Nat} (rom : PhysicalROM) (origin remaining : Nat) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 14)))
    (ht : state.register .total = BitVec.ofNat bits remaining) (hr : Fits bits remaining) :
    (executeOps rom (clearTest origin) state).pc =
      BitVec.ofNat bits (if remaining = 0 then 5 * (origin + 21) else 5 * (origin + 16)) ∧
    (executeOps rom (clearTest origin) state).heap = state.heap := by
  simp +decide [clearTest, clearTestLead, executeOps, packingExecuteOp, wordOp, wordInstruction,
    hp, ht, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr, BitVec.ofNat_add_ofNat]
  split <;> rename_i hh
  · rfl
  · congr 1

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
