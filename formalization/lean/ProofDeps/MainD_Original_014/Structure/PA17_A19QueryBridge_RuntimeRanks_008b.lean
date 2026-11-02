module

public import Structure.PA17_A19QueryBridge_RuntimeRanks_008a

/-! Actual fetch/embedding certificates for the four fixed rank phases.
Only the containing program's real code words and finite code addresses are
assumed; every run starts at its actual current PC, without a helper HALT. -/

@[expose] public section
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeRanks008

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments

structure Embedded (bits origin : Nat) (containing : List PackingOp) : Prop where
  bound : origin + (programAt origin).length ≤ containing.length
  code : ∀ i (hi : i < (programAt origin).length),
    containing[origin + i]'(by omega) = (programAt origin)[i]
  words : WordsFit bits (packingCode containing)
  pcfit : Fits bits (5 * containing.length)

theorem middle_get (before block after : List PackingOp) (index : Nat) (hi : index < block.length) :
    (before ++ block ++ after)[before.length + index]'(by simp only [List.length_append]; omega) = block[index] := by
  rw [List.getElem_append_left (by simp only [List.length_append]; omega), List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem phase_code {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (before block after : List PackingOp) (heq : programAt origin = before ++ block ++ after) :
    ∀ i (hi : i < block.length), containing[(origin + before.length) + i]'(by
      have hl := congrArg List.length heq
      have hb := em.bound
      simp only [List.length_append] at hl
      omega) = block[i] := by
  intro i hi
  have hl := congrArg List.length heq
  simp only [List.length_append] at hl
  have hc := em.code (before.length + i) (by omega)
  have hmiddle : (programAt origin)[before.length + i]'(by omega) = block[i] := by
    simpa only [heq] using middle_get before block after i hi
  simpa only [Nat.add_assoc] using hc.trans hmiddle

theorem setup_code {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing) :
    ∀ i (hi : i < setup.length), containing[origin + i]'(by have hb := em.bound; rw [setup_length] at hi; rw [programAt_length] at hb; omega) = setup[i] := by
  have heq : programAt origin = [] ++ setup ++ (testBlock origin ++ bodyBlock origin ++ footer) := by
    simp only [programAt, List.nil_append, List.append_assoc]
  simpa only [List.length_nil, Nat.add_zero] using phase_code em [] setup _ heq

theorem test_code {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing) :
    ∀ i (hi : i < (testBlock origin).length), containing[(origin + 8) + i]'(by
      have hb := em.bound; rw [testBlock_length] at hi; rw [programAt_length] at hb; omega) = (testBlock origin)[i] := by
  have heq : programAt origin = setup ++ testBlock origin ++ (bodyBlock origin ++ footer) := by
    simp only [programAt, List.append_assoc]
  simpa only [setup_length] using phase_code em setup (testBlock origin) _ heq

theorem body_code {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing) :
    ∀ i (hi : i < (bodyBlock origin).length), containing[(origin + 10) + i]'(by
      have hb := em.bound; rw [bodyBlock_length] at hi; rw [programAt_length] at hb; omega) = (bodyBlock origin)[i] := by
  have heq : programAt origin = (setup ++ testBlock origin) ++ bodyBlock origin ++ footer := rfl
  simpa only [List.length_append, setup_length, testBlock_length] using phase_code em (setup ++ testBlock origin) (bodyBlock origin) footer heq

theorem footer_code {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing) :
    ∀ i (hi : i < footer.length), containing[(origin + 23) + i]'(by
      have hb := em.bound; rw [footer_length] at hi; rw [programAt_length] at hb; omega) = footer[i] := by
  have heq : programAt origin = (setup ++ testBlock origin ++ bodyBlock origin) ++ footer ++ [] := by simp [programAt]
  simpa only [List.length_append, setup_length, testBlock_length, bodyBlock_length] using
    phase_code em (setup ++ testBlock origin ++ bodyBlock origin) footer [] heq

theorem fetched_setup {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (rom : PhysicalROM) (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * origin))
    (ha : state.halted = false) : packingRun rom containing 8 state = executeOps rom setup state := by
  simpa only [setup_length] using straight_segment rom containing setup origin
    (by have hb := em.bound; rw [setup_length, programAt_length] at *; omega) (setup_code em)
    setup_straight em.words em.pcfit state hp ha

theorem fetched_test {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (rom : PhysicalROM) (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (origin + 8)))
    (ha : state.halted = false) : packingRun rom containing 2 state = executeOps rom (testBlock origin) state := by
  rw [show 2 = (testLead origin).length + 1 from rfl,
    segment_last rom containing (testLead origin) (.jumpIfZero .index .old) (origin + 8)
      (by have hb := em.bound; rw [testLead_length, programAt_length] at *; omega) ?_ ?_
      (testLead_straight origin) em.words em.pcfit state hp ha,
    testBlock, executeOps_append]
  · rfl
  · intro i hi
    have hc := test_code em i (by rw [testLead_length] at hi; rw [testBlock_length]; omega)
    change i < 1 at hi
    have hzero : i = 0 := by omega
    subst i
    exact hc
  · have hc := test_code em 1 (by rw [testBlock_length]; decide)
    exact hc

theorem fetched_body {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (rom : PhysicalROM) (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (origin + 10)))
    (ha : state.halted = false) : packingRun rom containing 13 state = executeOps rom (bodyBlock origin) state := by
  rw [show 13 = (bodyLead origin).length + 1 from rfl,
    segment_last rom containing (bodyLead origin) (.jumpIfZero .flag .old) (origin + 10)
      (by have hb := em.bound; rw [bodyLead_length, programAt_length] at *; omega) ?_ ?_
      (bodyLead_straight origin) em.words em.pcfit state hp ha,
    bodyBlock, executeOps_append]
  · rfl
  · intro i hi
    have hc := body_code em i (by rw [bodyLead_length] at hi; rw [bodyBlock_length]; omega)
    change i < 12 at hi
    interval_cases i <;> exact hc
  · have hc := body_code em 12 (by rw [bodyBlock_length]; decide)
    exact hc

theorem fetched_footer {bits origin : Nat} {containing : List PackingOp} (em : Embedded bits origin containing)
    (rom : PhysicalROM) (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (origin + 23)))
    (ha : state.halted = false) : packingRun rom containing 28 state = executeOps rom footer state := by
  simpa only [footer_length] using straight_segment rom containing footer (origin + 23)
    (by have hb := em.bound; rw [footer_length, programAt_length] at *; omega) (footer_code em)
    footer_straight em.words em.pcfit state hp ha

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeRanks008
