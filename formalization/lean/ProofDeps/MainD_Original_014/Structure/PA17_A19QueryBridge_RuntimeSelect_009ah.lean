module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009ag

/-! Actual fetched embeddings and the internal state invariant of the ONE
fixed91op descent loop. The stored runtime fuel and node/tool pointers, not
dimensioned code or a precomputed traversal, drive this machine. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem descendBodyLead_straight (origin : Nat) : StraightProgram (descendBodyLead origin) := by
  intro op ho
  simp only [descendBodyLead, List.mem_append] at ho
  rcases ho with (ho | ho) | ho
  · exact descendIndex_straight op ho
  · exact leafReadProgram_straight op ho
  · exact descendTailLead_straight origin op ho

structure DescEmbedded (bits origin : Nat) (containing : List PackingOp) : Prop where
  bound : origin + (descendProgramAt origin).length ≤ containing.length
  code : ∀ i (hi : i < (descendProgramAt origin).length),
    containing[origin + i]'(by omega) = (descendProgramAt origin)[i]
  words : WordsFit bits (packingCode containing)
  pcfit : Fits bits (5 * containing.length)

theorem desc_phase_code {bits origin : Nat} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing)
    (before block after : List PackingOp) (heq : descendProgramAt origin = before ++ block ++ after) :
    ∀ i (hi : i < block.length), containing[(origin + before.length) + i]'(by
      have hl := congrArg List.length heq
      have hb := em.bound
      simp only [List.length_append] at hl
      omega) = block[i] := by
  intro i hi
  have hl := congrArg List.length heq
  simp only [List.length_append] at hl
  have hc := em.code (before.length + i) (by omega)
  have hm : (descendProgramAt origin)[before.length + i]'(by omega) = block[i] := by
    simpa only [heq] using PA17A19RuntimeRanks008.middle_get before block after i hi
  simpa only [Nat.add_assoc] using hc.trans hm

theorem desc_test_code {bits origin : Nat} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing) :
    ∀ i (hi : i < (descendTest origin).length), containing[origin + i]'(by
      have hh := em.bound; rw [descendTest_length] at hi; rw [descendProgramAt_length] at hh; omega) = (descendTest origin)[i] := by
  have he : descendProgramAt origin = [] ++ descendTest origin ++ descendBody origin := by
    simp only [descendProgramAt, List.nil_append]
  simpa only [List.length_nil, Nat.add_zero] using desc_phase_code em [] (descendTest origin) _ he

theorem desc_body_code {bits origin : Nat} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing) :
    ∀ i (hi : i < (descendBody origin).length), containing[(origin + 5) + i]'(by
      have hh := em.bound; rw [descendBody_length] at hi; rw [descendProgramAt_length] at hh; omega) = (descendBody origin)[i] := by
  have he : descendProgramAt origin = descendTest origin ++ descendBody origin ++ [] := by
    simp only [descendProgramAt, List.append_nil]
  simpa only [descendTest_length] using desc_phase_code em (descendTest origin) (descendBody origin) [] he

theorem fetched_desc_test {bits origin : Nat} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    packingRun rom containing 5 state = executeOps rom (descendTest origin) state := by
  rw [show 5 = (descendTestLead origin).length + 1 from rfl,
    segment_last rom containing (descendTestLead origin) (.jumpIfZero .total .old) origin
      (by have hh := em.bound; rw [descendTestLead_length, descendProgramAt_length] at *; omega) ?_ ?_
      (descendTestLead_straight origin) em.words em.pcfit state hp ha,
    descendTest, executeOps_append]
  · rfl
  · intro i hi
    have hc := desc_test_code em i (by rw [descendTestLead_length] at hi; rw [descendTest_length]; omega)
    change i < 4 at hi
    interval_cases i <;> exact hc
  · exact desc_test_code em 4 (by rw [descendTest_length]; decide)

theorem fetched_desc_body {bits origin : Nat} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 5))) (ha : state.halted = false) :
    packingRun rom containing 86 state = executeOps rom (descendBody origin) state := by
  rw [show 86 = (descendBodyLead origin).length + 1 from rfl,
    segment_last rom containing (descendBodyLead origin) (.jumpIfZero .flag .old) (origin + 5)
      (by have hh := em.bound; rw [descendBodyLead_length, descendProgramAt_length] at *; omega) ?_ ?_
      (descendBodyLead_straight origin) em.words em.pcfit state hp ha,
    descendBody, executeOps_append]
  · rfl
  · intro i hi
    have hc := desc_body_code em i (by rw [descendBodyLead_length] at hi; rw [descendBody_length]; omega)
    simpa only [descendBody, List.getElem_append_left hi] using hc
  · exact desc_body_code em 85 (by rw [descendBody_length]; decide)

theorem descendTail_pc {bits : Nat} (rom : PhysicalROM) (origin : Nat) (state : WordState bits) :
    (executeOps rom (descendTail origin) state).pc = BitVec.ofNat bits (5 * origin) := by
  simp +decide [descendTail, descendTailLead, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem descendBody_eq (origin : Nat) : descendBody origin = descendIndex ++ leafReadProgram ++ descendTail origin := by
  simp only [descendBody, descendBodyLead, descendTail, List.append_assoc]

structure DescReady {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (origin capWords header base counts parents size remaining : Nat) (state : WordState bits) : Prop where
  bound : remaining ≤ size
  address : state.register .address = BitVec.ofNat bits header
  fuel : state.heap (BitVec.ofNat bits (header + 13)) = BitVec.ofNat bits remaining
  nodePointer : state.heap (BitVec.ofNat bits (header + 14)) = BitVec.ofNat bits (nodeSlot header q size)
  toolPointer : state.heap (BitVec.ofNat bits (header + 15)) = BitVec.ofNat bits (toolSlot header q size)
  nodeBound : (state.heap (BitVec.ofNat bits (nodeSlot header q size))).toNat ≤ size
  candidates : CandidateBounded header q size state.heap
  pc : state.pc = BitVec.ofNat bits (5 * origin)
  active : state.halted = false
  data : ReverseHeapData full configuration capWords header base counts parents size state.heap

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
