module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009v

/-! Embedding and local facts for the complete fixed164op parent-building
kernel. The actual21 clear and38 initialization run before the real reverse
loop; no scratch/header8..12 content is assumed already prepared. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

structure ParentEmbedded (bits origin : Nat) (containing : List PackingOp) : Prop where
  bound : origin + (parentProgramAt origin).length ≤ containing.length
  code : ∀ i (hi : i < (parentProgramAt origin).length),
    containing[origin + i]'(by omega) = (parentProgramAt origin)[i]
  words : WordsFit bits (packingCode containing)
  pcfit : Fits bits (5 * containing.length)

theorem parent_phase_code {bits origin : Nat} {containing : List PackingOp}
    (em : ParentEmbedded bits origin containing)
    (before block after : List PackingOp) (heq : parentProgramAt origin = before ++ block ++ after) :
    ∀ i (hi : i < block.length), containing[(origin + before.length) + i]'(by
      have hl := congrArg List.length heq
      have hb := em.bound
      simp only [List.length_append] at hl
      omega) = block[i] := by
  intro i hi
  have hl := congrArg List.length heq
  simp only [List.length_append] at hl
  have hc := em.code (before.length + i) (by omega)
  have hm : (parentProgramAt origin)[before.length + i]'(by omega) = block[i] := by
    simpa only [heq] using PA17A19RuntimeRanks008.middle_get before block after i hi
  simpa only [Nat.add_assoc] using hc.trans hm

theorem parent_clear_embedded {bits origin : Nat} {containing : List PackingOp}
    (em : ParentEmbedded bits origin containing) : ClearEmbedded bits origin containing := by
  refine ⟨by have hh := em.bound; rw [parentProgramAt_length, clearProgramAt_length] at *; omega, ?_, em.words, em.pcfit⟩
  have he : parentProgramAt origin = [] ++ clearProgramAt origin ++ (preparePush ++ reverseProgramAt (origin + 59)) := by
    simp only [parentProgramAt, List.nil_append, List.append_assoc]
  simpa only [List.length_nil, Nat.add_zero] using parent_phase_code em [] (clearProgramAt origin) _ he

theorem parent_prepare_code {bits origin : Nat} {containing : List PackingOp}
    (em : ParentEmbedded bits origin containing) :
    ∀ i (hi : i < preparePush.length), containing[(origin + 21) + i]'(by
      have hh := em.bound; rw [parentProgramAt_length] at hh; rw [preparePush_length] at hi; omega) = preparePush[i] := by
  have he : parentProgramAt origin = clearProgramAt origin ++ preparePush ++ reverseProgramAt (origin + 59) := rfl
  simpa only [clearProgramAt_length] using parent_phase_code em (clearProgramAt origin) preparePush _ he

theorem parent_reverse_embedded {bits origin : Nat} {containing : List PackingOp}
    (em : ParentEmbedded bits origin containing) : ReverseEmbedded bits (origin + 59) containing := by
  refine ⟨by have hh := em.bound; rw [parentProgramAt_length, reverseProgramAt_length] at *; omega, ?_, em.words, em.pcfit⟩
  have he : parentProgramAt origin = (clearProgramAt origin ++ preparePush) ++ reverseProgramAt (origin + 59) ++ [] := by
    simp only [parentProgramAt, List.append_nil]
  simpa only [List.length_append, clearProgramAt_length, preparePush_length] using
    parent_phase_code em (clearProgramAt origin ++ preparePush) (reverseProgramAt (origin + 59)) [] he

theorem fetched_parent_prepare {bits origin : Nat} {containing : List PackingOp}
    (em : ParentEmbedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 21))) (ha : state.halted = false) :
    packingRun rom containing 38 state = executeOps rom preparePush state := by
  simpa only [preparePush_length] using straight_segment rom containing preparePush (origin + 21)
    (by have hh := em.bound; rw [parentProgramAt_length, preparePush_length] at *; omega)
    (parent_prepare_code em) preparePush_straight em.words em.pcfit state hp ha

theorem preparePush_actual_frame {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp)
    (origin header heapWords : Nat) (state : WordState bits)
    (hbound : origin + preparePush.length ≤ containing.length)
    (hcode : ∀ i (hi : i < preparePush.length), containing[origin + i]'(by omega) = preparePush[i])
    (hw : WordsFit bits (packingCode containing)) (hpc : Fits bits (5 * containing.length))
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (h1 : Fits bits 1) (hh : state.register .address = BitVec.ofNat bits header)
    (hinput : 1 < rom.input.length) (halloc : header + 12 < heapWords)
    (clock : Nat) (hc : clock ≤ 38) (address : BitVec bits) (hprotect : ClearProtected (header + 8) 5 address) :
    (packingRun rom containing clock state).heap address = state.heap address := by
  induction clock with
  | zero => rfl
  | succ clock ih =>
    have hcl : clock < preparePush.length := by rw [preparePush_length]; omega
    have point := preparePush_actual_point rom containing origin header heapWords state hbound hcode hw hpc hp ha
      h1 hh hinput halloc clock hcl
    rcases point with ⟨hactive, index, hi, hpcNat, _, _, hframe⟩
    rw [packingRun_succ, packingStep_of_index rom containing _ index hi hw hpcNat hactive]
    exact (hframe address hprotect).trans (ih (by omega))

theorem preparedPushHeap_cells {bits : Nat} (q size header row budget : Nat) (heap : BitVec bits → BitVec bits)
    (hroom : Fits bits (header + 13)) :
    let fresh := preparedPushHeap q size header row budget heap
    fresh (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits size ∧
      fresh (BitVec.ofNat bits (header + 9)) = BitVec.ofNat bits (row + budget * (size + 1) + 1) ∧
      fresh (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits (childBase header q) ∧
      fresh (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits (header - (size + (size + 1))) ∧
      fresh (BitVec.ofNat bits (header + 12)) = BitVec.ofNat bits (header - (size + 1)) := by
  have he (i j : Nat) (hi : i ≤ 12) (hj : j ≤ 12) :
      BitVec.ofNat bits (header + i) = BitVec.ofNat bits (header + j) ↔ i = j := by
    rw [ofNat_injective_of_fit _ _ ((show header + i ≤ header + 13 by omega).trans_lt hroom)
      ((show header + j ≤ header + 13 by omega).trans_lt hroom)]
    omega
  simp +decide (disch := omega) [preparedPushHeap, Function.update_apply, he]

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
