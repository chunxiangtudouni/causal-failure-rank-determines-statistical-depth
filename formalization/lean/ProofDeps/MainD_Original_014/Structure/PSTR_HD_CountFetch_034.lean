module

public import Structure.PSTR_HD_CountSpec_033

/-! The four fixed node-kernel phases are fetched from one containing code
array. Jumps target real encoded positions; no host invocation or intermediate
HALT is inserted between the setup, test, child body and footer. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments

def testBlock (origin : Nat) : List PackingOp := testLead origin ++ [.jumpIfZero .flag .total]
def bodyBlock (origin : Nat) : List PackingOp := bodyLead origin ++ [.jumpIfZero .flag .total]

theorem testBlock_length (origin : Nat) : (testBlock origin).length = 28 := rfl
theorem bodyBlock_length (origin : Nat) : (bodyBlock origin).length = 86 := rfl

theorem middle_get (before block after : List PackingOp) (index : Nat) (hi : index < block.length) :
    (before ++ block ++ after)[before.length + index]'(by simp only [List.length_append]; omega) = block[index] := by
  rw [List.getElem_append_left (by simp only [List.length_append]; omega),
    List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem code_slice (containing before block after : List PackingOp) (origin : Nat)
    (heq : programAt origin = before ++ block ++ after)
    (hbound : origin + (programAt origin).length ≤ containing.length)
    (hcode : ∀ i (hi : i < (programAt origin).length), containing[origin + i]'(by omega) = (programAt origin)[i]) :
    ∀ i (hi : i < block.length), containing[(origin + before.length) + i]'(by
      have hl := congrArg List.length heq
      simp only [List.length_append] at hl
      omega) = block[i] := by
  intro i hi
  have hl := congrArg List.length heq
  simp only [List.length_append] at hl
  have hc := hcode (before.length + i) (by omega)
  have hg := congrArg (fun ops : List PackingOp =>
    ops.getD (before.length + i) (.base (.base (.constant .value 0)))) heq
  rw [List.getD_eq_getElem (n := before.length + i) (programAt origin) (.base (.base (.constant .value 0))) (by omega),
    List.getD_eq_getElem (n := before.length + i) (before ++ block ++ after) (.base (.base (.constant .value 0)))
      (by simp only [List.length_append]; omega)] at hg
  have result := hc.trans (hg.trans (middle_get before block after i hi))
  simpa only [Nat.add_assoc] using result

theorem setup_code (containing : List PackingOp) (origin : Nat)
    (hbound : origin + (programAt origin).length ≤ containing.length)
    (hcode : ∀ i (hi : i < (programAt origin).length), containing[origin + i]'(by omega) = (programAt origin)[i]) :
    ∀ i (hi : i < setup.length), containing[origin + i]'(by rw [programAt_length, setup_length] at *; omega) = setup[i] := by
  have heq : programAt origin = [] ++ setup ++ (testBlock origin ++ bodyBlock origin ++ footer) := by
    simp only [programAt, testBlock, bodyBlock, List.nil_append, List.append_assoc]
  have hc := code_slice containing [] setup (testBlock origin ++ bodyBlock origin ++ footer) origin heq hbound hcode
  simpa only [List.length_nil, Nat.add_zero] using hc

theorem test_code (containing : List PackingOp) (origin : Nat)
    (hbound : origin + (programAt origin).length ≤ containing.length)
    (hcode : ∀ i (hi : i < (programAt origin).length), containing[origin + i]'(by omega) = (programAt origin)[i]) :
    ∀ i (hi : i < (testBlock origin).length), containing[(origin + 121) + i]'(by
      rw [programAt_length, testBlock_length] at *; omega) = (testBlock origin)[i] := by
  have heq : programAt origin = setup ++ testBlock origin ++ (bodyBlock origin ++ footer) := by
    simp only [programAt, testBlock, bodyBlock, List.append_assoc]
  have hc := code_slice containing setup (testBlock origin) (bodyBlock origin ++ footer) origin heq hbound hcode
  simpa only [setup_length] using hc

theorem body_code (containing : List PackingOp) (origin : Nat)
    (hbound : origin + (programAt origin).length ≤ containing.length)
    (hcode : ∀ i (hi : i < (programAt origin).length), containing[origin + i]'(by omega) = (programAt origin)[i]) :
    ∀ i (hi : i < (bodyBlock origin).length), containing[(origin + 149) + i]'(by
      rw [programAt_length, bodyBlock_length] at *; omega) = (bodyBlock origin)[i] := by
  have heq : programAt origin = (setup ++ testBlock origin) ++ bodyBlock origin ++ footer := by
    simp only [programAt, testBlock, bodyBlock, List.append_assoc]
  have hc := code_slice containing (setup ++ testBlock origin) (bodyBlock origin) footer origin heq hbound hcode
  simpa only [List.length_append, setup_length, testBlock_length] using hc

theorem footer_code (containing : List PackingOp) (origin : Nat)
    (hbound : origin + (programAt origin).length ≤ containing.length)
    (hcode : ∀ i (hi : i < (programAt origin).length), containing[origin + i]'(by omega) = (programAt origin)[i]) :
    ∀ i (hi : i < footer.length), containing[(origin + 235) + i]'(by
      rw [programAt_length, footer_length] at *; omega) = footer[i] := by
  have heq : programAt origin = (setup ++ testBlock origin ++ bodyBlock origin) ++ footer ++ [] := by
    simp only [programAt, testBlock, bodyBlock, List.append_assoc, List.append_nil]
  have hc := code_slice containing (setup ++ testBlock origin ++ bodyBlock origin) footer [] origin heq hbound hcode
  simpa only [List.length_append, setup_length, testBlock_length, bodyBlock_length] using hc

theorem fetched_setup {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (origin : Nat)
    (hbound : origin + (programAt origin).length ≤ containing.length)
    (hcode : ∀ i (hi : i < (programAt origin).length), containing[origin + i]'(by omega) = (programAt origin)[i])
    (hwords : WordsFit bits (packingCode containing)) (hpcfit : Fits bits (5 * containing.length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    packingRun rom containing 121 state = executeOps rom setup state := by
  exact straight_segment rom containing setup origin (by rw [programAt_length, setup_length] at *; omega)
    (setup_code containing origin hbound hcode) setup_straight hwords hpcfit state hpc ha

theorem fetched_test {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (origin : Nat)
    (hbound : origin + (programAt origin).length ≤ containing.length)
    (hcode : ∀ i (hi : i < (programAt origin).length), containing[origin + i]'(by omega) = (programAt origin)[i])
    (hwords : WordsFit bits (packingCode containing)) (hpcfit : Fits bits (5 * containing.length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * (origin + 121))) (ha : state.halted = false) :
    packingRun rom containing 28 state =
      packingExecuteOp rom (.jumpIfZero .flag .total) (executeOps rom (testLead origin) state) := by
  apply segment_last rom containing (testLead origin) (.jumpIfZero .flag .total) (origin + 121)
    (by rw [programAt_length, testLead_length] at *; omega) ?_ ?_
    (testLead_straight origin) hwords hpcfit state hpc ha
  · intro i hi
    have hc := test_code containing origin hbound hcode i (by rw [testBlock_length]; rw [testLead_length] at hi; omega)
    have hg : (testBlock origin)[i]'(by rw [testBlock_length]; rw [testLead_length] at hi; omega) = (testLead origin)[i] := by
      change (testLead origin ++ [.jumpIfZero .flag .total])[i]'(by simp only [List.length_append, List.length_cons, List.length_nil]; omega) = _
      exact List.getElem_append_left hi
    exact hc.trans hg
  · have hc := test_code containing origin hbound hcode (testLead origin).length (by rw [testBlock_length, testLead_length]; decide)
    have hg : (testBlock origin)[(testLead origin).length]'(by rw [testBlock_length, testLead_length]; decide) = .jumpIfZero .flag .total := by
      change (testLead origin ++ [.jumpIfZero .flag .total])[(testLead origin).length]'(by simp) = _
      exact List.getElem_append_right' (testLead origin) (l₂ := [.jumpIfZero .flag .total]) (i := 0) (by decide)
    exact hc.trans hg

theorem fetched_body {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (origin : Nat)
    (hbound : origin + (programAt origin).length ≤ containing.length)
    (hcode : ∀ i (hi : i < (programAt origin).length), containing[origin + i]'(by omega) = (programAt origin)[i])
    (hwords : WordsFit bits (packingCode containing)) (hpcfit : Fits bits (5 * containing.length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * (origin + 149))) (ha : state.halted = false) :
    packingRun rom containing 86 state =
      packingExecuteOp rom (.jumpIfZero .flag .total) (executeOps rom (bodyLead origin) state) := by
  apply segment_last rom containing (bodyLead origin) (.jumpIfZero .flag .total) (origin + 149)
    (by rw [programAt_length, bodyLead_length] at *; omega) ?_ ?_
    (bodyLead_straight origin) hwords hpcfit state hpc ha
  · intro i hi
    have hc := body_code containing origin hbound hcode i (by rw [bodyBlock_length]; rw [bodyLead_length] at hi; omega)
    have hg : (bodyBlock origin)[i]'(by rw [bodyBlock_length]; rw [bodyLead_length] at hi; omega) = (bodyLead origin)[i] := by
      change (bodyLead origin ++ [.jumpIfZero .flag .total])[i]'(by simp only [List.length_append, List.length_cons, List.length_nil]; omega) = _
      exact List.getElem_append_left hi
    exact hc.trans hg
  · have hc := body_code containing origin hbound hcode (bodyLead origin).length (by rw [bodyBlock_length, bodyLead_length]; decide)
    have hg : (bodyBlock origin)[(bodyLead origin).length]'(by rw [bodyBlock_length, bodyLead_length]; decide) = .jumpIfZero .flag .total := by
      change (bodyLead origin ++ [.jumpIfZero .flag .total])[(bodyLead origin).length]'(by simp) = _
      exact List.getElem_append_right' (bodyLead origin) (l₂ := [.jumpIfZero .flag .total]) (i := 0) (by decide)
    exact hc.trans hg

theorem fetched_footer {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (origin : Nat)
    (hbound : origin + (programAt origin).length ≤ containing.length)
    (hcode : ∀ i (hi : i < (programAt origin).length), containing[origin + i]'(by omega) = (programAt origin)[i])
    (hwords : WordsFit bits (packingCode containing)) (hpcfit : Fits bits (5 * containing.length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * (origin + 235))) (ha : state.halted = false) :
    packingRun rom containing 35 state = executeOps rom footer state := by
  exact straight_segment rom containing footer (origin + 235) (by rw [programAt_length, footer_length] at *; omega)
    (footer_code containing origin hbound hcode) footer_straight hwords hpcfit state hpc ha

end PaperProofs.Structure.LaminarTree.PSTRCountKernel
