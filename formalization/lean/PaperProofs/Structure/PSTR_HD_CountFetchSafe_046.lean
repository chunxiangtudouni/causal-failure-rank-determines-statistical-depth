module

public import PaperProofs.Structure.PSTR_HD_CountBranchSafe_045

/-! Prefix fetch safety for the four fixed phases in the one containing code. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

section Phases

variable {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (origin heapWords : Nat)
    (region : Nat → Prop)
    (hbound : origin + (programAt origin).length ≤ containing.length)
    (hcode : ∀ i (hi : i < (programAt origin).length), containing[origin + i]'(kernel_index_bound containing origin hbound i hi) = (programAt origin)[i])
    (hwords : WordsFit bits (packingCode containing)) (hpcfit : Fits bits (5 * containing.length))
    (state : WordState bits)

include hbound hcode hwords hpcfit

theorem setup_fetch_safe (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (safe : PrefixOK rom heapWords region setup state) (count : Nat) (hc : count < 121) :
    AtSafe rom containing heapWords (packingRun rom containing count state) ∧
      HeapFrame region state.heap (packingRun rom containing count state).heap := by
  exact straight_prefix_safe rom containing setup heapWords origin region
    (by rw [programAt_length] at hbound; rw [setup_length]; omega)
    (setup_code containing origin hbound hcode) setup_straight hwords hpcfit state hp ha safe count hc

theorem test_fetch_safe (hp : state.pc = BitVec.ofNat bits (5 * (origin + 121))) (ha : state.halted = false)
    (safe : PrefixOK rom heapWords region (testLead origin) state) (count : Nat) (hc : count < 28) :
    AtSafe rom containing heapWords (packingRun rom containing count state) ∧
      HeapFrame region state.heap (packingRun rom containing count state).heap := by
  apply branch_prefix_safe rom containing (testLead origin) heapWords (origin + 121) region
    (by rw [programAt_length] at hbound; rw [testLead_length]; omega) ?_ ?_
    (testLead_straight origin) hwords hpcfit state hp ha safe count (by rw [testLead_length]; omega)
  · intro i hi
    have hd := test_code containing origin hbound hcode i (by rw [testBlock_length]; rw [testLead_length] at hi; omega)
    have hg : (testBlock origin)[i]'(by rw [testBlock_length]; rw [testLead_length] at hi; omega) = (testLead origin)[i] := by
      change (testLead origin ++ [.jumpIfZero .flag .total])[i]'(by simp only [List.length_append, List.length_cons, List.length_nil]; omega) = _
      exact List.getElem_append_left hi
    exact hd.trans hg
  · have hd := test_code containing origin hbound hcode (testLead origin).length (by rw [testBlock_length, testLead_length]; decide)
    have hg : (testBlock origin)[(testLead origin).length]'(by rw [testBlock_length, testLead_length]; decide) = .jumpIfZero .flag .total := by
      change (testLead origin ++ [.jumpIfZero .flag .total])[(testLead origin).length]'(by simp) = _
      exact List.getElem_append_right' (testLead origin) (l₂ := [.jumpIfZero .flag .total]) (i := 0) (by decide)
    exact hd.trans hg

theorem body_fetch_safe (hp : state.pc = BitVec.ofNat bits (5 * (origin + 149))) (ha : state.halted = false)
    (safe : PrefixOK rom heapWords region (bodyLead origin) state) (count : Nat) (hc : count < 86) :
    AtSafe rom containing heapWords (packingRun rom containing count state) ∧
      HeapFrame region state.heap (packingRun rom containing count state).heap := by
  apply branch_prefix_safe rom containing (bodyLead origin) heapWords (origin + 149) region
    (by rw [programAt_length] at hbound; rw [bodyLead_length]; omega) ?_ ?_
    (bodyLead_straight origin) hwords hpcfit state hp ha safe count (by rw [bodyLead_length]; omega)
  · intro i hi
    have hd := body_code containing origin hbound hcode i (by rw [bodyBlock_length]; rw [bodyLead_length] at hi; omega)
    have hg : (bodyBlock origin)[i]'(by rw [bodyBlock_length]; rw [bodyLead_length] at hi; omega) = (bodyLead origin)[i] := by
      change (bodyLead origin ++ [.jumpIfZero .flag .total])[i]'(by simp only [List.length_append, List.length_cons, List.length_nil]; omega) = _
      exact List.getElem_append_left hi
    exact hd.trans hg
  · have hd := body_code containing origin hbound hcode (bodyLead origin).length (by rw [bodyBlock_length, bodyLead_length]; decide)
    have hg : (bodyBlock origin)[(bodyLead origin).length]'(by rw [bodyBlock_length, bodyLead_length]; decide) = .jumpIfZero .flag .total := by
      change (bodyLead origin ++ [.jumpIfZero .flag .total])[(bodyLead origin).length]'(by simp) = _
      exact List.getElem_append_right' (bodyLead origin) (l₂ := [.jumpIfZero .flag .total]) (i := 0) (by decide)
    exact hd.trans hg

theorem footer_fetch_safe (hp : state.pc = BitVec.ofNat bits (5 * (origin + 235))) (ha : state.halted = false)
    (safe : PrefixOK rom heapWords region footer state) (count : Nat) (hc : count < 35) :
    AtSafe rom containing heapWords (packingRun rom containing count state) ∧
      HeapFrame region state.heap (packingRun rom containing count state).heap := by
  exact straight_prefix_safe rom containing footer heapWords (origin + 235) region
    (by rw [programAt_length] at hbound; rw [footer_length]; omega)
    (footer_code containing origin hbound hcode) footer_straight hwords hpcfit state hp ha safe count hc

end Phases

end PaperProofs.Structure.LaminarTree.PSTRCountKernel
