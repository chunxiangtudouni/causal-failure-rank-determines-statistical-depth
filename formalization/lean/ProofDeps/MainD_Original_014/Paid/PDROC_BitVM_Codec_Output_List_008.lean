module

public import Paid.PDROC_BitVM_Codec_Output_List_007

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Codec.OutputList

open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

/-- A canonical word ending TRUE cannot be truncated by the ListBlank
quotient. Extra physical FALSE padding is retained explicitly as suffix. -/
theorem physical_prefix_of_last_true (actual expected : List Bool)
    (last : expected.getLast? = some true)
    (same : ListBlank.mk actual = ListBlank.mk expected) :
    ∃ suffix, actual = expected ++ suffix := by
  have related : BlankRel actual expected := Quotient.exact same
  rcases related with ⟨padding, extension⟩ | ⟨padding, extension⟩
  · cases padding with
    | zero =>
      refine ⟨[], ?_⟩
      simpa only [List.replicate_zero, List.append_nil] using extension.symm
    | succ padding =>
      have wrong : expected.getLast? = some false := by
        rw [extension, List.replicate_succ']
        simp only [← List.append_assoc, List.getLast?_append, List.getLast?_singleton,
          Option.some_or]
        rfl
      rw [last] at wrong
      cases wrong
  · exact ⟨List.replicate padding false, extension⟩

theorem count_word_last (value : ℕ) (positive : value ≠ 0) :
    (encodeNat value).getLast? = some true := by
  change (List.replicate (natBits value) true ++ [false] ++
    PSTRTMNatValue017.rawPayload value).getLast? = some true
  rw [List.getLast?_append, PSTRTMCanonical020.rawPayload_last value positive]
  rfl

/-- A stronger physical result of the same real counter. The zero-emission
case uses its actual literal-zero initializer; it is NOT inferred from
ListBlank equality, which would lose that trailing FALSE payload bit. -/
theorem count_complete_physical (word output ticks : List Bool) (store : CountStore) :
    ∃ (run : List CountState) (after : CountState) (suffix : List Bool),
      run.head? = some (countInitState word output ticks store) ∧
      run.IsChain (fun a b => TM2.step countProgram a = some b) ∧
      run.getLast? = some after ∧ TM2.step countProgram after = none ∧
      after.l = none ∧ countTape after = Tape.mk₁ (encodeNat ticks.length) ∧
      after.stk 0 = encodeNat ticks.length ++ suffix ∧
      after.stk 3 = [] ∧ after.stk 1 = output ∧
      run.length ≤ word.length + 2 + countCost 0 ticks.length := by
  cases ticks with
  | nil =>
    let middle := countInitialized output [] store.1
    let after := countStop middle
    let first := countInitTrace word output [] store
    have pair : [middle, after].IsChain
        (fun a b => TM2.step countProgram a = some b) :=
      List.isChain_cons_cons.mpr ⟨count_gate_nil middle rfl rfl, List.isChain_singleton _⟩
    have chain := PDROC.BitVM.Log.TwoStack.join_chain first [middle, after] middle
      (countInit_chain word output [] store) pair (countInit_last word output [] store) rfl
    refine ⟨first ++ [after], after, [], ?_, chain, ?_, rfl, rfl, ?_, ?_, rfl, rfl, ?_⟩
    · simp only [List.head?_append, first, countInit_head, Option.some_or]
    · exact List.getLast?_append_cons first after []
    · exact countInitialized_tape output [] store.1
    · rfl
    · simp only [List.length_append, List.length_singleton, first, countInit_length,
        List.length_nil, countCost]
      omega
  | cons bit rest =>
    obtain ⟨run, after, head, chain, last, halt, halted, tape, ticks, out, size⟩ :=
      count_complete word output (bit :: rest) store
    have right : ListBlank.mk (after.stk 0) = ListBlank.mk (encodeNat (bit :: rest).length) := by
      have same := congrArg Tape.right₀ tape
      change (Tape.mk₂ (after.stk 2) (after.stk 0)).right₀ =
        (Tape.mk₁ (encodeNat (bit :: rest).length)).right₀ at same
      simpa only [Tape.mk₁, Tape.mk₂, Tape.mk'_right₀] using same
    obtain ⟨suffix, exactWord⟩ := physical_prefix_of_last_true (after.stk 0)
      (encodeNat (bit :: rest).length) (count_word_last _ (by simp only [List.length_cons]; omega)) right
    exact ⟨run, after, suffix, head, chain, last, halt, halted, tape, exactWord, ticks, out, size⟩

end PDROC.BitVM.Codec.OutputList
