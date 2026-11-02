module

public import Paid.PDROC_BitVM_Codec_Output_List_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Codec.OutputList

open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

def countCost (value remaining : ℕ) : ℕ :=
  (remaining + 1) * (512 * (value + remaining + 2) ^ 2 + 4)

theorem countStop_tape (before : CountState) : countTape (countStop before) = countTape before := by
  change Tape.mk₂ ((Function.update before.stk 3 []) 2)
    ((Function.update before.stk 3 []) 0) = Tape.mk₂ (before.stk 2) (before.stk 0)
  simp only [Function.update_of_ne (by decide : (2 : EmitStack) ≠ 3),
    Function.update_of_ne (by decide : (0 : EmitStack) ≠ 3)]

/-- Iterate by actual tick pops. The induction variable specifies already
present DATA; it is absent from the fixed transition function. In particular
there is no count/fuel/width oracle supplied to the machine. -/
theorem count_loop (ticks : List Bool) (before : CountState) (value : ℕ)
    (position : before.l = some 0) (actualTicks : before.stk 3 = ticks)
    (tape : countTape before = Tape.mk₁ (encodeNat value)) :
    ∃ (run : List CountState) (after : CountState),
      run.head? = some before ∧
      run.IsChain (fun a b => TM2.step countProgram a = some b) ∧
      run.getLast? = some after ∧ TM2.step countProgram after = none ∧
      after.l = none ∧ countTape after = Tape.mk₁ (encodeNat (value + ticks.length)) ∧
      after.stk 3 = [] ∧ after.stk 1 = before.stk 1 ∧
      run.length ≤ countCost value ticks.length := by
  induction ticks generalizing before value with
  | nil =>
    have pair : [before, countStop before].IsChain
        (fun a b => TM2.step countProgram a = some b) :=
      List.isChain_cons_cons.mpr ⟨count_gate_nil before position actualTicks,
        List.isChain_singleton _⟩
    refine ⟨[before, countStop before], countStop before, rfl, pair, rfl, rfl, rfl,
      ?_, ?_, ?_, ?_⟩
    · simpa only [List.length_nil, Nat.add_zero] using (countStop_tape before).trans tape
    · rfl
    · rfl
    · simp only [List.length_cons, List.length_nil, countCost]
      omega
  | cons bit rest ih =>
    obtain ⟨first, middle, firstHead, firstChain, firstLast, middlePosition,
      middleTape, middleTicks, middleOutput, firstSize⟩ :=
      count_iteration before value bit rest position actualTicks tape
    obtain ⟨second, after, secondHead, secondChain, secondLast, halt, halted,
      afterTape, afterTicks, afterOutput, secondSize⟩ :=
      ih middle (value + 1) middlePosition middleTicks middleTape
    have actual := PDROC.BitVM.Log.TwoStack.join_chain
      first second middle firstChain secondChain firstLast secondHead
    have last : (first ++ second.tail).getLast? = some after := by
      have notOne : second.length ≠ 1 := by
        intro one
        have oneList : second = [middle] := by
          cases second with
          | nil => simp only [List.head?_nil, reduceCtorEq] at secondHead
          | cons head tail =>
            have same : head = middle := Option.some.inj secondHead
            have empty : tail = [] := List.length_eq_zero_iff.mp (by simpa [List.length_cons] using one)
            subst head
            subst tail
            rfl
        have equal : middle = after := Option.some.inj (by simpa only [oneList,
          List.getLast?_singleton] using secondLast)
        rw [← equal] at halted
        rw [middlePosition] at halted
        cases halted
      simp only [List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte,
        secondLast, Option.some_or]
    refine ⟨first ++ second.tail, after, ?_, actual, last, halt, halted, ?_,
      afterTicks, afterOutput.trans middleOutput, ?_⟩
    · simp only [List.head?_append, firstHead, Option.some_or]
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using afterTape
    · have width : natBits value ≤ value + 1 := by
        unfold natBits
        have log := Nat.log2_le_self value
        omega
      have square : (natBits value + 1) ^ 2 ≤ (value + (rest.length + 1) + 2) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      simp only [List.length_append, List.length_tail, List.length_cons,
        countCost] at secondSize ⊢
      have costEq : value + 1 + rest.length + 2 = value + (rest.length + 1) + 2 := by omega
      rw [costEq] at secondSize
      have firstBound : first.length ≤ 512 * (value + (rest.length + 1) + 2) ^ 2 + 2 := by
        omega
      calc
        _ ≤ (512 * (value + (rest.length + 1) + 2) ^ 2 + 2) +
            (rest.length + 1) * (512 * (value + (rest.length + 1) + 2) ^ 2 + 4) :=
          Nat.add_le_add firstBound ((Nat.sub_le _ _).trans secondSize)
        _ ≤ _ := by nlinarith

end PDROC.BitVM.Codec.OutputList
