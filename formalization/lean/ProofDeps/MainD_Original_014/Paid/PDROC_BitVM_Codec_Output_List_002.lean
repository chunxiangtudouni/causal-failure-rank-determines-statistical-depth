module

public import Paid.PDROC_BitVM_Codec_Output_List_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Codec.OutputList

open Turing PDROC.BitVM.Log.TwoStack

def copyReverseSecondTrace (word target : List Bool) : List State :=
  trace 2 0 1 .halt (fun _ => word.reverse ++ target) word.reverse [] none

def copyReverseTrace (word target : List Bool) : List State :=
  copyReverseFirstTrace word target [] none ++ (copyReverseSecondTrace word target).tail

theorem copyReverseSecond_head (word target : List Bool) :
    (copyReverseSecondTrace word target).head? =
      some (copyState (some 1) none [] (word.reverse ++ target) word.reverse) := by
  rw [copyReverseSecondTrace, trace_head]
  apply congrArg some
  have same : stackContents 2 0 word.reverse [] (fun _ => word.reverse ++ target) =
      threeStacks [] (word.reverse ++ target) word.reverse := by
    funext stack
    fin_cases stack <;> simp [stackContents, threeStacks]
  change (⟨some 1, none,
    stackContents 2 0 word.reverse [] (fun _ => word.reverse ++ target)⟩ : State) = _
  rw [same]
  rfl

theorem copyReverseSecond_last (word target : List Bool) :
    (copyReverseSecondTrace word target).getLast? =
      some (copyState none none word (word.reverse ++ target) []) := by
  rw [copyReverseSecondTrace, trace_last]
  simp only [List.reverse_reverse, List.append_nil, TM2.stepAux]
  apply congrArg some
  have same : stackContents 2 0 [] word (fun _ => word.reverse ++ target) =
      threeStacks word (word.reverse ++ target) [] := by
    funext stack
    fin_cases stack <;> simp [stackContents, threeStacks]
  rw [same]
  rfl

theorem copyReverse_chain (word target : List Bool) :
    (copyReverseTrace word target).IsChain
      (fun before after => TM2.step copyReverseProgram before = some after) := by
  apply join_chain _ _ (copyState (some 1) none [] (word.reverse ++ target) word.reverse)
  · exact copyReverseFirst_chain word target [] none
  · exact trace_chain copyReverseProgram 2 0 (by decide) 1 .halt
      (by simp [copyReverseProgram]) (fun _ => word.reverse ++ target) word.reverse [] none
  · simpa only [List.append_nil] using copyReverseFirst_last word target [] none
  · exact copyReverseSecond_head word target

theorem copyReverse_head (word target : List Bool) :
    (copyReverseTrace word target).head? =
      some (copyState (some 0) none word target []) := by
  simp only [copyReverseTrace, List.head?_append, copyReverseFirst_head, Option.some_or]

theorem copyReverse_last (word target : List Bool) :
    (copyReverseTrace word target).getLast? =
      some (copyState none none word (word.reverse ++ target) []) := by
  have notOne : (copyReverseSecondTrace word target).length ≠ 1 := by
    simp only [copyReverseSecondTrace, trace_length, List.length_reverse]
    omega
  simp only [copyReverseTrace, List.getLast?_append, List.getLast?_tail, notOne,
    ↓reduceIte, copyReverseSecond_last, Option.some_or]

theorem copyReverse_length (word target : List Bool) :
    (copyReverseTrace word target).length = 2 * word.length + 3 := by
  simp only [copyReverseTrace, copyReverseSecondTrace, List.length_append,
    List.length_tail, copyReverseFirst_length, trace_length, List.length_reverse]
  omega

/-- The loaded runtime Cell word is retained. Its ACTUAL popped Booleans
are prepended in reverse order to the output; scratch is empty again.
No unbounded word or Nat occurs in the fixed finite store. -/
theorem copyReverse_runs (word target : List Bool) :
    ∃ run : List State,
      run.head? = some (copyState (some 0) none word target []) ∧
      run.IsChain (fun before after => TM2.step copyReverseProgram before = some after) ∧
      run.getLast? = some (copyState none none word (word.reverse ++ target) []) ∧
      TM2.step copyReverseProgram (copyState none none word (word.reverse ++ target) []) = none ∧
      run.length = 2 * word.length + 3 ∧
      (copyState none none word (word.reverse ++ target) []).stk 0 = word ∧
      (copyState none none word (word.reverse ++ target) []).stk 1 = word.reverse ++ target ∧
      (copyState none none word (word.reverse ++ target) []).stk 2 = [] :=
  ⟨copyReverseTrace word target, copyReverse_head word target, copyReverse_chain word target,
    copyReverse_last word target, rfl, copyReverse_length word target, rfl, rfl, rfl⟩

end PDROC.BitVM.Codec.OutputList
