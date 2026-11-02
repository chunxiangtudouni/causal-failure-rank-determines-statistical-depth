module

public import Paid.PDROC_BitVM_Log_TM2_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

/-! Real append-to-history macro. Its input word is already encoded on stack
0; encoding a source event is a separate obligation. Two Boolean drains restore
the word's order while prepending it to stack 2, with no host append operation
in the program and no unbounded object in its finite internal store. -/

namespace PDROC.BitVM.Log.TwoStack

open Turing

def threeStacks (first second third : List Bool) : Stack → List Bool :=
  fun stack => if stack = 0 then first else if stack = 1 then second else third

def appendBefore (word history : List Bool) : State :=
  ⟨some 0, none, threeStacks word [] history⟩

def appendMiddle (word history : List Bool) : State :=
  ⟨some 1, none, threeStacks [] word.reverse history⟩

def appendAfter (word history : List Bool) : State :=
  ⟨none, none, threeStacks [] [] (word ++ history)⟩

def firstTrace (word history : List Bool) : List State :=
  trace 0 1 0 (.goto (fun _ => 1)) (fun _ => history) word [] none

def secondTrace (word history : List Bool) : List State :=
  trace 1 2 1 .halt (fun _ => []) word.reverse history none

def appendTrace (word history : List Bool) : List State :=
  firstTrace word history ++ (secondTrace word history).tail

theorem first_head (word history : List Bool) :
    (firstTrace word history).head? = some (appendBefore word history) := by
  rw [firstTrace, trace_head]
  rfl

theorem first_last (word history : List Bool) :
    (firstTrace word history).getLast? = some (appendMiddle word history) := by
  rw [firstTrace, trace_last]
  simp only [List.append_nil, TM2.stepAux]
  rfl

theorem second_head (word history : List Bool) :
    (secondTrace word history).head? = some (appendMiddle word history) := by
  rw [secondTrace, trace_head]
  apply congrArg some
  change (⟨some 1, none, stackContents 1 2 word.reverse history (fun _ => [])⟩ : State) = _
  have equal : stackContents 1 2 word.reverse history (fun _ => []) =
      threeStacks [] word.reverse history := by
    funext stack; fin_cases stack <;> simp [stackContents, threeStacks]
  rw [equal]
  rfl

theorem second_last (word history : List Bool) :
    (secondTrace word history).getLast? = some (appendAfter word history) := by
  rw [secondTrace, trace_last]
  simp only [List.reverse_reverse, TM2.stepAux]
  apply congrArg some
  have equal : stackContents 1 2 [] (word ++ history) (fun _ => []) =
      threeStacks [] [] (word ++ history) := by
    funext stack; fin_cases stack <;> simp [stackContents, threeStacks]
  rw [equal]
  rfl

theorem join_chain {α : Type} {relation : α → α → Prop}
    (first second : List α) (middle : α)
    (left : first.IsChain relation) (right : second.IsChain relation)
    (last : first.getLast? = some middle) (head : second.head? = some middle) :
    (first ++ second.tail).IsChain relation := by
  have splitLeft : first.dropLast ++ [middle] = first :=
    List.dropLast_append_getLast? middle (by rw [last]; rfl)
  have splitRight : [middle] ++ second.tail = second :=
    List.cons_head?_tail (by rw [head]; rfl)
  have left' : (first.dropLast ++ [middle]).IsChain relation := by
    rw [splitLeft]; exact left
  have right' : ([middle] ++ second.tail).IsChain relation := by
    rw [splitRight]; exact right
  simpa only [splitLeft] using left'.append_overlap right' (by simp)

theorem append_trace_head (word history : List Bool) :
    (appendTrace word history).head? = some (appendBefore word history) := by
  simp only [appendTrace, List.head?_append, first_head, Option.some_or]

theorem append_trace_last (word history : List Bool) :
    (appendTrace word history).getLast? = some (appendAfter word history) := by
  have notOne : (secondTrace word history).length ≠ 1 := by
    simp only [secondTrace, trace_length, List.length_reverse]
    omega
  simp only [appendTrace, List.getLast?_append, List.getLast?_tail, notOne,
    ↓reduceIte, second_last, Option.some_or]

theorem append_trace_chain (word history : List Bool) :
    (appendTrace word history).IsChain
      (fun before after => TM2.step program before = some after) := by
  apply join_chain _ _ (appendMiddle word history)
  · exact trace_chain program 0 1 (by decide) 0 (.goto (fun _ => 1))
      (by simp [program]) (fun _ => history) word [] none
  · exact trace_chain program 1 2 (by decide) 1 .halt
      (by simp [program]) (fun _ => []) word.reverse history none
  · exact first_last word history
  · exact second_head word history

theorem append_trace_length (word history : List Bool) :
    (appendTrace word history).length = 2 * word.length + 3 := by
  simp only [appendTrace, firstTrace, secondTrace, List.length_append,
    List.length_tail, trace_length, List.length_reverse]
  omega

theorem append_trace_halted (word history : List Bool) :
    TM2.step program (appendAfter word history) = none := rfl

theorem initial_append (word : List Bool) :
    TM2.init (Γ := Alphabet) (Λ := Label) (σ := Store) 0 word = appendBefore word [] := by
  have equal : Function.update (fun _ : Stack => ([] : List Bool)) 0 word =
      threeStacks word [] [] := by
    funext stack; fin_cases stack <;> simp [threeStacks]
  exact congrArg (fun slots : Stack → List Bool => (⟨some 0, none, slots⟩ : State)) equal

/-- The single selected real TM2 witness, from the actual macro entry to halt. -/
theorem append_runs (word history : List Bool) :
    ∃ run : List State,
      run.head? = some (appendBefore word history) ∧
      run.IsChain (fun before after => TM2.step program before = some after) ∧
      run.getLast? = some (appendAfter word history) ∧
      TM2.step program (appendAfter word history) = none ∧
      run.length = 2 * word.length + 3 ∧
      (appendAfter word history).stk 2 = word ++ history ∧
      (appendAfter word history).stk 0 = [] ∧
      (appendAfter word history).stk 1 = [] := by
  exact ⟨appendTrace word history, append_trace_head word history,
    append_trace_chain word history, append_trace_last word history,
    append_trace_halted word history, append_trace_length word history,
    by simp [appendAfter, threeStacks], by simp [appendAfter, threeStacks],
    by simp [appendAfter, threeStacks]⟩

end PDROC.BitVM.Log.TwoStack
