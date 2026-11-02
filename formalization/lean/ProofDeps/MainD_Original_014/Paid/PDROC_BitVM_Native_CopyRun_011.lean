module

public import Paid.PDROC_BitVM_Native_Copy_010

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Native.Copy

open Turing PDROC.BitVM.Log.TwoStack

def firstTrace (word target : List Bool) : List State :=
  trace 0 2 0 (.goto (fun _=>1)) (fun _=>target) word [] none

def secondTrace (word target : List Bool) : List State :=
  mirrorTrace word.reverse [] target none

def copyTrace (word target : List Bool) : List State :=
  firstTrace word target++(secondTrace word target).tail

theorem first_head (word target : List Bool) :
    (firstTrace word target).head?=some (state (some 0) none word target []) := by
  rw [firstTrace,trace_head]
  apply congrArg some
  have same : stackContents 0 2 word [] (fun _=>target)=threeStacks word target [] := by
    funext stack
    fin_cases stack <;> simp [stackContents,threeStacks]
  change (⟨some 0,none,stackContents 0 2 word [] (fun _=>target)⟩ : State)=_
  rw [same]
  rfl

theorem first_last (word target : List Bool) :
    (firstTrace word target).getLast?=some (state (some 1) none [] target word.reverse) := by
  rw [firstTrace,trace_last]
  simp only [List.append_nil,TM2.stepAux]
  apply congrArg some
  have same : stackContents 0 2 [] word.reverse (fun _=>target)=threeStacks [] target word.reverse := by
    funext stack
    fin_cases stack <;> simp [stackContents,threeStacks]
  rw [same]
  rfl

theorem second_head (word target : List Bool) :
    (secondTrace word target).head?=some (state (some 1) none [] target word.reverse) :=
  mirrorTrace_head word.reverse [] target none

theorem second_last (word target : List Bool) :
    (secondTrace word target).getLast?=some (state none none word (word++target) []) := by
  simp only [secondTrace,mirrorTrace_last,List.reverse_reverse,List.append_nil]

theorem copy_chain (word target : List Bool) :
    (copyTrace word target).IsChain (fun a b=>TM2.step program a=some b) := by
  apply join_chain _ _ (state (some 1) none [] target word.reverse)
  · exact trace_chain program 0 2 (by decide) 0 (.goto (fun _=>1))
      (by simp [program]) (fun _=>target) word [] none
  · exact mirrorTrace_chain word.reverse [] target none
  · exact first_last word target
  · exact second_head word target

theorem copy_head (word target : List Bool) :
    (copyTrace word target).head?=some (state (some 0) none word target []) := by
  simp only [copyTrace,List.head?_append,first_head,Option.some_or]

theorem copy_last (word target : List Bool) :
    (copyTrace word target).getLast?=some (state none none word (word++target) []) := by
  have notOne : (secondTrace word target).length≠1 := by
    simp only [secondTrace,mirrorTrace_length,List.length_reverse]
    omega
  simp only [copyTrace,List.getLast?_append,List.getLast?_tail,notOne,
    ↓reduceIte,second_last,Option.some_or]

theorem copy_length (word target : List Bool) :
    (copyTrace word target).length=2*word.length+3 := by
  simp only [copyTrace,firstTrace,secondTrace,List.length_append,List.length_tail,
    trace_length,mirrorTrace_length,List.length_reverse]
  omega

/-- Genuine copying of a runtime Boolean word. The original is preserved,
the destination gains the word in its original order, scratch is restored
empty and actual time is linear. A nonempty old destination is explicitly
retained; register replacement must really clear it first. -/
theorem copy_runs (word target : List Bool) :
    ∃ run : List State,
      run.head?=some (state (some 0) none word target []) ∧
      run.IsChain (fun a b=>TM2.step program a=some b) ∧
      run.getLast?=some (state none none word (word++target) []) ∧
      TM2.step program (state none none word (word++target) [])=none ∧
      run.length=2*word.length+3 ∧
      (state none none word (word++target) []).stk 0=word ∧
      (state none none word (word++target) []).stk 1=word++target ∧
      (state none none word (word++target) []).stk 2=[] :=
  ⟨copyTrace word target,copy_head word target,copy_chain word target,copy_last word target,
    rfl,copy_length word target,rfl,rfl,rfl⟩

end PDROC.BitVM.Native.Copy
