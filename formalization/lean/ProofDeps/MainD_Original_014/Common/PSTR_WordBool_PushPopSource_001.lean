module

public import Mathlib.Computability.TuringMachine.StackTuringMachine
public import Mathlib.Data.List.Chain
public import Mathlib.Tactic.FinCases

/-! Fixed finite-control source for a quantitative compiler prototype.
The two stackContents have Bool alphabets and the internal state is Unit. Input
length is data, never a control parameter. This is an actual TM2 source
trace, not yet an ORIGINAL Bool TM0 computes or a free input/output codec. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.PushPop

open Turing

abbrev Stack := Fin 2
abbrev Label := Fin 3
abbrev Alphabet (_ : Stack) := Bool
abbrev State := TM2.Cfg Alphabet Label Unit

def program (label : Label) : TM2.Stmt Alphabet Label Unit :=
  if label = 0 then
    .push 1 (fun _ => true) (.goto (fun _ => 1))
  else if label = 1 then
    .pop 1 (fun _ _ => ()) (.goto (fun _ => 2))
  else .halt

def stackContents (input scratch : List Bool) : Stack → List Bool :=
  fun stack => if stack = 0 then input else scratch

def state (input : List Bool) (label : Option Label) (scratch : List Bool) : State :=
  ⟨label, (), stackContents input scratch⟩

theorem update_scratch (input scratch replacement : List Bool) :
    Function.update (stackContents input scratch) 1 replacement = stackContents input replacement := by
  funext stack
  fin_cases stack <;> simp [stackContents]

theorem initial_eq (input : List Bool) :
    TM2.init (Γ := Alphabet) (Λ := Label) (σ := Unit) 0 input = state input (some 0) [] := by
  have equalStacks : Function.update (fun _ : Stack => ([] : List Bool)) 0 input = stackContents input [] := by
    funext stack
    fin_cases stack <;> simp [stackContents]
  exact congrArg (fun slots : Stack → List Bool => (⟨some 0, (), slots⟩ : State)) equalStacks

theorem step_push (input : List Bool) :
    TM2.step program (state input (some 0) []) = some (state input (some 1) [true]) := by
  change (some ⟨some 1, (), Function.update (stackContents input []) 1 [true]⟩ : Option State) = _
  rw [update_scratch]
  rfl

theorem step_pop (input : List Bool) :
    TM2.step program (state input (some 1) [true]) = some (state input (some 2) []) := by
  change (some ⟨some 2, (), Function.update (stackContents input [true]) 1 []⟩ : Option State) = _
  rw [update_scratch]
  rfl

theorem step_halt (input : List Bool) :
    TM2.step program (state input (some 2) []) = some (state input none []) := rfl

theorem final_halted (input : List Bool) : TM2.step program (state input none []) = none := rfl

def trace (input : List Bool) : List State :=
  [state input (some 0) [], state input (some 1) [true], state input (some 2) [], state input none []]

theorem trace_head (input : List Bool) :
    (trace input).head? = some (TM2.init (Γ := Alphabet) (Λ := Label) (σ := Unit) 0 input) :=
  congrArg some (initial_eq input).symm

theorem trace_chain (input : List Bool) :
    (trace input).IsChain (fun before after => TM2.step program before = some after) := by
  unfold trace
  apply List.isChain_cons_cons.mpr
  refine ⟨step_push input, ?_⟩
  apply List.isChain_cons_cons.mpr
  refine ⟨step_pop input, ?_⟩
  apply List.isChain_cons_cons.mpr
  exact ⟨step_halt input, List.isChain_singleton _⟩

theorem trace_last (input : List Bool) : (trace input).getLast? = some (state input none []) := rfl

theorem trace_length (input : List Bool) : (trace input).length = 4 := rfl

theorem final_input (input : List Bool) : (state input none []).stk 0 = input := by
  simp [state, stackContents]

theorem supports : TM2.Supports program (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label <;> simp [program, TM2.SupportsStmt]

end PaperProofs.Common.Native.PSTRWordBool.PushPop
