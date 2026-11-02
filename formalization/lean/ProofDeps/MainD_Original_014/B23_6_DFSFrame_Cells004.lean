module
public import B23_6_DFSFrame_Path002

/-! Actual executions of the reused Cells bodies, with arbitrary Bool data,
arbitrary finite store flags, and arbitrary untouched physical stacks. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace B23_6.DFSFrame
open Turing PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*}

theorem clear_empty (slot : Stack) (again next : Label)
    (codeAt : source (C:=C) again=clearBody slot again next) (memory : Store C) (before : Bank) :
    TM2.step source (state again memory (Function.update before slot []))=
      some (state next (clean memory) (Function.update before slot [])) := by
  simp [state,TM2.step,codeAt,clearBody_literal,TM2.stepAux,RatDrop.capture,clean]
theorem clear_cons (slot : Stack) (again next : Label)
    (codeAt : source (C:=C) again=clearBody slot again next) (memory : Store C) (before : Bank)
    (bit : Bool) (bits : List Bool) :
    TM2.step source (state again memory (Function.update before slot (bit::bits)))=
      some (state again (memory.1,true,bit) (Function.update before slot bits)) := by
  simp [state,TM2.step,codeAt,clearBody_literal,TM2.stepAux,RatDrop.capture]

theorem clear_run_cells (slot : Stack) (again next : Label)
    (codeAt : source (C:=C) again=clearBody slot again next) (proper : Interior again)
    (memory : Store C) (before : Bank) (bits : List Bool) :
    Run (state again memory (Function.update before slot bits))
      (state next (clean memory) (Function.update before slot [])) (bits.length+1) := by
  induction bits generalizing memory with
  | nil => exact Run.one (clear_empty slot again next codeAt memory before) (active_state _ _ _ proper)
  | cons bit bits ih =>
    simpa only [List.length_cons,clean] using
      Run.cons (clear_cons slot again next codeAt memory before bit bits) (active_state _ _ _ proper)
        (ih (memory.1,true,bit))

theorem clear_run (slot : Stack) (again next : Label)
    (codeAt : source (C:=C) again=clearBody slot again next) (proper : Interior again)
    (memory : Store C) (before : Bank) :
    Run (state again memory before) (state next (clean memory) (Function.update before slot []))
      ((before slot).length+1) := by
  simpa only [Function.update_eq_self] using clear_run_cells slot again next codeAt proper memory before (before slot)

def two (before : Bank) (src dst : Stack) (left right : List Bool) : Bank :=
  Function.update (Function.update before src left) dst right
theorem two_src (before : Bank) (src dst : Stack) (ne : src≠dst) (left right : List Bool) :
    two before src dst left right src=left := by simp only [two,Function.update_of_ne ne,Function.update_self]
theorem two_dst (before : Bank) (src dst : Stack) (left right : List Bool) :
    two before src dst left right dst=right := Function.update_self _ _ _
theorem two_set_src (before : Bank) (src dst : Stack) (ne : src≠dst) (left right value : List Bool) :
    Function.update (two before src dst left right) src value=two before src dst value right := by
  funext slot
  by_cases a : slot=src <;> by_cases b : slot=dst <;> simp_all [two]
theorem two_set_dst (before : Bank) (src dst : Stack) (left right value : List Bool) :
    Function.update (two before src dst left right) dst value=two before src dst left value := by
  simp only [two,Function.update_idem]

theorem reverse_empty (roles : Stack ≃ Stack) (again next : Label)
    (codeAt : source (C:=C) again=reverseBody roles again next) (memory : Store C) (before : Bank)
    (right : List Bool) :
    TM2.step source (state again memory (two before (roles 13) (roles 3) [] right))=
      some (state next (clean memory) (two before (roles 13) (roles 3) [] right)) := by
  have ne : roles 13≠roles 3:=by intro h;have:=roles.injective h;cases this
  simp [state,TM2.step,codeAt,reverseBody_literal,TM2.stepAux,RatDrop.capture,clean,
    two_src _ _ _ ne,two_set_src _ _ _ ne]
theorem reverse_cons (roles : Stack ≃ Stack) (again next : Label)
    (codeAt : source (C:=C) again=reverseBody roles again next) (memory : Store C) (before : Bank)
    (bit : Bool) (bits right : List Bool) :
    TM2.step source (state again memory (two before (roles 13) (roles 3) (bit::bits) right))=
      some (state again (memory.1,true,bit) (two before (roles 13) (roles 3) bits (bit::right))) := by
  have ne : roles 13≠roles 3:=by intro h;have:=roles.injective h;cases this
  simp [state,TM2.step,codeAt,reverseBody_literal,TM2.stepAux,RatDrop.capture,RatDrop.bit,
    two_src _ _ _ ne,two_dst,two_set_src _ _ _ ne,two_set_dst]

theorem reverse_run_cells (roles : Stack ≃ Stack) (again next : Label)
    (codeAt : source (C:=C) again=reverseBody roles again next) (proper : Interior again)
    (memory : Store C) (before : Bank) (left right : List Bool) :
    Run (state again memory (two before (roles 13) (roles 3) left right))
      (state next (clean memory) (two before (roles 13) (roles 3) [] (left.reverse++right))) (left.length+1) := by
  induction left generalizing memory right with
  | nil => exact Run.one (reverse_empty roles again next codeAt memory before right) (active_state _ _ _ proper)
  | cons bit bits ih =>
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,clean] using
      Run.cons (reverse_cons roles again next codeAt memory before bit bits right) (active_state _ _ _ proper)
        (ih (memory.1,true,bit) (bit::right))

theorem reverse_run (roles : Stack ≃ Stack) (again next : Label)
    (codeAt : source (C:=C) again=reverseBody roles again next) (proper : Interior again)
    (memory : Store C) (before : Bank) :
    Run (state again memory before)
      (state next (clean memory) (two before (roles 13) (roles 3) []
        ((before (roles 13)).reverse++before (roles 3)))) ((before (roles 13)).length+1) := by
  simpa only [two,Function.update_eq_self] using
    reverse_run_cells roles again next codeAt proper memory before (before (roles 13)) (before (roles 3))

end B23_6.DFSFrame
