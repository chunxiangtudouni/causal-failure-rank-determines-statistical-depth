module

public import Paid.PDROC_BitVM_Kernel_Clear_006
public import Paid.PDROC_BitVM_Native_Return_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Kernel.Reset

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

abbrev Label := (Stack × Bool) ⊕ Unit
abbrev Store := Option Bool × Unit
abbrev State := TM2.Cfg Alphabet Label Store
abbrev Statement := TM2.Stmt Alphabet Label Store

def readonly (slot : Stack) : Bool := decide (1≤slot.val ∧ slot.val≤13)
def isRegister (slot : Stack) : Bool := decide (14≤slot.val ∧ slot.val≤20)
def word (slot : Stack) : List Bool := if isRegister slot then encodeCellBits (.natural 0) else []
def clearLabel (slot : Stack) : Label := .inl (slot,false)
def installLabel (slot : Stack) : Label := .inl (slot,true)
def nextLabel (slot : Stack) : Label :=
  if bound : slot.val+1<32 then clearLabel ⟨slot.val+1,bound⟩ else .inr ()

def install (slot : Stack) (tail : Statement) : Statement :=
  .push slot (fun _=>false) (.push slot (fun _=>false)
    (.push slot (fun _=>true) (.push slot (fun _=>false) tail)))

theorem install_step (slot : Stack) (tail : Statement) (contents : Stack → List Bool) (saved : Store) :
    TM2.stepAux (install slot tail) saved contents=
      TM2.stepAux tail saved (Function.update contents slot (encodeCellBits (.natural 0)++contents slot)) := by
  simp only [install,TM2.stepAux,Function.update_self,Function.update_idem]
  rfl

/-- One fixed reset program, used after physically mounting the input bank.
Readonly cells1..13 survive; every other role is really cleared. Registers
receive four actual Nat-zero Cell bits. Heap history/output/scratch end empty. -/
def program : Label → Statement
  | .inl (slot,false) =>
    if readonly slot then .goto (fun _=>nextLabel slot)
    else Inline.statement (fun _ : Unit=>clearLabel slot) (installLabel slot) (Clear.program slot ())
  | .inl (slot,true) =>
    if isRegister slot then install slot (.goto (fun _=>nextLabel slot))
    else .goto (fun _=>nextLabel slot)
  | .inr _ => .halt

def before (slot : Stack) (contents : Stack → List Bool) (store : Option Bool) : State :=
  ⟨some (clearLabel slot),(store,()),contents⟩

def after (slot : Stack) (contents : Stack → List Bool) (store : Option Bool) : State :=
  if readonly slot then ⟨some (nextLabel slot),(store,()),contents⟩
  else ⟨some (nextLabel slot),(none,()),Function.update contents slot (word slot)⟩

theorem clear_agrees (slot : Stack) (writable : readonly slot=false) :
    ∀ label : Unit,program ((fun _ : Unit=>clearLabel slot) label)=
      Inline.statement (fun _ : Unit=>clearLabel slot) (installLabel slot) (Clear.program slot label) := by
  intro label
  cases label
  simp only [program,clearLabel,writable,Bool.false_eq_true,↓reduceIte]

theorem phase_runs (slot : Stack) (contents : Stack → List Bool) (store : Option Bool) :
    ∃ run : List State,run.head?=some (before slot contents store) ∧
      run.IsChain (fun a b=>TM2.step program a=some b) ∧
      run.getLast?=some (after slot contents store) ∧
      run.length≤(contents slot).length+3 := by
  cases read : readonly slot with
  | true =>
    have edge : TM2.step program (before slot contents store)=some (after slot contents store) := by
      simp only [before,after,read,↓reduceIte,TM2.step,program,clearLabel,TM2.stepAux]
    refine ⟨[before slot contents store,after slot contents store],rfl,
      List.isChain_cons_cons.mpr ⟨edge,List.isChain_singleton _⟩,rfl,?_⟩
    simp only [List.length_cons,List.length_nil]
    omega
  | false =>
    obtain ⟨source,head,chain,last,halt,length,_frame⟩ := Clear.runs slot contents store
    obtain ⟨run,returned,first,actual,finish,atReturn,stacksEq,storeEq,size⟩ :=
      Inline.actual_return_trace (fun _ : Unit=>clearLabel slot) (installLabel slot)
        (Clear.program slot) program (clear_agrees slot read) source
        (⟨some (),store,contents⟩ : Clear.State)
        (⟨none,none,Function.update contents slot []⟩ : Clear.State) () head chain last halt
    have returnedEq : returned=
        (⟨some (installLabel slot),(none,()),Function.update contents slot []⟩ : State) := by
      rcases returned with ⟨label,saved,physical⟩
      change label=some (installLabel slot) at atReturn
      change saved=(none,()) at storeEq
      change physical=Function.update contents slot [] at stacksEq
      subst label
      subst saved
      subst physical
      rfl
    have edge : TM2.step program returned=some (after slot contents store) := by
      rw [returnedEq]
      cases reg : isRegister slot with
      | false =>
        simp only [program,installLabel,reg,Bool.false_eq_true,↓reduceIte,TM2.step,TM2.stepAux,
          after,read,word]
      | true =>
        simp only [program,installLabel,reg,↓reduceIte,TM2.step,install_step,
          Function.update_self,List.append_nil,Function.update_idem,TM2.stepAux,after,read,word,
          Bool.false_eq_true]
    have pair : [returned,after slot contents store].IsChain (fun a b=>TM2.step program a=some b) :=
      List.isChain_cons_cons.mpr ⟨edge,List.isChain_singleton _⟩
    refine ⟨run++[after slot contents store],?_,
      PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain _ _ _ finish actual pair,
      List.getLast?_append_cons run (after slot contents store) [],?_⟩
    · simp only [List.head?_append,first,Option.some_or]
      rfl
    · simp only [List.length_append,List.length_cons,List.length_nil,size,length]
      omega

theorem supports : TM2.Supports program (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    rcases label with ⟨slot,flag⟩ | marker
    · cases flag
      · cases read : readonly slot
        · simp only [program,read,Bool.false_eq_true,↓reduceIte]
          exact Inline.supports_statement (fun _ : Unit=>clearLabel slot) (installLabel slot)
            Finset.univ Finset.univ (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _)
            (Clear.program slot ()) ((Clear.supports slot).2 () (Finset.mem_univ _))
        · simp [program,read,TM2.SupportsStmt]
      · cases reg : isRegister slot <;> simp [program,reg,install,TM2.SupportsStmt]
    · trivial

end PDROC.BitVM.Kernel.Reset
