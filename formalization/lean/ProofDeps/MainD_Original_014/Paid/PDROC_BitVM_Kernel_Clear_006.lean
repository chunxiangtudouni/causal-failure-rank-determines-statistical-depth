module

public import Paid.PDROC_BitVM_Kernel_Register_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Kernel.Clear

open Turing PDROC.BitVM.Kernel.RegisterGlobal

abbrev State := TM2.Cfg Alphabet Unit (Option Bool)

/-- The selected physical work role is a finite compile-time choice.
Every old Bool, including FALSE padding, is really removed. -/
def program (target : Stack) (_ : Unit) : TM2.Stmt Alphabet Unit (Option Bool) :=
  .pop target (fun _ symbol=>symbol) (.branch Option.isSome (.goto (fun _=>())) .halt)

def state (target : Stack) (contents : Stack → List Bool) (label : Option Unit)
    (store : Option Bool) (word : List Bool) : State :=
  ⟨label,store,Function.update contents target word⟩

theorem cons_step (target : Stack) (contents : Stack → List Bool)
    (store : Option Bool) (bit : Bool) (word : List Bool) :
    TM2.step (program target) (state target contents (some ()) store (bit::word))=
      some (state target contents (some ()) (some bit) word) := by
  simp only [state,program,TM2.step,TM2.stepAux,Function.update_self,List.head?_cons,
    List.tail_cons,Option.isSome_some,Bool.cond_true,Function.update_idem]

theorem nil_step (target : Stack) (contents : Stack → List Bool) (store : Option Bool) :
    TM2.step (program target) (state target contents (some ()) store [])=
      some (state target contents none none []) := by
  simp only [state,program,TM2.step,TM2.stepAux,Function.update_self,List.head?_nil,
    List.tail_nil,Option.isSome_none,Bool.cond_false,Function.update_idem]

def trace (target : Stack) (contents : Stack → List Bool) : List Bool → Option Bool → List State
  | [],store => [state target contents (some ()) store [],state target contents none none []]
  | bit::word,store => state target contents (some ()) store (bit::word)::trace target contents word (some bit)

theorem head (target : Stack) (contents : Stack → List Bool) (word : List Bool) (store : Option Bool) :
    (trace target contents word store).head?=some (state target contents (some ()) store word) := by
  cases word <;> rfl

theorem last (target : Stack) (contents : Stack → List Bool) (word : List Bool) (store : Option Bool) :
    (trace target contents word store).getLast?=some (state target contents none none []) := by
  induction word generalizing store with
  | nil => rfl
  | cons bit word ih =>
    rw [trace,List.getLast?_cons,ih]
    rfl

theorem length (target : Stack) (contents : Stack → List Bool) (word : List Bool) (store : Option Bool) :
    (trace target contents word store).length=word.length+2 := by
  induction word generalizing store with
  | nil => rfl
  | cons bit word ih => simp only [trace,List.length_cons,ih]

theorem chain (target : Stack) (contents : Stack → List Bool) (word : List Bool) (store : Option Bool) :
    (trace target contents word store).IsChain (fun a b=>TM2.step (program target) a=some b) := by
  induction word generalizing store with
  | nil => exact List.isChain_cons_cons.mpr ⟨nil_step target contents store,List.isChain_singleton _⟩
  | cons bit word ih =>
    apply List.IsChain.cons (ih (some bit))
    intro after member
    rw [head] at member
    have same : after=state target contents (some ()) (some bit) word := (Option.mem_some_iff.mp member).symm
    subst after
    exact cons_step target contents store bit word

/-- Actual global32-stack clear with arbitrary inactive data. No unrelated
stack is assumed empty, so heap and writer phases can reuse this directly. -/
theorem runs (target : Stack) (contents : Stack → List Bool) (store : Option Bool) :
    ∃ run : List State,
      run.head?=some (⟨some (),store,contents⟩ : State) ∧
      run.IsChain (fun a b=>TM2.step (program target) a=some b) ∧
      run.getLast?=some (⟨none,none,Function.update contents target []⟩ : State) ∧
      TM2.step (program target) (⟨none,none,Function.update contents target []⟩ : State)=none ∧
      run.length=(contents target).length+2 ∧
      ∀ other,other≠target → (Function.update contents target []) other=contents other := by
  refine ⟨trace target contents (contents target) store,?_,chain target contents (contents target) store,
    last target contents (contents target) store,rfl,length target contents (contents target) store,?_⟩
  · simpa only [state,Function.update_eq_self] using head target contents (contents target) store
  · intro other different
    exact Function.update_of_ne different _ _

theorem supports (target : Stack) : TM2.Supports (program target) (Finset.univ : Finset Unit) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    cases label
    simp [program,TM2.SupportsStmt]

end PDROC.BitVM.Kernel.Clear
