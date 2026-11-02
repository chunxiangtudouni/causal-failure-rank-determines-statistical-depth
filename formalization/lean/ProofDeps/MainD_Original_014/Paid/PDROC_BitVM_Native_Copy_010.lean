module

public import Paid.PDROC_BitVM_Log_TM2_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Native.Copy

open Turing
open PDROC.BitVM.Log.TwoStack

def state (label : Option Label) (store : Store) (source target scratch : List Bool) : State :=
  ⟨label,store,threeStacks source target scratch⟩

/-- Consume a reversed scratch word, pushing each real popped bit to BOTH
source and target. Control contains only Option Bool. -/
def mirror : Statement :=
  .pop 2 (fun _ symbol=>symbol)
    (.branch Option.isSome
      (.push 0 (fun symbol=>symbol.getD false)
        (.push 1 (fun symbol=>symbol.getD false) (.goto (fun _=>1)))) .halt)

def program (label : Label) : Statement :=
  if label=0 then drain 0 2 0 (.goto (fun _=>1))
  else if label=1 then mirror else .halt

theorem update_first (source target scratch replacement : List Bool) :
    Function.update (threeStacks source target scratch) 0 replacement=
      threeStacks replacement target scratch := by
  funext stack
  fin_cases stack <;> simp [threeStacks]

theorem update_second (source target scratch replacement : List Bool) :
    Function.update (threeStacks source target scratch) 1 replacement=
      threeStacks source replacement scratch := by
  funext stack
  fin_cases stack <;> simp [threeStacks]

theorem update_third (source target scratch replacement : List Bool) :
    Function.update (threeStacks source target scratch) 2 replacement=
      threeStacks source target replacement := by
  funext stack
  fin_cases stack <;> simp [threeStacks]

theorem mirror_cons (source target rest : List Bool) (bit : Bool) (store : Store) :
    TM2.step program (state (some 1) store source target (bit::rest))=
      some (state (some 1) (some bit) (bit::source) (bit::target) rest) := by
  change (some ⟨some 1,some bit,
    Function.update (Function.update (Function.update (threeStacks source target (bit::rest))
      2 rest) 0 (bit::source)) 1 (bit::target)⟩ : Option State)=_
  rw [update_third,update_first,update_second]
  rfl

theorem mirror_nil (source target : List Bool) (store : Store) :
    TM2.step program (state (some 1) store source target [])=
      some (state none none source target []) := by
  change (some ⟨none,none,Function.update (threeStacks source target []) 2 []⟩ : Option State)=_
  rw [update_third]
  rfl

def mirrorTrace : List Bool → List Bool → List Bool → Store → List State
  | [],source,target,store =>
      [state (some 1) store source target [],state none none source target []]
  | bit::rest,source,target,store =>
      state (some 1) store source target (bit::rest)::
        mirrorTrace rest (bit::source) (bit::target) (some bit)

theorem mirrorTrace_head (word source target : List Bool) (store : Store) :
    (mirrorTrace word source target store).head?=
      some (state (some 1) store source target word) := by
  cases word <;> rfl

theorem mirrorTrace_last (word source target : List Bool) (store : Store) :
    (mirrorTrace word source target store).getLast?=
      some (state none none (word.reverse++source) (word.reverse++target) []) := by
  induction word generalizing source target store with
  | nil => rfl
  | cons bit rest ih =>
    rw [mirrorTrace,List.getLast?_cons,ih]
    simp only [Option.getD_some,List.reverse_cons,List.append_assoc,List.singleton_append]

theorem mirrorTrace_length (word source target : List Bool) (store : Store) :
    (mirrorTrace word source target store).length=word.length+2 := by
  induction word generalizing source target store with
  | nil => rfl
  | cons bit rest ih => simp only [mirrorTrace,List.length_cons,ih]

theorem mirrorTrace_chain (word source target : List Bool) (store : Store) :
    (mirrorTrace word source target store).IsChain (fun a b=>TM2.step program a=some b) := by
  induction word generalizing source target store with
  | nil => exact List.isChain_cons_cons.mpr ⟨mirror_nil source target store,List.isChain_singleton _⟩
  | cons bit rest ih =>
    apply List.IsChain.cons (ih (bit::source) (bit::target) (some bit))
    intro after member
    rw [mirrorTrace_head] at member
    have equal : after=state (some 1) (some bit) (bit::source) (bit::target) rest :=
      (Option.mem_some_iff.mp member).symm
    subst after
    exact mirror_cons source target rest bit store

theorem supports : TM2.Supports program (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label <;> simp [program,drain,mirror,TM2.SupportsStmt]

end PDROC.BitVM.Native.Copy
