module

public import PSTR_WordBool_RatCmp_Meaning_001

/-! The actual guarded NUM/DEN consumption and physical Bool push.
The new result prefix alone is consumed; arbitrary old15/old3 remain. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatCmp.Reader

open Turing PSTRWordVM RationalControllerComputation PSTRTMRawNat010

variable {C : Type*}

def numTrace (background : Stack → List Bool) (context : C) (negative : Bool) :
    List Bool → Bool → Bool → List Bool → List Bool → List (State C)
  | [],seen,oldFlag,source,target=>
      [state background 1 context (negative,seen,oldFlag) (false::false::source) target,
       state background 2 context (negative,seen,false) source target]
  | bit::later,seen,oldFlag,source,target=>
      state background 1 context (negative,seen,oldFlag) (true::bit::(leftBlocks later++false::false::source)) target ::
      numTrace background context negative later (seen || bit) true source target

def denTrace (background : Stack → List Bool) (context : C) (negative seen : Bool) :
    List Bool → Bool → List Bool → List Bool → List (State C)
  | [],oldFlag,source,target=>
      [state background 2 context (negative,seen,oldFlag) (false::false::source) target,
       state background 3 context (negative,seen,false) source target]
  | bit::later,oldFlag,source,target=>
      state background 2 context (negative,seen,oldFlag) (true::bit::(leftBlocks later++false::false::source)) target ::
      denTrace background context negative seen later true source target

theorem num_head (background : Stack → List Bool) (context : C) (negative : Bool) (digits : List Bool)
    (seen oldFlag : Bool) (source target : List Bool) :
    (numTrace background context negative digits seen oldFlag source target).head?=
      some (state background 1 context (negative,seen,oldFlag) (leftBlocks digits++false::false::source) target) := by
  cases digits <;> rfl

theorem num_nonempty (background : Stack → List Bool) (context : C) (negative : Bool) (digits : List Bool)
    (seen oldFlag : Bool) (source target : List Bool) : numTrace background context negative digits seen oldFlag source target≠[] := by
  cases digits <;> intro same <;> cases same

theorem num_last (background : Stack → List Bool) (context : C) (negative : Bool) (digits : List Bool)
    (seen oldFlag : Bool) (source target : List Bool) :
    (numTrace background context negative digits seen oldFlag source target).getLast?=
      some (state background 2 context (negative,seen || anyTrue digits,false) source target) := by
  induction digits generalizing seen oldFlag with
  | nil => cases seen <;> rfl
  | cons bit later ih =>
    rw [numTrace,List.getLast?_cons_of_ne_nil (num_nonempty _ _ _ _ _ _ _ _),ih]
    simp only [anyTrue,Bool.or_assoc]

theorem num_chain (caller : Statement C) (background : Stack → List Bool) (context : C)
    (negative : Bool) (digits : List Bool) (seen oldFlag : Bool) (source target : List Bool) :
    (numTrace background context negative digits seen oldFlag source target).IsChain
      (fun a b=>TM2.step (program caller) a=some b) := by
  induction digits generalizing seen oldFlag with
  | nil => exact List.isChain_cons_cons.mpr ⟨num_end _ _ _ _ _ _ _ _,List.isChain_singleton _⟩
  | cons bit later ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_,ih (seen || bit) true⟩
    intro next member
    rw [num_head] at member
    have same : next= _ := (Option.mem_some_iff.mp member).symm
    subst next
    exact num_step caller background context negative seen oldFlag bit _ target

theorem num_length (background : Stack → List Bool) (context : C) (negative : Bool) (digits : List Bool)
    (seen oldFlag : Bool) (source target : List Bool) :
    (numTrace background context negative digits seen oldFlag source target).length=digits.length+2 := by
  induction digits generalizing seen oldFlag with
  | nil => rfl
  | cons bit later ih => simp only [numTrace,List.length_cons,ih]

theorem num_context (background : Stack → List Bool) (context : C) (negative : Bool) (digits : List Bool)
    (seen oldFlag : Bool) (source target : List Bool) :
    ∀ current∈numTrace background context negative digits seen oldFlag source target,current.var.1=context := by
  induction digits generalizing seen oldFlag with
  | nil =>
    intro current member
    rcases List.mem_cons.mp member with rfl|later
    · rfl
    · have same:=List.mem_singleton.mp later
      subst current
      rfl
  | cons bit later ih =>
    intro current member
    rcases List.mem_cons.mp member with rfl|rest
    · rfl
    · exact ih (seen || bit) true current rest

theorem den_head (background : Stack → List Bool) (context : C) (negative seen : Bool) (digits : List Bool)
    (oldFlag : Bool) (source target : List Bool) :
    (denTrace background context negative seen digits oldFlag source target).head?=
      some (state background 2 context (negative,seen,oldFlag) (leftBlocks digits++false::false::source) target) := by
  cases digits <;> rfl

theorem den_nonempty (background : Stack → List Bool) (context : C) (negative seen : Bool) (digits : List Bool)
    (oldFlag : Bool) (source target : List Bool) : denTrace background context negative seen digits oldFlag source target≠[] := by
  cases digits <;> intro same <;> cases same

theorem den_last (background : Stack → List Bool) (context : C) (negative seen : Bool) (digits : List Bool)
    (oldFlag : Bool) (source target : List Bool) :
    (denTrace background context negative seen digits oldFlag source target).getLast?=
      some (state background 3 context (negative,seen,false) source target) := by
  induction digits generalizing oldFlag with
  | nil => rfl
  | cons bit later ih => rw [denTrace,List.getLast?_cons_of_ne_nil (den_nonempty _ _ _ _ _ _ _ _),ih]

theorem den_chain (caller : Statement C) (background : Stack → List Bool) (context : C)
    (negative seen : Bool) (digits : List Bool) (oldFlag : Bool) (source target : List Bool) :
    (denTrace background context negative seen digits oldFlag source target).IsChain
      (fun a b=>TM2.step (program caller) a=some b) := by
  induction digits generalizing oldFlag with
  | nil => exact List.isChain_cons_cons.mpr ⟨den_end _ _ _ _ _ _ _ _,List.isChain_singleton _⟩
  | cons bit later ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_,ih true⟩
    intro next member
    rw [den_head] at member
    have same : next= _ := (Option.mem_some_iff.mp member).symm
    subst next
    exact den_step caller background context negative seen oldFlag bit _ target

theorem den_length (background : Stack → List Bool) (context : C) (negative seen : Bool) (digits : List Bool)
    (oldFlag : Bool) (source target : List Bool) :
    (denTrace background context negative seen digits oldFlag source target).length=digits.length+2 := by
  induction digits generalizing oldFlag with
  | nil => rfl
  | cons bit later ih => simp only [denTrace,List.length_cons,ih]

theorem den_context (background : Stack → List Bool) (context : C) (negative seen : Bool) (digits : List Bool)
    (oldFlag : Bool) (source target : List Bool) :
    ∀ current∈denTrace background context negative seen digits oldFlag source target,current.var.1=context := by
  induction digits generalizing oldFlag with
  | nil =>
    intro current member
    rcases List.mem_cons.mp member with rfl|later
    · rfl
    · have same:=List.mem_singleton.mp later
      subst current
      rfl
  | cons bit later ih =>
    intro current member
    rcases List.mem_cons.mp member with rfl|rest
    · rfl
    · exact ih true current rest

structure Path (caller : Statement C) (context : C) (before final : State C) (budget : Nat) where
  trace : List (State C)
  head : trace.head?=some before
  chain : trace.IsChain (fun a b=>TM2.step (program caller) a=some b)
  last : trace.getLast?=some final
  count : trace.length≤budget
  contexts : ∀ current∈trace,current.var.1=context

def Path.append {caller : Statement C} {context : C} {before middle final : State C} {frontBudget backBudget : Nat}
    (front : Path caller context before middle frontBudget) (back : Path caller context middle final backBudget) :
    Path caller context before final (frontBudget+backBudget-1) := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp back.head
    rw [same];rfl
  have size:=congrArg List.length shape
  simp only [List.length_cons] at size
  refine ⟨front.trace++back.trace.tail,?_,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.head];rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)
  · have first:=front.count;have second:=back.count
    simp only [List.length_append]
    omega
  · intro current member
    rcases List.mem_append.mp member with early|later
    · exact front.contexts current early
    · exact back.contexts current (List.mem_of_mem_tail later)

theorem actual_packet (caller : Statement C) (background : Stack → List Bool) (context : C) (memory : Store)
    (negative : Bool) (num den source target : List Bool) :
    ∃ trace : List (State C),
      trace.head?=some (state background 0 context memory (PSTRSymbolicRatExport.packet negative num den source) target) ∧
      trace.IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
      trace.getLast?=some (state background 4 context (negative,anyTrue num,false) source
        ((negative || !anyTrue num)::target)) ∧
      trace.length≤num.length+den.length+5 ∧ (∀ current∈trace,current.var.1=context) := by
  let afterNum:=leftBlocks den++false::false::source
  let s0:=state background 0 context memory (PSTRSymbolicRatExport.packet negative num den source) target
  let s1:=state background 1 context (negative,false,memory.2.2) (leftBlocks num++false::false::afterNum) target
  let s2:=state background 2 context (negative,anyTrue num,false) afterNum target
  let s3:=state background 3 context (negative,anyTrue num,false) source target
  let s4:=state background 4 context (negative,anyTrue num,false) source ((negative || !anyTrue num)::target)
  let p0 : Path caller context s0 s1 2 := {
    trace:=[s0,s1],head:=rfl,last:=rfl,count:=Nat.le_refl _
    chain:=List.isChain_cons_cons.mpr ⟨start_step _ _ _ _ _ _ _,List.isChain_singleton _⟩
    contexts:=by
      intro current member
      rcases List.mem_cons.mp member with rfl|later
      · rfl
      · have same:=List.mem_singleton.mp later
        subst current
        rfl }
  let pn : Path caller context s1 s2 (num.length+2) := {
    trace:=numTrace background context negative num false memory.2.2 afterNum target
    head:=num_head _ _ _ _ _ _ _ _,chain:=num_chain _ _ _ _ _ _ _ _ _
    last:=by simpa only [Bool.false_or] using num_last background context negative num false memory.2.2 afterNum target
    count:=(num_length _ _ _ _ _ _ _ _).le,contexts:=num_context _ _ _ _ _ _ _ _ }
  let pd : Path caller context s2 s3 (den.length+2) := {
    trace:=denTrace background context negative (anyTrue num) den false source target
    head:=den_head _ _ _ _ _ _ _ _,chain:=den_chain _ _ _ _ _ _ _ _ _
    last:=den_last _ _ _ _ _ _ _ _,count:=(den_length _ _ _ _ _ _ _ _).le,contexts:=den_context _ _ _ _ _ _ _ _ }
  let p4 : Path caller context s3 s4 2 := {
    trace:=[s3,s4],head:=rfl,last:=rfl,count:=Nat.le_refl _
    chain:=List.isChain_cons_cons.mpr ⟨finish_step _ _ _ _ _ _ _,List.isChain_singleton _⟩
    contexts:=by
      intro current member
      rcases List.mem_cons.mp member with rfl|later
      · rfl
      · have same:=List.mem_singleton.mp later
        subst current
        rfl }
  let whole:=((p0.append pn).append pd).append p4
  refine ⟨whole.trace,whole.head,whole.chain,whole.last,?_,whole.contexts⟩
  have count:=whole.count
  omega

end PaperProofs.Common.Native.PSTRWordBool.RatCmp.Reader
