module

public import RootB234_Cells_Public_003
public import Common.PSTR_TM_Canonical_020

/-! The exponent's physical canonical Nat packet is kept on11, a framed
stack of the renamed RatPair callee. Only the carry loop is new; restoration
executes the frozen Cells reverse body. No width, host counter or fuel is
stored in control. Both owned00 guards and an arbitrary packet tail survive. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.NatIncrement
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation PSTRWordVM
open PSTRTMIncrement009 PSTRTMRawNat010

abbrev Stack := RatInput.Stack
abbrev Label := RatDrop.Label
abbrev Store (C : Type*) := C × RatOutput.Store
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)
variable {C : Type*}

def reverseRoles : Stack ≃ Stack := Equiv.swap 2 11

def restoreBody : Statement C :=
  StackIso.statement reverseRoles (Cells.body .reverse3To2)

def program (caller : Statement C) (point : Label) : Statement C :=
  if point=0 then
    .pop 11 RatDrop.capture (.branch RatDrop.bit
      (.pop 11 RatDrop.capture (.branch RatDrop.bit
        (.push 3 (fun _ => true) (.push 3 (fun _ => false) (.goto (fun _ => 0))))
        (.push 11 (fun _ => true) (.push 11 (fun _ => true) (.goto (fun _ => 3))))))
      (.push 11 (fun _ => false) (.push 11 (fun _ => true)
        (.push 11 (fun _ => true) (.goto (fun _ => 3))))))
  else if point=3 then restoreBody else caller

def bank (background : Stack → List Bool) (source temporary : List Bool) : Stack → List Bool :=
  fun point => if point=11 then source else if point=3 then temporary else background point

def state (background : Stack → List Bool) (point : Label) (context : C)
    (memory : RatOutput.Store) (source temporary : List Bool) : State C :=
  ⟨some point,(context,memory),bank background source temporary⟩

theorem step_one (caller : Statement C) (background : Stack → List Bool) (context : C)
    (memory : RatOutput.Store) (source temporary : List Bool) :
    TM2.step (program caller) (state background 0 context memory (true::true::source) temporary)=
      some (state background 0 context (true,true) source (false::true::temporary)) := by
  change some (⟨some 0,(context,true,true),_⟩ : State C)=_
  congr 1; congr 1
  funext point;fin_cases point <;> rfl

theorem step_zero (caller : Statement C) (background : Stack → List Bool) (context : C)
    (memory : RatOutput.Store) (source temporary : List Bool) :
    TM2.step (program caller) (state background 0 context memory (true::false::source) temporary)=
      some (state background 3 context (true,false) (true::true::source) temporary) := by
  change some (⟨some 3,(context,true,false),_⟩ : State C)=_
  congr 1; congr 1
  funext point;fin_cases point <;> rfl

theorem step_guard (caller : Statement C) (background : Stack → List Bool) (context : C)
    (memory : RatOutput.Store) (tail temporary : List Bool) :
    TM2.step (program caller) (state background 0 context memory (false::false::tail) temporary)=
      some (state background 3 context (true,false) (true::true::false::false::tail) temporary) := by
  change some (⟨some 3,(context,true,false),_⟩ : State C)=_
  congr 1; congr 1
  funext point;fin_cases point <;> rfl

theorem step_restore (caller : Statement C) (background : Stack → List Bool) (context : C)
    (memory : RatOutput.Store) (bit : Bool) (source temporary : List Bool) :
    TM2.step (program caller) (state background 3 context memory source (bit::temporary))=
      some (state background 3 context (true,bit) (bit::source) temporary) := by
  change some (⟨some 3,(context,true,bit),_⟩ : State C)=_
  congr 1; congr 1
  funext point;fin_cases point <;> rfl

theorem step_return (caller : Statement C) (background : Stack → List Bool) (context : C)
    (memory : RatOutput.Store) (source : List Bool) :
    TM2.step (program caller) (state background 3 context memory source [])=
      some (state background 4 context (false,false) source []) := by
  change some (⟨some 4,(context,false,false),_⟩ : State C)=_
  congr 1; congr 1
  funext point;fin_cases point <;> rfl

def restoreTrace (background : Stack → List Bool) (context : C) :
    RatOutput.Store → List Bool → List Bool → List (State C)
  | memory,source,[] => [state background 3 context memory source [],
      state background 4 context (false,false) source []]
  | memory,source,bit::later => state background 3 context memory source (bit::later) ::
      restoreTrace background context (true,bit) (bit::source) later

theorem restore_head (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (source temporary : List Bool) :
    (restoreTrace background context memory source temporary).head?=
      some (state background 3 context memory source temporary) := by cases temporary <;> rfl

theorem restore_nonempty (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (source temporary : List Bool) : restoreTrace background context memory source temporary≠[] := by
  cases temporary <;> simp [restoreTrace]

theorem restore_chain (caller : Statement C) (background : Stack → List Bool) (context : C)
    (memory : RatOutput.Store) (source temporary : List Bool) :
    (restoreTrace background context memory source temporary).IsChain
      (fun before after => TM2.step (program caller) before=some after) := by
  induction temporary generalizing memory source with
  | nil => exact List.isChain_cons_cons.mpr ⟨step_return caller background context memory source,by simp⟩
  | cons bit later ih =>
      apply List.isChain_cons.mpr
      refine ⟨?_,ih _ _⟩
      intro next head
      rw [restore_head] at head
      have same := (Option.mem_some_iff.mp head).symm
      subst next
      exact step_restore caller background context memory bit source later

theorem restore_last (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (source temporary : List Bool) :
    (restoreTrace background context memory source temporary).getLast?=
      some (state background 4 context (false,false) (temporary.reverse++source) []) := by
  induction temporary generalizing memory source with
  | nil => rfl
  | cons bit later ih =>
      rw [restoreTrace,List.getLast?_cons_of_ne_nil (restore_nonempty _ _ _ _ _),ih]
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

theorem restore_length (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (source temporary : List Bool) :
    (restoreTrace background context memory source temporary).length=temporary.length+2 := by
  induction temporary generalizing memory source with
  | nil => rfl
  | cons bit later ih => simp only [restoreTrace,List.length_cons,ih]

def actualTrace (background : Stack → List Bool) (context : C) :
    RatOutput.Store → List Bool → List Bool → List Bool → List (State C)
  | memory,[],tail,temporary =>
      state background 0 context memory (false::false::tail) temporary ::
        restoreTrace background context (true,false) (true::true::false::false::tail) temporary
  | memory,false::later,tail,temporary =>
      state background 0 context memory (true::false::(leftBlocks later++false::false::tail)) temporary ::
        restoreTrace background context (true,false) (true::true::(leftBlocks later++false::false::tail)) temporary
  | memory,true::later,tail,temporary =>
      state background 0 context memory (true::true::(leftBlocks later++false::false::tail)) temporary ::
        actualTrace background context (true,true) later tail (false::true::temporary)

theorem actual_head (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (digits tail temporary : List Bool) :
    (actualTrace background context memory digits tail temporary).head?=
      some (state background 0 context memory (leftBlocks digits++false::false::tail) temporary) := by
  cases digits with
  | nil => rfl
  | cons bit later => cases bit <;> rfl

theorem actual_nonempty (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (digits tail temporary : List Bool) : actualTrace background context memory digits tail temporary≠[] := by
  intro empty
  have head := actual_head background context memory digits tail temporary
  rw [empty] at head
  cases head

theorem actual_chain (caller : Statement C) (background : Stack → List Bool) (context : C)
    (memory : RatOutput.Store) (digits tail temporary : List Bool) :
    (actualTrace background context memory digits tail temporary).IsChain
      (fun before after => TM2.step (program caller) before=some after) := by
  induction digits generalizing memory temporary with
  | nil =>
      apply List.isChain_cons.mpr
      refine ⟨?_,restore_chain caller _ _ _ _ _⟩
      intro next head
      rw [restore_head] at head
      have same := (Option.mem_some_iff.mp head).symm
      subst next
      exact step_guard caller background context memory tail temporary
  | cons bit later ih =>
      cases bit with
      | false =>
          apply List.isChain_cons.mpr
          refine ⟨?_,restore_chain caller _ _ _ _ _⟩
          intro next head
          rw [restore_head] at head
          have same := (Option.mem_some_iff.mp head).symm
          subst next
          exact step_zero caller background context memory _ _
      | true =>
          apply List.isChain_cons.mpr
          refine ⟨?_,ih _ _⟩
          intro next head
          rw [actual_head] at head
          have same := (Option.mem_some_iff.mp head).symm
          subst next
          exact step_one caller background context memory _ _

theorem actual_last (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (digits tail temporary : List Bool) :
    (actualTrace background context memory digits tail temporary).getLast?=
      some (state background 4 context (false,false)
        (temporary.reverse++leftBlocks (bumpDigits digits)++false::false::tail) []) := by
  induction digits generalizing memory temporary with
  | nil =>
      rw [actualTrace,List.getLast?_cons_of_ne_nil (restore_nonempty _ _ _ _ _),restore_last]
      simp [bumpDigits,leftBlocks,List.append_assoc]
  | cons bit later ih =>
      cases bit with
      | false =>
          rw [actualTrace,List.getLast?_cons_of_ne_nil (restore_nonempty _ _ _ _ _),restore_last]
          simp [bumpDigits,leftBlocks,List.append_assoc]
      | true =>
          rw [actualTrace,List.getLast?_cons_of_ne_nil (actual_nonempty _ _ _ _ _ _),ih]
          simp only [List.reverse_cons,List.append_assoc,bumpDigits,leftBlocks,
            List.flatMap_cons,List.cons_append,List.nil_append]

theorem actual_length (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (digits tail temporary : List Bool) :
    (actualTrace background context memory digits tail temporary).length≤3*digits.length+temporary.length+3 := by
  induction digits generalizing memory temporary with
  | nil => simp only [actualTrace,List.length_cons,restore_length,List.length_nil]; omega
  | cons bit later ih =>
      cases bit with
      | false => simp only [actualTrace,List.length_cons,restore_length]; omega
      | true =>
          have bound := ih (true,true) (false::true::temporary)
          simp only [actualTrace,List.length_cons] at *
          omega

theorem actual_natural (caller : Statement C) (background : Stack → List Bool) (context : C)
    (memory : RatOutput.Store) (number : Nat) (tail : List Bool) :
    ∃ run : List (State C),
      run.head?=some (state background 0 context memory (B23_4_RatWordPrep.NatField.packet number tail) []) ∧
      run.IsChain (fun before after => TM2.step (program caller) before=some after) ∧
      run.getLast?=some (state background 4 context (false,false) (B23_4_RatWordPrep.NatField.packet (number+1) tail) []) ∧
      run.length≤3*(PSTRTMNatValue017.rawPayload number).length+3 := by
  refine ⟨actualTrace background context memory (PSTRTMNatValue017.rawPayload number) tail [],actual_head _ _ _ _ _ _,
    actual_chain caller _ _ _ _ _ _,?_,?_⟩
  · simpa only [PSTRTMCanonical020.bump_rawPayload_eq,List.reverse_nil,List.nil_append,
      B23_4_RatWordPrep.NatField.packet] using
        actual_last background context memory (PSTRTMNatValue017.rawPayload number) tail []
  · simpa only [List.length_nil,Nat.add_zero] using
      actual_length background context memory (PSTRTMNatValue017.rawPayload number) tail []

end RootB234.PrepExponent.NatIncrement
