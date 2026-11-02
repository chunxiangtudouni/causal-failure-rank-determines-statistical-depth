module

public import PSTR_WordBool_RatDrop_Code_001

/-! Actual field paths and current-data mass/frame invariants for result
parking or operand disposal. The field-end00 is consumed physically. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatDrop

open Turing PSTRWordVM RationalControllerComputation PSTRTMRawNat010
open scoped BigOperators

variable {C : Type*}

def outside (background : Stack→List Bool) : Nat:=
  ∑ slot,if slot=15 ∨ slot=3 then 0 else (background slot).length

def Safe (background : Stack→List Bool) (context : C) (bound : Nat) (current : State C) : Prop:=
  current.var.1=context ∧
    (∀ slot,slot≠15→slot≠3→current.stk slot=background slot) ∧ RatInput.occupied current.stk≤bound

theorem occupied_state (background : Stack→List Bool) (point : Label) (context : C)
    (memory : RatOutput.Store) (source parked : List Bool) :
    RatInput.occupied (state background point context memory source parked).stk=
      outside background+source.length+parked.length := by
  simp [RatInput.occupied,state,cells,outside,Fin.sum_univ_succ,Nat.add_assoc]
  omega

theorem safe_state (background : Stack→List Bool) (point : Label) (context : C)
    (memory : RatOutput.Store) (source parked : List Bool) (bound : Nat)
    (mass : outside background+source.length+parked.length≤bound) :
    Safe background context bound (state background point context memory source parked) := by
  refine ⟨rfl,?_,?_⟩
  · intro slot noSource noPark
    simp only [state,cells,noSource,noPark,ite_false]
  · rw [occupied_state]
    exact mass

theorem safe_mono {background : Stack→List Bool} {context : C} {small large : Nat} {current : State C}
    (safe : Safe background context small current) (le : small≤large) : Safe background context large current :=
  ⟨safe.1,safe.2.1,safe.2.2.trans le⟩

def fieldCopied (keep : Bool) (digits parked : List Bool) : List Bool:=
  if keep then (leftBlocks digits++[false,false]).reverse++parked else parked

def fieldTrace (keep : Bool) (background : Stack→List Bool) (context : C) (point next : Label) :
    List Bool→RatOutput.Store→List Bool→List Bool→List (State C)
  | [],memory,source,parked=>
      [state background point context memory (false::false::source) parked,
       state background next context (true,false) source (if keep then false::false::parked else parked)]
  | digit::later,memory,source,parked=>
      state background point context memory (true::digit::(leftBlocks later++false::false::source)) parked::
        fieldTrace keep background context point next later (true,digit) source
          (if keep then digit::true::parked else parked)

theorem field_head (keep : Bool) (background : Stack→List Bool) (context : C) (point next : Label)
    (digits : List Bool) (memory : RatOutput.Store) (source parked : List Bool) :
    (fieldTrace keep background context point next digits memory source parked).head?=
      some (state background point context memory (leftBlocks digits++false::false::source) parked) := by
  cases digits <;> rfl

theorem field_nonempty (keep : Bool) (background : Stack→List Bool) (context : C) (point next : Label)
    (digits : List Bool) (memory : RatOutput.Store) (source parked : List Bool) :
    fieldTrace keep background context point next digits memory source parked≠[] := by
  cases digits <;> intro same <;> cases same

theorem field_last (keep : Bool) (background : Stack→List Bool) (context : C) (point next : Label)
    (digits : List Bool) (memory : RatOutput.Store) (source parked : List Bool) :
    (fieldTrace keep background context point next digits memory source parked).getLast?=
      some (state background next context (true,false) source (fieldCopied keep digits parked)) := by
  induction digits generalizing memory parked with
  | nil => cases keep <;> rfl
  | cons digit later ih =>
    rw [fieldTrace,List.getLast?_cons_of_ne_nil (field_nonempty _ _ _ _ _ _ _ _ _),ih]
    cases keep <;> simp [fieldCopied,leftBlocks,List.flatMap_cons,List.reverse_cons,List.append_assoc]

theorem field_chain (caller : Statement C) (keep : Bool) (background : Stack→List Bool) (context : C)
    (point next : Label) (code : program caller point=fieldBody keep point next)
    (digits : List Bool) (memory : RatOutput.Store) (source parked : List Bool) :
    (fieldTrace keep background context point next digits memory source parked).IsChain
      (fun a b=>TM2.step (program caller) a=some b) := by
  induction digits generalizing memory parked with
  | nil =>
    exact List.isChain_cons_cons.mpr ⟨field_end caller keep point next code background context memory source parked,
      List.isChain_singleton _⟩
  | cons digit later ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_,ih (true,digit) (if keep then digit::true::parked else parked)⟩
    intro after member
    rw [field_head] at member
    have equal : after=_:=(Option.mem_some_iff.mp member).symm
    subst after
    exact field_bit caller keep point next code background context memory digit
      (leftBlocks later++false::false::source) parked

theorem field_length (keep : Bool) (background : Stack→List Bool) (context : C) (point next : Label)
    (digits : List Bool) (memory : RatOutput.Store) (source parked : List Bool) :
    (fieldTrace keep background context point next digits memory source parked).length=digits.length+2 := by
  induction digits generalizing memory parked with
  | nil => rfl
  | cons digit later ih => simp only [fieldTrace,List.length_cons,ih]

theorem field_safe (keep : Bool) (background : Stack→List Bool) (context : C) (point next : Label)
    (digits : List Bool) (memory : RatOutput.Store) (source parked : List Bool) :
    ∀ current∈fieldTrace keep background context point next digits memory source parked,
      Safe background context (outside background+2*digits.length+2+source.length+parked.length) current := by
  induction digits generalizing memory parked with
  | nil =>
    intro current member
    simp only [fieldTrace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · apply safe_state
      simp only [List.length_cons,List.length_nil]
      omega
    · apply safe_state
      cases keep <;> simp only [Bool.false_eq_true,ite_false,ite_true,List.length_cons,List.length_nil]
      all_goals omega
  | cons digit later ih =>
    intro current member
    rcases List.mem_cons.mp member with same|remaining
    · subst current
      apply safe_state
      simp only [List.length_cons,List.length_append,RatOutput.flagged_length]
      omega
    · apply safe_mono (ih (true,digit) (if keep then digit::true::parked else parked) current remaining)
      cases keep <;> simp only [Bool.false_eq_true,ite_false,ite_true,List.length_cons]
      all_goals omega

end PaperProofs.Common.Native.PSTRWordBool.RatDrop
