module

public import Common.PSTR_WordBool_RatOutputCode_074

/-! Actual two-field loops. Header tally is physically stored above a
fresh TRUE sentinel on7; payload consumes exactly those actual FALSEs.
No runtime length, Nat value or supplied rational answer enters control. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatOutput

open Turing RationalControllerComputation PSTRTMRawNat010

variable {C : Type*}

def Safe (background : Stack → List Bool) (context : C) (bound : Nat) (current : State C) : Prop :=
  current.var.1 = context ∧
    (∀ slot, slot ≠ 13 → slot ≠ 14 → slot ≠ 7 → slot ≠ 15 → current.stk slot = background slot) ∧
    occupied current.stk ≤ bound

theorem safe_state (background : Stack → List Bool) (context : C) (memory : Store) (point : Label)
    (right left counter target : List Bool) (bound : Nat)
    (mass : outside background + right.length + left.length + counter.length + target.length ≤ bound) :
    Safe background context bound (state background point context memory right left counter target) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro slot notR notL notC notT
    simp only [state,cells,notR,notL,notC,notT,ite_false]
  · rw [occupied_state]
    exact mass

theorem safe_mono {background : Stack → List Bool} {context : C} {small large : Nat} {current : State C}
    (safe : Safe background context small current) (bound : small ≤ large) : Safe background context large current :=
  ⟨safe.1,safe.2.1,safe.2.2.trans bound⟩

def headerTrace (second : Bool) (background : Stack → List Bool) (context : C) :
    Nat → Store → List Bool → List Bool → List Bool → List Bool → List (State C)
  | 0,memory,right,left,counter,target =>
      [state background (if second then 4 else 2) context memory (false::right) left counter target,
       state background (if second then 5 else 3) context (true,false) right left counter target]
  | count+1,memory,right,left,counter,target =>
      state background (if second then 4 else 2) context memory
        (List.replicate (count+1) true ++ false::right) left counter target ::
      headerTrace second background context count (true,true) right left (false::counter) target

theorem header_head (second : Bool) (background : Stack → List Bool) (context : C) (count : Nat)
    (memory : Store) (right left counter target : List Bool) :
    (headerTrace second background context count memory right left counter target).head? =
      some (state background (if second then 4 else 2) context memory
        (List.replicate count true ++ false::right) left counter target) := by
  cases count <;> rfl

theorem header_nonempty (second : Bool) (background : Stack → List Bool) (context : C) (count : Nat)
    (memory : Store) (right left counter target : List Bool) :
    headerTrace second background context count memory right left counter target ≠ [] := by
  cases count <;> intro same <;> cases same

theorem header_last (second : Bool) (background : Stack → List Bool) (context : C) (count : Nat)
    (memory : Store) (right left counter target : List Bool) :
    (headerTrace second background context count memory right left counter target).getLast? =
      some (state background (if second then 5 else 3) context (true,false) right left
        (List.replicate count false ++ counter) target) := by
  induction count generalizing memory counter with
  | zero => rfl
  | succ count ih =>
    rw [headerTrace,List.getLast?_cons_of_ne_nil (header_nonempty _ _ _ _ _ _ _ _ _),ih]
    simp only [List.replicate_succ',List.append_assoc,List.singleton_append]

theorem header_chain (caller : Statement C) (second : Bool) (background : Stack → List Bool) (context : C)
    (count : Nat) (memory : Store) (right left counter target : List Bool) :
    (headerTrace second background context count memory right left counter target).IsChain
      (fun a b => TM2.step (program caller) a = some b) := by
  induction count generalizing memory counter with
  | zero => exact List.isChain_cons_cons.mpr ⟨header_false caller background context memory second right left counter target,
      List.isChain_singleton _⟩
  | succ count ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_,ih (true,true) (false::counter)⟩
    intro next member
    rw [header_head] at member
    have same : next = _ := (Option.mem_some_iff.mp member).symm
    subst next
    simpa only [List.replicate_succ,List.cons_append] using
      header_true caller background context memory second (List.replicate count true ++ false::right) left counter target

theorem header_length (second : Bool) (background : Stack → List Bool) (context : C) (count : Nat)
    (memory : Store) (right left counter target : List Bool) :
    (headerTrace second background context count memory right left counter target).length = count+2 := by
  induction count generalizing memory counter with
  | zero => rfl
  | succ count ih => simp only [headerTrace,List.length_cons,ih]

theorem header_safe (second : Bool) (background : Stack → List Bool) (context : C) (count : Nat)
    (memory : Store) (right left counter target : List Bool) :
    ∀ current ∈ headerTrace second background context count memory right left counter target,
      Safe background context (outside background + (count+1+right.length) + left.length + counter.length + target.length) current := by
  induction count generalizing memory counter with
  | zero =>
    intro current member
    simp only [headerTrace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals apply safe_state
    all_goals try simp only [List.length_cons]
    all_goals omega
  | succ count ih =>
    intro current member
    rcases List.mem_cons.mp member with same | later
    · subst current
      apply safe_state
      simp only [List.length_append,List.length_replicate,List.length_cons]
      omega
    · exact safe_mono (ih (true,true) (false::counter) current later)
        (by simp only [List.length_cons]; omega)

def payloadTrace (second : Bool) (background : Stack → List Bool) (context : C) :
    List Bool → Store → List Bool → List Bool → List Bool → List Bool → List (State C)
  | [],memory,right,left,counter,target =>
      [state background (if second then 5 else 3) context memory right left (true::counter) target,
       state background (if second then 6 else 4) context (true,true)
         (if second then right.tail else right) (false::false::left)
         (if second then counter else true::counter) target]
  | digit::later,memory,right,left,counter,target =>
      state background (if second then 5 else 3) context memory (digit::(later++right)) left
        (List.replicate (later.length+1) false ++ true::counter) target ::
      payloadTrace second background context later (true,digit) right (digit::true::left) counter target

theorem payload_head (second : Bool) (background : Stack → List Bool) (context : C) (digits : List Bool)
    (memory : Store) (right left counter target : List Bool) :
    (payloadTrace second background context digits memory right left counter target).head? =
      some (state background (if second then 5 else 3) context memory (digits++right) left
        (List.replicate digits.length false ++ true::counter) target) := by
  cases digits <;> rfl

theorem payload_nonempty (second : Bool) (background : Stack → List Bool) (context : C) (digits : List Bool)
    (memory : Store) (right left counter target : List Bool) :
    payloadTrace second background context digits memory right left counter target ≠ [] := by
  cases digits <;> intro same <;> cases same

theorem payload_last (second : Bool) (background : Stack → List Bool) (context : C) (digits : List Bool)
    (memory : Store) (right left counter target : List Bool) :
    (payloadTrace second background context digits memory right left counter target).getLast? =
      some (state background (if second then 6 else 4) context (true,true)
        (if second then right.tail else right) (false::false::((leftBlocks digits).reverse++left))
        (if second then counter else true::counter) target) := by
  induction digits generalizing memory left with
  | nil => rfl
  | cons digit later ih =>
    rw [payloadTrace,List.getLast?_cons_of_ne_nil (payload_nonempty _ _ _ _ _ _ _ _ _),ih]
    simp only [leftBlocks,List.flatMap_cons,List.reverse_cons,
      List.append_assoc,List.nil_append,List.cons_append]

theorem payload_chain (caller : Statement C) (second : Bool) (background : Stack → List Bool) (context : C)
    (digits : List Bool) (memory : Store) (right left counter target : List Bool) :
    (payloadTrace second background context digits memory right left counter target).IsChain
      (fun a b => TM2.step (program caller) a = some b) := by
  induction digits generalizing memory left with
  | nil =>
    apply List.isChain_cons_cons.mpr
    refine ⟨?_,List.isChain_singleton _⟩
    cases second
    · exact numerator_done caller background context memory right left counter target
    · exact denominator_done caller background context memory right left counter target
  | cons digit later ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_,ih (true,digit) (digit::true::left)⟩
    intro next member
    rw [payload_head] at member
    have same : next = _ := (Option.mem_some_iff.mp member).symm
    subst next
    simpa only [List.replicate_succ,List.cons_append] using payload_step caller background context memory second digit
      (later++right) left (List.replicate later.length false ++ true::counter) target

theorem payload_length (second : Bool) (background : Stack → List Bool) (context : C) (digits : List Bool)
    (memory : Store) (right left counter target : List Bool) :
    (payloadTrace second background context digits memory right left counter target).length = digits.length+2 := by
  induction digits generalizing memory left with
  | nil => rfl
  | cons digit later ih => simp only [payloadTrace,List.length_cons,ih]

theorem flagged_length (digits : List Bool) : (leftBlocks digits).length = 2*digits.length := by
  induction digits with
  | nil => rfl
  | cons bit later ih => simp only [leftBlocks,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at *; omega

theorem payload_safe (second : Bool) (background : Stack → List Bool) (context : C) (digits : List Bool)
    (memory : Store) (right left counter target : List Bool) :
    ∀ current ∈ payloadTrace second background context digits memory right left counter target,
      Safe background context (outside background + 2*digits.length + right.length + left.length + counter.length + target.length + 3) current := by
  induction digits generalizing memory left with
  | nil =>
    intro current member
    simp only [payloadTrace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · apply safe_state; simp only [List.length_cons]; omega
    · cases second <;> apply safe_state <;> simp only [Bool.false_eq_true,ite_false,ite_true,List.length_cons,List.length_tail] <;> omega
  | cons digit later ih =>
    intro current member
    rcases List.mem_cons.mp member with same | remaining
    · subst current
      apply safe_state
      simp only [List.length_cons,List.length_append,List.length_replicate]
      omega
    · exact safe_mono (ih (true,digit) (digit::true::left) current remaining)
        (by simp only [List.length_cons]; omega)

end PaperProofs.Common.Native.PSTRWordBool.RatOutput
