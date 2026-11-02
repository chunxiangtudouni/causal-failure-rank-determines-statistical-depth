module

public import Common.PSTR_WordBool_RatInputCode_082

/-! Actual signed packet-field collection. Source cells are really popped
and backed above the TRUE sentinel. The field bits are raw lists, not
fixed-width structural Words; no length or answer is a control field. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatInput

open Turing RationalControllerComputation PSTRSymbolicNaturalExport PSTRTMRawNat010

variable {C : Type*}

def fieldTrace (second : Bool) (background : Stack → List Bool) (context : C) (mode : Bool) :
    List Bool → Bool → Bool → List Bool → List Bool → List Bool → List Bool → List Bool → List Bool → List (State C)
  | [],bit,flag,copied,source,scratch,numerator,denominator,raw =>
      [state background (if second then 2 else 1) context (bit,flag,mode)
        (false::false::source) (backups copied ++ true::scratch) numerator denominator raw,
       state background (if second then 3 else 2) context (false,false,mode) source
         (backups (false::false::copied) ++ true::scratch) numerator denominator raw]
  | digit::later,bit,flag,copied,source,scratch,numerator,denominator,raw =>
      state background (if second then 2 else 1) context (bit,flag,mode)
        (true::digit::(leftBlocks later ++ false::false::source)) (backups copied ++ true::scratch) numerator denominator raw ::
      fieldTrace second background context mode later digit true (digit::true::copied) source scratch
        (if second then numerator else digit::numerator) (if second then digit::denominator else denominator) raw

theorem field_head (second : Bool) (background : Stack → List Bool) (context : C) (mode : Bool) (digits : List Bool)
    (bit flag : Bool) (copied source scratch numerator denominator raw : List Bool) :
    (fieldTrace second background context mode digits bit flag copied source scratch numerator denominator raw).head? =
      some (state background (if second then 2 else 1) context (bit,flag,mode)
        (leftBlocks digits ++ false::false::source) (backups copied ++ true::scratch) numerator denominator raw) := by
  cases digits <;> rfl

theorem field_nonempty (second : Bool) (background : Stack → List Bool) (context : C) (mode : Bool) (digits : List Bool)
    (bit flag : Bool) (copied source scratch numerator denominator raw : List Bool) :
    fieldTrace second background context mode digits bit flag copied source scratch numerator denominator raw ≠ [] := by
  cases digits <;> intro same <;> cases same

theorem field_length (second : Bool) (background : Stack → List Bool) (context : C) (mode : Bool) (digits : List Bool)
    (bit flag : Bool) (copied source scratch numerator denominator raw : List Bool) :
    (fieldTrace second background context mode digits bit flag copied source scratch numerator denominator raw).length = digits.length+2 := by
  induction digits generalizing bit flag copied numerator denominator with
  | nil => rfl
  | cons digit later ih => simp only [fieldTrace,List.length_cons,ih]

theorem field_chain (caller : Statement C) (second : Bool) (background : Stack → List Bool) (context : C)
    (mode : Bool) (digits : List Bool) (bit flag : Bool) (copied source scratch numerator denominator raw : List Bool) :
    (fieldTrace second background context mode digits bit flag copied source scratch numerator denominator raw).IsChain
      (fun a b => TM2.step (program caller) a = some b) := by
  induction digits generalizing bit flag copied numerator denominator with
  | nil =>
    apply List.isChain_cons_cons.mpr
    refine ⟨?_,List.isChain_singleton _⟩
    cases second
    · simpa only [Bool.false_eq_true,ite_false,backups,List.flatMap_cons,List.cons_append,List.nil_append] using
        numerator_end caller background context bit flag mode source (backups copied ++ true::scratch) numerator denominator raw
    · simpa only [ite_true,backups,List.flatMap_cons,List.cons_append,List.nil_append] using
        denominator_end caller background context bit flag mode source (backups copied ++ true::scratch) numerator denominator raw
  | cons digit later ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_,ih digit true (digit::true::copied) _ _⟩
    intro next member
    rw [field_head] at member
    have same : next = _ := (Option.mem_some_iff.mp member).symm
    subst next
    cases second
    · simpa only [Bool.false_eq_true,ite_false,backups,List.flatMap_cons,List.cons_append,List.nil_append] using
        numerator_step caller background context bit flag mode digit (leftBlocks later ++ false::false::source)
          (backups copied ++ true::scratch) numerator denominator raw
    · simpa only [ite_true,backups,List.flatMap_cons,List.cons_append,List.nil_append] using
        denominator_step caller background context bit flag mode digit (leftBlocks later ++ false::false::source)
          (backups copied ++ true::scratch) numerator denominator raw

theorem field_last (second : Bool) (background : Stack → List Bool) (context : C) (mode : Bool) (digits : List Bool)
    (bit flag : Bool) (copied source scratch numerator denominator raw : List Bool) :
    (fieldTrace second background context mode digits bit flag copied source scratch numerator denominator raw).getLast? =
      some (state background (if second then 3 else 2) context (false,false,mode) source
        (backups (false::false::((leftBlocks digits).reverse++copied)) ++ true::scratch)
        (if second then numerator else digits.reverse++numerator)
        (if second then digits.reverse++denominator else denominator) raw) := by
  induction digits generalizing bit flag copied numerator denominator with
  | nil => cases second <;> rfl
  | cons digit later ih =>
    rw [fieldTrace,List.getLast?_cons_of_ne_nil (field_nonempty _ _ _ _ _ _ _ _ _ _ _ _ _),ih]
    cases second <;> simp [leftBlocks,List.flatMap_cons,List.reverse_cons,List.append_assoc]

def baseMass (background : Stack → List Bool) : Nat :=
  ∑ point, if point = (15 : Stack) ∨ point = 7 ∨ point = 3 ∨ point = 4 ∨ point = 13 then 0 else (background point).length

def occupied (contents : Stack → List Bool) : Nat := ∑ point, (contents point).length

theorem occupied_state (background : Stack → List Bool) (point : Label) (context : C) (memory : Store)
    (source scratch numerator denominator raw : List Bool) :
    occupied (state background point context memory source scratch numerator denominator raw).stk =
      baseMass background+source.length+scratch.length+numerator.length+denominator.length+raw.length := by
  simp [occupied,state,cells,baseMass,Fin.sum_univ_succ,Nat.add_assoc]
  omega

theorem field_mass (second : Bool) (background : Stack → List Bool) (context : C) (mode : Bool) (digits : List Bool)
    (bit flag : Bool) (copied source scratch numerator denominator raw : List Bool) :
    ∀ current ∈ fieldTrace second background context mode digits bit flag copied source scratch numerator denominator raw,
      occupied current.stk ≤ baseMass background+5*digits.length+2*copied.length+source.length+scratch.length+
        numerator.length+denominator.length+raw.length+5 := by
  induction digits generalizing bit flag copied numerator denominator with
  | nil =>
    intro current member
    simp only [fieldTrace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals rw [occupied_state]
    all_goals simp only [List.length_cons,List.length_append,backups_length]
    all_goals omega
  | cons digit later ih =>
    intro current member
    rcases List.mem_cons.mp member with same | remaining
    · subst current
      rw [occupied_state]
      simp only [List.length_cons,List.length_append,backups_length,RatOutput.flagged_length]
      omega
    · have bound := ih digit true (digit::true::copied) _ _ current remaining
      cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true,List.length_cons] at bound ⊢ <;> omega

end PaperProofs.Common.Native.PSTRWordBool.RatInput
