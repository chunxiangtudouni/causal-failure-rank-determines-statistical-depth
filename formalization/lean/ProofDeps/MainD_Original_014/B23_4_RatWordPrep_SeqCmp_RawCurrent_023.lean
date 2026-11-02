module

public import B23_4_RatWordPrep_SeqCmp_RawRun_022

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.RawGetter

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PA17TMRatArithmeticParse002

variable {C : Type*}

theorem blank_cancel_prefix (bits left right : List Bool)
    (same : ListBlank.mk (bits++left)=ListBlank.mk (bits++right)) : ListBlank.mk left=ListBlank.mk right := by
  induction bits with
  | nil => exact same
  | cons bit later ih =>
    apply ih
    exact congrArg ListBlank.tail same

/-- Original encodings have a final TRUE. That genuine marker recovers a
finite rational prefix from whole-Tape equality without discarding or
inventing the physical trailing blank cells. No source-stack reset occurs. -/
theorem actual_current_field (caller : Statement C) (background : RatInput.Stack → List Bool)
    (memory : Store C) (x : Rat) (suffix : List Bool)
    (right : ListBlank.mk (background 0)=ListBlank.mk (encodeDatum (.rational x)++suffix++[true])) :
    ∃ trace : List (State C), ∃ final parsed : State C,
      trace.head?=some (⟨some .boot,memory,background⟩ : State C) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ parsed∈trace ∧ final.l=some .done ∧ final.var.1.1=memory.1.1 ∧
      final.stk=Function.update parsed.stk 15 (RatInput.Encoder.packet x (background 15)) ∧
      Tape.mk' (ListBlank.mk (parsed.stk 1)) (ListBlank.mk (parsed.stk 0))=Tape.mk₂
        (bothLeft (false::sign x::true::background 1) (numeratorDigits x) (denominatorDigits x)) (suffix++[true]) ∧
      parsed.stk 7=background 7 ∧ parsed.stk 15=background 15 ∧ trace.length≤time x := by
  obtain ⟨physicalTail,shape⟩ := PSTRSymbolicNaturalExport.finite_marked_prefix
    (encodeDatum (.rational x)++suffix) [] (background 0) right
  let actualSuffix := suffix++true::physicalTail
  have source : background 0=encodeDatum (.rational x)++actualSuffix := by
    simpa only [actualSuffix,List.append_assoc] using shape
  have suffixTape : ListBlank.mk actualSuffix=ListBlank.mk (suffix++[true]) := by
    apply blank_cancel_prefix (encodeDatum (.rational x))
    rw [←source]
    simpa only [List.append_assoc] using right
  obtain ⟨trace,final,parsed,first,chain,last,member,active,context,contents,tape,scratch,target,count⟩ :=
    actual_raw_field caller background memory x actualSuffix
  have actualFirst : entry background memory x actualSuffix=(⟨some .boot,memory,background⟩ : State C) := by
    unfold entry
    rw [←source,Function.update_eq_self]
  have actualTape : Tape.mk₂
      (bothLeft (false::sign x::true::background 1) (numeratorDigits x) (denominatorDigits x)) actualSuffix=
      Tape.mk₂ (bothLeft (false::sign x::true::background 1) (numeratorDigits x) (denominatorDigits x)) (suffix++[true]) :=
    congrArg (Tape.mk' (ListBlank.mk (bothLeft (false::sign x::true::background 1) (numeratorDigits x) (denominatorDigits x)))) suffixTape
  exact ⟨trace,final,parsed,first.trans (congrArg some actualFirst),chain,last,member,active,context,contents,
    tape.trans actualTape,scratch,target,count⟩

end B23_4_RatWordPrep.RawGetter
