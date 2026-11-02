module

public import PSTR_WordBool_RatDrop_Reverse_003

/-! A whole actual packet is parked or disposed with its two real guards.
The original signed flagged packet format is reused without another codec. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatDrop

open Turing PSTRWordVM RationalControllerComputation PSTRTMRawNat010

variable {C : Type*}

theorem packet_length (negative : Bool) (num den tail : List Bool) :
    (PSTRSymbolicRatExport.packet negative num den tail).length=2*(num.length+den.length)+6+tail.length := by
  simp only [PSTRSymbolicRatExport.packet,List.length_cons,List.length_append,RatOutput.flagged_length]
  omega

theorem copied_length (keep : Bool) (digits parked : List Bool) :
    (fieldCopied keep digits parked).length≤2*digits.length+2+parked.length := by
  cases keep with
  | false => simp [fieldCopied]
  | true =>
    simp only [fieldCopied,ite_true,List.length_append,List.length_reverse,
      RatOutput.flagged_length,List.length_cons,List.length_nil]
    omega

theorem copied_packet (keep : Bool) (negative : Bool) (num den parked : List Bool) :
    fieldCopied keep den (fieldCopied keep num (if keep then negative::true::parked else parked))=
      if keep then (PSTRSymbolicRatExport.packet negative num den []).reverse++parked else parked := by
  cases keep <;> simp [fieldCopied,PSTRSymbolicRatExport.packet,List.reverse_append,List.append_assoc]

structure Segment (caller : Statement C) (background : Stack→List Bool) (context : C) (bound : Nat)
    (before final : State C) (budget : Nat) where
  trace : List (State C)
  head : trace.head?=some before
  chain : trace.IsChain (fun a b=>TM2.step (program caller) a=some b)
  last : trace.getLast?=some final
  count : trace.length≤budget
  safe : ∀ current∈trace,Safe background context bound current

def Segment.append {caller : Statement C} {background : Stack→List Bool} {context : C} {bound : Nat}
    {before middle final : State C} {frontBudget backBudget : Nat}
    (front : Segment caller background context bound before middle frontBudget)
    (back : Segment caller background context bound middle final backBudget) :
    Segment caller background context bound before final (frontBudget+backBudget-1) := by
  have shape : middle::back.trace.tail=back.trace :=by
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
    · exact front.safe current early
    · exact back.safe current (List.mem_of_mem_tail later)

theorem actual_packet (caller : Statement C) (keep : Bool) (background : Stack→List Bool) (context : C)
    (header numPoint denPoint next : Label)
    (headerCode : program caller header=headerBody keep numPoint)
    (numCode : program caller numPoint=fieldBody keep numPoint denPoint)
    (denCode : program caller denPoint=fieldBody keep denPoint next)
    (memory : RatOutput.Store) (negative : Bool) (num den tail parked : List Bool) :
    ∃ trace : List (State C),
      trace.head?=some (state background header context memory (PSTRSymbolicRatExport.packet negative num den tail) parked) ∧
      trace.IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
      trace.getLast?=some (state background next context (true,false) tail
        (if keep then (PSTRSymbolicRatExport.packet negative num den []).reverse++parked else parked)) ∧
      trace.length≤num.length+den.length+4 ∧
      ∀ current∈trace,Safe background context
        (outside background+(PSTRSymbolicRatExport.packet negative num den tail).length+parked.length) current := by
  let K:=outside background+(PSTRSymbolicRatExport.packet negative num den tail).length+parked.length
  let afterNum:=leftBlocks den++false::false::tail
  let hPark:=if keep then negative::true::parked else parked
  let nPark:=fieldCopied keep num hPark
  let dPark:=fieldCopied keep den nPark
  let s0:=state background header context memory (PSTRSymbolicRatExport.packet negative num den tail) parked
  let s1:=state background numPoint context (true,negative) (leftBlocks num++false::false::afterNum) hPark
  let s2:=state background denPoint context (true,false) afterNum nPark
  let s3:=state background next context (true,false) tail dPark
  have headerStep : TM2.step (program caller) s0=some s1:=
    header_step caller keep header numPoint headerCode background context memory negative
      (leftBlocks num++false::false::afterNum) parked
  have hBound : hPark.length≤parked.length+2 :=by cases keep <;> simp [hPark]
  have nBound : nPark.length≤2*num.length+parked.length+4:=by
    have copied:=copied_length keep num hPark
    dsimp only [nPark]
    omega
  have boot : Segment caller background context K s0 s1 2:={
    trace:=[s0,s1],head:=rfl,last:=rfl,count:=Nat.le_refl _
    chain:=List.isChain_cons_cons.mpr ⟨headerStep,List.isChain_singleton _⟩
    safe:=by
      intro current member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl
      · apply safe_state
        exact Nat.le_refl _
      · apply safe_state
        dsimp only [K,afterNum]
        rw [packet_length]
        simp only [List.length_append,List.length_cons,RatOutput.flagged_length]
        omega }
  have first : Segment caller background context K s1 s2 (num.length+2):={
    trace:=fieldTrace keep background context numPoint denPoint num (true,negative) afterNum hPark
    head:=field_head keep background context numPoint denPoint num (true,negative) afterNum hPark
    chain:=field_chain caller keep background context numPoint denPoint numCode num (true,negative) afterNum hPark
    last:=field_last keep background context numPoint denPoint num (true,negative) afterNum hPark
    count:=(field_length keep background context numPoint denPoint num (true,negative) afterNum hPark).le
    safe:=by
      intro current member
      apply safe_mono (field_safe keep background context numPoint denPoint num (true,negative) afterNum hPark current member)
      dsimp only [K,afterNum]
      rw [packet_length]
      simp only [List.length_append,List.length_cons,RatOutput.flagged_length]
      omega }
  have second : Segment caller background context K s2 s3 (den.length+2):={
    trace:=fieldTrace keep background context denPoint next den (true,false) tail nPark
    head:=field_head keep background context denPoint next den (true,false) tail nPark
    chain:=field_chain caller keep background context denPoint next denCode den (true,false) tail nPark
    last:=field_last keep background context denPoint next den (true,false) tail nPark
    count:=(field_length keep background context denPoint next den (true,false) tail nPark).le
    safe:=by
      intro current member
      apply safe_mono (field_safe keep background context denPoint next den (true,false) tail nPark current member)
      dsimp only [K]
      rw [packet_length]
      omega }
  let whole:=(boot.append first).append second
  refine ⟨whole.trace,whole.head,whole.chain,?_,?_,whole.safe⟩
  · have same:=copied_packet keep negative num den parked
    change dPark=_ at same
    exact whole.last.trans (congrArg some (congrArg (state background next context (true,false) tail) same))
  · have count:=whole.count
    omega

end PaperProofs.Common.Native.PSTRWordBool.RatDrop
