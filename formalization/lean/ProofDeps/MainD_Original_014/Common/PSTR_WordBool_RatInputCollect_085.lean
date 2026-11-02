module

public import Common.PSTR_WordBool_RatInputRestore_084

/-! ONE actual packet copy/restore path. Original15 is restored exactly,
3/4 contain actual reversed raw fields, and13 has its really pushed TRUE
footer. No input Nat, width, sign or field-list is an executable argument. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatInput

open Turing RationalControllerComputation PSTRSymbolicNaturalExport PSTRTMRawNat010

variable {C : Type*}

def Stable (background : Stack → List Bool) (context : C) (bound : Nat) (current : State C) : Prop :=
  current.var.1=context ∧
    (∀ slot, slot≠15 → slot≠7 → slot≠3 → slot≠4 → slot≠13 → current.stk slot=background slot) ∧
    occupied current.stk≤bound

theorem state_stable (background : Stack → List Bool) (point : Label) (context : C) (memory : Store)
    (source scratch numerator denominator raw : List Bool) (bound : Nat)
    (mass : baseMass background+source.length+scratch.length+numerator.length+denominator.length+raw.length≤bound) :
    Stable background context bound (state background point context memory source scratch numerator denominator raw) := by
  refine ⟨rfl,?_,?_⟩
  · intro slot notT notS notN notD notR
    simp only [state,cells,notT,notS,notN,notD,notR,ite_false]
  · rw [occupied_state]
    exact mass

theorem field_frames (second : Bool) (background : Stack → List Bool) (context : C) (mode : Bool) (digits : List Bool)
    (bit flag : Bool) (copied source scratch numerator denominator raw : List Bool) :
    ∀ current ∈ fieldTrace second background context mode digits bit flag copied source scratch numerator denominator raw,
      current.var.1=context ∧ ∀ slot, slot≠15 → slot≠7 → slot≠3 → slot≠4 → slot≠13 → current.stk slot=background slot := by
  induction digits generalizing bit flag copied numerator denominator with
  | nil =>
    intro current member
    simp only [fieldTrace,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals refine ⟨rfl,?_⟩
    all_goals intro slot notT notS notN notD notR
    all_goals simp only [state,cells,notT,notS,notN,notD,notR,ite_false]
  | cons digit later ih =>
    intro current member
    rcases List.mem_cons.mp member with same | remaining
    · subst current
      have stable := state_stable background (if second then 2 else 1) context (bit,flag,mode)
        (true::digit::(leftBlocks later++false::false::source)) (backups copied++true::scratch) numerator denominator raw _ (Nat.le_refl _)
      exact ⟨stable.1,stable.2.1⟩
    · exact ih digit true (digit::true::copied) _ _ current remaining

structure Segment (caller : Statement C) (background : Stack → List Bool) (context : C) (bound : Nat)
    (before final : State C) (budget : Nat) where
  trace : List (State C)
  head : trace.head?=some before
  chain : trace.IsChain (fun a b=>TM2.step (program caller) a=some b)
  last : trace.getLast?=some final
  count : trace.length≤budget
  stable : ∀ current∈trace, Stable background context bound current

def Segment.append {caller : Statement C} {background : Stack → List Bool} {context : C} {bound : Nat}
    {before middle final : State C} {frontBudget backBudget : Nat}
    (front : Segment caller background context bound before middle frontBudget)
    (back : Segment caller background context bound middle final backBudget) :
    Segment caller background context bound before final (frontBudget+backBudget-1) := by
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
    · exact front.stable current early
    · exact back.stable current (List.mem_of_mem_tail later)

theorem actual_collect (caller : Statement C) (background : Stack → List Bool) (context : C) (memory : Store)
    (negative : Bool) (numerator denominator source scratch oldNum oldDen raw : List Bool) :
    ∃ trace : List (State C),
      trace.head?=some (state background 0 context memory (PSTRSymbolicRatExport.packet negative numerator denominator source)
        scratch oldNum oldDen raw) ∧
      trace.IsChain (fun a b=>TM2.step (program caller) a=some b) ∧
      trace.getLast?=some (state background 4 context
        (finalBit (RatOutput.outputLeft negative numerator denominator) false,true,negative)
        (PSTRSymbolicRatExport.packet negative numerator denominator source) scratch
        (numerator.reverse++oldNum) (denominator.reverse++oldDen) (true::raw)) ∧
      trace.length≤3*(numerator.length+denominator.length)+11 ∧
      ∀ current∈trace, Stable background context
        (baseMass background+source.length+scratch.length+oldNum.length+oldDen.length+raw.length+
          8*(numerator.length+denominator.length)+30) current := by
  let M:=baseMass background+source.length+scratch.length+oldNum.length+oldDen.length+raw.length+
    8*(numerator.length+denominator.length)+30
  let afterNum:=leftBlocks denominator++false::false::source
  let nCopied:=RatOutput.numLeft negative numerator
  let allCopied:=RatOutput.outputLeft negative numerator denominator
  let nWord:=numerator.reverse++oldNum
  let dWord:=denominator.reverse++oldDen
  let rawTail:=true::raw
  let s0:=state background 0 context memory (PSTRSymbolicRatExport.packet negative numerator denominator source) scratch oldNum oldDen raw
  let s1:=state background 1 context (true,memory.2.1,negative) (leftBlocks numerator++false::false::afterNum)
    (backups [negative,true]++true::scratch) oldNum oldDen rawTail
  let s2:=state background 2 context (false,false,negative) afterNum (backups nCopied++true::scratch) nWord oldDen rawTail
  let s3:=state background 3 context (false,false,negative) source (backups allCopied++true::scratch) nWord dWord rawTail
  let s4:=state background 4 context (finalBit allCopied false,true,negative) (allCopied.reverse++source) scratch nWord dWord rawTail
  have boot : Segment caller background context M s0 s1 2 := {
    trace:=[s0,s1],head:=rfl,last:=rfl,count:=Nat.le_refl _
    chain:=List.isChain_cons_cons.mpr ⟨start_step caller background context memory negative
      (leftBlocks numerator++false::false::afterNum) scratch oldNum oldDen raw,List.isChain_singleton _⟩
    stable:=by
      intro current member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl
      all_goals apply state_stable
      all_goals dsimp [M,s0,s1,PSTRSymbolicRatExport.packet,afterNum,rawTail]
      all_goals simp only [List.length_cons,List.length_append,List.length_nil,RatOutput.flagged_length,backups_length]
      all_goals omega }
  have first : Segment caller background context M s1 s2 (numerator.length+2) := {
    trace:=fieldTrace false background context negative numerator true memory.2.1 [negative,true] afterNum scratch oldNum oldDen rawTail
    head:=field_head false background context negative numerator true memory.2.1 [negative,true] afterNum scratch oldNum oldDen rawTail
    chain:=field_chain caller false background context negative numerator true memory.2.1 [negative,true] afterNum scratch oldNum oldDen rawTail
    last:=field_last false background context negative numerator true memory.2.1 [negative,true] afterNum scratch oldNum oldDen rawTail
    count:=(field_length false background context negative numerator true memory.2.1 [negative,true] afterNum scratch oldNum oldDen rawTail).le
    stable:=by
      intro current member
      have frame:=field_frames false background context negative numerator true memory.2.1 [negative,true] afterNum scratch oldNum oldDen rawTail current member
      refine ⟨frame.1,frame.2,?_⟩
      have mass:=field_mass false background context negative numerator true memory.2.1 [negative,true] afterNum scratch oldNum oldDen rawTail current member
      apply mass.trans
      dsimp [M,afterNum,rawTail]
      simp only [List.length_cons,List.length_append,RatOutput.flagged_length]
      omega }
  have second : Segment caller background context M s2 s3 (denominator.length+2) := {
    trace:=fieldTrace true background context negative denominator false false nCopied source scratch nWord oldDen rawTail
    head:=field_head true background context negative denominator false false nCopied source scratch nWord oldDen rawTail
    chain:=field_chain caller true background context negative denominator false false nCopied source scratch nWord oldDen rawTail
    last:=field_last true background context negative denominator false false nCopied source scratch nWord oldDen rawTail
    count:=(field_length true background context negative denominator false false nCopied source scratch nWord oldDen rawTail).le
    stable:=by
      intro current member
      have frame:=field_frames true background context negative denominator false false nCopied source scratch nWord oldDen rawTail current member
      refine ⟨frame.1,frame.2,?_⟩
      have mass:=field_mass true background context negative denominator false false nCopied source scratch nWord oldDen rawTail current member
      apply mass.trans
      dsimp [M,nCopied,nWord,rawTail]
      simp only [RatOutput.numLeft_length,List.length_append,List.length_reverse]
      omega }
  have back : Segment caller background context M s3 s4 (allCopied.length+2) := {
    trace:=restoreTrace background context false false negative allCopied source scratch nWord dWord rawTail
    head:=restore_head background context false false negative allCopied source scratch nWord dWord rawTail
    chain:=restore_chain caller background context false false negative allCopied source scratch nWord dWord rawTail
    last:=restore_last background context false false negative allCopied source scratch nWord dWord rawTail
    count:=(restore_length background context false false negative allCopied source scratch nWord dWord rawTail).le
    stable:=by
      intro current member
      have frame:=restore_frames background context false false negative allCopied source scratch nWord dWord rawTail current member
      refine ⟨frame.1,?_,?_⟩
      · intro slot notT notS notN notD notR
        exact (frame.2 slot notS notT).trans (by simp only [cells,notT,notS,notN,notD,notR,ite_false])
      · have mass:=restore_mass background context false false negative allCopied source scratch nWord dWord rawTail current member
        apply mass.trans
        dsimp [M,allCopied,nWord,dWord,rawTail]
        simp only [RatOutput.outputLeft_length,List.length_append,List.length_reverse]
        omega }
  let whole:=((boot.append first).append second).append back
  refine ⟨whole.trace,whole.head,whole.chain,?_,?_,whole.stable⟩
  · have finalEq : s4=state background 4 context
        (finalBit allCopied false,true,negative) (PSTRSymbolicRatExport.packet negative numerator denominator source)
        scratch nWord dWord rawTail := by
      dsimp only [s4,allCopied]
      rw [RatOutput.outputLeft_reverse]
    exact whole.last.trans (congrArg some finalEq)
  · have count:=whole.count
    have size:=RatOutput.outputLeft_length negative numerator denominator
    change allCopied.length=2*(numerator.length+denominator.length)+6 at size
    omega

end PaperProofs.Common.Native.PSTRWordBool.RatInput
