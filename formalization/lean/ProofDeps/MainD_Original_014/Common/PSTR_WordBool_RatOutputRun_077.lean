module

public import Common.PSTR_WordBool_RatOutputCleanup_076

/-! The one actual count1/tag/sign/NUM/DEN/footer path and real cleanup.
The source layout below is exactly the ORIGINAL singleton RCC encoding;
the destination is frozen094.packet, not a new encoding convention. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatOutput

open Turing RationalControllerComputation PA17TMRatArithmeticParse002 PSTRTMRawNat010

variable {C : Type*}

def rawInput (negative : Bool) (numerator denominator padding : List Bool) : List Bool :=
  true::false::true::true::negative::(rawField numerator ++ rawField denominator ++ true::padding)

def numLeft (negative : Bool) (numerator : List Bool) : List Bool :=
  false::false::((leftBlocks numerator).reverse ++ [negative,true])

def outputLeft (negative : Bool) (numerator denominator : List Bool) : List Bool :=
  false::false::((leftBlocks denominator).reverse ++ numLeft negative numerator)

theorem rawInput_length (negative : Bool) (numerator denominator padding : List Bool) :
    (rawInput negative numerator denominator padding).length = 2*(numerator.length+denominator.length)+padding.length+8 := by
  simp only [rawInput,rawField,List.length_cons,List.length_append,List.length_replicate]
  omega

theorem numLeft_length (negative : Bool) (numerator : List Bool) :
    (numLeft negative numerator).length = 2*numerator.length+4 := by
  simp only [numLeft,List.length_cons,List.length_append,List.length_reverse,flagged_length,List.length_nil]

theorem outputLeft_length (negative : Bool) (numerator denominator : List Bool) :
    (outputLeft negative numerator denominator).length = 2*(numerator.length+denominator.length)+6 := by
  simp only [outputLeft,List.length_cons,List.length_append,List.length_reverse,flagged_length,numLeft_length]
  omega

theorem outputLeft_reverse (negative : Bool) (numerator denominator target : List Bool) :
    (outputLeft negative numerator denominator).reverse ++ target =
      PSTRSymbolicRatExport.packet negative numerator denominator target := by
  simp [outputLeft,numLeft,PSTRSymbolicRatExport.packet,List.reverse_append,List.append_assoc]

def massBound (background : Stack → List Bool) (numerator denominator padding left counter target : List Bool) : Nat :=
  outside background + 2*(numerator.length+denominator.length)+padding.length+left.length+counter.length+target.length+16

theorem actual_reader (caller : Statement C) (background : Stack → List Bool) (context : C) (memory : Store)
    (negative : Bool) (numerator denominator padding left counter target : List Bool) :
    ∃ trace : List (State C),
      trace.head? = some (state background 0 context memory (rawInput negative numerator denominator padding) left counter target) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a = some b) ∧
      trace.getLast? = some (state background 8 context (false,false) [] [] counter
        (PSTRSymbolicRatExport.packet negative numerator denominator target)) ∧
      trace.length ≤ left.length + padding.length + 4*(numerator.length+denominator.length)+15 ∧
      ∀ current ∈ trace, Safe background context (massBound background numerator denominator padding left counter target) current := by
  let M := massBound background numerator denominator padding left counter target
  let right := rawInput negative numerator denominator padding
  let afterSign := rawField numerator ++ rawField denominator ++ true::padding
  let afterNum := rawField denominator ++ true::padding
  let nLeft := numLeft negative numerator
  let outLeft := outputLeft negative numerator denominator
  let s0 := state background 0 context memory right left counter target
  let s1 := state background 1 context (false,false) right [] counter target
  let s2 := state background 2 context (true,negative) afterSign [negative,true] (true::counter) target
  let s3 := state background 3 context (true,false) (numerator++afterNum) [negative,true]
    (List.replicate numerator.length false ++ true::counter) target
  let s4 := state background 4 context (true,true) afterNum nLeft (true::counter) target
  let s5 := state background 5 context (true,false) (denominator++true::padding) nLeft
    (List.replicate denominator.length false ++ true::counter) target
  let s6 := state background 6 context (true,true) padding outLeft counter target
  let s7 := state background 7 context (false,false) [] outLeft counter target
  let s8 := state background 8 context (false,false) [] [] counter (outLeft.reverse++target)
  have first : Segment caller background context M s0 s1 (left.length+2) := {
    trace := clearTrace false background context left memory right counter target
    head := clear_head false background context left memory right counter target
    chain := clear_chain caller false background context left memory right counter target
    last := clear_last false background context left memory right counter target
    count := (clear_length false background context left memory right counter target).le
    safe := by
      intro current member
      apply safe_mono (clear_safe false background context left memory right counter target current member)
      dsimp [M,massBound,right]
      rw [rawInput_length]
      omega }
  have header : Segment caller background context M s1 s2 2 := {
    trace := [s1,s2]
    head := rfl
    chain := List.isChain_cons_cons.mpr ⟨start_step caller background context (false,false) negative afterSign [] counter target,
      List.isChain_singleton _⟩
    last := rfl
    count := Nat.le_refl _
    safe := by
      intro current member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      all_goals apply safe_state
      all_goals dsimp [M,massBound,right,afterSign]
      all_goals simp only [rawInput_length,rawField_length,List.length_append,List.length_cons]
      all_goals omega }
  have nHeader : Segment caller background context M s2 s3 (numerator.length+2) := {
    trace := headerTrace false background context numerator.length (true,negative)
      (numerator++afterNum) [negative,true] (true::counter) target
    head := by
      simpa only [s2,afterSign,afterNum,rawField,List.append_assoc,List.cons_append,Bool.false_eq_true,ite_false] using
        header_head false background context numerator.length (true,negative) (numerator++afterNum) [negative,true] (true::counter) target
    chain := header_chain caller false background context numerator.length (true,negative)
      (numerator++afterNum) [negative,true] (true::counter) target
    last := header_last false background context numerator.length (true,negative) (numerator++afterNum) [negative,true] (true::counter) target
    count := (header_length false background context numerator.length (true,negative) (numerator++afterNum) [negative,true] (true::counter) target).le
    safe := by
      intro current member
      apply safe_mono (header_safe false background context numerator.length (true,negative)
        (numerator++afterNum) [negative,true] (true::counter) target current member)
      dsimp [M,massBound,afterNum]
      simp only [rawField_length,List.length_append,List.length_cons]
      omega }
  have nPayload : Segment caller background context M s3 s4 (numerator.length+2) := {
    trace := payloadTrace false background context numerator (true,false) afterNum [negative,true] counter target
    head := payload_head false background context numerator (true,false) afterNum [negative,true] counter target
    chain := payload_chain caller false background context numerator (true,false) afterNum [negative,true] counter target
    last := payload_last false background context numerator (true,false) afterNum [negative,true] counter target
    count := (payload_length false background context numerator (true,false) afterNum [negative,true] counter target).le
    safe := by
      intro current member
      apply safe_mono (payload_safe false background context numerator (true,false) afterNum [negative,true] counter target current member)
      dsimp [M,massBound,afterNum]
      simp only [rawField_length,List.length_append,List.length_cons]
      omega }
  have dHeader : Segment caller background context M s4 s5 (denominator.length+2) := {
    trace := headerTrace true background context denominator.length (true,true) (denominator++true::padding) nLeft (true::counter) target
    head := by
      simpa only [s4,afterNum,rawField,List.append_assoc,List.cons_append,ite_true] using
        header_head true background context denominator.length (true,true) (denominator++true::padding) nLeft (true::counter) target
    chain := header_chain caller true background context denominator.length (true,true) (denominator++true::padding) nLeft (true::counter) target
    last := header_last true background context denominator.length (true,true) (denominator++true::padding) nLeft (true::counter) target
    count := (header_length true background context denominator.length (true,true) (denominator++true::padding) nLeft (true::counter) target).le
    safe := by
      intro current member
      apply safe_mono (header_safe true background context denominator.length (true,true) (denominator++true::padding) nLeft (true::counter) target current member)
      dsimp [M,massBound,nLeft]
      simp only [numLeft_length,List.length_append,List.length_cons]
      omega }
  have dPayload : Segment caller background context M s5 s6 (denominator.length+2) := {
    trace := payloadTrace true background context denominator (true,false) (true::padding) nLeft counter target
    head := payload_head true background context denominator (true,false) (true::padding) nLeft counter target
    chain := payload_chain caller true background context denominator (true,false) (true::padding) nLeft counter target
    last := payload_last true background context denominator (true,false) (true::padding) nLeft counter target
    count := (payload_length true background context denominator (true,false) (true::padding) nLeft counter target).le
    safe := by
      intro current member
      apply safe_mono (payload_safe true background context denominator (true,false) (true::padding) nLeft counter target current member)
      dsimp [M,massBound,nLeft]
      simp only [numLeft_length]
      omega }
  have clear : Segment caller background context M s6 s7 (padding.length+2) := {
    trace := clearTrace true background context padding (true,true) outLeft counter target
    head := clear_head true background context padding (true,true) outLeft counter target
    chain := clear_chain caller true background context padding (true,true) outLeft counter target
    last := clear_last true background context padding (true,true) outLeft counter target
    count := (clear_length true background context padding (true,true) outLeft counter target).le
    safe := by
      intro current member
      apply safe_mono (clear_safe true background context padding (true,true) outLeft counter target current member)
      dsimp [M,massBound,outLeft]
      rw [outputLeft_length]
      omega }
  have reverse : Segment caller background context M s7 s8 (outLeft.length+2) := {
    trace := reverseTrace background context outLeft (false,false) [] counter target
    head := reverse_head background context outLeft (false,false) [] counter target
    chain := reverse_chain caller background context outLeft (false,false) [] counter target
    last := reverse_last background context outLeft (false,false) [] counter target
    count := (reverse_length background context outLeft (false,false) [] counter target).le
    safe := by
      intro current member
      apply safe_mono (reverse_safe background context outLeft (false,false) [] counter target current member)
      dsimp [M,massBound,outLeft]
      simp only [outputLeft_length]
      omega }
  let whole := ((((((first.append header).append nHeader).append nPayload).append dHeader).append dPayload).append clear).append reverse
  refine ⟨whole.trace,whole.head,whole.chain,?_,?_,whole.safe⟩
  · have finalEq : s8 = state background 8 context (false,false) [] [] counter
        (PSTRSymbolicRatExport.packet negative numerator denominator target) := by
      dsimp only [s8,outLeft]
      rw [outputLeft_reverse]
    exact whole.last.trans (congrArg some finalEq)
  · have count := whole.count
    have size : outLeft.length = 2*(numerator.length+denominator.length)+6 := outputLeft_length negative numerator denominator
    omega

end PaperProofs.Common.Native.PSTRWordBool.RatOutput
