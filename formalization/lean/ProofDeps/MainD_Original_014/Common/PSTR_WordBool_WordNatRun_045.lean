module

public import Common.PSTR_WordBool_WordNatHeader_044

/-! One actual fixed-code Word-to-canonical-Nat formatting path, including
physical zero, length header, delimiter and real caller edge. Every listed
configuration is bounded by current data length, never elapsed run time. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.WordNatIO

open Turing
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTrimCode103 (trimmed)

def FormatBounds (background : Stack → List Bool) (width : Nat) (output : List Bool)
    (current : State) : Prop :=
  ∃ (word left payload tally : List Bool) (flags : Label × Store),
    current = state background flags.1 flags.2 word left payload tally ∧
    word.length + left.length ≤ width ∧
    payload.length + tally.length ≤ output.length + 2 * width + 3

theorem actual_format (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (word output : List Bool) :
    ∃ trace : List State,
      trace.head? = some (state background 0 memory word [] output []) ∧
      trace.IsChain (fun before after => TM2.step (program caller) before = some after) ∧
      trace.getLast? = some (state background 6 (false, false) [] []
        (encodeNat (PSTRTMIncrement009.valueDigits word) ++ output) []) ∧
      trace.length ≤ 4 * word.length + 11 ∧
      ∀ current ∈ trace, FormatBounds background word.length output current := by
  let reversePart := reverseTrace background memory word [] output []
  have reverseFirst := reverseTrace_head background memory word [] output []
  have reverseChain := reverseTrace_chain caller background memory word [] output []
  have reverseLast : reversePart.getLast? =
      some (state background 1 (false, false) [] word.reverse output []) := by
    simpa only [List.append_nil] using reverseTrace_last background memory word [] output []
  have reverseLength : reversePart.length = word.length + 2 :=
    reverseTrace_length background memory word [] output []
  have reverseFields : ∀ current ∈ reversePart, FormatBounds background word.length output current := by
    intro current present
    obtain ⟨remaining, reversed, flags, same, mass⟩ :=
      reverseTrace_fields background memory word [] output [] current present
    refine ⟨remaining, reversed, output, [], flags, same, ?_, ?_⟩
    · simp only [List.length_nil, Nat.add_zero] at mass
      omega
    · simp only [List.length_nil, Nat.add_zero]
      omega
  obtain ⟨payloadPart, payloadFirst, payloadChain, payloadLast, payloadLength, payloadFields⟩ :=
    actual_payload caller background (false, false) word output
  have body := join_paths caller reversePart payloadPart
    (state background 0 memory word [] output [])
    (state background 1 (false, false) [] word.reverse output []) _
    reverseFirst reverseChain reverseLast payloadFirst payloadChain payloadLast
  let bodyPart := reversePart ++ payloadPart.tail
  have bodyFields : ∀ current ∈ bodyPart, FormatBounds background word.length output current := by
    intro current present
    rcases List.mem_append.mp present with early | later
    · exact reverseFields current early
    · obtain ⟨left, payload, tally, flags, same, leftBound, payloadBound, tallyBound⟩ :=
        payloadFields current (List.mem_of_mem_tail later)
      refine ⟨[], left, payload, tally, flags, same, ?_, ?_⟩
      · simpa only [List.length_nil, Nat.zero_add] using leftBound
      · omega
  let payload := trimmed word ++ output
  let counter := List.replicate (trimmed word).length true
  let headerPart := state background 3 (false, false) [] [] payload counter ::
    headerTrace background (false, false) (false :: payload) counter
  have headerFirst : headerPart.head? =
      some (state background 3 (false, false) [] [] payload counter) := rfl
  have headerChain : headerPart.IsChain
      (fun before after => TM2.step (program caller) before = some after) := by
    apply List.isChain_cons.mpr
    refine ⟨?_, headerTrace_chain caller background (false, false) (false :: payload) counter⟩
    intro next present
    rw [headerTrace_head] at present
    have same := Option.some.inj (Option.mem_def.mp present)
    subst next
    exact delimiter_step caller background (false, false) payload counter
  have canonical : List.replicate counter.length true ++ false :: payload =
      encodeNat (PSTRTMIncrement009.valueDigits word) ++ output := by
    change List.replicate (List.replicate (trimmed word).length true).length true ++
      false :: (trimmed word ++ output) = _
    rw [List.length_replicate, ← encodedWord_correct]
    simp only [encodedWord, List.append_assoc, List.cons_append]
  have headerLast : headerPart.getLast? =
      some (state background 6 (false, false) [] []
        (encodeNat (PSTRTMIncrement009.valueDigits word) ++ output) []) := by
    rw [StatementClock.prepend_last _ _ (by rw [headerTrace_length]; omega), headerTrace_last,
      canonical]
  have headerLength : headerPart.length = (trimmed word).length + 4 := by
    simp only [headerPart, List.length_cons, headerTrace_length, counter, List.length_replicate]
  have trimmedLength := PSTRTMTrimValue104.trimmed_length_le word
  have headerFields : ∀ current ∈ headerPart, FormatBounds background word.length output current := by
    intro current present
    rcases List.mem_cons.mp present with same | later
    · subst current
      refine ⟨[], [], payload, counter, (3, (false, false)), rfl, by simp, ?_⟩
      simp only [payload, counter, List.length_append, List.length_replicate]
      omega
    · obtain ⟨nowPayload, nowTally, flags, same, mass⟩ :=
        headerTrace_fields background (false, false) (false :: payload) counter current later
      refine ⟨[], [], nowPayload, nowTally, flags, same, by simp, ?_⟩
      simp only [payload, counter, List.length_append, List.length_replicate,
        List.length_cons] at mass
      omega
  have full := join_paths caller bodyPart headerPart
    (state background 0 memory word [] output [])
    (state background 3 (false, false) [] [] payload counter) _
    body.1 body.2.1 body.2.2.1 headerFirst headerChain headerLast
  refine ⟨bodyPart ++ headerPart.tail, full.1, full.2.1, full.2.2.1, ?_, ?_⟩
  · have bodyLength := body.2.2.2
    change bodyPart.length ≤ reversePart.length + payloadPart.length at bodyLength
    have fullLength := full.2.2.2
    omega
  · intro current present
    rcases List.mem_append.mp present with early | later
    · exact bodyFields current early
    · exact headerFields current (List.mem_of_mem_tail later)

theorem state_stack_bound (background : Stack → List Bool) (label : Label) (memory : Store)
    (word left payload tally : List Bool) (bound : Nat)
    (wordBound : word.length ≤ bound) (leftBound : left.length ≤ bound)
    (payloadBound : payload.length ≤ bound) (tallyBound : tally.length ≤ bound)
    (slot : Stack) :
    ((state background label memory word left payload tally).stk slot).length ≤
      (background slot).length + bound := by
  fin_cases slot <;> simp only [state, cells]
  all_goals norm_num
  all_goals omega

theorem format_bounds_stack (background : Stack → List Bool) (width : Nat) (output : List Bool)
    (current : State) (bounded : FormatBounds background width output current) (slot : Stack) :
    (current.stk slot).length ≤ (background slot).length + output.length + 3 * width + 3 := by
  obtain ⟨word, left, payload, tally, flags, same, dataBound, payloadBound⟩ := bounded
  subst current
  have bound := state_stack_bound background flags.1 flags.2 word left payload tally
    (output.length + 3 * width + 3) (by omega) (by omega) (by omega) (by omega) slot
  omega

theorem format_bounds_frame (background : Stack → List Bool) (width : Nat) (output : List Bool)
    (current : State) (bounded : FormatBounds background width output current)
    (slot : Stack) (notWord : slot ≠ 3) (notLeft : slot ≠ 1) (notOutput : slot ≠ 0)
    (notCounter : slot ≠ 12) : current.stk slot = background slot := by
  obtain ⟨word, left, payload, tally, flags, same, _dataBound, _payloadBound⟩ := bounded
  subst current
  exact cells_frame background word left payload tally slot notWord notLeft notOutput notCounter

theorem actual_format_frames (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (word output : List Bool) :
    ∃ trace : List State,
      trace.head? = some (state background 0 memory word [] output []) ∧
      trace.IsChain (fun before after => TM2.step (program caller) before = some after) ∧
      trace.getLast? = some (state background 6 (false, false) [] []
        (encodeNat (PSTRTMIncrement009.valueDigits word) ++ output) []) ∧
      trace.length ≤ 4 * word.length + 11 ∧
      (∀ current ∈ trace, ∀ slot,
        (current.stk slot).length ≤ (background slot).length + output.length + 3 * word.length + 3) ∧
      (∀ current ∈ trace, ∀ slot, slot ≠ 3 → slot ≠ 1 → slot ≠ 0 → slot ≠ 12 →
        current.stk slot = background slot) := by
  obtain ⟨trace, first, chain, last, length, bounded⟩ := actual_format caller background memory word output
  refine ⟨trace, first, chain, last, length, ?_, ?_⟩
  · intro current present slot
    exact format_bounds_stack background word.length output current (bounded current present) slot
  · intro current present slot notWord notLeft notOutput notCounter
    exact format_bounds_frame background word.length output current (bounded current present)
      slot notWord notLeft notOutput notCounter

end PaperProofs.Common.Native.PSTRWordBool.WordNatIO
