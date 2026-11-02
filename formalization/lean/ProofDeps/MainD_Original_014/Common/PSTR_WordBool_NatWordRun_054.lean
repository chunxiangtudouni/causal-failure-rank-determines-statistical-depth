module

public import Common.PSTR_WordBool_NatWordMeaning_053

/-! One actual canonical-Nat-to-Word read. Six real phases share their
boundary configurations. All listed configurations satisfy current-data
space bounds; the width and every untouched stack are restored. The active
caller port is reached by the real return edge, never assumed for free. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.NatWordIO

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

def ReadBounds (background : Stack → List Bool) (rightSize leftSize width : Nat)
    (current : State) : Prop :=
  ∃ (right left value reversed room used : List Bool) (flags : Label × Store),
    current = state background flags.1 flags.2 right left value reversed room used ∧
    right.length ≤ rightSize ∧ left.length ≤ leftSize + rightSize ∧
    value.length ≤ width ∧ reversed.length ≤ width ∧ room.length ≤ width ∧ used.length ≤ width

structure ReadSegment (caller : Statement) (invariant : State → Prop)
    (before final : State) (budget : Nat) where
  trace : List State
  head : trace.head? = some before
  chain : trace.IsChain (fun before after => TM2.step (program caller) before = some after)
  last : trace.getLast? = some final
  count : trace.length ≤ budget
  fields : ∀ current ∈ trace, invariant current

def ReadSegment.append {caller : Statement} {invariant : State → Prop}
    {before middle final : State} {frontBudget backBudget : Nat}
    (front : ReadSegment caller invariant before middle frontBudget)
    (back : ReadSegment caller invariant middle final backBudget) :
    ReadSegment caller invariant before final (frontBudget + backBudget) := by
  have decomposed : middle :: back.trace.tail = back.trace := by
    obtain ⟨rest, same⟩ := List.head?_eq_some_iff.mp back.head
    rw [same]
    rfl
  refine ⟨front.trace ++ back.trace.tail, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_append, front.head]
    rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (decomposed.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (decomposed.symm ▸ back.last)
  · have frontCount := front.count
    have backCount := back.count
    simp only [List.length_append, List.length_tail]
    omega
  · intro current present
    rcases List.mem_append.mp present with early | later
    · exact front.fields current early
    · exact back.fields current (List.mem_of_mem_tail later)

theorem actual_read (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (value width : Nat) (right left : List Bool)
    (same : ListBlank.mk right = ListBlank.mk (encodeNat value)) :
    ∃ (bits : List Bool) (trace : List State),
      trace.head? = some (state background 0 memory right left [] [] (List.replicate width true) []) ∧
      trace.IsChain (fun before after => TM2.step (program caller) before = some after) ∧
      trace.getLast? = some (state background 7 (false, false) [] [] bits []
        (List.replicate width true) []) ∧
      bits.length = width ∧
      BitVec.ofNat width (PSTRTMIncrement009.valueDigits bits) = BitVec.ofNat width value ∧
      trace.length ≤ left.length + 3 * right.length + 2 * width + 13 ∧
      ∀ current ∈ trace, ReadBounds background right.length left.length width current := by
  let count := natBits value
  let payload := right.drop (count + 1)
  let tally := List.replicate count true
  let room := (List.replicate width true).drop count
  let kept := min count width
  let reversed := (readBits kept payload).reverse
  let used := List.replicate kept true
  let padded := List.replicate room.length false ++ reversed
  let result := readBits width payload
  let headerMemory : Store := ((right.drop count).head?.isSome, false)
  let invariant := ReadBounds background right.length left.length width
  have certificate := original_nat_header value right same
  have countBound : count ≤ right.length := header_length_le _ _ _ certificate
  have payloadSame : ListBlank.mk payload = ListBlank.mk (PSTRTMNatValue017.rawPayload value) :=
    header_payload _ _ _ certificate
  have payloadBound : payload.length ≤ right.length := by
    simp only [payload, List.length_drop]
    omega
  have remainingBound : (payload.drop count).length ≤ right.length := by
    simp only [List.length_drop]
    omega
  have keptBound : kept ≤ width := Nat.min_le_right _ _
  have roomSize : room.length = width - kept := by
    simp only [room, List.length_drop, List.length_replicate]
    omega
  have widthMass : room.length + kept = width := by omega
  have reverseSize : reversed.length = kept := by
    simp only [reversed, List.length_reverse, readBits_length]
  have usedSize : used.length = kept := List.length_replicate
  have paddedSize : padded.length = width := by
    simp only [padded, List.length_append, List.length_replicate, reverseSize]
    exact widthMass
  have paddedValue : padded.reverse = result := by
    dsimp only [padded, reversed, result]
    rw [reversed_padded_bits, roomSize]
    exact padded_readBits value width payload payloadSame
  have paddedUsed : List.replicate room.length true ++ used = List.replicate width true := by
    rw [← List.replicate_add, widthMass]
  have resultSize : result.length = width := readBits_length _ _
  let firstPart : ReadSegment caller invariant
      (state background 0 memory right left [] [] (List.replicate width true) [])
      (state background 1 (false, false) right [] [] [] (List.replicate width true) [])
      (left.length + 2) := {
    trace := clearLeftTrace background memory right left [] [] (List.replicate width true) []
    head := clearLeftTrace_head _ _ _ _ _ _ _ _
    chain := clearLeftTrace_chain _ _ _ _ _ _ _ _ _
    last := clearLeftTrace_last _ _ _ _ _ _ _ _
    count := (clearLeftTrace_length _ _ _ _ _ _ _ _).le
    fields := by
      intro current present
      obtain ⟨remaining, flags, equal, bounded⟩ :=
        clearLeftTrace_fields background memory right left [] [] (List.replicate width true) [] current present
      refine ⟨right, remaining, [], [], List.replicate width true, [], flags, equal,
        le_rfl, by omega, by simp, by simp, ?_, by simp⟩
      simp only [List.length_replicate]
      exact le_rfl }
  let headerPart : ReadSegment caller invariant
      (state background 1 (false, false) right [] [] [] (List.replicate width true) [])
      (state background 2 headerMemory payload tally [] [] (List.replicate width true) [])
      (count + 2) := {
    trace := headerTrace background (false, false) count right [] [] [] (List.replicate width true) []
    head := headerTrace_head _ _ _ _ _ _ _ _ _
    chain := headerTrace_chain caller background (false, false) count _ right [] [] []
      (List.replicate width true) [] certificate
    last := by simpa only [List.append_nil] using
      headerTrace_last background (false, false) count right [] [] [] (List.replicate width true) []
    count := (headerTrace_length _ _ _ _ _ _ _ _ _).le
    fields := by
      intro current present
      obtain ⟨remaining, counter, flags, equal, dataBound, tallyBound⟩ :=
        headerTrace_fields background (false, false) count right [] [] [] (List.replicate width true) []
          current present
      refine ⟨remaining, counter, [], [], List.replicate width true, [], flags, equal,
        dataBound, ?_, by simp, by simp, ?_, by simp⟩
      · simp only [List.length_nil, Nat.zero_add] at tallyBound
        omega
      · simp only [List.length_replicate]
        exact le_rfl }
  let payloadPart : ReadSegment caller invariant
      (state background 2 headerMemory payload tally [] [] (List.replicate width true) [])
      (state background 3 (false, false) (payload.drop count) [] [] reversed room used)
      (count + 2) := {
    trace := payloadTrace background headerMemory payload tally [] [] (List.replicate width true) []
    head := payloadTrace_head _ _ _ _ _ _ _ _
    chain := payloadTrace_chain _ _ _ _ _ _ _ _ _
    last := by simpa only [tally, List.length_replicate, List.append_nil] using
      payloadTrace_last background headerMemory payload tally [] [] (List.replicate width true) []
    count := by
      rw [payloadTrace_length, List.length_replicate]
    fields := by
      intro current present
      obtain ⟨remaining, counter, reverseNow, roomNow, usedNow, flags, equal,
        dataBound, counterBound, tallyMass, reverseMass⟩ :=
        payloadTrace_fields background headerMemory payload tally [] [] (List.replicate width true) []
          current present
      simp only [tally, List.length_replicate, List.length_nil, Nat.add_zero, Nat.zero_add] at counterBound tallyMass reverseMass
      exact ⟨remaining, counter, [], reverseNow, roomNow, usedNow, flags, equal,
        by omega, by omega, by simp, by omega, by omega, by omega⟩ }
  let padPart : ReadSegment caller invariant
      (state background 3 (false, false) (payload.drop count) [] [] reversed room used)
      (state background 4 (false, false) (payload.drop count) [] [] padded [] (List.replicate width true))
      (room.length + 2) := {
    trace := padTrace background (false, false) (payload.drop count) [] reversed room used
    head := padTrace_head _ _ _ _ _ _ _
    chain := padTrace_chain _ _ _ _ _ _ _ _
    last := by simpa only [paddedUsed] using
      padTrace_last background (false, false) (payload.drop count) [] reversed room used
    count := (padTrace_length _ _ _ _ _ _ _).le
    fields := by
      intro current present
      obtain ⟨reverseNow, roomNow, usedNow, flags, equal, reverseMass, tallyMass⟩ :=
        padTrace_fields background (false, false) (payload.drop count) [] reversed room used current present
      rw [reverseSize] at reverseMass
      rw [usedSize] at tallyMass
      exact ⟨payload.drop count, [], [], reverseNow, roomNow, usedNow, flags, equal,
        remainingBound, by simp, by simp, by omega, by omega, by omega⟩ }
  let restorePart : ReadSegment caller invariant
      (state background 4 (false, false) (payload.drop count) [] [] padded [] (List.replicate width true))
      (state background 5 (false, false) (payload.drop count) [] result [] (List.replicate width true) [])
      (width + 2) := {
    trace := restoreTrace background (false, false) (payload.drop count) [] padded [] (List.replicate width true)
    head := restoreTrace_head _ _ _ _ _ _ _
    chain := restoreTrace_chain _ _ _ _ _ _ _ _
    last := by simpa only [paddedValue, paddedSize, List.append_nil, List.drop_replicate,
      Nat.sub_self, List.replicate_zero] using
      restoreTrace_last background (false, false) (payload.drop count) [] padded [] (List.replicate width true)
    count := by
      rw [restoreTrace_length, paddedSize]
    fields := by
      intro current present
      obtain ⟨valueNow, reverseNow, roomNow, usedNow, flags, equal, dataMass, roomBound, tallyBound⟩ :=
        restoreTrace_fields background (false, false) (payload.drop count) [] padded []
          (List.replicate width true) current present
      simp only [List.length_nil, Nat.zero_add, paddedSize, List.length_replicate] at dataMass roomBound tallyBound
      exact ⟨payload.drop count, [], valueNow, reverseNow, roomNow, usedNow, flags, equal,
        remainingBound, by simp, by omega, by omega, roomBound, tallyBound⟩ }
  let finalPart : ReadSegment caller invariant
      (state background 5 (false, false) (payload.drop count) [] result [] (List.replicate width true) [])
      (state background 7 (false, false) [] [] result [] (List.replicate width true) [])
      ((payload.drop count).length + 3) := {
    trace := clearRightTrace background (false, false) (payload.drop count) result (List.replicate width true) []
    head := clearRightTrace_head _ _ _ _ _ _
    chain := clearRightTrace_chain _ _ _ _ _ _ _
    last := clearRightTrace_last _ _ _ _ _ _
    count := (clearRightTrace_length _ _ _ _ _ _).le
    fields := by
      intro current present
      obtain ⟨remaining, flags, equal, dataBound⟩ :=
        clearRightTrace_fields background (false, false) (payload.drop count) result
          (List.replicate width true) [] current present
      refine ⟨remaining, [], result, [], List.replicate width true, [], flags, equal,
        by omega, by simp, resultSize.le, by simp, ?_, by simp⟩
      simp only [List.length_replicate]
      exact le_rfl }
  let full := ((((firstPart.append headerPart).append payloadPart).append padPart).append restorePart).append finalPart
  refine ⟨result, full.trace, full.head, full.chain, full.last, resultSize,
    word_of_readBits value width payload payloadSame, ?_, full.fields⟩
  have length := full.count
  change full.trace.length ≤
    (left.length + 2 + (count + 2) + (count + 2) + (room.length + 2) + (width + 2) +
      ((payload.drop count).length + 3)) at length
  omega

theorem read_bounds_stack (background : Stack → List Bool) (rightSize leftSize width : Nat)
    (current : State) (bounded : ReadBounds background rightSize leftSize width current) (slot : Stack) :
    (current.stk slot).length ≤ (background slot).length + rightSize + leftSize + width := by
  obtain ⟨right, left, value, reversed, room, used, flags, equal,
    rightBound, leftBound, valueBound, reverseBound, roomBound, usedBound⟩ := bounded
  subst current
  fin_cases slot <;> simp only [state, cells]
  all_goals norm_num
  all_goals omega

theorem read_bounds_frame (background : Stack → List Bool) (rightSize leftSize width : Nat)
    (current : State) (bounded : ReadBounds background rightSize leftSize width current)
    (slot : Stack) (notRight : slot ≠ 0) (notLeft : slot ≠ 1) (notValue : slot ≠ 3)
    (notReverse : slot ≠ 7) (notWidth : slot ≠ 11) (notUsed : slot ≠ 12) :
    current.stk slot = background slot := by
  obtain ⟨right, left, value, reversed, room, used, flags, equal, _bounds⟩ := bounded
  subst current
  exact cells_frame background right left value reversed room used slot
    notRight notLeft notValue notReverse notWidth notUsed

end PaperProofs.Common.Native.PSTRWordBool.NatWordIO
