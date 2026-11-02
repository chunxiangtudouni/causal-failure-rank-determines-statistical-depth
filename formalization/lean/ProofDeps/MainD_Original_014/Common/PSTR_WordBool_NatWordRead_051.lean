module

public import Common.PSTR_WordBool_NatWordPayload_050

/-! The SAME actual payload run consumes every real Nat-header tally cell.
Width cells control which bits are retained; excess bits are really read and
discarded. Missing finite R cells read as blank FALSE. No min/count is stored
in control: these are exact descriptions of the executed trace. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.NatWordIO

open Turing

def payloadTrace (background : Stack → List Bool) :
    Store → List Bool → List Bool → List Bool → List Bool → List Bool → List Bool → List State
  | memory, right, [], value, reverseWord, width, used =>
      [state background 2 memory right [] value reverseWord width used,
        state background 3 (false, false) right [] value reverseWord width used]
  | memory, right, countBit :: left, value, reverseWord, [], used =>
      state background 2 memory right (countBit :: left) value reverseWord [] used ::
        payloadTrace background (false, right.head?.getD false) right.tail left value reverseWord [] used
  | memory, right, countBit :: left, value, reverseWord, widthBit :: width, used =>
      state background 2 memory right (countBit :: left) value reverseWord (widthBit :: width) used ::
        payloadTrace background (true, right.head?.getD false) right.tail left value
          (right.head?.getD false :: reverseWord) width (true :: used)

theorem payloadTrace_head (background : Stack → List Bool) (memory : Store)
    (right left value reverseWord width used : List Bool) :
    (payloadTrace background memory right left value reverseWord width used).head? =
      some (state background 2 memory right left value reverseWord width used) := by
  cases left <;> cases width <;> rfl

theorem payloadTrace_length (background : Stack → List Bool) (memory : Store)
    (right left value reverseWord width used : List Bool) :
    (payloadTrace background memory right left value reverseWord width used).length = left.length + 2 := by
  induction left generalizing memory right reverseWord width used with
  | nil => rfl
  | cons countBit left ih =>
    cases width <;> simp only [payloadTrace, List.length_cons, ih]

theorem payloadTrace_last (background : Stack → List Bool) (memory : Store)
    (right left value reverseWord width used : List Bool) :
    (payloadTrace background memory right left value reverseWord width used).getLast? =
      some (state background 3 (false, false) (right.drop left.length) [] value
        ((readBits (min left.length width.length) right).reverse ++ reverseWord)
        (width.drop left.length) (List.replicate (min left.length width.length) true ++ used)) := by
  induction left generalizing memory right reverseWord width used with
  | nil => rfl
  | cons countBit left ih =>
    cases width with
    | nil =>
      rw [payloadTrace, StatementClock.prepend_last _ _ (by rw [payloadTrace_length]; omega), ih]
      simp only [List.length_cons, List.length_nil, Nat.min_zero, readBits_zero, List.reverse_nil,
        List.nil_append, List.drop_nil, List.replicate_zero, List.drop_tail]
    | cons widthBit width =>
      rw [payloadTrace, StatementClock.prepend_last _ _ (by rw [payloadTrace_length]; omega), ih]
      simp only [List.length_cons, Nat.succ_min_succ, readBits_succ, List.reverse_cons,
        List.append_assoc, List.cons_append, List.nil_append, List.drop_tail,
        List.drop_succ_cons, List.replicate_succ']

theorem payloadTrace_chain (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (right left value reverseWord width used : List Bool) :
    (payloadTrace background memory right left value reverseWord width used).IsChain
      (fun before after => TM2.step (program caller) before = some after) := by
  induction left generalizing memory right reverseWord width used with
  | nil =>
    exact List.isChain_cons_cons.mpr ⟨payload_done caller background memory right value reverseWord width used,
      List.isChain_singleton _⟩
  | cons countBit left ih =>
    cases width with
    | nil =>
      apply List.isChain_cons.mpr
      refine ⟨?_, ih (false, right.head?.getD false) right.tail reverseWord [] used⟩
      intro next present
      rw [payloadTrace_head] at present
      have same := Option.some.inj (Option.mem_def.mp present)
      subst next
      exact payload_discard caller background memory countBit right left value reverseWord used
    | cons widthBit width =>
      apply List.isChain_cons.mpr
      refine ⟨?_, ih (true, right.head?.getD false) right.tail
        (right.head?.getD false :: reverseWord) width (true :: used)⟩
      intro next present
      rw [payloadTrace_head] at present
      have same := Option.some.inj (Option.mem_def.mp present)
      subst next
      exact payload_copy caller background memory countBit widthBit right left value reverseWord width used

theorem payloadTrace_fields (background : Stack → List Bool) (memory : Store)
    (right left value reverseWord width used : List Bool) :
    ∀ current ∈ payloadTrace background memory right left value reverseWord width used,
      ∃ (remaining counter reversed room tally : List Bool) (flags : Label × Store),
        current = state background flags.1 flags.2 remaining counter value reversed room tally ∧
        remaining.length ≤ right.length ∧ counter.length ≤ left.length ∧
        room.length + tally.length = width.length + used.length ∧
        reversed.length + room.length = reverseWord.length + width.length := by
  induction left generalizing memory right reverseWord width used with
  | nil =>
    intro current present
    simp only [payloadTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact ⟨right, [], reverseWord, width, used, (2, memory), rfl, le_rfl, le_rfl, rfl, rfl⟩
    · exact ⟨right, [], reverseWord, width, used, (3, (false, false)), rfl, le_rfl, le_rfl, rfl, rfl⟩
  | cons countBit left ih =>
    cases width with
    | nil =>
      intro current present
      rcases List.mem_cons.mp present with same | later
      · subst current
        exact ⟨right, countBit :: left, reverseWord, [], used, (2, memory), rfl, le_rfl, le_rfl, rfl, rfl⟩
      · obtain ⟨remaining, counter, reversed, room, tally, flags, same, rBound, lBound, tallyMass, reverseMass⟩ :=
          ih (false, right.head?.getD false) right.tail reverseWord [] used current later
        refine ⟨remaining, counter, reversed, room, tally, flags, same, ?_, ?_, tallyMass, reverseMass⟩
        · simp only [List.length_tail] at rBound
          omega
        · simp only [List.length_cons]
          omega
    | cons widthBit width =>
      intro current present
      rcases List.mem_cons.mp present with same | later
      · subst current
        exact ⟨right, countBit :: left, reverseWord, widthBit :: width, used,
          (2, memory), rfl, le_rfl, le_rfl, rfl, rfl⟩
      · obtain ⟨remaining, counter, reversed, room, tally, flags, same, rBound, lBound, tallyMass, reverseMass⟩ :=
          ih (true, right.head?.getD false) right.tail
            (right.head?.getD false :: reverseWord) width (true :: used) current later
        refine ⟨remaining, counter, reversed, room, tally, flags, same, ?_, ?_, ?_, ?_⟩
        · simp only [List.length_tail] at rBound
          omega
        · simp only [List.length_cons]
          omega
        · simp only [List.length_cons] at tallyMass ⊢
          omega
        · simp only [List.length_cons] at reverseMass ⊢
          omega

end PaperProofs.Common.Native.PSTRWordBool.NatWordIO
