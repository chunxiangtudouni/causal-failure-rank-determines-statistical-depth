module

public import Common.PSTR_WordBool_NatWordPayload_050

/-! Actual physical padding, reversal/width restoration, and complete virtual
right cleanup with the paid caller edge. These phases retain the SAME state
and exact background; every real finite FALSE cell is cleared by presence. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.NatWordIO

open Turing

def padTrace (background : Stack → List Bool) :
    Store → List Bool → List Bool → List Bool → List Bool → List Bool → List State
  | memory, right, value, reverseWord, [], used =>
      [state background 3 memory right [] value reverseWord [] used,
        state background 4 (false, false) right [] value reverseWord [] used]
  | memory, right, value, reverseWord, widthBit :: width, used =>
      state background 3 memory right [] value reverseWord (widthBit :: width) used ::
        padTrace background (true, widthBit) right value (false :: reverseWord) width (true :: used)

theorem padTrace_head (background : Stack → List Bool) (memory : Store)
    (right value reverseWord width used : List Bool) :
    (padTrace background memory right value reverseWord width used).head? =
      some (state background 3 memory right [] value reverseWord width used) := by
  cases width <;> rfl

theorem padTrace_length (background : Stack → List Bool) (memory : Store)
    (right value reverseWord width used : List Bool) :
    (padTrace background memory right value reverseWord width used).length = width.length + 2 := by
  induction width generalizing memory reverseWord used with
  | nil => rfl
  | cons widthBit width ih => simp only [padTrace, List.length_cons, ih]

theorem padTrace_last (background : Stack → List Bool) (memory : Store)
    (right value reverseWord width used : List Bool) :
    (padTrace background memory right value reverseWord width used).getLast? =
      some (state background 4 (false, false) right [] value
        (List.replicate width.length false ++ reverseWord) []
        (List.replicate width.length true ++ used)) := by
  induction width generalizing memory reverseWord used with
  | nil => rfl
  | cons widthBit width ih =>
    rw [padTrace, StatementClock.prepend_last _ _ (by rw [padTrace_length]; omega), ih]
    simp only [List.length_cons, List.replicate_succ', List.append_assoc,
      List.cons_append, List.nil_append]

theorem padTrace_chain (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (right value reverseWord width used : List Bool) :
    (padTrace background memory right value reverseWord width used).IsChain
      (fun before after => TM2.step (program caller) before = some after) := by
  induction width generalizing memory reverseWord used with
  | nil =>
    exact List.isChain_cons_cons.mpr ⟨pad_done caller background memory right value reverseWord used,
      List.isChain_singleton _⟩
  | cons widthBit width ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_, ih (true, widthBit) (false :: reverseWord) (true :: used)⟩
    intro next present
    rw [padTrace_head] at present
    have same := Option.some.inj (Option.mem_def.mp present)
    subst next
    exact pad_bit caller background memory widthBit right value reverseWord width used

theorem padTrace_fields (background : Stack → List Bool) (memory : Store)
    (right value reverseWord width used : List Bool) :
    ∀ current ∈ padTrace background memory right value reverseWord width used,
      ∃ (reversed room tally : List Bool) (flags : Label × Store),
        current = state background flags.1 flags.2 right [] value reversed room tally ∧
        reversed.length + room.length = reverseWord.length + width.length ∧
        room.length + tally.length = width.length + used.length := by
  induction width generalizing memory reverseWord used with
  | nil =>
    intro current present
    simp only [padTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact ⟨reverseWord, [], used, (3, memory), rfl, rfl, rfl⟩
    · exact ⟨reverseWord, [], used, (4, (false, false)), rfl, rfl, rfl⟩
  | cons widthBit width ih =>
    intro current present
    rcases List.mem_cons.mp present with same | later
    · subst current
      exact ⟨reverseWord, widthBit :: width, used, (3, memory), rfl, rfl, rfl⟩
    · obtain ⟨reversed, room, tally, flags, same, dataMass, tallyMass⟩ :=
        ih (true, widthBit) (false :: reverseWord) (true :: used) current later
      refine ⟨reversed, room, tally, flags, same, ?_, ?_⟩
      · simp only [List.length_cons] at dataMass ⊢
        omega
      · simp only [List.length_cons] at tallyMass ⊢
        omega

def restoreTrace (background : Stack → List Bool) :
    Store → List Bool → List Bool → List Bool → List Bool → List Bool → List State
  | memory, right, value, [], width, used =>
      [state background 4 memory right [] value [] width used,
        state background 5 (false, false) right [] value [] width used]
  | memory, right, value, bit :: reverseWord, width, used =>
      state background 4 memory right [] value (bit :: reverseWord) width used ::
        restoreTrace background (true, bit) right (bit :: value) reverseWord (true :: width) used.tail

theorem restoreTrace_head (background : Stack → List Bool) (memory : Store)
    (right value reverseWord width used : List Bool) :
    (restoreTrace background memory right value reverseWord width used).head? =
      some (state background 4 memory right [] value reverseWord width used) := by
  cases reverseWord <;> rfl

theorem restoreTrace_length (background : Stack → List Bool) (memory : Store)
    (right value reverseWord width used : List Bool) :
    (restoreTrace background memory right value reverseWord width used).length = reverseWord.length + 2 := by
  induction reverseWord generalizing memory value width used with
  | nil => rfl
  | cons bit reverseWord ih => simp only [restoreTrace, List.length_cons, ih]

theorem restoreTrace_last (background : Stack → List Bool) (memory : Store)
    (right value reverseWord width used : List Bool) :
    (restoreTrace background memory right value reverseWord width used).getLast? =
      some (state background 5 (false, false) right [] (reverseWord.reverse ++ value) []
        (List.replicate reverseWord.length true ++ width) (used.drop reverseWord.length)) := by
  induction reverseWord generalizing memory value width used with
  | nil => rfl
  | cons bit reverseWord ih =>
    rw [restoreTrace, StatementClock.prepend_last _ _ (by rw [restoreTrace_length]; omega), ih]
    simp only [List.reverse_cons, List.length_cons, List.replicate_succ', List.append_assoc,
      List.cons_append, List.nil_append, List.drop_tail]

theorem restoreTrace_chain (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (right value reverseWord width used : List Bool) :
    (restoreTrace background memory right value reverseWord width used).IsChain
      (fun before after => TM2.step (program caller) before = some after) := by
  induction reverseWord generalizing memory value width used with
  | nil =>
    exact List.isChain_cons_cons.mpr ⟨restore_done caller background memory right value width used,
      List.isChain_singleton _⟩
  | cons bit reverseWord ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_, ih (true, bit) (bit :: value) (true :: width) used.tail⟩
    intro next present
    rw [restoreTrace_head] at present
    have same := Option.some.inj (Option.mem_def.mp present)
    subst next
    exact restore_bit caller background memory bit right value reverseWord width used

theorem restoreTrace_fields (background : Stack → List Bool) (memory : Store)
    (right value reverseWord width used : List Bool) :
    ∀ current ∈ restoreTrace background memory right value reverseWord width used,
      ∃ (result reversed room tally : List Bool) (flags : Label × Store),
        current = state background flags.1 flags.2 right [] result reversed room tally ∧
        result.length + reversed.length = value.length + reverseWord.length ∧
        room.length ≤ width.length + reverseWord.length ∧ tally.length ≤ used.length := by
  induction reverseWord generalizing memory value width used with
  | nil =>
    intro current present
    simp only [restoreTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact ⟨value, [], width, used, (4, memory), rfl, rfl, by simp, le_rfl⟩
    · exact ⟨value, [], width, used, (5, (false, false)), rfl, rfl, by simp, le_rfl⟩
  | cons bit reverseWord ih =>
    intro current present
    rcases List.mem_cons.mp present with same | later
    · subst current
      exact ⟨value, bit :: reverseWord, width, used, (4, memory), rfl, rfl, by simp, le_rfl⟩
    · obtain ⟨result, reversed, room, tally, flags, same, dataMass, roomBound, tallyBound⟩ :=
        ih (true, bit) (bit :: value) (true :: width) used.tail current later
      refine ⟨result, reversed, room, tally, flags, same, ?_, ?_, ?_⟩
      · simp only [List.length_cons] at dataMass ⊢
        omega
      · simp only [List.length_cons] at roomBound ⊢
        omega
      · simp only [List.length_tail] at tallyBound
        omega

def clearRightTrace (background : Stack → List Bool) :
    Store → List Bool → List Bool → List Bool → List Bool → List State
  | memory, [], value, width, used =>
      [state background 5 memory [] [] value [] width used,
        state background 6 (false, false) [] [] value [] width used,
        state background 7 (false, false) [] [] value [] width used]
  | memory, bit :: right, value, width, used =>
      state background 5 memory (bit :: right) [] value [] width used ::
        clearRightTrace background (true, bit) right value width used

theorem clearRightTrace_head (background : Stack → List Bool) (memory : Store)
    (right value width used : List Bool) :
    (clearRightTrace background memory right value width used).head? =
      some (state background 5 memory right [] value [] width used) := by
  cases right <;> rfl

theorem clearRightTrace_length (background : Stack → List Bool) (memory : Store)
    (right value width used : List Bool) :
    (clearRightTrace background memory right value width used).length = right.length + 3 := by
  induction right generalizing memory with
  | nil => rfl
  | cons bit right ih => simp only [clearRightTrace, List.length_cons, ih]

theorem clearRightTrace_last (background : Stack → List Bool) (memory : Store)
    (right value width used : List Bool) :
    (clearRightTrace background memory right value width used).getLast? =
      some (state background 7 (false, false) [] [] value [] width used) := by
  induction right generalizing memory with
  | nil => rfl
  | cons bit right ih =>
    rw [clearRightTrace, StatementClock.prepend_last _ _ (by rw [clearRightTrace_length]; omega), ih]

theorem clearRightTrace_chain (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (right value width used : List Bool) :
    (clearRightTrace background memory right value width used).IsChain
      (fun before after => TM2.step (program caller) before = some after) := by
  induction right generalizing memory with
  | nil =>
    exact List.isChain_cons_cons.mpr ⟨clear_right_done caller background memory value width used,
      List.isChain_cons_cons.mpr ⟨return_step caller background (false, false) value width used,
        List.isChain_singleton _⟩⟩
  | cons bit right ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_, ih (true, bit)⟩
    intro next present
    rw [clearRightTrace_head] at present
    have same := Option.some.inj (Option.mem_def.mp present)
    subst next
    exact clear_right_bit caller background memory bit right value width used

theorem clearRightTrace_fields (background : Stack → List Bool) (memory : Store)
    (right value width used : List Bool) :
    ∀ current ∈ clearRightTrace background memory right value width used,
      ∃ (remaining : List Bool) (flags : Label × Store),
        current = state background flags.1 flags.2 remaining [] value [] width used ∧
        remaining.length ≤ right.length := by
  induction right generalizing memory with
  | nil =>
    intro current present
    simp only [clearRightTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl
    · exact ⟨[], (5, memory), rfl, le_rfl⟩
    · exact ⟨[], (6, (false, false)), rfl, le_rfl⟩
    · exact ⟨[], (7, (false, false)), rfl, le_rfl⟩
  | cons bit right ih =>
    intro current present
    rcases List.mem_cons.mp present with same | later
    · subst current
      exact ⟨bit :: right, (5, memory), rfl, le_rfl⟩
    · obtain ⟨remaining, flags, same, small⟩ := ih (true, bit) current later
      refine ⟨remaining, flags, same, ?_⟩
      simp only [List.length_cons]
      omega

end PaperProofs.Common.Native.PSTRWordBool.NatWordIO
