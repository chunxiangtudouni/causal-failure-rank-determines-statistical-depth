module

public import Common.PSTR_WordBool_WordNatCode_042

/-! The actual high-FALSE trim and binary payload emission phases of the
fixed Word-to-Nat formatter. A zero payload and its tally cell are physically
pushed by the program. The permanent word bank is always framed. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.WordNatIO

open Turing
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTrimCode103 (keepReverse)

theorem trim_false (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (left output counter : List Bool) :
    TM2.step (program caller) (state background 1 memory [] (false :: left) output counter) =
      some (state background 1 (true, false) [] left output counter) := by
  change some (TM2.stepAux (program caller 1) memory
    (cells background [] (false :: left) output counter)) = _
  simp only [program_one, TM2.stepAux, cells_left, List.head?_cons, List.tail_cons, capture,
    Option.isSome_some, Option.getD_some, Bool.cond_true, Bool.cond_false, jump]
  rw [update_left]
  rfl

theorem trim_true (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (left output counter : List Bool) :
    TM2.step (program caller) (state background 1 memory [] (true :: left) output counter) =
      some (state background 2 (true, true) [] (true :: left) output counter) := by
  change some (TM2.stepAux (program caller 1) memory
    (cells background [] (true :: left) output counter)) = _
  simp only [program_one, TM2.stepAux, cells_left, List.head?_cons, List.tail_cons, capture,
    Option.isSome_some, Option.getD_some, Bool.cond_true, jump]
  rw [update_left, cells_left, update_left]
  rfl

theorem trim_zero (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (output counter : List Bool) :
    TM2.step (program caller) (state background 1 memory [] [] output counter) =
      some (state background 3 (false, false) [] [] (false :: output) (true :: counter)) := by
  change some (TM2.stepAux (program caller 1) memory
    (cells background [] [] output counter)) = _
  simp only [program_one, TM2.stepAux, cells_left, List.head?_nil, List.tail_nil, capture,
    Option.isSome_none, Option.getD_none, Bool.cond_false, jump]
  rw [update_left, cells_output, update_output, cells_counter, update_counter]
  rfl

def trimTrace (background : Stack → List Bool) :
    Store → List Bool → List Bool → List Bool → List State
  | memory, [], output, counter =>
      [state background 1 memory [] [] output counter,
        state background 3 (false, false) [] [] (false :: output) (true :: counter)]
  | memory, false :: left, output, counter =>
      state background 1 memory [] (false :: left) output counter ::
        trimTrace background (true, false) left output counter
  | memory, true :: left, output, counter =>
      [state background 1 memory [] (true :: left) output counter,
        state background 2 (true, true) [] (true :: left) output counter]

def afterTrim (background : Stack → List Bool) (left output counter : List Bool) : State :=
  match keepReverse left with
  | [] => state background 3 (false, false) [] [] (false :: output) (true :: counter)
  | bit :: rest => state background 2 (true, true) [] (bit :: rest) output counter

theorem trimTrace_head (background : Stack → List Bool) (memory : Store)
    (left output counter : List Bool) :
    (trimTrace background memory left output counter).head? =
      some (state background 1 memory [] left output counter) := by
  cases left with
  | nil => rfl
  | cons bit rest => cases bit <;> rfl

theorem trimTrace_length (background : Stack → List Bool) (memory : Store)
    (left output counter : List Bool) :
    2 ≤ (trimTrace background memory left output counter).length ∧
      (trimTrace background memory left output counter).length ≤ left.length + 2 := by
  induction left generalizing memory with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | cons bit left ih =>
    cases bit
    · simpa only [trimTrace, List.length_cons] using
        (show 2 ≤ (trimTrace background (true, false) left output counter).length + 1 ∧
          (trimTrace background (true, false) left output counter).length + 1 ≤ left.length + 1 + 2 by
          obtain ⟨lower, upper⟩ := ih (true, false)
          omega)
    · simp only [trimTrace, List.length_cons, List.length_nil]
      omega

theorem trimTrace_last (background : Stack → List Bool) (memory : Store)
    (left output counter : List Bool) :
    (trimTrace background memory left output counter).getLast? =
      some (afterTrim background left output counter) := by
  induction left generalizing memory with
  | nil => rfl
  | cons bit left ih =>
    cases bit
    · rw [trimTrace, StatementClock.prepend_last _ _ (by
        have positive := (trimTrace_length background (true, false) left output counter).1
        omega)]
      simpa only [afterTrim, keepReverse] using ih (true, false)
    · rfl

theorem trimTrace_chain (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (left output counter : List Bool) :
    (trimTrace background memory left output counter).IsChain
      (fun before after => TM2.step (program caller) before = some after) := by
  induction left generalizing memory with
  | nil =>
    exact List.isChain_cons_cons.mpr ⟨trim_zero caller background memory output counter,
      List.isChain_singleton _⟩
  | cons bit left ih =>
    cases bit
    · apply List.isChain_cons.mpr
      refine ⟨?_, ih (true, false)⟩
      intro next present
      rw [trimTrace_head] at present
      have same := Option.some.inj (Option.mem_def.mp present)
      subst next
      exact trim_false caller background memory left output counter
    · exact List.isChain_cons_cons.mpr ⟨trim_true caller background memory left output counter,
        List.isChain_singleton _⟩

theorem trimTrace_fields (background : Stack → List Bool) (memory : Store)
    (left output counter : List Bool) :
    ∀ current ∈ trimTrace background memory left output counter,
      ∃ (remaining payload tally : List Bool) (flags : Label × Store),
        current = state background flags.1 flags.2 [] remaining payload tally ∧
        remaining.length ≤ left.length ∧ payload.length ≤ output.length + 1 ∧
        tally.length ≤ counter.length + 1 := by
  induction left generalizing memory with
  | nil =>
    intro current present
    simp only [trimTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact ⟨[], output, counter, (1, memory), rfl, by omega, by omega, by omega⟩
    · exact ⟨[], false :: output, true :: counter, (3, (false, false)), rfl,
        by omega, by simp only [List.length_cons]; omega, by simp only [List.length_cons]; omega⟩
  | cons bit left ih =>
    cases bit
    · intro current present
      rcases List.mem_cons.mp present with same | later
      · subst current
        exact ⟨false :: left, output, counter, (1, memory), rfl, by omega, by omega, by omega⟩
      · obtain ⟨remaining, payload, tally, flags, same, small, payloadBound, tallyBound⟩ :=
          ih (true, false) current later
        exact ⟨remaining, payload, tally, flags, same,
          small.trans (by simp only [List.length_cons]; omega), payloadBound, tallyBound⟩
    · intro current present
      simp only [trimTrace, List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl
      · exact ⟨true :: left, output, counter, (1, memory), rfl, by omega, by omega, by omega⟩
      · exact ⟨true :: left, output, counter, (2, (true, true)), rfl, by omega, by omega, by omega⟩

theorem emit_bit (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (bit : Bool) (left output counter : List Bool) :
    TM2.step (program caller) (state background 2 memory [] (bit :: left) output counter) =
      some (state background 2 (true, bit) [] left (bit :: output) (true :: counter)) := by
  change some (TM2.stepAux (program caller 2) memory
    (cells background [] (bit :: left) output counter)) = _
  simp only [program_two, TM2.stepAux, cells_left, List.head?_cons, List.tail_cons, capture,
    Option.isSome_some, Option.getD_some, Bool.cond_true, jump]
  rw [update_left, cells_output, update_output, cells_counter, update_counter]
  rfl

theorem emit_done (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (output counter : List Bool) :
    TM2.step (program caller) (state background 2 memory [] [] output counter) =
      some (state background 3 (false, false) [] [] output counter) := by
  change some (TM2.stepAux (program caller 2) memory
    (cells background [] [] output counter)) = _
  simp only [program_two, TM2.stepAux, cells_left, List.head?_nil, List.tail_nil, capture,
    Option.isSome_none, Option.getD_none, Bool.cond_false, jump]
  rw [update_left]
  rfl

def emitTrace (background : Stack → List Bool) :
    Store → List Bool → List Bool → List Bool → List State
  | memory, [], output, counter =>
      [state background 2 memory [] [] output counter,
        state background 3 (false, false) [] [] output counter]
  | memory, bit :: left, output, counter =>
      state background 2 memory [] (bit :: left) output counter ::
        emitTrace background (true, bit) left (bit :: output) (true :: counter)

theorem emitTrace_head (background : Stack → List Bool) (memory : Store)
    (left output counter : List Bool) :
    (emitTrace background memory left output counter).head? =
      some (state background 2 memory [] left output counter) := by
  cases left <;> rfl

theorem emitTrace_length (background : Stack → List Bool) (memory : Store)
    (left output counter : List Bool) :
    (emitTrace background memory left output counter).length = left.length + 2 := by
  induction left generalizing memory output counter with
  | nil => rfl
  | cons bit left ih => simp only [emitTrace, List.length_cons, ih]

theorem emitTrace_last (background : Stack → List Bool) (memory : Store)
    (left output counter : List Bool) :
    (emitTrace background memory left output counter).getLast? =
      some (state background 3 (false, false) [] [] (left.reverse ++ output)
        (List.replicate left.length true ++ counter)) := by
  induction left generalizing memory output counter with
  | nil => rfl
  | cons bit left ih =>
    rw [emitTrace, StatementClock.prepend_last _ _ (by rw [emitTrace_length]; omega), ih]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append,
      List.length_cons, List.replicate_succ']

theorem emitTrace_chain (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (left output counter : List Bool) :
    (emitTrace background memory left output counter).IsChain
      (fun before after => TM2.step (program caller) before = some after) := by
  induction left generalizing memory output counter with
  | nil => exact List.isChain_cons_cons.mpr ⟨emit_done caller background memory output counter,
      List.isChain_singleton _⟩
  | cons bit left ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_, ih (true, bit) (bit :: output) (true :: counter)⟩
    intro next present
    rw [emitTrace_head] at present
    have same := Option.some.inj (Option.mem_def.mp present)
    subst next
    exact emit_bit caller background memory bit left output counter

theorem emitTrace_fields (background : Stack → List Bool) (memory : Store)
    (left output counter : List Bool) :
    ∀ current ∈ emitTrace background memory left output counter,
      ∃ (remaining payload tally : List Bool) (flags : Label × Store),
        current = state background flags.1 flags.2 [] remaining payload tally ∧
        remaining.length + payload.length = left.length + output.length ∧
        tally.length + remaining.length = counter.length + left.length := by
  induction left generalizing memory output counter with
  | nil =>
    intro current present
    simp only [emitTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact ⟨[], output, counter, (2, memory), rfl, by omega, by omega⟩
    · exact ⟨[], output, counter, (3, (false, false)), rfl, by omega, by omega⟩
  | cons bit left ih =>
    intro current present
    rcases List.mem_cons.mp present with same | later
    · subst current
      exact ⟨bit :: left, output, counter, (2, memory), rfl, rfl, rfl⟩
    · obtain ⟨remaining, payload, tally, flags, same, dataMass, tallyMass⟩ :=
        ih (true, bit) (bit :: output) (true :: counter) current later
      refine ⟨remaining, payload, tally, flags, same, ?_, ?_⟩
      · simp only [List.length_cons] at dataMass ⊢; omega
      · simp only [List.length_cons] at tallyMass ⊢; omega

end PaperProofs.Common.Native.PSTRWordBool.WordNatIO
