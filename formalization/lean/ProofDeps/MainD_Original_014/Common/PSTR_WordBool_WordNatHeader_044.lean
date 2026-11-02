module

public import Common.PSTR_WordBool_WordNatPayload_043

/-! Actual unary length header, delimiter and paid caller return for the
fixed formatter; shared-endpoint trace composition and canonical payload
assembly reuse the frozen actual trace library. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.WordNatIO

open Turing
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTrimCode103 (keepReverse trimmed)

theorem delimiter_step (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (output counter : List Bool) :
    TM2.step (program caller) (state background 3 memory [] [] output counter) =
      some (state background 4 memory [] [] (false :: output) counter) := by
  change some (TM2.stepAux (program caller 3) memory
    (cells background [] [] output counter)) = _
  simp only [program_three, TM2.stepAux, cells_output, jump]
  rw [update_output]
  rfl

theorem header_bit (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (bit : Bool) (output counter : List Bool) :
    TM2.step (program caller) (state background 4 memory [] [] output (bit :: counter)) =
      some (state background 4 (true, bit) [] [] (true :: output) counter) := by
  change some (TM2.stepAux (program caller 4) memory
    (cells background [] [] output (bit :: counter))) = _
  simp only [program_four, TM2.stepAux, cells_counter, List.head?_cons, List.tail_cons, capture,
    Option.isSome_some, Option.getD_some, Bool.cond_true, jump]
  rw [update_counter, cells_output, update_output]
  rfl

theorem header_done (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (output : List Bool) :
    TM2.step (program caller) (state background 4 memory [] [] output []) =
      some (state background 5 (false, false) [] [] output []) := by
  change some (TM2.stepAux (program caller 4) memory
    (cells background [] [] output [])) = _
  simp only [program_four, TM2.stepAux, cells_counter, List.head?_nil, List.tail_nil, capture,
    Option.isSome_none, Option.getD_none, Bool.cond_false, jump]
  rw [update_counter]
  rfl

theorem return_step (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (output : List Bool) :
    TM2.step (program caller) (state background 5 memory [] [] output []) =
      some (state background 6 memory [] [] output []) := by
  change some (TM2.stepAux (program caller 5) memory
    (cells background [] [] output [])) = _
  rw [program_five]
  rfl

def headerTrace (background : Stack → List Bool) : Store → List Bool → List Bool → List State
  | memory, output, [] =>
      [state background 4 memory [] [] output [],
        state background 5 (false, false) [] [] output [],
        state background 6 (false, false) [] [] output []]
  | memory, output, bit :: counter =>
      state background 4 memory [] [] output (bit :: counter) ::
        headerTrace background (true, bit) (true :: output) counter

theorem headerTrace_head (background : Stack → List Bool) (memory : Store)
    (output counter : List Bool) :
    (headerTrace background memory output counter).head? =
      some (state background 4 memory [] [] output counter) := by
  cases counter <;> rfl

theorem headerTrace_length (background : Stack → List Bool) (memory : Store)
    (output counter : List Bool) :
    (headerTrace background memory output counter).length = counter.length + 3 := by
  induction counter generalizing memory output with
  | nil => rfl
  | cons bit counter ih => simp only [headerTrace, List.length_cons, ih]

theorem headerTrace_last (background : Stack → List Bool) (memory : Store)
    (output counter : List Bool) :
    (headerTrace background memory output counter).getLast? =
      some (state background 6 (false, false) [] []
        (List.replicate counter.length true ++ output) []) := by
  induction counter generalizing memory output with
  | nil => rfl
  | cons bit counter ih =>
    rw [headerTrace, StatementClock.prepend_last _ _ (by rw [headerTrace_length]; omega), ih]
    simp only [List.length_cons, List.replicate_succ', List.append_assoc,
      List.cons_append, List.nil_append]

theorem headerTrace_chain (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (output counter : List Bool) :
    (headerTrace background memory output counter).IsChain
      (fun before after => TM2.step (program caller) before = some after) := by
  induction counter generalizing memory output with
  | nil =>
    exact List.isChain_cons_cons.mpr ⟨header_done caller background memory output,
      List.isChain_cons_cons.mpr ⟨return_step caller background (false, false) output,
        List.isChain_singleton _⟩⟩
  | cons bit counter ih =>
    apply List.isChain_cons.mpr
    refine ⟨?_, ih (true, bit) (true :: output)⟩
    intro next present
    rw [headerTrace_head] at present
    have same := Option.some.inj (Option.mem_def.mp present)
    subst next
    exact header_bit caller background memory bit output counter

theorem headerTrace_fields (background : Stack → List Bool) (memory : Store)
    (output counter : List Bool) :
    ∀ current ∈ headerTrace background memory output counter,
      ∃ (payload tally : List Bool) (flags : Label × Store),
        current = state background flags.1 flags.2 [] [] payload tally ∧
        payload.length + tally.length = output.length + counter.length := by
  induction counter generalizing memory output with
  | nil =>
    intro current present
    simp only [headerTrace, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl
    · exact ⟨output, [], (4, memory), rfl, rfl⟩
    · exact ⟨output, [], (5, (false, false)), rfl, rfl⟩
    · exact ⟨output, [], (6, (false, false)), rfl, rfl⟩
  | cons bit counter ih =>
    intro current present
    rcases List.mem_cons.mp present with same | later
    · subst current
      exact ⟨output, bit :: counter, (4, memory), rfl, rfl⟩
    · obtain ⟨payload, tally, flags, same, conserved⟩ :=
        ih (true, bit) (true :: output) current later
      refine ⟨payload, tally, flags, same, ?_⟩
      simp only [List.length_cons] at conserved ⊢
      omega

theorem join_paths (caller : Statement) (frontPart backPart : List State)
    (before middle final : State)
    (frontHead : frontPart.head? = some before)
    (frontChain : frontPart.IsChain (fun before after => TM2.step (program caller) before = some after))
    (frontLast : frontPart.getLast? = some middle)
    (backHead : backPart.head? = some middle)
    (backChain : backPart.IsChain (fun before after => TM2.step (program caller) before = some after))
    (backLast : backPart.getLast? = some final) :
    (frontPart ++ backPart.tail).head? = some before ∧
      (frontPart ++ backPart.tail).IsChain
        (fun before after => TM2.step (program caller) before = some after) ∧
      (frontPart ++ backPart.tail).getLast? = some final ∧
      (frontPart ++ backPart.tail).length ≤ frontPart.length + backPart.length := by
  have decomposed : middle :: backPart.tail = backPart := by
    obtain ⟨rest, same⟩ := List.head?_eq_some_iff.mp backHead
    rw [same]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.head?_append, frontHead]
    rfl
  · exact NativeTrace.join_chain frontPart middle backPart.tail frontLast frontChain
      (decomposed.symm ▸ backChain)
  · exact (NativeTrace.join_last frontPart middle backPart.tail frontLast).trans
      (decomposed.symm ▸ backLast)
  · simp only [List.length_append, List.length_tail]
    omega

def PayloadBounds (background : Stack → List Bool) (width : Nat) (output : List Bool)
    (current : State) : Prop :=
  ∃ (remaining payload tally : List Bool) (flags : Label × Store),
    current = state background flags.1 flags.2 [] remaining payload tally ∧
    remaining.length ≤ width ∧ payload.length ≤ output.length + width + 1 ∧
    tally.length ≤ width + 1

theorem actual_payload (caller : Statement) (background : Stack → List Bool) (memory : Store)
    (word output : List Bool) :
    ∃ trace : List State,
      trace.head? = some (state background 1 memory [] word.reverse output []) ∧
      trace.IsChain (fun before after => TM2.step (program caller) before = some after) ∧
      trace.getLast? = some (state background 3 (false, false) [] [] (trimmed word ++ output)
        (List.replicate (trimmed word).length true)) ∧
      trace.length ≤ 2 * word.length + 4 ∧
      ∀ current ∈ trace, PayloadBounds background word.length output current := by
  let firstPart := trimTrace background memory word.reverse output []
  have firstBounds : ∀ current ∈ firstPart, PayloadBounds background word.length output current := by
    intro current present
    obtain ⟨remaining, payload, tally, flags, same, leftBound, outputBound, countBound⟩ :=
      trimTrace_fields background memory word.reverse output [] current present
    refine ⟨remaining, payload, tally, flags, same, ?_, ?_, ?_⟩
    · simpa only [List.length_reverse] using leftBound
    · omega
    · simp only [List.length_nil] at countBound
      omega
  have firstLength : firstPart.length ≤ word.length + 2 := by
    simpa only [List.length_reverse] using
      (trimTrace_length background memory word.reverse output []).2
  have firstHead := trimTrace_head background memory word.reverse output []
  have firstChain := trimTrace_chain caller background memory word.reverse output []
  have firstLast := trimTrace_last background memory word.reverse output []
  cases kept : keepReverse word.reverse with
  | nil =>
    refine ⟨firstPart, firstHead, firstChain, ?_, by omega, firstBounds⟩
    simpa only [afterTrim, trimmed, kept, List.length_cons, List.length_nil,
      List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append] using firstLast
  | cons bit rest =>
    let secondPart := emitTrace background (true, true) (bit :: rest) output []
    have middle : afterTrim background word.reverse output [] =
        state background 2 (true, true) [] (bit :: rest) output [] := by
      simp only [afterTrim, kept]
    have final : state background 3 (false, false) [] [] ((bit :: rest).reverse ++ output)
        (List.replicate (bit :: rest).length true ++ []) =
        state background 3 (false, false) [] [] (trimmed word ++ output)
          (List.replicate (trimmed word).length true) := by
      simp only [trimmed, kept, List.length_reverse, List.append_nil]
    have joined := join_paths caller firstPart secondPart
      (state background 1 memory [] word.reverse output [])
      (state background 2 (true, true) [] (bit :: rest) output []) _
      firstHead firstChain (firstLast.trans (congrArg some middle))
      (emitTrace_head background (true, true) (bit :: rest) output [])
      (emitTrace_chain caller background (true, true) (bit :: rest) output [])
      ((emitTrace_last background (true, true) (bit :: rest) output []).trans (congrArg some final))
    have keptBound : (bit :: rest).length ≤ word.length := by
      have bound := PSTRTMTrimValue104.keep_length_le word.reverse
      simpa only [kept, List.length_reverse] using bound
    have secondLength : secondPart.length = (bit :: rest).length + 2 :=
      emitTrace_length background (true, true) (bit :: rest) output []
    refine ⟨firstPart ++ secondPart.tail, joined.1, joined.2.1, joined.2.2.1, by
      have count := joined.2.2.2
      omega, ?_⟩
    intro current present
    rcases List.mem_append.mp present with early | later
    · exact firstBounds current early
    · have inside : current ∈ secondPart := List.mem_of_mem_tail later
      obtain ⟨remaining, payload, tally, flags, same, dataMass, countMass⟩ :=
        emitTrace_fields background (true, true) (bit :: rest) output [] current inside
      simp only [List.length_nil] at countMass
      refine ⟨remaining, payload, tally, flags, same, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega

end PaperProofs.Common.Native.PSTRWordBool.WordNatIO
