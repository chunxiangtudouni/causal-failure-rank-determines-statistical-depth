module

public import Common.PSTR_SYM_RawEOFPolynomial_064

/-! The SAME concrete059 parser/cursor loop stops at its counted first
TRUE footer while preserving an arbitrary unread physical suffix. A first
stream EOF is not asserted to be global blank. The next stream's actual
RIGHT/header/zero branch remains a separate producer obligation. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawLoop

open Turing PSTRTMSeq005 PSTRTMRawNat010 PSTRTMIncrement009
open PSTRTMThresholdCountdownCode164 PSTRSymbolicCounter
open PSTRSymbolicLaneScan PSTRSymbolicLaneArchive PSTRSymbolicCursorArchive

def pendingSuffix (data : List Datum) (base digits : List Bool)
    (remaining : List Datum) (unread : List Bool) : Tape Bool :=
  Tape.mk₂ ((navigationCells (allDatumPairs data)).reverse ++ false :: (leftBlocks digits.reverse ++ false :: base))
    (remaining.flatMap encodeDatum ++ true :: unread)

theorem pendingSuffix_cons (data : List Datum) (base digits : List Bool)
    (value : Datum) (remaining : List Datum) (unread : List Bool) :
    pendingSuffix data base digits (value :: remaining) unread =
      datumEntryTape data base digits (remaining.flatMap encodeDatum ++ true :: unread) value := by
  simp only [pendingSuffix,datumEntryTape,List.flatMap_cons,List.append_assoc]

theorem actual_remaining_suffix (data remaining : List Datum) (base digits unread : List Bool) (bytes : Nat)
    (nonempty : remaining ≠ []) (archiveRoom : 3 ≤ (allDatumPairs data).length)
    (headerRoom : 3 ≤ digits.length) (countValue : valueDigits digits = remaining.length)
    (sized : ∀ value ∈ remaining, (encodeDatum value).length ≤ bytes) :
    ∃ (endDigits : List Bool) (trace : List (TM0.Cfg Bool LoopLabel)) (final : TM0.Cfg Bool LoopLabel),
      trace.head? = some ⟨.datum 0,pendingSuffix data base digits remaining unread⟩ ∧
      trace.IsChain (fun before after => TM0.step loopCode before = some after) ∧
      trace.getLast? = some final ∧
      final.q = .cursor (PSTRSymbolicCursorFinite.labels (.halt true)) ∧
      final.Tape = archiveTape (data ++ remaining) base endDigits unread true ∧
      TM0.step loopCode final = some ⟨.done true,final.Tape⟩ ∧
      valueDigits endDigits = 0 ∧ endDigits.length = digits.length ∧
      trace.length ≤ remaining.length * cycleBudget (allDatumPairs (data ++ remaining)).length digits.length bytes := by
  induction remaining generalizing data digits with
  | nil => exact False.elim (nonempty rfl)
  | cons value remaining ih =>
    have updatedRoom : 3 ≤ (allDatumPairs (data ++ [value])).length := by
      rw [pairs_append,List.length_append]
      omega
    have positive : true ∈ digits := has_true_of_value_pos digits (by rw [countValue]; simp)
    have tailNonempty : remaining.flatMap encodeDatum ++ true :: unread ≠ [] := by simp
    obtain ⟨tag,suffix,suffixShape⟩ := List.exists_cons_of_ne_nil tailNonempty
    obtain ⟨bodyTrace,bodyFinal,bodyHead,bodyChain,bodyLast,bodyPort,bodyTape,bodyNext,bodyTime⟩ :=
      actual_cycle data value base digits suffix tag updatedRoom headerRoom positive
    have initialHead : bodyTrace.head? =
        some ⟨.datum 0,pendingSuffix data base digits (value :: remaining) unread⟩ := by
      rw [pendingSuffix_cons,suffixShape]
      exact bodyHead
    have valueAfter : valueDigits (predDigits digits) = remaining.length := by
      have decremented := counterRound_value digits positive
      simp only [List.length_cons] at countValue
      omega
    have widthAfter : (predDigits digits).length = digits.length := pred_length digits
    have physical : bodyFinal.Tape = pendingSuffix (data ++ [value]) base (predDigits digits) remaining unread := by
      rw [bodyTape]
      change Tape.mk₂ _ (tag :: suffix) = Tape.mk₂ _ (remaining.flatMap encodeDatum ++ true :: unread)
      rw [suffixShape]
    have fullShape : (data ++ [value]) ++ remaining = data ++ value :: remaining := by
      simp only [List.append_assoc,List.singleton_append]
    have prefixPairs : (allDatumPairs (data ++ [value])).length ≤
        (allDatumPairs (data ++ value :: remaining)).length := by
      rw [← fullShape,pairs_append (data ++ [value]) remaining,List.length_append]
      omega
    have valueSize : (encodeDatum value).length ≤ bytes := sized value (by simp)
    have square := Nat.pow_le_pow_left (Nat.add_le_add_right valueSize 1) 2
    have charged : bodyTrace.length ≤
        cycleBudget (allDatumPairs (data ++ value :: remaining)).length digits.length bytes := by
      unfold cycleBudget
      omega
    cases remaining with
    | nil =>
      have suffixValues : tag = true ∧ suffix = unread := by
        simpa only [List.flatMap_nil,List.nil_append,List.cons.injEq] using suffixShape.symm
      rcases suffixValues with ⟨rfl,rfl⟩
      have oldOne : valueDigits digits = 1 := by simpa only [List.length_singleton] using countValue
      have zero : decide (valueDigits digits = 1) = true := by simp only [oldOne,decide_true]
      rw [zero] at bodyPort bodyNext
      refine ⟨predDigits digits,bodyTrace,bodyFinal,initialHead,bodyChain,bodyLast,bodyPort,bodyTape,?_,?_,widthAfter,?_⟩
      · exact bodyNext
      · exact valueAfter
      · simpa only [List.length_singleton,Nat.one_mul] using charged
    | cons next later =>
      have oldNotOne : valueDigits digits ≠ 1 := by
        simp only [List.length_cons] at countValue
        omega
      have zero : decide (valueDigits digits = 1) = false := by simp only [oldNotOne,decide_false]
      rw [zero] at bodyPort bodyNext
      have restSized : ∀ item ∈ next :: later, (encodeDatum item).length ≤ bytes := by
        intro item member
        exact sized item (List.mem_cons_of_mem value member)
      have newHeaderRoom : 3 ≤ (predDigits digits).length := by rw [widthAfter]; exact headerRoom
      obtain ⟨endDigits,restTrace,restFinal,restHead,restChain,restLast,restPort,restTape,restNext,
        endValue,endWidth,restTime⟩ := ih (data := data ++ [value]) (digits := predDigits digits)
          (by simp) updatedRoom newHeaderRoom valueAfter restSized
      have bridge : TM0.step loopCode bodyFinal = some
          ⟨.datum 0,pendingSuffix (data ++ [value]) base (predDigits digits) (next :: later) unread⟩ := by
        simpa [physical] using bodyNext
      let trace := bodyTrace ++ restTrace
      have chain : trace.IsChain (fun before after => TM0.step loopCode before = some after) := by
        apply List.IsChain.append bodyChain restChain
        intro before beforeLast after afterHead
        simp only [bodyLast,Option.mem_some_iff] at beforeLast
        simp only [restHead,Option.mem_some_iff] at afterHead
        subst before
        subst after
        exact bridge
      rw [fullShape] at restTape restTime
      rw [widthAfter] at restTime endWidth
      refine ⟨endDigits,trace,restFinal,?_,chain,?_,restPort,restTape,restNext,endValue,endWidth,?_⟩
      · simp only [trace,List.head?_append,initialHead,Option.some_or]
      · simp only [trace,List.getLast?_append,restLast,Option.some_or]
      · calc
          trace.length = bodyTrace.length + restTrace.length := List.length_append
          _ ≤ cycleBudget (allDatumPairs (data ++ value :: next :: later)).length digits.length bytes +
              (next :: later).length * cycleBudget (allDatumPairs (data ++ value :: next :: later)).length digits.length bytes :=
            Nat.add_le_add charged restTime
          _ = (value :: next :: later).length *
              cycleBudget (allDatumPairs (data ++ value :: next :: later)).length digits.length bytes := by
            simp only [List.length_cons,Nat.succ_mul]
            omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawLoop
