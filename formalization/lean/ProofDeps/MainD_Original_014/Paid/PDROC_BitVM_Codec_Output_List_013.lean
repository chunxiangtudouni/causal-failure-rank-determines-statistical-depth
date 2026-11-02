module

public import Paid.PDROC_BitVM_Codec_Output_List_012

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Codec.OutputList

open Turing

structure FinalPath (before after : FinalState) where
  states : List FinalState
  first : states.head? = some before
  actual : states.IsChain (fun a b => TM2.step finalProgram a = some b)
  last : states.getLast? = some after

theorem joined_last (left right : List FinalState) (middle after : FinalState)
    (leftLast : left.getLast? = some middle) (rightHead : right.head? = some middle)
    (rightLast : right.getLast? = some after) :
    (left ++ right.tail).getLast? = some after := by
  cases right with
  | nil => simp only [List.head?_nil, reduceCtorEq] at rightHead
  | cons head tail =>
    cases tail with
    | nil =>
      have start : head = middle := Option.some.inj rightHead
      have finish : head = after := Option.some.inj rightLast
      simp only [List.tail_cons, List.append_nil]
      exact leftLast.trans (congrArg some (start.symm.trans finish))
    | cons next rest =>
      have notOne : (head :: next :: rest).length ≠ 1 := by
        simp only [List.length_cons]
        omega
      simp only [List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte,
        rightLast, Option.some_or]

def FinalPath.append {before middle after : FinalState}
    (left : FinalPath before middle) (right : FinalPath middle after) : FinalPath before after where
  states := left.states ++ right.states.tail
  first := by simp only [List.head?_append, left.first, Option.some_or]
  actual := PDROC.BitVM.Log.TwoStack.join_chain left.states right.states middle
    left.actual right.actual left.last right.first
  last := joined_last left.states right.states middle after left.last right.first right.last

theorem FinalPath.append_length {before middle after : FinalState}
    (left : FinalPath before middle) (right : FinalPath middle after) :
    (left.append right).states.length ≤ left.states.length + right.states.length := by
  simp only [FinalPath.append, List.length_append, List.length_tail]
  omega

theorem finalState_eq (left right : FinalState) (label : left.l = right.l)
    (store : left.var = right.var) (data : left.stk = right.stk) : left = right := by
  rcases left with ⟨leftLabel, leftStore, leftData⟩
  rcases right with ⟨rightLabel, rightStore, rightData⟩
  change leftLabel = rightLabel at label
  change leftStore = rightStore at store
  change leftData = rightData at data
  subst rightLabel
  subst rightStore
  subst rightData
  rfl

def finalBefore (word bytes ticks initialLeft : List Bool) (store : CountStore) : FinalState :=
  PDROC.BitVM.Native.Inline.cfg preCleanLabels 2 ()
    (cleanBefore word bytes.reverse initialLeft ticks store)

def finalAfter (state : FinalState) : FinalState := ⟨none, state.var, state.stk⟩

theorem final_halt_edge (before : FinalState) (position : before.l = some 15) :
    TM2.step finalProgram before = some (finalAfter before) := by
  rcases before with ⟨label, store, contents⟩
  change label = some 15 at position
  subst label
  rfl

/-- All input lists here describe physical runtime data. Count n is not an
argument of the fixed machine: it comes from actually consuming ticks.
This certificate selects the counter witness ONCE and joins its actual
return, left cleanup, official Nat reader, right cleanup and two drains. -/
theorem final_build (word bytes ticks initialLeft : List Bool) (store : CountStore) :
    ∃ (counter : List CountState) (counted : CountState) (padding : List Bool) (after : FinalState)
      (path : FinalPath (finalBefore word bytes ticks initialLeft store) after),
      counter.head? = some (countInitState word bytes.reverse ticks (store.1, none)) ∧
      counter.IsChain (fun a b => TM2.step countProgram a = some b) ∧
      counter.getLast? = some counted ∧
      counted.stk 0 = PaperProofs.Common.Native.RationalControllerComputation.encodeNat ticks.length ++ padding ∧
      counted.stk 1 = bytes.reverse ∧ counted.stk 3 = [] ∧
      counter.length ≤ word.length + 2 + countCost 0 ticks.length ∧
      after.l = none ∧ after.stk = emitSlots
        (PaperProofs.Common.Native.RationalControllerComputation.encodeNat ticks.length ++
          bytes ++ [true]) [] [] [] ∧
      path.states.length ≤ initialLeft.length + 2 + counter.length + (counted.stk 2).length + padding.length +
        bytes.length + 4 * PaperProofs.Common.Native.RationalControllerComputation.natBits ticks.length + 20 := by
  let readyStore : CountStore := (store.1, none)
  let preStart := cleanBefore word bytes.reverse initialLeft ticks store
  let preFinal := cleanAfter word bytes.reverse ticks store
  obtain ⟨preRun, preEnd, preHead, preActual, preLast, preReturn, preFrame,
    preStore, preLength⟩ :=
    PDROC.BitVM.Native.Inline.actual_return_trace preCleanLabels 2 cleanProgram finalProgram
      final_preClean_agrees (cleanTrace word bytes.reverse ticks initialLeft store)
      preStart preFinal () (clean_head _ _ _ _ _) (clean_chain _ _ _ _ _) (clean_last _ _ _ _ _) rfl
  obtain ⟨counter, counted, padding, counterHead, counterChain, counterLast, counterHalt,
    _counterPosition, _counterTape, physical, countTicks, countOutput, counterSize⟩ :=
    count_complete_physical word bytes.reverse ticks readyStore
  have countData : counted.stk = emitSlots
      (PaperProofs.Common.Native.RationalControllerComputation.encodeNat ticks.length ++ padding)
      bytes.reverse (counted.stk 2) [] := by
    funext role
    fin_cases role
    · exact physical
    · exact countOutput
    · rfl
    · exact countTicks
  obtain ⟨countRun, countEnd, countHead, countActual, countLast, countReturn, countFrame,
    countStore, countLength⟩ :=
    PDROC.BitVM.Native.Inline.actual_return_trace countLabels 4 countProgram finalProgram
      final_count_agrees counter (countInitState word bytes.reverse ticks readyStore) counted ()
      counterHead counterChain counterLast counterHalt
  have boundary0 : preEnd = PDROC.BitVM.Native.Inline.cfg countLabels 4 ()
      (countInitState word bytes.reverse ticks readyStore) := by
    apply finalState_eq
    · exact preReturn
    · exact preStore
    · exact preFrame
  let right := PaperProofs.Common.Native.RationalControllerComputation.encodeNat ticks.length ++ padding
  let cleanStart := cleanBefore right bytes.reverse (counted.stk 2) [] counted.var
  let cleanFinal := cleanAfter right bytes.reverse [] counted.var
  have boundary1 : countEnd = PDROC.BitVM.Native.Inline.cfg cleanLabels 6 () cleanStart := by
    apply finalState_eq
    · exact countReturn
    · exact countStore
    · exact countFrame.trans countData
  obtain ⟨cleanRun, cleanEnd, cleanHead, cleanActual, cleanLast, cleanReturn, cleanFrame,
    cleanStore, cleanLength⟩ :=
    PDROC.BitVM.Native.Inline.actual_return_trace cleanLabels 6 cleanProgram finalProgram
      final_clean_agrees (cleanTrace right bytes.reverse [] (counted.stk 2) counted.var)
      cleanStart cleanFinal () (clean_head _ _ _ _ _) (clean_chain _ _ _ _ _) (clean_last _ _ _ _ _) rfl
  let readStart := readerBefore ticks.length padding bytes.reverse (counted.var.1, none)
  let readFinal := readerAfter ticks.length padding bytes.reverse counted.var.1
  have boundary2 : cleanEnd = PDROC.BitVM.Native.Inline.cfg readLabels 11 () readStart := by
    apply finalState_eq
    · exact cleanReturn
    · exact cleanStore
    · exact cleanFrame
  obtain ⟨readSource, readHead, readChain, readLast, readHalt, readSize,
    _readRight, _readOut, _readTicks, _readHeader⟩ :=
    reader_runs ticks.length padding bytes.reverse (counted.var.1, none)
  obtain ⟨readRun, readEnd, readFirst, readActual, readFinish, readReturn, readFrame,
    readStore, readLength⟩ :=
    PDROC.BitVM.Native.Inline.actual_return_trace readLabels 11 readerProgram finalProgram
      final_read_agrees readSource readStart readFinal () readHead readChain readLast readHalt
  let header := PaperProofs.Common.Native.RationalControllerComputation.encodeNat ticks.length
  let flushStart := flushBefore padding bytes header (counted.var.1, none)
  let flushFinal := flushAfter bytes header counted.var.1
  have boundary3 : readEnd = PDROC.BitVM.Native.Inline.cfg flushLabels 15 () flushStart := by
    apply finalState_eq
    · exact readReturn
    · exact readStore
    · exact readFrame
  obtain ⟨flushSource, flushHead, flushActual, flushLast, flushHalt, flushSize,
    _finalBytes, _outEmpty, _leftEmpty, _headerEmpty⟩ :=
    flush_runs padding bytes header (counted.var.1, none)
  obtain ⟨flushRun, flushEnd, flushFirst, flushReal, flushFinish, flushReturn, flushFrame,
    flushStore, flushLength⟩ :=
    PDROC.BitVM.Native.Inline.actual_return_trace flushLabels 15 flushProgram finalProgram
      final_flush_agrees flushSource flushStart flushFinal () flushHead flushActual flushLast flushHalt
  let part0 : FinalPath (finalBefore word bytes ticks initialLeft store) preEnd :=
    ⟨preRun, preHead, preActual, preLast⟩
  let part1 : FinalPath preEnd countEnd :=
    ⟨countRun, by rw [boundary0]; exact countHead, countActual, countLast⟩
  let part2 : FinalPath countEnd cleanEnd :=
    ⟨cleanRun, by rw [boundary1]; exact cleanHead, cleanActual, cleanLast⟩
  let part3 : FinalPath cleanEnd readEnd :=
    ⟨readRun, by rw [boundary2]; exact readFirst, readActual, readFinish⟩
  let part4 : FinalPath readEnd flushEnd :=
    ⟨flushRun, by rw [boundary3]; exact flushFirst, flushReal, flushFinish⟩
  let part5 : FinalPath flushEnd (finalAfter flushEnd) :=
    ⟨[flushEnd, finalAfter flushEnd], rfl,
      List.isChain_cons_cons.mpr ⟨final_halt_edge flushEnd flushReturn, List.isChain_singleton _⟩, rfl⟩
  let combined := ((((part0.append part1).append part2).append part3).append part4).append part5
  have total : combined.states.length ≤ preRun.length + countRun.length + cleanRun.length + readRun.length +
      flushRun.length + 2 := by
    have zero := part0.append_length part1
    have one := (part0.append part1).append_length part2
    have two := ((part0.append part1).append part2).append_length part3
    have three := (((part0.append part1).append part2).append part3).append_length part4
    have four := ((((part0.append part1).append part2).append part3).append part4).append_length part5
    change _ ≤ preRun.length + countRun.length + cleanRun.length + readRun.length + flushRun.length + 2
    dsimp only [part0, part1, part2, part3, part4, part5] at zero one two three four
    simp only [List.length_cons, List.length_nil] at four
    dsimp only [combined, part0, part1, part2, part3, part4, part5]
    omega
  have size : combined.states.length ≤ initialLeft.length + 2 + counter.length + (counted.stk 2).length + padding.length +
      bytes.length + 4 * PaperProofs.Common.Native.RationalControllerComputation.natBits ticks.length + 20 := by
    rw [preLength, clean_length, countLength, cleanLength, clean_length,
      readLength, readSize, flushLength, flushSize] at total
    have headerSize : header.length =
        2 * PaperProofs.Common.Native.RationalControllerComputation.natBits ticks.length + 1 := by
      simp [header, PaperProofs.Common.Native.RationalControllerComputation.encodeNat]
      omega
    rw [headerSize] at total
    omega
  exact ⟨counter, counted, padding, finalAfter flushEnd, combined, counterHead, counterChain, counterLast,
    physical, countOutput, countTicks, counterSize, rfl, flushFrame, size⟩

end PDROC.BitVM.Codec.OutputList
