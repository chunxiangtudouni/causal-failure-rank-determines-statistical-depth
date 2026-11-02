module
public import Common.PSTR_TM_B1CounterCall_073

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1Iteration074
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMB1LoopCode071 PSTRTMB1CounterCall073

def columnsLeft (pairs : List (Bool × Bool)) : List Bool := PSTRTMCompareCode054.leftColumns pairs.reverse ++ [false]
def nextDigits (digits : List Bool) : List Bool := PSTRTMIncrement009.bumpDigits digits
def counterSuffix (digits : List Bool) : List Bool := true :: false :: PSTRTMIncrement009.blocks digits

private theorem append_link (xs ys : List (MachineState 81)) (last first : MachineState 81)
    (hx : xs.IsChain (fun a b => Turing.TM0.step loopMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step loopMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step loopMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def counterBeforeTrace (pairs : List (Bool × Bool)) (digits : List Bool) : List (MachineState 81) :=
  counterCallTrace (columnsLeft pairs) digits ++
    (PSTRTMColumnRewind067.fullTrace [] pairs.reverse (endRegion (nextDigits digits))).map liftRewindBefore

theorem counterBefore_head (pairs : List (Bool × Bool)) (digits : List Bool) :
    (counterBeforeTrace pairs digits).head? = some
      (state 68 (false :: columnsLeft pairs) (false :: true :: false :: PSTRTMIncrement009.blocks digits)) := by
  simp only [counterBeforeTrace, List.head?_append, counterCall_head, Option.some_or]

theorem counterBefore_last (pairs : List (Bool × Bool)) (digits : List Bool) :
    (counterBeforeTrace pairs digits).getLast? = some (liftRewindBefore (PSTRTMColumnRewind067.state 5 [false]
      (PSTRTMBinaryAdd024.operandColumns pairs ++ endRegion (nextDigits digits)))) := by
  simp only [counterBeforeTrace, List.getLast?_append, List.getLast?_map, PSTRTMColumnRewind067.full_last,
    List.reverse_reverse, Option.map_some, Option.some_or]

theorem counterBefore_chain (pairs : List (Bool × Bool)) (digits : List Bool) :
    (counterBeforeTrace pairs digits).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) := by
  unfold counterBeforeTrace
  refine append_link _ _ _ _ (counterCall_chain (columnsLeft pairs) digits)
    (PSTRTMB1LoopLift072.rewindBefore_chain _ (PSTRTMColumnRewind067.full_chain [] pairs.reverse _))
    (counterCall_last (columnsLeft pairs) digits) ?_ (fromCounter_advance (columnsLeft pairs) (nextDigits digits))
  simp only [List.head?_map, PSTRTMColumnRewind067.full_head, Option.map_some, columnsLeft]

theorem counterBefore_length_le (pairs : List (Bool × Bool)) (digits : List Bool) :
    (counterBeforeTrace pairs digits).length ≤ 4*pairs.length+8*digits.length+18 := by
  have hc := counterCall_length_le (columnsLeft pairs) digits
  simp only [counterBeforeTrace, List.length_append, List.length_map, PSTRTMColumnRewind067.full_length, List.length_reverse]
  omega

def shiftAfterTrace (pairs : List (Bool × Bool)) (digits : List Bool) : List (MachineState 81) :=
  (PSTRTMShiftColumnTrace066.shiftTrace false [false] [] pairs (counterSuffix (nextDigits digits))).map liftShift ++
    (PSTRTMColumnRewind067.fullTrace [] (PSTRTMShiftColumnCode065.shiftPairs false pairs).reverse
      (endRegion (nextDigits digits))).map liftRewindAfter

theorem shiftAfter_head (pairs : List (Bool × Bool)) (digits : List Bool) :
    (shiftAfterTrace pairs digits).head? = some (liftShift (PSTRTMShiftColumnCode065.state 0 [false]
      (PSTRTMBinaryAdd024.operandColumns pairs ++ endRegion (nextDigits digits)))) := by
  simp only [shiftAfterTrace, List.head?_append, List.head?_map, PSTRTMShiftColumnTrace066.shift_head,
    Option.map_some, Option.some_or, PSTRTMCompareCode054.leftColumns, List.flatMap_nil, List.nil_append]
  rfl

theorem shiftAfter_last (pairs : List (Bool × Bool)) (digits : List Bool) :
    (shiftAfterTrace pairs digits).getLast? = some (liftRewindAfter (PSTRTMColumnRewind067.state 5 [false]
      (PSTRTMBinaryAdd024.operandColumns (PSTRTMShiftColumnCode065.shiftPairs false pairs) ++ endRegion (nextDigits digits)))) := by
  simp only [shiftAfterTrace, List.getLast?_append, List.getLast?_map, PSTRTMColumnRewind067.full_last,
    List.reverse_reverse, Option.map_some, Option.some_or]

theorem shiftAfter_length (pairs : List (Bool × Bool)) (digits : List Bool) :
    (shiftAfterTrace pairs digits).length = 11*pairs.length+6 := by
  simp only [shiftAfterTrace, List.length_append, List.length_map, PSTRTMShiftColumnTrace066.shift_length,
    PSTRTMColumnRewind067.full_length, List.length_reverse, PSTRTMShiftColumnCode065.shiftPairs_length]
  omega

theorem shiftAfter_chain (pairs : List (Bool × Bool)) (digits : List Bool)
    (noOverflow : PSTRTMShiftColumnCode065.finalCarry false pairs = false) :
    (shiftAfterTrace pairs digits).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) := by
  unfold shiftAfterTrace
  refine append_link _ _
    (liftShift (PSTRTMShiftColumnCode065.state (PSTRTMShiftColumnCode065.haltLabel false)
      (columnsLeft (PSTRTMShiftColumnCode065.shiftPairs false pairs)) (endRegion (nextDigits digits))))
    (liftRewindAfter (PSTRTMColumnRewind067.state 0
      (columnsLeft (PSTRTMShiftColumnCode065.shiftPairs false pairs)) (endRegion (nextDigits digits))))
    (PSTRTMB1LoopLift072.shift_chain _ (PSTRTMShiftColumnTrace066.shift_chain false [false] [] pairs _))
    (PSTRTMB1LoopLift072.rewindAfter_chain _ (PSTRTMColumnRewind067.full_chain [] _ _)) ?_ ?_ ?_
  · simp only [List.getLast?_map, PSTRTMShiftColumnTrace066.shift_last, List.append_nil,
      Option.map_some, noOverflow, columnsLeft]
    rfl
  · simp only [List.head?_map, PSTRTMColumnRewind067.full_head, Option.map_some, columnsLeft]
  · simpa [liftShift, shiftLabel, PSTRTMShiftColumnCode065.state, PSTRTMShiftColumnCode065.haltLabel,
      liftRewindAfter, rewindAfterLabel, PSTRTMColumnRewind067.state] using shift_rewind_transfer
        (Turing.Tape.mk₂ (columnsLeft (PSTRTMShiftColumnCode065.shiftPairs false pairs)) (endRegion (nextDigits digits)))

def iterationTrace (pairs : List (Bool × Bool)) (digits : List Bool) : List (MachineState 81) :=
  counterBeforeTrace pairs digits ++ shiftAfterTrace pairs digits

theorem iteration_head (pairs : List (Bool × Bool)) (digits : List Bool) :
    (iterationTrace pairs digits).head? = some
      (state 68 (false :: columnsLeft pairs) (false :: true :: false :: PSTRTMIncrement009.blocks digits)) := by
  simp only [iterationTrace, List.head?_append, counterBefore_head, Option.some_or]

theorem iteration_last (pairs : List (Bool × Bool)) (digits : List Bool) :
    (iterationTrace pairs digits).getLast? = some (liftRewindAfter (PSTRTMColumnRewind067.state 5 [false]
      (PSTRTMBinaryAdd024.operandColumns (PSTRTMShiftColumnCode065.shiftPairs false pairs) ++ endRegion (nextDigits digits)))) := by
  simp only [iterationTrace, List.getLast?_append, shiftAfter_last, Option.some_or]

theorem iteration_length_le (pairs : List (Bool × Bool)) (digits : List Bool) :
    (iterationTrace pairs digits).length ≤ 15*pairs.length+8*digits.length+24 := by
  have hc := counterBefore_length_le pairs digits
  simp only [iterationTrace, List.length_append, shiftAfter_length]
  omega

/-- EVERY actual counter call/transport, both whole rewinds, column write,
and head-preserving transfer is present. noOverflow is an explicit fact of
the current real columns, to be derived from068/070 in the whole B1 proof;
it is not runtime input or a supplied performance certificate. -/
theorem iteration_chain (pairs : List (Bool × Bool)) (digits : List Bool)
    (noOverflow : PSTRTMShiftColumnCode065.finalCarry false pairs = false) :
    (iterationTrace pairs digits).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) := by
  unfold iterationTrace
  refine append_link _ _ _ _ (counterBefore_chain pairs digits) (shiftAfter_chain pairs digits noOverflow)
    (counterBefore_last pairs digits) (shiftAfter_head pairs digits) ?_
  simpa [liftRewindBefore, rewindBeforeLabel, PSTRTMColumnRewind067.state,
    liftShift, shiftLabel, PSTRTMShiftColumnCode065.state] using before_shift_transfer
      (Turing.Tape.mk₂ [false] (PSTRTMBinaryAdd024.operandColumns pairs ++ endRegion (nextDigits digits)))

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1Iteration074
