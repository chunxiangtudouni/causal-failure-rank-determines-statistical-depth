module
public import Common.PSTR_TM_B1LoopLift_072

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1CounterCall073
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMB1LoopCode071

def endRegion (digits : List Bool) : List Bool := false :: false :: true :: false :: PSTRTMIncrement009.blocks digits
def counterArchive (left : List Bool) : List Bool := true :: false :: false :: left

def toCounterTrace (left digits : List Bool) : List (MachineState 81) :=
  [state 68 (false :: left) (false :: true :: false :: PSTRTMIncrement009.blocks digits),
    state 69 (false :: false :: left) (true :: false :: PSTRTMIncrement009.blocks digits),
    state 70 (true :: false :: false :: left) (false :: PSTRTMIncrement009.blocks digits)]

theorem toCounter_head (left digits : List Bool) : (toCounterTrace left digits).head? = some
    (state 68 (false :: left) (false :: true :: false :: PSTRTMIncrement009.blocks digits)) := rfl

theorem toCounter_last (left digits : List Bool) : (toCounterTrace left digits).getLast? = some
    (state 70 (true :: false :: false :: left) (false :: PSTRTMIncrement009.blocks digits)) := rfl

theorem toCounter_length (left digits : List Bool) : (toCounterTrace left digits).length = 3 := rfl

theorem toCounter_chain (left digits : List Bool) :
    (toCounterTrace left digits).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) := by
  simp [toCounterTrace, List.isChain_cons_cons, Turing.TM0.step, loopMachine, state, Turing.Tape.mk₂]

theorem compare_less_transfer (left digits : List Bool) :
    Turing.TM0.step loopMachine
      (liftCompare (PSTRTMCompareCode054.state (PSTRTMCompareCode054.haltLabel 1) left (endRegion digits))) =
      some (state 68 (false :: left) (false :: true :: false :: PSTRTMIncrement009.blocks digits)) := by
  simp [Turing.TM0.step, loopMachine, liftCompare, compareLabel, PSTRTMCompareCode054.state,
    PSTRTMCompareCode054.haltLabel, state, endRegion, Turing.Tape.mk₂]

theorem toCounter_advance (left digits : List Bool) :
    Turing.TM0.step loopMachine
      (state 70 (true :: false :: false :: left) (false :: PSTRTMIncrement009.blocks digits)) =
      some (liftCounter (PSTRTMIncrement009.state 0 (false :: counterArchive left) (PSTRTMIncrement009.blocks digits))) := by
  simp [Turing.TM0.step, loopMachine, state, liftCounter, counterLabel,
    PSTRTMIncrement009.state, counterArchive, Turing.Tape.mk₂]

def fromCounterTrace (left digits : List Bool) : List (MachineState 81) :=
  [state 71 (true :: false :: false :: left) (false :: PSTRTMIncrement009.blocks digits),
    state 72 (false :: false :: left) (true :: false :: PSTRTMIncrement009.blocks digits),
    state 73 (false :: left) (false :: true :: false :: PSTRTMIncrement009.blocks digits)]

theorem fromCounter_head (left digits : List Bool) : (fromCounterTrace left digits).head? = some
    (state 71 (true :: false :: false :: left) (false :: PSTRTMIncrement009.blocks digits)) := rfl

theorem fromCounter_last (left digits : List Bool) : (fromCounterTrace left digits).getLast? = some
    (state 73 (false :: left) (false :: true :: false :: PSTRTMIncrement009.blocks digits)) := rfl

theorem fromCounter_length (left digits : List Bool) : (fromCounterTrace left digits).length = 3 := rfl

theorem fromCounter_chain (left digits : List Bool) :
    (fromCounterTrace left digits).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) := by
  simp [fromCounterTrace, List.isChain_cons_cons, Turing.TM0.step, loopMachine, state, Turing.Tape.mk₂]

theorem counter_return_transfer (left digits : List Bool) :
    Turing.TM0.step loopMachine
      (liftCounter (PSTRTMIncrement009.state 14 (false :: counterArchive left) (PSTRTMIncrement009.blocks digits))) =
      some (state 71 (true :: false :: false :: left) (false :: PSTRTMIncrement009.blocks digits)) := by
  simp [Turing.TM0.step, loopMachine, state, liftCounter, counterLabel,
    PSTRTMIncrement009.state, counterArchive, Turing.Tape.mk₂]

theorem fromCounter_advance (left digits : List Bool) :
    Turing.TM0.step loopMachine
      (state 73 (false :: left) (false :: true :: false :: PSTRTMIncrement009.blocks digits)) =
      some (liftRewindBefore (PSTRTMColumnRewind067.state 0 left (endRegion digits))) := by
  simp [Turing.TM0.step, loopMachine, state, liftRewindBefore, rewindBeforeLabel,
    PSTRTMColumnRewind067.state, endRegion, Turing.Tape.mk₂]

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

def counterCallTrace (left digits : List Bool) : List (MachineState 81) :=
  toCounterTrace left digits ++
    (PSTRTMCounterFrame064.counterTrace (counterArchive left) 0 digits).map liftCounter ++
    fromCounterTrace left (PSTRTMIncrement009.bumpDigits digits)

theorem counterCall_head (left digits : List Bool) : (counterCallTrace left digits).head? = some
    (state 68 (false :: left) (false :: true :: false :: PSTRTMIncrement009.blocks digits)) := by
  simp only [counterCallTrace, List.head?_append, toCounter_head, Option.some_or]

theorem counterCall_last (left digits : List Bool) : (counterCallTrace left digits).getLast? = some
    (state 73 (false :: left) (false :: true :: false :: PSTRTMIncrement009.blocks (PSTRTMIncrement009.bumpDigits digits))) := by
  simp only [counterCallTrace, List.getLast?_append, fromCounter_last, Option.some_or]

theorem counterCall_length_le (left digits : List Bool) : (counterCallTrace left digits).length ≤ 8*digits.length+15 := by
  have hc := PSTRTMCounterFrame064.counter_length_le (counterArchive left) 0 digits
  simp only [counterCallTrace, List.length_append, List.length_map, toCounter_length, fromCounter_length]
  omega

theorem counterCall_chain (left digits : List Bool) :
    (counterCallTrace left digits).IsChain (fun a b => Turing.TM0.step loopMachine a = some b) := by
  unfold counterCallTrace
  refine append_link _ _
    (liftCounter (PSTRTMIncrement009.state 14 (false :: counterArchive left)
      (PSTRTMIncrement009.blocks (PSTRTMIncrement009.bumpDigits digits))))
    (state 71 (true :: false :: false :: left) (false :: PSTRTMIncrement009.blocks (PSTRTMIncrement009.bumpDigits digits)))
    ?_ (fromCounter_chain left _) ?_ (fromCounter_head left _) (counter_return_transfer left _)
  · refine append_link _ _ _ _ (toCounter_chain left digits)
      (PSTRTMB1LoopLift072.counter_chain _ (PSTRTMCounterFrame064.counter_chain (counterArchive left) 0 digits))
      (toCounter_last left digits) ?_ (toCounter_advance left digits)
    simp only [List.head?_map, PSTRTMCounterFrame064.counter_head, Option.map_some,
      PSTRTMCounterFrame064.counterLeft, PSTRTMIncrement009.zeroLeft, List.nil_append]
  · simp only [List.getLast?_append, List.getLast?_map, PSTRTMCounterFrame064.counter_last,
      PSTRTMIncrement009.restoreRight, Option.map_some, Option.some_or]

/-- These are actual instructions preserving the SAME tape and head.
They contribute transitions to the trace; no subprogram state is reset. -/
theorem before_shift_transfer (tape : Turing.Tape Bool) :
    Turing.TM0.step loopMachine ⟨41,tape⟩ = some ⟨42,tape⟩ := by
  simp [Turing.TM0.step, loopMachine, Turing.Tape.write_self]

theorem shift_rewind_transfer (tape : Turing.Tape Bool) :
    Turing.TM0.step loopMachine ⟨60,tape⟩ = some ⟨62,tape⟩ := by
  simp [Turing.TM0.step, loopMachine, Turing.Tape.write_self]

theorem after_compare_transfer (tape : Turing.Tape Bool) :
    Turing.TM0.step loopMachine ⟨67,tape⟩ = some ⟨0,tape⟩ := by
  simp [Turing.TM0.step, loopMachine, Turing.Tape.write_self]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMB1CounterCall073
