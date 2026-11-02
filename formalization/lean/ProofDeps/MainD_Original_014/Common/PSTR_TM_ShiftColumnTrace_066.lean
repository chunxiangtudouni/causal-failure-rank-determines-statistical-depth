module
public import Common.PSTR_TM_ShiftColumnCode_065

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMShiftColumnTrace066
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMShiftColumnCode065

def unitTrace (carry a b : Bool) (left right : List Bool) : List (MachineState 19) :=
  [state (readA carry) left (a :: true :: b :: true :: right),
    state (flagA carry a) (a :: left) (true :: b :: true :: right),
    state (writeA carry a) left (a :: true :: b :: true :: right),
    state (advance 0 a) left (carry :: true :: b :: true :: right),
    state (advance 1 a) (carry :: left) (true :: b :: true :: right),
    state (advance 2 a) (true :: carry :: left) (b :: true :: right),
    state (advance 3 a) (b :: true :: carry :: left) (true :: right)]

theorem unit_head (carry a b : Bool) (left right : List Bool) :
    (unitTrace carry a b left right).head? = some (state (readA carry) left (a :: true :: b :: true :: right)) := rfl

theorem unit_last (carry a b : Bool) (left right : List Bool) :
    (unitTrace carry a b left right).getLast? = some (state (advance 3 a) (b :: true :: carry :: left) (true :: right)) := rfl

theorem unit_length (carry a b : Bool) (left right : List Bool) : (unitTrace carry a b left right).length = 7 := rfl

theorem unit_chain (carry a b : Bool) (left right : List Bool) :
    (unitTrace carry a b left right).IsChain (fun before after => Turing.TM0.step shiftMachine before = some after) := by
  cases carry <;> cases a <;> cases b <;>
    simp [unitTrace, List.isChain_cons_cons, Turing.TM0.step, shiftMachine, state,
      readA, flagA, writeA, advance, Turing.Tape.mk₂]

theorem unit_advance (a : Bool) (left right : List Bool) :
    Turing.TM0.step shiftMachine (state (advance 3 a) left (true :: right)) =
      some (state (readA a) (true :: left) right) := by
  cases a <;> simp [Turing.TM0.step, shiftMachine, state, readA, advance, Turing.Tape.mk₂]

def endTrace (carry : Bool) (left suffix : List Bool) : List (MachineState 19) :=
  [state (readA carry) left (false :: false :: suffix),
    state (flagA carry false) (false :: left) (false :: suffix),
    state (haltLabel carry) left (false :: false :: suffix)]

theorem end_head (carry : Bool) (left suffix : List Bool) :
    (endTrace carry left suffix).head? = some (state (readA carry) left (false :: false :: suffix)) := rfl

theorem end_last (carry : Bool) (left suffix : List Bool) :
    (endTrace carry left suffix).getLast? = some (state (haltLabel carry) left (false :: false :: suffix)) := rfl

theorem end_length (carry : Bool) (left suffix : List Bool) : (endTrace carry left suffix).length = 3 := rfl

theorem end_chain (carry : Bool) (left suffix : List Bool) :
    (endTrace carry left suffix).IsChain (fun before after => Turing.TM0.step shiftMachine before = some after) := by
  cases carry <;> simp [endTrace, List.isChain_cons_cons, Turing.TM0.step, shiftMachine,
    state, readA, flagA, haltLabel, Turing.Tape.mk₂]

def shiftTrace (carry : Bool) (context : List Bool) (previous : List (Bool × Bool)) :
    List (Bool × Bool) → List Bool → List (MachineState 19)
  | [], suffix => endTrace carry (PSTRTMCompareCode054.leftColumns previous ++ context) suffix
  | (a,b) :: later, suffix =>
    unitTrace carry a b (PSTRTMCompareCode054.leftColumns previous ++ context)
      (PSTRTMBinaryAdd024.operandColumns later ++ false :: false :: suffix) ++
      shiftTrace a context ((carry,b) :: previous) later suffix

theorem shift_head (carry : Bool) (context : List Bool) (previous pairs : List (Bool × Bool)) (suffix : List Bool) :
    (shiftTrace carry context previous pairs suffix).head? = some
      (state (readA carry) (PSTRTMCompareCode054.leftColumns previous ++ context)
        (PSTRTMBinaryAdd024.operandColumns pairs ++ false :: false :: suffix)) := by
  cases pairs with
  | nil => rfl
  | cons pair later =>
    obtain ⟨a,b⟩ := pair
    simp [shiftTrace, List.head?_append, unit_head, PSTRTMBinaryAdd024.operandColumns]

theorem shift_last (carry : Bool) (context : List Bool) (previous pairs : List (Bool × Bool)) (suffix : List Bool) :
    (shiftTrace carry context previous pairs suffix).getLast? = some
      (state (haltLabel (finalCarry carry pairs))
        (PSTRTMCompareCode054.leftColumns ((shiftPairs carry pairs).reverse ++ previous) ++ context)
        (false :: false :: suffix)) := by
  induction pairs generalizing carry previous with
  | nil => simpa only [shiftTrace, shiftPairs, finalCarry, List.reverse_nil, List.nil_append] using end_last carry _ suffix
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp [shiftTrace, List.getLast?_append, ih, shiftPairs, finalCarry, List.reverse_cons, List.append_assoc]

theorem shift_length (carry : Bool) (context : List Bool) (previous pairs : List (Bool × Bool)) (suffix : List Bool) :
    (shiftTrace carry context previous pairs suffix).length = 7 * pairs.length + 3 := by
  induction pairs generalizing carry previous with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp only [shiftTrace, List.length_append, unit_length, ih, List.length_cons]
    omega

theorem shift_chain (carry : Bool) (context : List Bool) (previous pairs : List (Bool × Bool)) (suffix : List Bool) :
    (shiftTrace carry context previous pairs suffix).IsChain (fun before after => Turing.TM0.step shiftMachine before = some after) := by
  induction pairs generalizing carry previous with
  | nil => exact end_chain carry _ suffix
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    rw [shiftTrace]
    apply (unit_chain carry a b _ _).append (ih a ((carry,b) :: previous))
    intro before hb after ha
    simp only [unit_last, Option.mem_some_iff] at hb
    simp only [shift_head, Option.mem_some_iff] at ha
    subst before
    subst after
    simpa only [PSTRTMCompareCode054.leftColumns, List.flatMap_cons, List.cons_append, List.nil_append] using
      unit_advance a (b :: true :: carry :: (PSTRTMCompareCode054.leftColumns previous ++ context))
        (PSTRTMBinaryAdd024.operandColumns later ++ false :: false :: suffix)

/-- Genuine whole-tape frame: A shifts left by one binary digit while B,
every flag, all left context and ALL suffix past OWN00 remain intact.
Actual overflow is retained in HALT control, never assumed away. -/
theorem shift_runsFrom (carry : Bool) (context : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom shiftMachine
      (state (readA carry) context (PSTRTMBinaryAdd024.operandColumns pairs ++ false :: false :: suffix))
      (shiftTrace carry context [] pairs suffix)
      (state (haltLabel (finalCarry carry pairs)) (PSTRTMCompareCode054.leftColumns (shiftPairs carry pairs).reverse ++ context)
        (false :: false :: suffix)) := by
  refine ⟨?_, shift_chain carry context [] pairs suffix, ?_, shift_halt _ _ _⟩
  · simpa only [PSTRTMCompareCode054.leftColumns, List.flatMap_nil, List.nil_append] using shift_head carry context [] pairs suffix
  · simpa only [List.append_nil] using shift_last carry context [] pairs suffix

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMShiftColumnTrace066
