module
public import PaperProofs.Common.PSTR_TM_OperandCursor_027

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMContextRaw028
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMRawNat010

/-- Actual false guard immediately before a raw operand, with arbitrary
retained earlier operands beyond it. These are real tape cells. -/
def contextLeft (context previous : List Bool) : List Bool := leftBlocks previous ++ false :: context

def unitTrace (context : List Bool) (bit : Bool) (previous later suffix : List Bool) : List (MachineState 16) :=
  let k := later.length
  let left := contextLeft context previous
  let tail := later ++ suffix
  [state 0 left (List.replicate (k + 1) true ++ false :: bit :: tail),
    state 1 left (false :: (List.replicate k true ++ false :: bit :: tail))] ++
    scanRight k (false :: left) (bit :: tail) ++
    [state 3 (false :: (List.replicate k true ++ false :: left)) (bit :: tail),
      state (payloadMode bit) (false :: (List.replicate k true ++ false :: left)) (false :: tail),
      state (markerMode bit) (List.replicate k true ++ false :: left) (false :: false :: tail),
      state (leftStartMode bit) (List.replicate k true ++ false :: left) (true :: false :: tail)] ++
    scanLeft bit k left (true :: false :: tail) ++
    [state 14 left (bit :: (List.replicate (k + 1) true ++ false :: tail)),
      state 15 (bit :: left) (List.replicate (k + 1) true ++ false :: tail)]

theorem unit_head (context : List Bool) (bit : Bool) (previous later suffix : List Bool) :
    (unitTrace context bit previous later suffix).head? = some
      (state 0 (contextLeft context previous) (List.replicate (later.length + 1) true ++ false :: bit :: (later ++ suffix))) := rfl

theorem unit_length (context : List Bool) (bit : Bool) (previous later suffix : List Bool) :
    (unitTrace context bit previous later suffix).length = 2 * later.length + 10 := by
  simp only [unitTrace, List.length_append, List.length_cons, List.length_nil,
    scanRight_length, scanLeft_length]
  omega

theorem unit_last (context : List Bool) (bit : Bool) (previous later suffix : List Bool) :
    (unitTrace context bit previous later suffix).getLast? = some
      (state 15 (bit :: contextLeft context previous) (List.replicate (later.length + 1) true ++ false :: (later ++ suffix))) := by
  unfold unitTrace
  rw [List.getLast?_append]
  rfl

private theorem append_link (xs ys : List (MachineState 16)) (last first : MachineState 16)
    (hx : xs.IsChain (fun a b => Turing.TM0.step rawNatMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step rawNatMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step rawNatMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step rawNatMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

/-- A full marker/scan/restore rotation of one actual payload bit. -/
theorem unit_chain (context : List Bool) (bit : Bool) (previous later suffix : List Bool) :
    (unitTrace context bit previous later suffix).IsChain (fun before after =>
      Turing.TM0.step rawNatMachine before = some after) := by
  let k := later.length
  let left := contextLeft context previous
  let tail := later ++ suffix
  let first := [state 0 left (List.replicate (k + 1) true ++ false :: bit :: tail),
    state 1 left (false :: (List.replicate k true ++ false :: bit :: tail))]
  let middle := [state 3 (false :: (List.replicate k true ++ false :: left)) (bit :: tail),
    state (payloadMode bit) (false :: (List.replicate k true ++ false :: left)) (false :: tail),
    state (markerMode bit) (List.replicate k true ++ false :: left) (false :: false :: tail),
    state (leftStartMode bit) (List.replicate k true ++ false :: left) (true :: false :: tail)]
  let last := [state 14 left (bit :: (List.replicate (k + 1) true ++ false :: tail)),
    state 15 (bit :: left) (List.replicate (k + 1) true ++ false :: tail)]
  have hfirst : first.IsChain (fun a b => Turing.TM0.step rawNatMachine a = some b) := by
    simp [first, List.isChain_cons_cons, Turing.TM0.step, rawNatMachine, state,
      Turing.Tape.mk₂, List.replicate_succ]
  have hmiddle : middle.IsChain (fun a b => Turing.TM0.step rawNatMachine a = some b) := by
    cases bit <;> simp [middle, List.isChain_cons_cons, payloadMode, markerMode, leftStartMode,
      Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂]
  have hlast : last.IsChain (fun a b => Turing.TM0.step rawNatMachine a = some b) := by
    simp [last, List.isChain_cons_cons, Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂]
  have hleftLast : Turing.TM0.step rawNatMachine
      (state (leftMode bit) left (false :: (List.replicate k true ++ true :: false :: tail))) =
        some (state 14 left (bit :: (List.replicate (k + 1) true ++ false :: tail))) := by
    cases bit <;> simp [leftMode, Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂, PSTRTMHeader003.replicate_push]
  have hleft := append_link (scanLeft bit k left (true :: false :: tail)) last _ _
    (scanLeft_chain _ _ _ _) hlast (scanLeft_last _ _ _ _) (by rfl) hleftLast
  have hleftHead : (scanLeft bit k left (true :: false :: tail) ++ last).head? =
      some (scanLeftInitial bit k left (true :: false :: tail)) := by
    simp [List.head?_append, scanLeft_head]
  have hboundary : Turing.TM0.step rawNatMachine
      (state (leftStartMode bit) (List.replicate k true ++ false :: left) (true :: false :: tail)) =
        some (scanLeftInitial bit k left (true :: false :: tail)) := by
    cases k <;> cases bit <;> simp [scanLeftInitial, leftStartMode, leftMode, Turing.TM0.step,
      rawNatMachine, state, Turing.Tape.mk₂, List.replicate_succ]
  have hmiddleRest := append_link middle (scanLeft bit k left (true :: false :: tail) ++ last) _ _
    hmiddle hleft (by rfl) hleftHead hboundary
  have hmiddleHead : (middle ++ scanLeft bit k left (true :: false :: tail) ++ last).head? =
      some (state 3 (false :: (List.replicate k true ++ false :: left)) (bit :: tail)) := by
    simp [middle]
  have hscanBoundary : Turing.TM0.step rawNatMachine
      (state 2 (List.replicate k true ++ false :: left) (false :: bit :: tail)) =
        some (state 3 (false :: (List.replicate k true ++ false :: left)) (bit :: tail)) := by
    simp [Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂]
  have hright := append_link (scanRight k (false :: left) (bit :: tail))
    (middle ++ scanLeft bit k left (true :: false :: tail) ++ last) _ _
    (scanRight_chain _ _ _) hmiddleRest (scanRight_last _ _ _) hmiddleHead hscanBoundary
  have hrightHead : (scanRight k (false :: left) (bit :: tail) ++ middle ++
      scanLeft bit k left (true :: false :: tail) ++ last).head? =
        some (state 2 (false :: left) (List.replicate k true ++ false :: bit :: tail)) := by
    simp [List.head?_append, scanRight_head]
  change (first ++ scanRight k (false :: left) (bit :: tail) ++ middle ++
    scanLeft bit k left (true :: false :: tail) ++ last).IsChain _
  have hfinal := append_link first
    (scanRight k (false :: left) (bit :: tail) ++ (middle ++ (scanLeft bit k left (true :: false :: tail) ++ last))) _ _
    hfirst (by simpa only [List.append_assoc] using hright) (by rfl)
    (by simpa only [List.append_assoc] using hrightHead)
    (by simp [Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂])
  simpa only [List.append_assoc] using hfinal


def contextRewindInitial (context : List Bool) : List Bool → List Bool → MachineState 16
  | [], right => state 12 context (false :: right)
  | bit :: previous, right => state 12 (bit :: contextLeft context previous) (true :: right)

def contextRewind (context : List Bool) : List Bool → List Bool → List (MachineState 16)
  | [], right => [state 12 context (false :: right), state 16 (false :: context) right]
  | bit :: previous, right =>
    state 12 (bit :: contextLeft context previous) (true :: right) ::
    state 13 (contextLeft context previous) (bit :: true :: right) ::
      contextRewind context previous (bit :: true :: right)

theorem contextRewind_head (context previous right : List Bool) :
    (contextRewind context previous right).head? = some (contextRewindInitial context previous right) := by
  cases previous <;> rfl

theorem contextRewind_length (context previous right : List Bool) :
    (contextRewind context previous right).length = 2 * previous.length + 2 := by
  induction previous generalizing right with
  | nil => rfl
  | cons bit previous ih =>
    simp only [contextRewind, List.length_cons, ih]
    omega

theorem contextRewind_last (context previous right : List Bool) :
    (contextRewind context previous right).getLast? = some
      (state 16 (false :: context) (PSTRTMIncrement009.blocks previous.reverse ++ right)) := by
  induction previous generalizing right with
  | nil => rfl
  | cons bit previous ih =>
    have hne : contextRewind context previous (bit :: true :: right) ≠ [] := by
      have hh := contextRewind_head context previous (bit :: true :: right)
      intro h
      simp [h] at hh
    simp only [contextRewind, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne, ih]
    simp [PSTRTMIncrement009.blocks, List.reverse_cons, List.flatMap_append, List.append_assoc]

theorem contextRewind_chain (context previous right : List Bool) :
    (contextRewind context previous right).IsChain (fun a b => Turing.TM0.step rawNatMachine a = some b) := by
  induction previous generalizing right with
  | nil => simp [contextRewind, List.isChain_cons_cons, Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂]
  | cons bit previous ih =>
    rw [contextRewind]
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro next hn
      rw [contextRewind_head] at hn
      have he := Option.mem_some_iff.mp hn
      subst next
      cases previous <;> simp [contextRewindInitial, contextLeft, leftBlocks,
        Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂]
    · exact ih _

def contextDone (context previous suffix : List Bool) : List (MachineState 16) :=
  state 0 (contextLeft context previous) (false :: suffix) ::
    contextRewind context previous (false :: suffix)

theorem contextDone_chain (context previous suffix : List Bool) :
    (contextDone context previous suffix).IsChain (fun a b => Turing.TM0.step rawNatMachine a = some b) := by
  apply List.isChain_cons.mpr
  constructor
  · intro next hn
    rw [contextRewind_head] at hn
    have he := Option.mem_some_iff.mp hn
    subst next
    cases previous <;> simp [contextRewindInitial, contextLeft, leftBlocks,
      Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂]
  · exact contextRewind_chain _ _ _

theorem contextDone_last (context previous suffix : List Bool) :
    (contextDone context previous suffix).getLast? = some
      (state 16 (false :: context) (PSTRTMIncrement009.blocks previous.reverse ++ false :: suffix)) := by
  have hne : contextRewind context previous (false :: suffix) ≠ [] := by
    have hh := contextRewind_head context previous (false :: suffix)
    intro h
    simp [h] at hh
  rw [contextDone, List.getLast?_cons_of_ne_nil hne, contextRewind_last]

def contextTrace (context previous : List Bool) : List Bool → List Bool → List (MachineState 16)
  | [], suffix => contextDone context previous suffix
  | bit :: later, suffix => unitTrace context bit previous later suffix ++
      contextTrace context (bit :: previous) later suffix

theorem context_head (context previous digits suffix : List Bool) :
    (contextTrace context previous digits suffix).head? = some
      (state 0 (contextLeft context previous)
        (List.replicate digits.length true ++ false :: (digits ++ suffix))) := by
  cases digits with
  | nil => rfl
  | cons bit later => simp [contextTrace, List.head?_append, unit_head]

theorem context_length (context previous digits suffix : List Bool) :
    (contextTrace context previous digits suffix).length =
      digits.length^2 + 11 * digits.length + 2 * previous.length + 3 := by
  induction digits generalizing previous with
  | nil =>
    have h := contextRewind_length context previous (false :: suffix)
    simp only [contextTrace, contextDone, List.length_cons, List.length_nil]
    omega
  | cons bit later ih =>
    simp only [contextTrace, List.length_append, unit_length, ih, List.length_cons]
    ring

theorem context_last (context previous digits suffix : List Bool) :
    (contextTrace context previous digits suffix).getLast? = some
      (state 16 (false :: context)
        (PSTRTMIncrement009.blocks (previous.reverse ++ digits) ++ false :: suffix)) := by
  induction digits generalizing previous with
  | nil => simpa [contextTrace] using contextDone_last context previous suffix
  | cons bit later ih =>
    simp [contextTrace, List.getLast?_append, ih, List.reverse_cons, List.append_assoc]

theorem context_chain (context previous digits suffix : List Bool) :
    (contextTrace context previous digits suffix).IsChain (fun a b => Turing.TM0.step rawNatMachine a = some b) := by
  induction digits generalizing previous with
  | nil => exact contextDone_chain context previous suffix
  | cons bit later ih =>
    rw [contextTrace]
    apply append_link _ _ _ _ (unit_chain context bit previous later suffix) (ih (bit :: previous))
      (unit_last context bit previous later suffix) (context_head context (bit :: previous) later suffix)
    simp [Turing.TM0.step, rawNatMachine, state, Turing.Tape.mk₂, contextLeft, leftBlocks,
      List.replicate_succ]

/-- The old17-label raw machine really runs while retaining arbitrary
earlier operands beyond ONE actual false guard. No context oracle is read. -/
theorem context_runsFrom (context digits suffix : List Bool) :
    PSTRTMSeq005.RunsFrom rawNatMachine
      (state 0 (false :: context) (List.replicate digits.length true ++ false :: (digits ++ suffix)))
      (contextTrace context [] digits suffix)
      (state 16 (false :: context) (PSTRTMIncrement009.blocks digits ++ false :: suffix)) := by
  refine ⟨?_, context_chain context [] digits suffix, ?_, rawNat_halt _ _⟩
  · simpa [contextLeft, leftBlocks] using context_head context [] digits suffix
  · simpa using context_last context [] digits suffix

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMContextRaw028
