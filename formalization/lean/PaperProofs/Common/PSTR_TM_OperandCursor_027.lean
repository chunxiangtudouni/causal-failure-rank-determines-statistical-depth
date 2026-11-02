module
public import PaperProofs.Common.PSTR_TM_FullRawPadding_015

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMOperandCursor027
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMFullRawPadding015 PSTRTMPaddedNat012 PSTRTMTrace002

/-- Actual transport cursor for the NEXT original raw operand after the
first operand's real00+10 protected separator. It retains the entire first
operand and all separator cells on the left of the real head. -/
def cursorMachine : Machine 4 := fun q symbol =>
  match q.val with
  | 0 => some (1, .move .right)
  | 1 => some (if symbol then 0 else 2, .move .right)
  | 2 => some (3, .move .right)
  | 3 => some (4, .move .right)
  | _ => none

def cursorState (q : Fin 5) (left right : List Bool) : MachineState 4 := ⟨q, Turing.Tape.mk₂ left right⟩

def cursorTrace (previous : List Bool) : List Bool → List Bool → List (MachineState 4)
  | [], suffix =>
    [cursorState 0 (PSTRTMRawNat010.leftBlocks previous) (false :: false :: true :: false :: suffix),
      cursorState 1 (false :: PSTRTMRawNat010.leftBlocks previous) (false :: true :: false :: suffix),
      cursorState 2 (false :: false :: PSTRTMRawNat010.leftBlocks previous) (true :: false :: suffix),
      cursorState 3 (true :: false :: false :: PSTRTMRawNat010.leftBlocks previous) (false :: suffix),
      cursorState 4 (false :: true :: false :: false :: PSTRTMRawNat010.leftBlocks previous) suffix]
  | bit :: later, suffix =>
    cursorState 0 (PSTRTMRawNat010.leftBlocks previous)
      (bit :: true :: (PSTRTMIncrement009.blocks later ++ false :: false :: true :: false :: suffix)) ::
    cursorState 1 (bit :: PSTRTMRawNat010.leftBlocks previous)
      (true :: (PSTRTMIncrement009.blocks later ++ false :: false :: true :: false :: suffix)) ::
      cursorTrace (bit :: previous) later suffix

theorem cursor_head (previous digits suffix : List Bool) :
    (cursorTrace previous digits suffix).head? = some
      (cursorState 0 (PSTRTMRawNat010.leftBlocks previous)
        (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: suffix)) := by
  cases digits <;> rfl

theorem cursor_length (previous digits suffix : List Bool) :
    (cursorTrace previous digits suffix).length = 2 * digits.length + 5 := by
  induction digits generalizing previous with
  | nil => rfl
  | cons bit later ih => simp only [cursorTrace, List.length_cons, ih]; omega

theorem cursor_last (previous digits suffix : List Bool) :
    (cursorTrace previous digits suffix).getLast? = some
      (cursorState 4 (false :: true :: false :: false ::
        PSTRTMRawNat010.leftBlocks (digits.reverse ++ previous)) suffix) := by
  induction digits generalizing previous with
  | nil => rfl
  | cons bit later ih =>
    have hne : cursorTrace (bit :: previous) later suffix ≠ [] := by
      have hh := cursor_head (bit :: previous) later suffix
      intro h
      simp [h] at hh
    simp only [cursorTrace, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem cursor_chain (previous digits suffix : List Bool) :
    (cursorTrace previous digits suffix).IsChain (fun a b => Turing.TM0.step cursorMachine a = some b) := by
  induction digits generalizing previous with
  | nil => simp [cursorTrace, List.isChain_cons_cons, Turing.TM0.step, cursorMachine, cursorState, Turing.Tape.mk₂]
  | cons bit later ih =>
    rw [cursorTrace]
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [Turing.TM0.step, cursorMachine, cursorState, Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro next hn
      rw [cursor_head] at hn
      have he := Option.mem_some_iff.mp hn
      subst next
      simp [Turing.TM0.step, cursorMachine, cursorState, Turing.Tape.mk₂, PSTRTMRawNat010.leftBlocks]
    · exact ih _

theorem cursor_runs (digits suffix : List Bool) :
    Runs cursorMachine (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: suffix)
      (cursorTrace [] digits suffix)
      (cursorState 4 (false :: true :: false :: false :: PSTRTMRawNat010.leftBlocks digits.reverse) suffix) := by
  apply runs_of_chain
  · simpa [Turing.TM0.init, cursorState, Turing.Tape.mk₁, PSTRTMRawNat010.leftBlocks] using cursor_head [] digits suffix
  · exact cursor_chain [] digits suffix
  · simpa using cursor_last [] digits suffix
  · simp [Turing.TM0.step, cursorMachine, cursorState]

def firstOperandMachine : Machine 111 := PSTRTMSeq005.seqMachine paddedNatMachine cursorMachine

def firstOperandTrace (digits suffix : List Bool) : List (MachineState 111) :=
  (paddedTrace [] digits suffix).map (PSTRTMSeq005.leftCfg (b := 4)) ++
    (cursorTrace [] digits suffix).map (PSTRTMSeq005.rightCfg (a := 106))

def firstOperandFinal (digits suffix : List Bool) : MachineState 111 :=
  PSTRTMSeq005.rightCfg (a := 106)
    (cursorState 4 (false :: true :: false :: false :: PSTRTMRawNat010.leftBlocks digits.reverse) suffix)

theorem firstOperand_runs (digits suffix : List Bool) :
    Runs firstOperandMachine (List.replicate digits.length true ++ false :: (digits ++ suffix))
      (firstOperandTrace digits suffix) (firstOperandFinal digits suffix) := by
  apply PSTRTMSeq005.seq_runs paddedNatMachine cursorMachine
    (List.replicate digits.length true ++ false :: (digits ++ suffix))
    (PSTRTMPaddedNat012.state (post suffix.headI 44) [false]
      (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: suffix))
    (cursorState 4 (false :: true :: false :: false :: PSTRTMRawNat010.leftBlocks digits.reverse) suffix)
    (paddedTrace [] digits suffix) (cursorTrace [] digits suffix)
  · exact padded_runs digits suffix
  · have h := cursor_runs digits suffix
    refine ⟨?_, h.2.1, h.2.2.1, h.2.2.2.1⟩
    rw [padded_final_tape]
    exact h.1

/-- Precise entire tape at the second raw field. The first field and the
actual separator are retained, so contextual decoding can use the leading
false on the left as its real rewind guard. -/
theorem firstOperand_final_tape (digits suffix : List Bool) :
    (firstOperandFinal digits suffix).Tape =
      Turing.Tape.mk₂ (false :: true :: false :: false :: PSTRTMRawNat010.leftBlocks digits.reverse) suffix := rfl

theorem firstOperand_length (digits suffix : List Bool) :
    (firstOperandTrace digits suffix).length = digits.length^2 + 27 * digits.length + 32 := by
  simp only [firstOperandTrace, List.length_append, List.length_map, padded_length,
    cursor_length, List.length_nil]
  ring

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMOperandCursor027
