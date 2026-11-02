module
public import Common.PSTR_TM_CompactSetup_050

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompactRun051
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMCompactCode046 PSTRTMCompactUnit048

def loopTrace (previous : List Bool) : List Bool → List (MachineState 54)
  | [] => PSTRTMCompactFinish049.finishTrace previous
  | a :: later => unitTrace a (PSTRTMRawNat010.leftBlocks previous) later ++ loopTrace (a :: previous) later

theorem loop_head (previous digits : List Bool) :
    (loopTrace previous digits).head? = some
      (state 6 (PSTRTMRawNat010.leftBlocks previous) (PSTRTMBinaryAdd024.resultColumns digits ++ [true,false])) := by
  cases digits with
  | nil => simpa [loopTrace, PSTRTMBinaryAdd024.resultColumns] using PSTRTMCompactFinish049.finish_head previous
  | cons a later => simp only [loopTrace, List.head?_append, unit_head, Option.some_or]

theorem loop_last (previous digits : List Bool) :
    (loopTrace previous digits).getLast? = some
      (state 54 [false] (PSTRTMIncrement009.blocks (previous.reverse ++ digits) ++ [false,false])) := by
  induction digits generalizing previous with
  | nil => simpa [loopTrace] using PSTRTMCompactFinish049.finish_last previous
  | cons a later ih =>
    simp [loopTrace, List.getLast?_append, ih, List.reverse_cons, List.append_assoc]

theorem loop_length (previous digits : List Bool) :
    (loopTrace previous digits).length = 12 * digits.length^2 + 5 * digits.length + 2 * previous.length + 6 := by
  induction digits generalizing previous with
  | nil => simpa [loopTrace] using PSTRTMCompactFinish049.finish_length previous
  | cons a later ih =>
    simp only [loopTrace, List.length_append, unit_length, ih, List.length_cons]
    ring

theorem loop_chain (previous digits : List Bool) :
    (loopTrace previous digits).IsChain (fun before after => Turing.TM0.step compactMachine before = some after) := by
  induction digits generalizing previous with
  | nil => simpa only [loopTrace] using PSTRTMCompactFinish049.finish_chain previous
  | cons a later ih =>
    rw [loopTrace]
    apply (unit_chain a (PSTRTMRawNat010.leftBlocks previous) later).append (ih (a :: previous))
    intro before hb after ha
    simp only [unit_last, Option.mem_some_iff] at hb
    simp only [loop_head, Option.mem_some_iff] at ha
    subst before
    subst after
    simpa only [PSTRTMRawNat010.leftBlocks, List.flatMap_cons, List.cons_append, List.nil_append] using
      restore_advance a (PSTRTMRawNat010.leftBlocks previous) (PSTRTMBinaryAdd024.resultColumns later ++ [true,false])

def compactTrace (digits : List Bool) : List (MachineState 54) :=
  PSTRTMCompactSetup050.setupTrace (paddedDigits digits) ++ loopTrace [] digits

theorem compact_head (digits : List Bool) :
    (compactTrace digits).head? = some (state 0 [] (PSTRTMBinaryAdd024.resultColumns digits)) := by
  simp only [compactTrace, List.head?_append, PSTRTMCompactSetup050.setup_head, Option.some_or, blocks_paddedDigits]

theorem compact_last (digits : List Bool) :
    (compactTrace digits).getLast? = some (state 54 [false] (PSTRTMIncrement009.blocks digits ++ [false,false])) := by
  simp [compactTrace, List.getLast?_append, loop_last]

theorem compact_length (digits : List Bool) :
    (compactTrace digits).length = 12 * digits.length^2 + 13 * digits.length + 11 := by
  simp only [compactTrace, List.length_append, PSTRTMCompactSetup050.setup_length,
    paddedDigits_length, loop_length, List.length_nil]
  ring

theorem compact_chain (digits : List Bool) :
    (compactTrace digits).IsChain (fun before after => Turing.TM0.step compactMachine before = some after) := by
  apply (PSTRTMCompactSetup050.setup_chain (paddedDigits digits)).append (loop_chain [] digits)
  intro before hb after ha
  simp only [PSTRTMCompactSetup050.setup_last, Option.mem_some_iff] at hb
  simp only [loop_head, PSTRTMRawNat010.leftBlocks, List.flatMap_nil, Option.mem_some_iff] at ha
  subst before
  subst after
  simpa only [blocks_paddedDigits] using PSTRTMCompactSetup050.setup_advance (paddedDigits digits)

theorem compact_runs (digits : List Bool) :
    Runs compactMachine (PSTRTMBinaryAdd024.resultColumns digits) (compactTrace digits)
      (state 54 [false] (PSTRTMIncrement009.blocks digits ++ [false,false])) := by
  apply PSTRTMTrace002.runs_of_chain
  · simpa [Turing.TM0.init, state, Turing.Tape.mk₁] using compact_head digits
  · exact compact_chain digits
  · exact compact_last digits
  · exact compact_halt _ _

theorem compact_final_tape (digits : List Bool) :
    (state 54 [false] (PSTRTMIncrement009.blocks digits ++ [false,false])).Tape =
      Turing.Tape.mk₁ (PSTRTMIncrement009.blocks digits) := by
  simpa only [List.reverse_reverse] using PSTRTMCompactFinish049.finish_final_tape digits.reverse

theorem resultColumns_length (digits : List Bool) : (PSTRTMBinaryAdd024.resultColumns digits).length = 4 * digits.length := by
  rw [← blocks_paddedDigits, PSTRTMIncrement009.blocks_length, paddedDigits_length]
  omega

/-- Genuine isolated4-cell to2-cell codec, charging actual suffix copies,
marker allocation/relocation/clearing and final real output rewind. -/
theorem compact_computes (digits : List Bool) :
    computes compactMachine (PSTRTMBinaryAdd024.resultColumns digits) (PSTRTMIncrement009.blocks digits)
      (128 * (digits.length + 1)^2) (128 * (digits.length + 1)^2) := by
  refine ⟨compactTrace digits, state 54 [false] (PSTRTMIncrement009.blocks digits ++ [false,false]),
    compact_runs digits, ?_, ?_, ?_⟩
  · rw [compact_final_tape]
    simp [Turing.Tape.mk₁, Turing.Tape.mk₂]
  · rw [compact_length]
    nlinarith
  · have hs := PSTRTMTrace002.visitedSpace_le compactMachine (PSTRTMBinaryAdd024.resultColumns digits).length (compactTrace digits)
    rw [resultColumns_length, compact_length] at hs
    rw [resultColumns_length]
    nlinarith

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompactRun051
