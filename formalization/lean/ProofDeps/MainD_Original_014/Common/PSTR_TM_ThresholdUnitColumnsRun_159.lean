module
public import Common.PSTR_TM_ThresholdUnitColumnsEOF_158
public import Common.PSTR_TM_PackLoop_043

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdUnitColumnsRun159
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdUnitColumnsCode156 PSTRTMThresholdUnitColumnsStep157
open PSTRTMThresholdUnitColumnsEOF158 PSTRTMOverlap132

def outputDigits : Bool → List Bool → List Bool
  | _,[] => []
  | first,bit::later => first::bit::outputDigits false later

def frontier (archive previous : List Bool) (first : Bool) (digits : List Bool) : MachineState 213 :=
  state (startLabel first) (leftOf archive previous) (PSTRTMIncrement009.blocks digits)

def final (archive previous : List Bool) (first : Bool) (digits : List Bool) : MachineState 213 :=
  state 213 (false::archive) (PSTRTMIncrement009.blocks (previous.reverse++outputDigits first digits))

def loopTrace (archive previous : List Bool) (first : Bool) : List Bool → List (MachineState 213)
  | [] => eofTrace archive previous first
  | bit::later => glue (unitTrace first bit (leftOf archive previous) later)
      (loopTrace archive (bit::first::previous) false later)

private theorem unit_boundary (archive previous : List Bool) (first bit : Bool) (later : List Bool) :
    (unitTrace first bit (leftOf archive previous) later).getLast?=
      some (frontier archive (bit::first::previous) false later) := by
  simpa only [frontier,startLabel,Bool.false_eq_true,↓reduceIte,leftOf,PSTRTMRawNat010.leftBlocks,
    List.flatMap_cons,List.cons_append,List.nil_append] using
    unit_last first bit (leftOf archive previous) later

theorem loop_head (archive previous : List Bool) (first : Bool) (digits : List Bool) :
    (loopTrace archive previous first digits).head?=some (frontier archive previous first digits) := by
  induction digits generalizing previous first with
  | nil => exact eof_head _ _ _
  | cons bit later ih =>
    have h := glue_head _ _ _ _ (unit_head first bit (leftOf archive previous) later)
      (unit_boundary archive previous first bit later) (ih (bit::first::previous) false)
    simpa only [loopTrace,frontier,PSTRTMIncrement009.blocks,List.flatMap_cons,
      List.cons_append,List.nil_append] using h

theorem loop_last (archive previous : List Bool) (first : Bool) (digits : List Bool) :
    (loopTrace archive previous first digits).getLast?=some (final archive previous first digits) := by
  induction digits generalizing previous first with
  | nil => simpa only [loopTrace,final,outputDigits,List.append_nil] using eof_last archive previous first
  | cons bit later ih =>
    have h := glue_last (unitTrace first bit (leftOf archive previous) later)
      (loopTrace archive (bit::first::previous) false later) _ (ih _ _)
    simpa only [loopTrace,final,outputDigits,List.reverse_cons,List.append_assoc,List.singleton_append,
      List.cons_append,List.nil_append] using h

theorem loop_chain (archive previous : List Bool) (first : Bool) (digits : List Bool) :
    (loopTrace archive previous first digits).IsChain
      (fun before after => Turing.TM0.step unitMachine before=some after) := by
  induction digits generalizing previous first with
  | nil => exact eof_chain _ _ _
  | cons bit later ih =>
    exact glue_chain unitMachine _ _ _ (unit_chain _ _ _ _) (ih _ _)
      (unit_boundary archive previous first bit later) (loop_head _ _ _ _)

theorem unit_columns_runsFrom (archive digits : List Bool) :
    PSTRTMSeq005.RunsFrom unitMachine (state 0 (false::archive) (PSTRTMIncrement009.blocks digits))
      (loopTrace archive [] true digits) (final archive [] true digits) := by
  refine ⟨?_,loop_chain _ _ _ _,loop_last _ _ _ _,unit_halt _ _⟩
  simpa only [frontier,startLabel,↓reduceIte,leftOf,PSTRTMRawNat010.leftBlocks,
    List.flatMap_nil,List.nil_append] using loop_head archive [] true digits

def outputPairs : Bool → List Bool → List (Bool × Bool)
  | _,[] => []
  | first,bit::later => (first,bit)::outputPairs false later

theorem output_digits_pairs (first : Bool) (digits : List Bool) :
    outputDigits first digits=PSTRTMPackLoop043.pairedDigits (outputPairs first digits) := by
  induction digits generalizing first with
  | nil => rfl
  | cons bit later ih => simpa only [outputDigits,outputPairs,PSTRTMPackLoop043.pairedDigits,
      List.flatMap_cons,List.cons_append,List.nil_append] using congrArg (fun tail => first::bit::tail) (ih false)

theorem zero_pairs (digits : List Bool) :
    outputPairs false digits=PSTRTMPackCode036.digitPairs [] digits := by
  induction digits with
  | nil => simp only [outputPairs,PSTRTMPackCode036.digitPairs]
  | cons bit later ih => simp only [outputPairs,PSTRTMPackCode036.digitPairs,ih]

theorem one_pairs (digits : List Bool) (hn : digits≠[]) :
    outputPairs true digits=PSTRTMPackCode036.digitPairs [true] digits := by
  cases digits with
  | nil => exact False.elim (hn rfl)
  | cons bit later => simp only [outputPairs,PSTRTMPackCode036.digitPairs,zero_pairs]

/-- Whole final tape at the actual first A digit. All arbitrary archive
cells and the real false guard survive. A is exactly ONE zero-extended
to the nonempty B word, and every B digit/flag is physically retained. -/
theorem unit_columns_final_tape (archive digits : List Bool) (hn : digits≠[]) :
    (final archive [] true digits).Tape=Turing.Tape.mk₂ (false::archive)
      (PSTRTMBinaryAdd024.operandColumns (PSTRTMPackCode036.digitPairs [true] digits)) := by
  simp only [final,state,List.reverse_nil,List.nil_append,output_digits_pairs,one_pairs digits hn,
    PSTRTMPackLoop043.pairedDigits_blocks]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdUnitColumnsRun159
