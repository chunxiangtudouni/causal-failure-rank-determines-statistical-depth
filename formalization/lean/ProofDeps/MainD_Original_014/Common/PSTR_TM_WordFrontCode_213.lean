module
public import Common.PSTR_TM_ThresholdDenominatorRaw_202
public import Structure.PA17_TM_RatArithmetic_Parse_002c

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMWordFrontCode213
open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Statistics

/-- The ORIGINAL word datum list; no computed odds or bound is supplied. -/
def wordData (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : List Datum :=
  rawExperiment E ++ [.rational target] ++ rawWord E word

def wordTail (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : List Bool :=
  ((wordData E target word).tail.flatMap encodeDatum) ++ [true]

theorem wordData_head (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    wordData E target word = .natural E.alphabetSize :: (wordData E target word).tail := rfl

theorem word_input (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    wordInput E target word = encodeNat (wordData E target word).length ++
      false::(encodeNat E.alphabetSize ++ wordTail E target word) := by
  change encode (wordData E target word) = _
  have hf : (wordData E target word).flatMap encodeDatum =
      encodeDatum (.natural E.alphabetSize) ++ (wordData E target word).tail.flatMap encodeDatum := by
    conv_lhs => rw [wordData_head E target word]
    rfl
  unfold encode
  rw [hf]
  simp only [encodeDatum,wordTail,List.append_assoc,List.cons_append]

/-- Consume the actual original natural-Datum tag. No field is reset or
loaded from a host list. The right field can be arbitrarily wide. -/
def tagMachine : Machine 1 := fun q _ =>
  if q.val = 0 then some (1,.move .right) else none

def tagTrace (left right : List Bool) : List (MachineState 1) :=
  [⟨0,Turing.Tape.mk₂ left (false::right)⟩,⟨1,Turing.Tape.mk₂ (false::left) right⟩]

theorem tag_runsFrom (left right : List Bool) :
    PSTRTMSeq005.RunsFrom tagMachine ⟨0,Turing.Tape.mk₂ left (false::right)⟩
      (tagTrace left right) ⟨1,Turing.Tape.mk₂ (false::left) right⟩ := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [tagTrace,List.isChain_cons_cons,Turing.TM0.step,tagMachine,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,tagMachine]

def alphaMachine : Machine 19 :=
  PSTRTMSeq005.seqMachine tagMachine PA17TMRatArithmeticParse002.streamMachine

def alphaTrace (left : List Bool) (alphabet : Nat) (suffix : List Bool) : List (MachineState 19) :=
  (tagTrace left (encodeNat alphabet ++ suffix)).map (PSTRTMSeq005.leftCfg (b := 17)) ++
    (PA17TMRatArithmeticParse002.streamTrace (false::left) []
      (PSTRTMNatValue017.rawPayload alphabet) suffix).map (PSTRTMSeq005.rightCfg (a := 1))

def alphaFinal (left : List Bool) (alphabet : Nat) (suffix : List Bool) : MachineState 19 :=
  PSTRTMSeq005.rightCfg (a := 1)
    (PA17TMRatArithmeticParse002.streamFinal (false::left) (PSTRTMNatValue017.rawPayload alphabet) suffix)

theorem alpha_runsFrom (left : List Bool) (alphabet : Nat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom alphaMachine
      ⟨0,Turing.Tape.mk₂ left (false::(encodeNat alphabet ++ suffix))⟩
      (alphaTrace left alphabet suffix) (alphaFinal left alphabet suffix) := by
  apply PSTRTMSeq005.seq_runsFrom tagMachine PA17TMRatArithmeticParse002.streamMachine
    ⟨0,Turing.Tape.mk₂ left (false::(encodeNat alphabet ++ suffix))⟩
    ⟨1,Turing.Tape.mk₂ (false::left) (encodeNat alphabet ++ suffix)⟩
    (PA17TMRatArithmeticParse002.streamFinal (false::left) (PSTRTMNatValue017.rawPayload alphabet) suffix)
    (tagTrace left (encodeNat alphabet ++ suffix))
    (PA17TMRatArithmeticParse002.streamTrace (false::left) []
      (PSTRTMNatValue017.rawPayload alphabet) suffix) (tag_runsFrom _ _)
  simpa only [PA17TMRatArithmeticParse002.streamState] using
    PA17TMRatArithmeticParse002.encodeNat_stream_runsFrom (false::left) suffix alphabet

/-- Fixed38 labels, original outer count followed by original alphabet.
Both unbounded values are actual Bool fields; neither is a finite word or
an input-dependent control state. Full word evaluation is still open. -/
def frontMachine : Machine 37 :=
  PSTRTMSeq005.seqMachine PA17TMRatArithmeticParse002.streamMachine alphaMachine

def countLeft (count : Nat) : List Bool :=
  false::PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload count).reverse

def frontTrace (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : List (MachineState 37) :=
  (PA17TMRatArithmeticParse002.streamTrace [] [] (PSTRTMNatValue017.rawPayload (wordData E target word).length)
    (false::(encodeNat E.alphabetSize ++ wordTail E target word))).map (PSTRTMSeq005.leftCfg (b := 19)) ++
  (alphaTrace (countLeft (wordData E target word).length) E.alphabetSize (wordTail E target word)).map
    (PSTRTMSeq005.rightCfg (a := 17))

def frontFinal (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : MachineState 37 :=
  PSTRTMSeq005.rightCfg (a := 17) (alphaFinal (countLeft (wordData E target word).length)
    E.alphabetSize (wordTail E target word))

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMWordFrontCode213
