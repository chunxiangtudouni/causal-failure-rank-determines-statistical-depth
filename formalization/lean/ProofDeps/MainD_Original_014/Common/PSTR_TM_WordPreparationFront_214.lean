module
public import Common.PSTR_TM_WordFrontCode_213

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMWordPreparationFront214
open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Statistics
open PSTRTMWordFrontCode213

/-! ONE fixed38-label program reads the actual raw outer count, then the
first original natural Datum. Word uses alphabetSize; preparation uses
stageCount. The code never receives either value, a width, fuel or EOF flag.
The real cursor ends on the next original suffix cell, which is retained. -/

def headerLeft (left : List Bool) (count : Nat) : List Bool :=
  false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload count).reverse ++ left)

def fieldLeft (left : List Bool) (count first : Nat) : List Bool :=
  false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload first).reverse ++
    false::headerLeft left count)

def headerTrace (left : List Bool) (count first : Nat) (suffix : List Bool) : List (MachineState 37) :=
  (PA17TMRatArithmeticParse002.streamTrace left [] (PSTRTMNatValue017.rawPayload count)
    (false::(encodeNat first ++ suffix))).map (PSTRTMSeq005.leftCfg (b := 19)) ++
  (alphaTrace (headerLeft left count) first suffix).map (PSTRTMSeq005.rightCfg (a := 17))

def headerFinal (left : List Bool) (count first : Nat) (suffix : List Bool) : MachineState 37 :=
  PSTRTMSeq005.rightCfg (a := 17) (alphaFinal (headerLeft left count) first suffix)

theorem header_runsFrom (left : List Bool) (count first : Nat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom frontMachine
      ⟨0,Turing.Tape.mk₂ left (encodeNat count ++ false::(encodeNat first ++ suffix))⟩
      (headerTrace left count first suffix) (headerFinal left count first suffix) := by
  apply PSTRTMSeq005.seq_runsFrom PA17TMRatArithmeticParse002.streamMachine alphaMachine
    (PA17TMRatArithmeticParse002.streamState 0 left
      (encodeNat count ++ false::(encodeNat first ++ suffix)))
    (PA17TMRatArithmeticParse002.streamFinal left (PSTRTMNatValue017.rawPayload count)
      (false::(encodeNat first ++ suffix)))
    (alphaFinal (headerLeft left count) first suffix)
    (PA17TMRatArithmeticParse002.streamTrace left [] (PSTRTMNatValue017.rawPayload count)
      (false::(encodeNat first ++ suffix)))
    (alphaTrace (headerLeft left count) first suffix)
    (PA17TMRatArithmeticParse002.encodeNat_stream_runsFrom left _ count)
  exact alpha_runsFrom (headerLeft left count) first suffix

/-- ENTIRE tape, not only right0: every external archive cell and every
suffix cell remains at the real decoded-field boundary. -/
theorem header_final_tape (left : List Bool) (count first : Nat) (suffix : List Bool) :
    (headerFinal left count first suffix).Tape =
      Turing.Tape.mk₂ (fieldLeft left count first) suffix := rfl

theorem header_trace_length (left : List Bool) (count first : Nat) (suffix : List Bool) :
    (headerTrace left count first suffix).length =
      (natBits count)^2 + (natBits first)^2 + 9*(natBits count + natBits first) + 6 := by
  simp only [headerTrace,alphaTrace,List.length_append,List.length_map,
    PA17TMRatArithmeticParse002.streamTrace_length,tagTrace,List.length_cons,List.length_nil,
    PSTRTMNatValue017.rawPayload,List.length_ofFn]
  ring

private theorem clock_arithmetic (countWidth firstWidth inputLength : Nat)
    (hwidth : countWidth + firstWidth ≤ inputLength) :
    countWidth^2 + firstWidth^2 + 9*(countWidth + firstWidth) + 6 ≤
      16*(inputLength + 1)^2 := by
  have hsum : countWidth^2 + firstWidth^2 ≤ (countWidth + firstWidth)^2 := by
    nlinarith [Nat.zero_le (countWidth*firstWidth)]
  have hp := Nat.pow_le_pow_left hwidth 2
  nlinarith [Nat.zero_le (inputLength^2)]

private theorem space_arithmetic (inputLength clock : Nat)
    (hclock : clock ≤ 16*(inputLength + 1)^2) :
    inputLength + 2*clock + 1 ≤ 64*(inputLength + 1)^2 := by
  nlinarith [Nat.zero_le (inputLength^2)]

/-- Parameter `inputLength` is a charged accounting length. The public
original-input consumers below DERIVE this width inequality from actual
encodeNat cells; it is not a new machine input or qualification. -/
theorem header_time_le (left : List Bool) (count first : Nat) (suffix : List Bool)
    (inputLength : Nat) (hwidth : natBits count + natBits first ≤ inputLength) :
    (headerTrace left count first suffix).length ≤ 16*(inputLength + 1)^2 := by
  rw [header_trace_length]
  exact clock_arithmetic _ _ _ hwidth

theorem header_prefix_space_le (left : List Bool) (count first : Nat) (suffix : List Bool)
    (inputLength clock : Nat) (hwidth : natBits count + natBits first ≤ inputLength) :
    visitedSpace frontMachine inputLength ((headerTrace left count first suffix).take clock) ≤
      64*(inputLength + 1)^2 := by
  have ht := header_time_le left count first suffix inputLength hwidth
  have hs := PSTRTMTrace002.visitedSpace_le frontMachine inputLength
    ((headerTrace left count first suffix).take clock)
  have hl : ((headerTrace left count first suffix).take clock).length ≤
      (headerTrace left count first suffix).length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  exact hs.trans (space_arithmetic _ _ (hl.trans ht))

/-! Original WORD input consumer. No target positivity is required merely
to parse the actual first original natural; full wordOutput is still open. -/

theorem word_front_runs (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    Runs frontMachine (wordInput E target word) (frontTrace E target word) (frontFinal E target word) := by
  have hh := header_runsFrom [] (wordData E target word).length E.alphabetSize (wordTail E target word)
  have h : PSTRTMSeq005.RunsFrom frontMachine (Turing.TM0.init (wordInput E target word))
      (frontTrace E target word) (frontFinal E target word) := by
    simpa only [Turing.TM0.init,Fin.default_eq_zero,Turing.Tape.mk₁,word_input,headerTrace,headerFinal,headerLeft,
      frontTrace,frontFinal,countLeft,List.append_nil] using hh
  exact PSTRTMTrace002.runs_of_chain _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2

theorem word_front_final_tape (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    (frontFinal E target word).Tape =
      Turing.Tape.mk₂ (fieldLeft [] (wordData E target word).length E.alphabetSize)
        (wordTail E target word) := by
  simpa only [frontFinal,countLeft,headerFinal,headerLeft,List.append_nil] using
    header_final_tape [] (wordData E target word).length E.alphabetSize (wordTail E target word)

private theorem word_width_le (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    natBits (wordData E target word).length + natBits E.alphabetSize ≤ (wordInput E target word).length := by
  rw [word_input]
  simp only [List.length_append,List.length_cons,PSTRTMLength004.encodeNat_length]
  omega

theorem word_front_time_le (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    (frontTrace E target word).length ≤ 16*((wordInput E target word).length + 1)^2 := by
  have h := header_time_le [] (wordData E target word).length E.alphabetSize (wordTail E target word)
    (wordInput E target word).length (word_width_le E target word)
  simpa only [headerTrace,headerLeft,frontTrace,countLeft,List.append_nil] using h

theorem word_front_prefix_space_le (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) (clock : Nat) :
    visitedSpace frontMachine (wordInput E target word).length ((frontTrace E target word).take clock) ≤
      64*((wordInput E target word).length + 1)^2 := by
  have h := header_prefix_space_le [] (wordData E target word).length E.alphabetSize (wordTail E target word)
    (wordInput E target word).length clock (word_width_le E target word)
  simpa only [headerTrace,headerLeft,frontTrace,countLeft,List.append_nil] using h

/-! Original PREPARATION input consumer, SAME38 labels. It actually reads
the original outer count and stageCount, stopping on the original toolCount
Datum. Nothing is assumed about any stage/alphabet fitting a finite Word. -/

variable {I : Instance}

def preparationData (input : StatisticalInput I) (C : Contract I) (budget : Rat) : List Datum :=
  rawInstance input ++ rawContract C ++ [.rational budget]

def preparationTail (input : StatisticalInput I) (C : Contract I) (budget : Rat) : List Bool :=
  (preparationData input C budget).tail.flatMap encodeDatum ++ [true]

theorem preparationData_head (input : StatisticalInput I) (C : Contract I) (budget : Rat) :
    preparationData input C budget = .natural I.stageCount :: (preparationData input C budget).tail := rfl

theorem preparation_input (input : StatisticalInput I) (C : Contract I) (budget : Rat) :
    preparationInput input C budget = encodeNat (preparationData input C budget).length ++
      false::(encodeNat I.stageCount ++ preparationTail input C budget) := by
  change encode (preparationData input C budget) = _
  have hf : (preparationData input C budget).flatMap encodeDatum =
      encodeDatum (.natural I.stageCount) ++ (preparationData input C budget).tail.flatMap encodeDatum := by
    conv_lhs => rw [preparationData_head input C budget]
    rfl
  unfold encode
  rw [hf]
  simp only [encodeDatum,preparationTail,List.append_assoc,List.cons_append]

def preparationTrace (input : StatisticalInput I) (C : Contract I) (budget : Rat) : List (MachineState 37) :=
  headerTrace [] (preparationData input C budget).length I.stageCount (preparationTail input C budget)

def preparationFinal (input : StatisticalInput I) (C : Contract I) (budget : Rat) : MachineState 37 :=
  headerFinal [] (preparationData input C budget).length I.stageCount (preparationTail input C budget)

theorem preparation_front_runs (input : StatisticalInput I) (C : Contract I) (budget : Rat) :
    Runs frontMachine (preparationInput input C budget)
      (preparationTrace input C budget) (preparationFinal input C budget) := by
  have hh := header_runsFrom [] (preparationData input C budget).length I.stageCount (preparationTail input C budget)
  have h : PSTRTMSeq005.RunsFrom frontMachine (Turing.TM0.init (preparationInput input C budget))
      (preparationTrace input C budget) (preparationFinal input C budget) := by
    simpa only [Turing.TM0.init,Fin.default_eq_zero,Turing.Tape.mk₁,preparation_input,preparationTrace,preparationFinal] using hh
  exact PSTRTMTrace002.runs_of_chain _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2

theorem preparation_front_final_tape (input : StatisticalInput I) (C : Contract I) (budget : Rat) :
    (preparationFinal input C budget).Tape =
      Turing.Tape.mk₂ (fieldLeft [] (preparationData input C budget).length I.stageCount)
        (preparationTail input C budget) := rfl

private theorem preparation_width_le (input : StatisticalInput I) (C : Contract I) (budget : Rat) :
    natBits (preparationData input C budget).length + natBits I.stageCount ≤
      (preparationInput input C budget).length := by
  rw [preparation_input]
  simp only [List.length_append,List.length_cons,PSTRTMLength004.encodeNat_length]
  omega

theorem preparation_front_time_le (input : StatisticalInput I) (C : Contract I) (budget : Rat) :
    (preparationTrace input C budget).length ≤ 16*((preparationInput input C budget).length + 1)^2 :=
  header_time_le [] _ _ _ _ (preparation_width_le input C budget)

theorem preparation_front_prefix_space_le (input : StatisticalInput I) (C : Contract I) (budget : Rat) (clock : Nat) :
    visitedSpace frontMachine (preparationInput input C budget).length
      ((preparationTrace input C budget).take clock) ≤
      64*((preparationInput input C budget).length + 1)^2 :=
  header_prefix_space_le [] _ _ _ _ clock (preparation_width_le input C budget)

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMWordPreparationFront214
