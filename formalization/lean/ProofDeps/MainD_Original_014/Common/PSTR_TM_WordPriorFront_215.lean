module
public import Common.PSTR_TM_WordPreparationFront_214
public import Structure.PA17_TM_RatArithmetic_Parse_002d

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMWordPriorFront215
open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Statistics
open PSTRTMWordFrontCode213 PSTRTMWordPreparationFront214

/-! Actual original word front -> actual original prior Rat stream call.
The borrowed46-label parser supports ALL signs/zero/arbitrary suffix and
really moves the sign and parses NUM/DEN. In particular the denominator's
field-end FALSE followed by the fee's TRUE tag is01, never assumed OWN00. -/

def afterPrior (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : List Bool :=
  ((wordData E target word).drop 2).flatMap encodeDatum ++ [true]

theorem word_prior_tail (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    wordTail E target word = encodeDatum (.rational E.priorOne) ++ afterPrior E target word := by
  have hh : (wordData E target word).tail =
      .rational E.priorOne :: (wordData E target word).drop 2 := rfl
  unfold wordTail
  rw [hh,List.flatMap_cons]
  exact List.append_assoc _ _ _

def priorBase (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : List Bool :=
  fieldLeft [] (wordData E target word).length E.alphabetSize

/-- One fixed84-label code, before ALL original E/target/word. Runtime
count, alphabet and rational numerator/denominator stay on the Bool tape. -/
def priorMachine : Machine 83 :=
  PSTRTMSeq005.seqMachine frontMachine PA17TMRatArithmeticParse002.ratMachine

def priorTrace (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : List (MachineState 83) :=
  (frontTrace E target word).map (PSTRTMSeq005.leftCfg (b := 45)) ++
  (PA17TMRatArithmeticParse002.ratTrace (priorBase E target word)
    (PA17TMRatArithmeticParse002.sign E.priorOne)
    (PA17TMRatArithmeticParse002.numeratorDigits E.priorOne)
    (PA17TMRatArithmeticParse002.denominatorDigits E.priorOne)
    (afterPrior E target word)).map (PSTRTMSeq005.rightCfg (a := 37))

def priorFinal (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : MachineState 83 :=
  PSTRTMSeq005.rightCfg (a := 37)
    (PA17TMRatArithmeticParse002.ratFinal (priorBase E target word)
      (PA17TMRatArithmeticParse002.sign E.priorOne)
      (PA17TMRatArithmeticParse002.numeratorDigits E.priorOne)
      (PA17TMRatArithmeticParse002.denominatorDigits E.priorOne) (afterPrior E target word))

theorem prior_runs (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    Runs priorMachine (wordInput E target word) (priorTrace E target word) (priorFinal E target word) := by
  apply PSTRTMSeq005.seq_runs frontMachine PA17TMRatArithmeticParse002.ratMachine
    (wordInput E target word) (frontFinal E target word)
    (PA17TMRatArithmeticParse002.ratFinal (priorBase E target word)
      (PA17TMRatArithmeticParse002.sign E.priorOne)
      (PA17TMRatArithmeticParse002.numeratorDigits E.priorOne)
      (PA17TMRatArithmeticParse002.denominatorDigits E.priorOne) (afterPrior E target word))
    (frontTrace E target word)
    (PA17TMRatArithmeticParse002.ratTrace (priorBase E target word)
      (PA17TMRatArithmeticParse002.sign E.priorOne)
      (PA17TMRatArithmeticParse002.numeratorDigits E.priorOne)
      (PA17TMRatArithmeticParse002.denominatorDigits E.priorOne) (afterPrior E target word))
    (word_front_runs E target word)
  rw [word_front_final_tape,word_prior_tail]
  exact PA17TMRatArithmeticParse002.encodeDatum_rat_runsFrom (priorBase E target word)
    (afterPrior E target word) E.priorOne

theorem prior_final_tape (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    (priorFinal E target word).Tape = Turing.Tape.mk₂
      (PA17TMRatArithmeticParse002.bothLeft
        (false::PA17TMRatArithmeticParse002.sign E.priorOne::priorBase E target word)
        (PA17TMRatArithmeticParse002.numeratorDigits E.priorOne)
        (PA17TMRatArithmeticParse002.denominatorDigits E.priorOne))
      (afterPrior E target word) := rfl

private theorem prior_width_le (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    natBits E.priorOne.num.natAbs + natBits E.priorOne.den ≤ (wordInput E target word).length := by
  rw [word_input,word_prior_tail]
  simp only [List.length_append,List.length_cons,PSTRTMLength004.encodeNat_length,
    PSTRTMLength004.encodeDatum_rational_length]
  omega

private theorem prior_arithmetic (first second inputLength : Nat)
    (hwidth : first + second ≤ inputLength) :
    first^2 + second^2 + 9*(first + second) + 11 ≤ 16*(inputLength + 1)^2 := by
  have hsum : first^2 + second^2 ≤ (first + second)^2 := by
    nlinarith [Nat.zero_le (first*second)]
  have hp := Nat.pow_le_pow_left hwidth 2
  nlinarith [Nat.zero_le (inputLength^2)]

theorem prior_time_le (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    (priorTrace E target word).length ≤ 32*((wordInput E target word).length + 1)^2 := by
  have hfront := word_front_time_le E target word
  have hrat : (PA17TMRatArithmeticParse002.ratTrace (priorBase E target word)
      (PA17TMRatArithmeticParse002.sign E.priorOne)
      (PA17TMRatArithmeticParse002.numeratorDigits E.priorOne)
      (PA17TMRatArithmeticParse002.denominatorDigits E.priorOne)
      (afterPrior E target word)).length ≤ 16*((wordInput E target word).length + 1)^2 := by
    rw [PA17TMRatArithmeticParse002.ratTrace_length]
    simpa only [PA17TMRatArithmeticParse002.numeratorDigits,PA17TMRatArithmeticParse002.denominatorDigits,
      PSTRTMNatValue017.rawPayload,List.length_ofFn] using
      prior_arithmetic _ _ _ (prior_width_le E target word)
  simp only [priorTrace,List.length_append,List.length_map]
  omega

private theorem space_arithmetic (inputLength clock : Nat)
    (hclock : clock ≤ 32*(inputLength + 1)^2) :
    inputLength + 2*clock + 1 ≤ 128*(inputLength + 1)^2 := by
  nlinarith [Nat.zero_le (inputLength^2)]

/-- Original visitedSpace on EVERY prefix of the SAME actual84-label run.
Input width bounds come only from the actual serialized original prior. -/
theorem prior_prefix_space_le (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) (clock : Nat) :
    visitedSpace priorMachine (wordInput E target word).length ((priorTrace E target word).take clock) ≤
      128*((wordInput E target word).length + 1)^2 := by
  have ht := prior_time_le E target word
  have hs := PSTRTMTrace002.visitedSpace_le priorMachine (wordInput E target word).length
    ((priorTrace E target word).take clock)
  have hl : ((priorTrace E target word).take clock).length ≤ (priorTrace E target word).length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  exact hs.trans (space_arithmetic _ _ (hl.trans ht))

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMWordPriorFront215
