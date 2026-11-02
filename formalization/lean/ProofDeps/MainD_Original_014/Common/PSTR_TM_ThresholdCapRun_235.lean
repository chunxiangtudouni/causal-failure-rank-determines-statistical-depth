module
public import Common.PSTR_TM_ThresholdCapCode_234

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCapRun235
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCapCode234

/-! Canonical natural Datum -> TRUE/FALSE HALT control, with its whole
literal tape preserved except for at most FOUR real right head moves.
Arbitrary left archive and arbitrary right suffix are supported. Zero
has its original one-bit FALSE payload, never an empty tape surrogate. -/

theorem datum_classify_contract (n : Nat) (left suffix : List Bool) :
    ∃ trace last distance,
      PSTRTMSeq005.RunsFrom classifyMachine ⟨0,Turing.Tape.mk₂ left (encodeDatum (.natural n)++suffix)⟩ trace last ∧
      last.q = (if n ≤ 2 then 5 else 6) ∧ trace.length ≤ 6 ∧ distance ≤ 4 ∧
      last.Tape = rightSteps distance (Turing.Tape.mk₂ left (encodeDatum (.natural n)++suffix)) := by
  rcases Nat.lt_or_ge n 4 with hsmall | hlarge
  · interval_cases n
    · refine ⟨smallTrace left (false::suffix),smallFinal left (false::suffix),2,?_,rfl,by simp [smallTrace],by decide,?_⟩
      · exact small_runsFrom _ _
      · exact small_final_tape _ _
    · refine ⟨smallTrace left (true::suffix),smallFinal left (true::suffix),2,?_,rfl,by simp [smallTrace],by decide,?_⟩
      · exact small_runsFrom _ _
      · exact small_final_tape _ _
    · refine ⟨pairTrace left false (true::suffix),pairFinal left false (true::suffix),4,?_,rfl,by simp [pairTrace],by decide,?_⟩
      · exact pair_runsFrom _ _ _
      · exact pair_final_tape _ _ _
    · refine ⟨pairTrace left true (true::suffix),pairFinal left true (true::suffix),4,?_,rfl,by simp [pairTrace],by decide,?_⟩
      · exact pair_runsFrom _ _ _
      · exact pair_final_tape _ _ _
  · have hfour : natBits 4 = 3 := by decide
    have hwidth := PSTRTMArithmetic008.natBits_mono hlarge
    rw [hfour] at hwidth
    let tail := List.replicate (natBits n-3) true++false::(PSTRTMNatValue017.rawPayload n++suffix)
    have hheader : encodeDatum (.natural n)++suffix = false::true::true::true::tail := by
      dsimp only [tail]
      rw [encodeDatum,PA17TMRatArithmeticParse002.encodeNat_rawField]
      simp only [PA17TMRatArithmeticParse002.rawField]
      have hl : (PSTRTMNatValue017.rawPayload n).length = natBits n := by
        simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]
      rw [hl]
      have he : natBits n = 3+(natBits n-3) := by omega
      conv_lhs => rw [he,List.replicate_add]
      simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc]
    refine ⟨wideTrace left tail,wideFinal left tail,3,?_,?_,by simp [wideTrace],by decide,?_⟩
    · rw [hheader]
      exact wide_runsFrom _ _
    · have hn : ¬n ≤ 2 := by omega
      simp only [wideFinal,state,hn,ite_false]
    · rw [hheader]
      exact wide_final_tape _ _

/-- Official original visitedSpace, for EVERY prefix of the SAME
returned classifier run. Its fixed six configurations cost at most13
additional cells in the general trace bound; no width is supplied. -/
theorem datum_classify_bounded (n : Nat) (left suffix : List Bool) (inputLength : Nat) :
    ∃ trace last distance,
      PSTRTMSeq005.RunsFrom classifyMachine ⟨0,Turing.Tape.mk₂ left (encodeDatum (.natural n)++suffix)⟩ trace last ∧
      last.q = (if n ≤ 2 then 5 else 6) ∧ trace.length ≤ 6 ∧ distance ≤ 4 ∧
      last.Tape = rightSteps distance (Turing.Tape.mk₂ left (encodeDatum (.natural n)++suffix)) ∧
      ∀ clock, visitedSpace classifyMachine inputLength (trace.take clock) ≤ inputLength+13 := by
  obtain ⟨trace,last,distance,hrun,hq,ht,hd,htape⟩ := datum_classify_contract n left suffix
  refine ⟨trace,last,distance,hrun,hq,ht,hd,htape,?_⟩
  intro clock
  have hs := PSTRTMTrace002.visitedSpace_le classifyMachine inputLength (trace.take clock)
  have hl : (trace.take clock).length ≤ trace.length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCapRun235
