module
public import Common.PSTR_TM_ThresholdDenominatorRawCost_203
public import Structure.PA17_TM_RatArithmetic_Prefix5_060b

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdTargetDatum222
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDenominatorRaw202

/-! ORIGINAL risk/depth -> ORIGINAL target Rat Datum, with the same actual
B/risk archive and false guard. The frozen A17 Prefix5 physically creates
the required space; no left credit or width/performance input is supplied. -/

def targetMachine : Machine 1928 :=
  PSTRTMSeq005.seqMachine rawDenMachine PA17TMRatArithmeticPrefix5060.prefixMachine

def targetFinal (risk : Rat) (depth : Nat) : MachineState 1928 :=
  PSTRTMSeq005.rightCfg (a := 1374) (b := 553)
    ⟨553,Turing.Tape.mk₂ (false::PSTRTMThresholdBReblock195.savedLeft risk depth)
      (encodeDatum (.rational (PaperProofs.Statistics.controllerTarget risk depth)))⟩

theorem target_final_tape (risk : Rat) (depth : Nat) :
    (targetFinal risk depth).Tape = Turing.Tape.mk₂
      (false::PSTRTMThresholdBReblock195.savedLeft risk depth)
      (encodeDatum (.rational (PaperProofs.Statistics.controllerTarget risk depth))) := rfl

theorem target_fragment_bits (risk : Rat) (depth : Nat) :
    PA17TMRatArithmeticPrefix5060.fragment ++
        encodeNat (4*(PaperProofs.Statistics.controllerB risk depth+1)) =
      encodeDatum (.rational (PaperProofs.Statistics.controllerTarget risk depth)) := by
  simpa only [PA17TMRatArithmeticPrefix5060.fragment_original_datum,List.append_assoc] using
    (target_datum_bits risk depth).symm

private theorem arithmetic_time (input depth width main extra : Nat)
    (hm : main ≤ 67108864*(input+depth+1)^3)
    (hp : extra ≤ 128*(width+1)^2) (hw : width ≤ input+7) :
    main+extra ≤ 100663296*(input+depth+1)^3 := by
  let scale := input+depth+1
  have hs : 1 ≤ scale := by dsimp only [scale]; omega
  have hwidth : width+1 ≤ 8*scale := by dsimp only [scale]; omega
  have hpow := Nat.pow_le_pow_left hwidth 2
  have htail : extra ≤ 8192*scale^2 := by nlinarith
  have hcube : scale^2 ≤ scale^3 := Nat.pow_le_pow_right hs (by decide : 2 ≤ 3)
  have htail' := htail.trans (Nat.mul_le_mul_left 8192 hcube)
  change main+extra ≤ 100663296*scale^3
  have hm' : main ≤ 67108864*scale^3 := hm
  omega

private theorem scale_cube (input depth : Nat) : input+1 ≤ (input+depth+1)^3 := by
  have hs : 1 ≤ input+depth+1 := by omega
  have hp : input+depth+1 ≤ (input+depth+1)^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hs (by decide : 1 ≤ 3)
  omega

/-- One SAME genuine original run provides output, true HALT, time and
EVERY-prefix official visitedSpace. Prefix trace existence is proved by
the fixed imported machine, never an extra original input/certificate. -/
theorem original_targetDatum_contract (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    ∃ trace, Runs targetMachine (encode [.rational risk,.natural depth]) trace (targetFinal risk depth) ∧
      trace.length ≤ 100663296*((encode [.rational risk,.natural depth]).length+depth+1)^3 ∧
      ∀ clock, visitedSpace targetMachine (encode [.rational risk,.natural depth]).length (trace.take clock) ≤
        268435456*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
  obtain ⟨part,hpart,htail⟩ := PA17TMRatArithmeticPrefix5060.prefix_bounded
    (4*(PaperProofs.Statistics.controllerB risk depth+1)) (by omega)
    (PSTRTMThresholdBReblock195.savedLeft risk depth)
  rw [target_fragment_bits] at hpart
  let trace := (rawDenTrace risk depth).map (PSTRTMSeq005.leftCfg (b := 553)) ++
    part.map (PSTRTMSeq005.rightCfg (a := 1374))
  have hrun : Runs targetMachine (encode [.rational risk,.natural depth]) trace (targetFinal risk depth) := by
    apply PSTRTMSeq005.seq_runs rawDenMachine PA17TMRatArithmeticPrefix5060.prefixMachine
      (encode [.rational risk,.natural depth]) (rawDenFinal risk depth)
      ⟨553,Turing.Tape.mk₂ (false::PSTRTMThresholdBReblock195.savedLeft risk depth)
        (encodeDatum (.rational (PaperProofs.Statistics.controllerTarget risk depth)))⟩
      (rawDenTrace risk depth) part (rawDen_runs risk depth hr hd)
    rw [rawDen_final_tape]
    exact hpart
  have htime : trace.length ≤ 100663296*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
    have hm := PSTRTMThresholdDenominatorRawCost203.rawDen_length_le risk depth hr hd
    have hw := PSTRTMThresholdDenominatorCost201.targetDen_bits_le risk depth hr hd
    simp only [trace,List.length_append,List.length_map]
    exact arithmetic_time _ _ _ _ _ hm htail hw
  refine ⟨trace,hrun,htime,?_⟩
  intro clock
  have hs := PSTRTMTrace002.visitedSpace_le targetMachine (encode [.rational risk,.natural depth]).length (trace.take clock)
  have hl : (trace.take clock).length ≤ trace.length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  have hp := scale_cube (encode [.rational risk,.natural depth]).length depth
  omega

/-- Exact canonical SECOND threshold Datum from the ORIGINAL input, fixed
1929-label code before ALL risk/depth, without consuming the saved guards. -/
theorem original_targetDatum_computes (risk : Rat) (depth : Nat) (hr : 0 < risk) (hd : 1 ≤ depth) :
    computes targetMachine (encode [.rational risk,.natural depth])
      (encodeDatum (.rational (PaperProofs.Statistics.controllerTarget risk depth)))
      (268435456*((encode [.rational risk,.natural depth]).length+depth+1)^3)
      (268435456*((encode [.rational risk,.natural depth]).length+depth+1)^3) := by
  obtain ⟨trace,hrun,htime,hspace⟩ := original_targetDatum_contract risk depth hr hd
  refine ⟨trace,targetFinal risk depth,hrun,?_,?_,?_⟩
  · rw [target_final_tape]
    simp only [Turing.Tape.mk₂,Turing.Tape.mk'_right₀]
  · omega
  · simpa only [List.take_length] using hspace trace.length

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdTargetDatum222
