module
public import Structure.RootB23_Threshold_ReturnDWork_038
public import Structure.RootB23_Threshold_OutputArithmetic_OddsInverse_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnNineSource
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002

def d (n : ℕ) : ℕ := OutputArithmetic.Target.denominator n
def odds (n : ℕ) : Rat := ((d n-1 : ℕ) : Rat)
def inverse (n : ℕ) : Rat := 1/((d n-1 : ℕ) : Rat)
def beforeOdds (left : List Bool) (n : ℕ) : List Bool :=
  false::PA17TMRatArithmeticCopy006.sourceLeft (ReturnDWork.denArchive left n) (PSTRTMNatValue017.rawPayload (d n))
def rawLeft (left : List Bool) (n : ℕ) : List Bool := ratLeft (ratLeft (beforeOdds left n) (odds n)) (inverse n)
def arithmeticCode : Machine 1137 := PSTRTMSeq005.seqMachine ReturnDWork.code OutputArithmetic.OddsInverse.code
def parsedCode : Machine 1229 := PSTRTMSeq005.seqMachine arithmeticCode pairMachine
def code : Machine 1231 := PSTRTMSeq005.seqMachine parsedCode (PA17TMRatArithmeticAllocate013.setMarkerMachine false)
def finalTape (left : List Bool) (n : ℕ) : Tape Bool := Tape.mk₂ (rawLeft left n) [false]

private theorem arithmetic_fee (n den pred : ℕ) (width : den≤n+3) (small : pred≤den) :
    4096*(n+1)^2+32768*(den+1)^2+128*(pred+2)^2+2≤1048576*(n+1)^2 := by
  have first : den+1≤4*(n+1) := by omega
  have second : pred+2≤5*(n+1) := by omega
  have square1:=Nat.pow_le_pow_left first 2
  have square2:=Nat.pow_le_pow_left second 2
  have unit : 1≤(n+1)^2 := by nlinarith only [Nat.zero_le (n^2),Nat.zero_le n]
  simp only [Nat.mul_pow] at square1 square2
  nlinarith only [square1,square2,unit]

theorem parse_bounded (left : List Bool) (n : ℕ) :
    BoundedRun pairMachine (Tape.mk₂ (beforeOdds left n) (OutputArithmetic.OddsInverse.output (d n))) 91
      (Tape.mk₂ (rawLeft left n) [true]) (128*(natBits (d n-1)+2)^2) := by
  have positive : 0<d n-1 := by have bound:=ReturnDWork.denominator_at_least_two n;dsimp only [d];omega
  have first:=FactorWalk.rational_scan (beforeOdds left n) (encodeDatum (.rational (inverse n))++[true]) (odds n)
  have second:=FactorWalk.rational_scan (ratLeft (beforeOdds left n) (odds n)) [true] (inverse n)
  have actual:=first.seq second
  have port : PSTRTMSeq005.rightLabel (a:=45) (45 : Fin 46)=(91 : Fin 92) := by decide
  rw [port] at actual
  have unit : natBits 1=1 := by decide
  have fee : 64*(natBits (odds n).num.natAbs+natBits (odds n).den+1)^2+
      64*(natBits (inverse n).num.natAbs+natBits (inverse n).den+1)^2≤128*(natBits (d n-1)+2)^2 := by
    simp only [odds,inverse,Rat.num_natCast,Int.natAbs_natCast,Rat.den_natCast,
      OutputArithmetic.OddsInverse.inv_num _ positive,OutputArithmetic.OddsInverse.inv_den _ positive,Int.natAbs_one,unit]
    rw [show natBits (d n-1)+1+1=natBits (d n-1)+2 by omega,
      show 1+natBits (d n-1)+1=natBits (d n-1)+2 by omega]
    omega
  simpa only [pairMachine,rawLeft,OutputArithmetic.OddsInverse.output,odds,inverse,List.append_assoc] using actual.mono fee

/-- Actual B/target -> actual D copy -> true odds/inverse/footer -> actual
pair parse -> real clamping of that old footer. Together with the already
parsed nearest badRisk this is the genuine near nine-field source bank;
no numerical answer or list of source fields was supplied to the code. -/
theorem bounded (left : List Bool) (n : ℕ) :
    BoundedRun code (Tape.mk₂ left (OutputArithmetic.Pair.output n)) 1231 (finalTape left n)
      (1048576*(natBits n+1)^2) := by
  have prepared:=ReturnDWork.bounded left n
  have computed:=OutputArithmetic.OddsInverse.bounded
    (PA17TMRatArithmeticCopy006.sourceLeft (ReturnDWork.denArchive left n) (PSTRTMNatValue017.rawPayload (d n)))
    (d n) (ReturnDWork.denominator_at_least_two n)
  have parsed:=parse_bounded left n
  have clamped : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine false)
      (Tape.mk₂ (rawLeft left n) [true]) 1 (finalTape left n) 2 :=
    ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace true false (rawLeft left n) [],
      PA17TMRatArithmeticAllocate013.setMarker_runsFrom _ _ _ _,by rfl⟩
  have actual:=((prepared.seq computed).seq parsed).seq clamped
  have port : PSTRTMSeq005.rightLabel (a:=1229) (1 : Fin 2)=(1231 : Fin 1232) := by decide
  rw [port] at actual
  have width:=OutputArithmetic.Target.denominator_width n
  have small:=PSTRTMArithmetic008.natBits_mono (Nat.sub_le (d n) 1)
  have fee:=arithmetic_fee (natBits n) (natBits (d n)) (natBits (d n-1)) width small
  simpa only [code,parsedCode,arithmeticCode,ReturnDWork.finalTape,beforeOdds,d] using actual.mono fee

theorem actual_bounded (risk : Rat) (depth : ℕ) (y : Rat) (left : ℕ) :
    BoundedRun code (ReturnPairReady.finalTape risk depth y left) 1231
      (finalTape (List.replicate 9 false++ReturnReady.archive risk depth y left) (PaperProofs.Statistics.controllerB risk depth))
      (1048576*(natBits (PaperProofs.Statistics.controllerB risk depth)+1)^2) := by
  have actual:=bounded (List.replicate 9 false++ReturnReady.archive risk depth y left) (PaperProofs.Statistics.controllerB risk depth)
  rw [ReturnPairReady.output_exact] at actual
  exact actual

end RootB23.Threshold.ReturnNineSource
