module
public import Structure.RootB23_Threshold_ReturnPairReady_037

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnDWork
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002
open PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

def natArchive (left : List Bool) (n : ℕ) : List Bool := firstLeft (false::left) (PSTRTMNatValue017.rawPayload n)
def denArchive (left : List Bool) (n : ℕ) : List Bool :=
  PSTRTMRawNat010.leftBlocks (numeratorDigits (OutputArithmetic.Target.value n)).reverse++
    false::sign (OutputArithmetic.Target.value n)::natArchive left n
def natCode : Machine 19 := PSTRTMSeq005.seqMachine footerMachine streamMachine
def parseCode : Machine 65 := PSTRTMSeq005.seqMachine natCode ratMachine
def backCode : Machine 71 := PSTRTMSeq005.seqMachine parseCode fieldBackMachine
def code : Machine 122 := PSTRTMSeq005.seqMachine backCode counterCopyMachine
def finalTape (left : List Bool) (n : ℕ) : Tape Bool :=
  Tape.mk₂ (false::PA17TMRatArithmeticCopy006.sourceLeft (denArchive left n)
    (PSTRTMNatValue017.rawPayload (OutputArithmetic.Target.denominator n)))
    (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (OutputArithmetic.Target.denominator n)))

theorem value_num (n : ℕ) : (OutputArithmetic.Target.value n).num=1 := by
  unfold OutputArithmetic.Target.value
  rw [one_div]
  exact Rat.inv_natCast_num_of_pos (by unfold OutputArithmetic.Target.denominator;omega)
theorem value_den (n : ℕ) : (OutputArithmetic.Target.value n).den=OutputArithmetic.Target.denominator n := by
  unfold OutputArithmetic.Target.value
  rw [one_div]
  exact Rat.inv_natCast_den_of_pos (by unfold OutputArithmetic.Target.denominator;omega)
theorem denominator_digits (n : ℕ) : denominatorDigits (OutputArithmetic.Target.value n)=
    PSTRTMNatValue017.rawPayload (OutputArithmetic.Target.denominator n) := by rw [denominatorDigits,value_den]
theorem archive_exact (left : List Bool) (n : ℕ) :
    ratLeft (natArchive left n) (OutputArithmetic.Target.value n)=
      PA17TMRatArithmeticCopy006.sourceLeft (denArchive left n)
        (PSTRTMNatValue017.rawPayload (OutputArithmetic.Target.denominator n)) := by
  simp only [ratLeft,bothLeft,firstLeft,denominator_digits,denArchive,PA17TMRatArithmeticCopy006.sourceLeft]

private theorem copy_fee (n : ℕ) : 4*n^2+22*n+21≤64*(n+1)^2 := by nlinarith only [Nat.zero_le (n^2)]
private theorem arithmetic_fee (n d : ℕ) (width : d≤n+3) :
    2+16*(n+1)^2+64*(d+2)^2+(2*d+5)+64*(d+1)^2≤4096*(n+1)^2 := by
  have first : d+2≤5*(n+1) := by omega
  have second : d+1≤4*(n+1) := by omega
  have square1:=Nat.pow_le_pow_left first 2
  have square2:=Nat.pow_le_pow_left second 2
  have linear : 2*d+7≤16*(n+1)^2 := by nlinarith only [width,Nat.zero_le (n^2)]
  simp only [Nat.mul_pow] at square1 square2
  nlinarith only [square1,square2,linear]

/-- Actual parse of the existing B/target fields, real DEN rewind and
the frozen nearest-field copy produce an actual D DATA workspace. D is
computed from the preceding target bytes, never an original caller input.
All original parsed B/target and the arbitrary outside left are retained. -/
theorem bounded (left : List Bool) (n : ℕ) :
    BoundedRun code (Tape.mk₂ left (OutputArithmetic.Pair.output n)) 122 (finalTape left n)
      (4096*(natBits n+1)^2) := by
  let d:=OutputArithmetic.Target.denominator n
  let q:=OutputArithmetic.Target.value n
  let digits:=PSTRTMNatValue017.rawPayload d
  have moved:=MarshalAnchor.footer_any_bounded left false (encodeNat n++encodeDatum (.rational q))
  have native : BoundedRun streamMachine
      (Tape.mk₂ (false::left) (encodeNat n++encodeDatum (.rational q))) 17
      (Tape.mk₂ (natArchive left n) (encodeDatum (.rational q))) (16*(natBits n+1)^2) := by
    refine ⟨streamTrace (false::left) [] (PSTRTMNatValue017.rawPayload n) (encodeDatum (.rational q)),
      encodeNat_stream_runsFrom _ _ _,?_⟩
    simpa only [PSTRTMNatValue017.rawPayload,List.length_ofFn] using
      stream_length_le (false::left) (PSTRTMNatValue017.rawPayload n) (encodeDatum (.rational q))
  have parsed:=FactorWalk.rational_scan (natArchive left n) [] q
  have qNum : q.num=1 := value_num n
  have qDen : q.den=d := value_den n
  have unit : natBits 1=1 := by decide
  have parsed' : BoundedRun ratMachine (Tape.mk₂ (natArchive left n) (encodeDatum (.rational q))) 45
      (Tape.mk₂ (ratLeft (natArchive left n) q) []) (64*(natBits d+2)^2) := by
    simpa only [List.append_nil,qNum,qDen,Int.natAbs_one,unit,show 1+natBits d+1=natBits d+2 by omega] using parsed
  have back:=ReturnHeadroom.field_bounded (denArchive left n) digits []
  have backInput : PA17TMRatArithmeticCopy006.sourceLeft (denArchive left n) digits=ratLeft (natArchive left n) q :=
    (archive_exact left n).symm
  rw [backInput] at back
  have noTail : Tape.mk₂ (false::denArchive left n) (PSTRTMIncrement009.blocks digits++[false])=
      Tape.mk₂ (false::denArchive left n) (PSTRTMIncrement009.blocks digits) :=
    PA17TMRatArithmeticBankCopy024.tape_append_false _ _
  rw [noTail] at back
  have back':=back.mono (b:=2*natBits d+5) (by
    simp only [digits,PSTRTMNatValue017.rawPayload,List.length_ofFn]
    exact le_refl _)
  have copied:=counterCopy_bounded (denArchive left n) digits
  have copied' : BoundedRun counterCopyMachine
      (Tape.mk₂ (false::denArchive left n) (PSTRTMIncrement009.blocks digits)) 50
      (finalTape left n) (64*(natBits d+1)^2) := by
    have actual:=copied.mono (b:=64*(natBits d+1)^2) (by
      simp only [digits,PSTRTMNatValue017.rawPayload,List.length_ofFn]
      exact copy_fee (natBits d))
    simpa only [PA17TMRatArithmeticCopy006.workspace,copiedCounterLeft,finalTape,digits,d,
      OutputArithmetic.Target.two_right_blanks] using actual
  have actual:=(((moved.seq native).seq parsed').seq back').seq copied'
  have port : PSTRTMSeq005.rightLabel (a:=71) (50 : Fin 51)=(122 : Fin 123) := by decide
  rw [port] at actual
  have width:=OutputArithmetic.Target.denominator_width n
  have fee := arithmetic_fee (natBits n) (natBits d) width
  simpa only [code,backCode,parseCode,natCode,OutputArithmetic.Pair.output,encodeDatum,List.cons_append,q,
    digits,PSTRTMNatValue017.rawPayload,List.length_ofFn] using actual.mono fee

theorem denominator_at_least_two (n : ℕ) : 2≤OutputArithmetic.Target.denominator n := by
  unfold OutputArithmetic.Target.denominator
  omega

theorem actual_bounded (risk : Rat) (depth : ℕ) (y : Rat) (left : ℕ) :
    BoundedRun code (ReturnPairReady.finalTape risk depth y left) 122
      (finalTape (List.replicate 9 false++ReturnReady.archive risk depth y left) (PaperProofs.Statistics.controllerB risk depth))
      (4096*(natBits (PaperProofs.Statistics.controllerB risk depth)+1)^2) := by
  have actual:=bounded (List.replicate 9 false++ReturnReady.archive risk depth y left) (PaperProofs.Statistics.controllerB risk depth)
  rw [ReturnPairReady.output_exact] at actual
  exact actual

end RootB23.Threshold.ReturnDWork
