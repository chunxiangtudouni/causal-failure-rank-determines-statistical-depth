module
public import Structure.RootB23_Threshold_FactorWalk_008
public import Structure.PA17_TM_RatArithmetic_PairEncode_017c

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.FactorBack
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002 FactorWalk

def pairCode : Machine 53 := PSTRTMSeq005.seqMachine fieldBackMachine
  (PA17TMRatArithmeticPairEncode017.pairMachine false)
def restoreCode : Machine 60 := PSTRTMSeq005.seqMachine pairCode PSTRTMThresholdIntegerDatum217.tagMachine

private theorem restore_cost (n d : ℕ) :
    (2*d+5)+64*(n+d+1)^2+7 ≤ 128*(n+d+1)^2 := by
  nlinarith only [Nat.zero_le (n^2),Nat.zero_le (d^2),Nat.zero_le (n*d)]

/-- Inverse of the actual factor parse, retaining the original FALSE
footer and arbitrary real suffix. Both original tag/sign cells are used. -/
theorem restore_bounded (left suffix : List Bool) (q : Rat) (nonnegative : 0 ≤ q) :
    BoundedRun restoreCode (Tape.mk₂ (ratLeft left q) (false::suffix)) 60
      (Tape.mk₂ left (encodeDatum (.rational q)++false::suffix))
      (128*(natBits q.num.natAbs+natBits q.den+1)^2) := by
  let n:=q.num.natAbs
  let d:=q.den
  let archived:=PA17TMRatArithmeticPairEncode017.aArchive (false::left) n
  have zeroSign : sign q=false := by
    simp only [sign,decide_eq_false_iff_not]
    exact not_lt.mpr nonnegative
  have geometry : ratLeft left q=false::(PSTRTMRawNat010.leftBlocks (denominatorDigits q).reverse++false::archived) := by
    dsimp only [ratLeft,bothLeft,firstLeft]
    rw [zeroSign]
    rfl
  let last:=fieldBackFinal archived (denominatorDigits q) (false::suffix)
  have back : BoundedRun fieldBackMachine (Tape.mk₂ (ratLeft left q) (false::suffix)) last.q
      (Tape.mk₂ (false::archived) (PSTRTMIncrement009.blocks (denominatorDigits q)++false::false::suffix))
      (2*natBits d+5) := by
    rw [geometry]
    refine ⟨fieldBackTrace archived (denominatorDigits q) (false::suffix),
      fieldBack_runsFrom _ _ _,?_⟩
    rw [fieldBackTrace_length,denominatorDigits_length]
  have pair : BoundedRun (PA17TMRatArithmeticPairEncode017.pairMachine false)
      (Tape.mk₂ (false::archived) (PSTRTMIncrement009.blocks (denominatorDigits q)++false::false::suffix)) 47
      (Tape.mk₂ (false::false::left) (encodeNat n++encodeNat d++false::suffix))
      (64*(natBits n+natBits d+1)^2) := by
    refine ⟨PA17TMRatArithmeticPairEncode017.pairTrace false (false::left) n d suffix,
      PA17TMRatArithmeticPairEncode017.pair_explicit_runsFrom false (false::left) n d suffix,?_⟩
    simpa only [PA17TMRatArithmeticPairEncode017.payload_length] using
      PA17TMRatArithmeticPairEncode017.pair_time_le false (false::left) n d suffix
  have datum : encodeDatum (.rational q)=true::false::(encodeNat n++encodeNat d) := by
    rw [encodeDatum,show decide (q<0)=false from zeroSign]
    rfl
  have tagged:=PSTRTMThresholdIntegerDatum217.tag_runsFrom left (encodeNat n++encodeNat d++false::suffix)
  have tagEq : PSTRTMThresholdIntegerDatum217.tagFinal left (encodeNat n++encodeNat d++false::suffix)=
      (⟨6,Tape.mk₂ left (encodeDatum (.rational q)++false::suffix)⟩ : MachineState 6) := by
    change (⟨PSTRTMSeq005.rightLabel (a:=3) (2 : Fin 3),_⟩ : MachineState 6)=_
    have labelEq : PSTRTMSeq005.rightLabel (a:=3) (2 : Fin 3)=(6 : Fin 7) := by decide
    rw [labelEq,datum]
    rfl
  rw [tagEq] at tagged
  have tag : BoundedRun PSTRTMThresholdIntegerDatum217.tagMachine
      (Tape.mk₂ (false::false::left) (encodeNat n++encodeNat d++false::suffix)) 6
      (Tape.mk₂ left (encodeDatum (.rational q)++false::suffix)) 7 :=
    ⟨PSTRTMThresholdIntegerDatum217.tagTrace left (encodeNat n++encodeNat d++false::suffix),
      tagged,by rw [PSTRTMThresholdIntegerDatum217.tag_length]⟩
  exact ((back.seq pair).seq tag).mono (restore_cost _ _)

def bBackCode : Machine 64 := PSTRTMSeq005.seqMachine restoreCode PSTRTMMulRewind085.rewindMachine
def commonCode : Machine 73 := PSTRTMSeq005.seqMachine bBackCode PSTRTMThresholdRiskReturn228.depthMachine
def denCode : Machine 82 := PSTRTMSeq005.seqMachine commonCode PSTRTMThresholdRiskMarkers232.markerMachine
def numCode : Machine 91 := PSTRTMSeq005.seqMachine commonCode PSTRTMThresholdRiskMarkers232.riskFieldsMachine

def depthArchive (left depth : List Bool) (gap : ℕ) : List Bool :=
  List.replicate (2*gap+1) false++(PSTRTMRawNat010.leftBlocks depth.reverse++false::left)

theorem common_bounded (left depth b suffix : List Bool) (gap : ℕ) (q : Rat)
    (nonnegative : 0 ≤ q) (nonempty : depth≠[]) :
    BoundedRun commonCode (Tape.mk₂ (ratLeft (bBase (false::left) depth b gap) q) (false::suffix)) 73
      (Tape.mk₂ (false::left) (depthRight depth b gap q suffix))
      (128*(natBits q.num.natAbs+natBits q.den+1)^2+2*b.length+2*gap+2*depth.length+13) := by
  have restore:=restore_bounded (bBase (false::left) depth b gap) suffix q nonnegative
  have entry : bBase (false::left) depth b gap=
      PSTRTMRawNat010.leftBlocks b.reverse++false::depthArchive left depth gap := by
    rw [bBase,depthArchive,show 2*gap+2=(2*gap+1)+1 by omega,List.replicate_succ]
    simp only [List.append_assoc,List.cons_append]
  have rewind : BoundedRun PSTRTMMulRewind085.rewindMachine
      (Tape.mk₂ (bBase (false::left) depth b gap) (encodeDatum (.rational q)++false::suffix)) 3
      (Tape.mk₂ (false::depthArchive left depth gap) (bRight b q suffix)) (2*b.length+3) := by
    rw [entry]
    refine ⟨PSTRTMPairRewind105.fullTrace (depthArchive left depth gap) b.reverse (encodeDatum (.rational q)++false::suffix),?_,
      by rw [PSTRTMPairRewind105.full_length,List.length_reverse]⟩
    simpa only [PSTRTMMulRewind085.state,bRight,List.append_assoc] using
      PSTRTMPairRewind105.rewind_runsFrom (depthArchive left depth gap) b (encodeDatum (.rational q)++false::suffix)
  cases reversed : depth.reverse with
  | nil =>
    have equal:=congrArg List.reverse reversed
    simp only [List.reverse_reverse,List.reverse_nil] at equal
    exact False.elim (nonempty equal)
  | cons bit earlier =>
    have original : (bit::earlier).reverse=depth := by rw [←reversed,List.reverse_reverse]
    have len:=congrArg List.length reversed
    simp only [List.length_reverse,List.length_cons] at len
    have depthEntry : false::depthArchive left depth gap=
        List.replicate (2*gap+2) false++(PSTRTMRawNat010.leftBlocks (bit::earlier)++false::left) := by
      rw [depthArchive,show 2*gap+2=(2*gap+1)+1 by omega,List.replicate_succ,reversed]
      rfl
    have depthRun:=PSTRTMThresholdRiskReturn228.depth_runsFrom left bit earlier (bRight b q suffix) (2*gap+2)
    rw [←depthEntry] at depthRun
    have finalEq : PSTRTMThresholdRiskReturn228.depthFinal left bit earlier (bRight b q suffix) (2*gap+2)=
        (⟨8,Tape.mk₂ (false::left) (depthRight depth b gap q suffix)⟩ : MachineState 8) := by
      change (⟨PSTRTMSeq005.rightLabel (a:=4) (3 : Fin 4),_⟩ : MachineState 8)=_
      have labelEq : PSTRTMSeq005.rightLabel (a:=4) (3 : Fin 4)=(8 : Fin 9) := by decide
      rw [labelEq]
      simp only [depthRight,original]
      rfl
    rw [finalEq] at depthRun
    have back : BoundedRun PSTRTMThresholdRiskReturn228.depthMachine
        (Tape.mk₂ (false::depthArchive left depth gap) (bRight b q suffix)) 8
        (Tape.mk₂ (false::left) (depthRight depth b gap q suffix)) (2*gap+2*earlier.length+12) :=
      ⟨_,depthRun,by rw [PSTRTMThresholdRiskReturn228.depth_length];omega⟩
    exact ((restore.seq rewind).seq back).mono (by omega)

theorem denominator_bounded (archive den depth b suffix : List Bool) (gap : ℕ) (q : Rat)
    (nonnegative : 0 ≤ q) (nonempty : depth≠[]) :
    BoundedRun denCode (Tape.mk₂ (ratLeft (bBase (markedLeft (false::archive) den) depth b gap) q) (false::suffix)) 82
      (Tape.mk₂ (false::archive) (denRight den depth b gap q suffix))
      (2*den.length+2*depth.length+2*gap+2*b.length+128*(natBits q.num.natAbs+natBits q.den+1)^2+21) := by
  let stored:=PSTRTMThresholdDenPrepare141.denArchive archive den
  have deep:=common_bounded stored depth b suffix gap q nonnegative nonempty
  have run:=PSTRTMThresholdRiskMarkers232.marker_runsFrom archive den (depthRight depth b gap q suffix)
  have lastEq : PSTRTMThresholdRiskMarkers232.markerFinal archive den (depthRight depth b gap q suffix)=
      (⟨8,Tape.mk₂ (false::archive) (denRight den depth b gap q suffix)⟩ : MachineState 8) := by
    change (⟨PSTRTMSeq005.rightLabel (a:=4) (3 : Fin 4),_⟩ : MachineState 8)=_
    have labelEq : PSTRTMSeq005.rightLabel (a:=4) (3 : Fin 4)=(8 : Fin 9) := by decide
    rw [labelEq]
    rfl
  rw [lastEq] at run
  have fields : BoundedRun PSTRTMThresholdRiskMarkers232.markerMachine
      (Tape.mk₂ (false::stored) (depthRight depth b gap q suffix)) 8
      (Tape.mk₂ (false::archive) (denRight den depth b gap q suffix)) (2*den.length+8) :=
    ⟨PSTRTMThresholdRiskMarkers232.markerTrace archive den (depthRight depth b gap q suffix),run,
      by rw [PSTRTMThresholdRiskMarkers232.marker_length]⟩
  exact (deep.seq fields).mono (by omega)

theorem numerator_bounded (archive num den depth b suffix : List Bool) (gap : ℕ) (q : Rat)
    (nonnegative : 0 ≤ q) (nonempty : depth≠[]) :
    BoundedRun numCode
      (Tape.mk₂ (ratLeft (bBase (markedLeft (markedLeft (false::archive) num) den) depth b gap) q) (false::suffix)) 91
      (Tape.mk₂ (false::archive) (numRight num den depth b gap q suffix))
      (2*num.length+2*den.length+2*depth.length+2*gap+2*b.length+
        128*(natBits q.num.natAbs+natBits q.den+1)^2+29) := by
  let stored:=PSTRTMThresholdDenPrepare141.denArchive
    (PSTRTMThresholdDenPrepare141.denArchive archive num) den
  have deep:=common_bounded stored depth b suffix gap q nonnegative nonempty
  have run:=PSTRTMThresholdRiskMarkers232.riskFields_runsFrom archive num den (depthRight depth b gap q suffix)
  have lastEq : PSTRTMThresholdRiskMarkers232.riskFieldsFinal archive num den (depthRight depth b gap q suffix)=
      (⟨17,Tape.mk₂ (false::archive) (numRight num den depth b gap q suffix)⟩ : MachineState 17) := by
    change (⟨PSTRTMSeq005.rightLabel (a:=8)
      (PSTRTMSeq005.rightLabel (a:=4) (3 : Fin 4)),_⟩ : MachineState 17)=_
    have labelEq : PSTRTMSeq005.rightLabel (a:=8)
        (PSTRTMSeq005.rightLabel (a:=4) (3 : Fin 4))=(17 : Fin 18) := by decide
    rw [labelEq]
    rfl
  rw [lastEq] at run
  have fields : BoundedRun PSTRTMThresholdRiskMarkers232.riskFieldsMachine
      (Tape.mk₂ (false::stored) (depthRight depth b gap q suffix)) 17
      (Tape.mk₂ (false::archive) (numRight num den depth b gap q suffix))
      (2*(num.length+den.length)+16) :=
    ⟨PSTRTMThresholdRiskMarkers232.riskFieldsTrace archive num den (depthRight depth b gap q suffix),run,
      by rw [PSTRTMThresholdRiskMarkers232.riskFields_length]⟩
  exact (deep.seq fields).mono (by omega)

end RootB23.Threshold.FactorBack
