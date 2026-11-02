module
public import Structure.RootB23_Threshold_NatSplice_001
public import Structure.RootB23_Threshold_SourceRoutes_010
public import Structure.RootB23_Threshold_Uncapped_Steps_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.FactorGap
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002

/-- The factor has actual denominator one. Its retained DATA bit is
cleared after three real LEFTs; the surrounding flags and WEST stay put. -/
def clampCode : Machine 4 := fun q _=>match q.val with
  | 0=>some (1,.move .left)
  | 1=>some (2,.move .left)
  | 2=>some (3,.move .left)
  | 3=>some (4,.write false)
  | _=>none
def clampTrace (left suffix : List Bool) : List (MachineState 4) :=
  [⟨0,Tape.mk₂ (false::true::true::left) (false::suffix)⟩,
   ⟨1,Tape.mk₂ (true::true::left) (false::false::suffix)⟩,
   ⟨2,Tape.mk₂ (true::left) (true::false::false::suffix)⟩,
   ⟨3,Tape.mk₂ left (true::true::false::false::suffix)⟩,
   ⟨4,Tape.mk₂ left (false::true::false::false::suffix)⟩]
theorem clamp_bounded (left suffix : List Bool) :
    BoundedRun clampCode (Tape.mk₂ (false::true::true::left) (false::suffix)) 4
      (Tape.mk₂ left (false::true::false::false::suffix)) 5 := by
  refine ⟨clampTrace left suffix,⟨rfl,?_,rfl,?_⟩,by rfl⟩
  · simp [clampTrace,List.isChain_cons_cons,TM0.step,clampCode,Tape.mk₂]
  · simp [TM0.step,clampCode]

/-- The last bit of Den1 is genuinely planted in the old gap. It is
neither supplied as a suffix nor identified with the next Rat's tag. -/
def plantCode : Machine 5 := fun q _=>match q.val with
  | 0=>some (1,.move .right)
  | 1=>some (2,.move .right)
  | 2=>some (3,.write true)
  | 3=>some (4,.move .left)
  | 4=>some (5,.move .left)
  | _=>none
def plantTrace (left suffix : List Bool) : List (MachineState 5) :=
  [⟨0,Tape.mk₂ left (false::false::false::suffix)⟩,
   ⟨1,Tape.mk₂ (false::left) (false::false::suffix)⟩,
   ⟨2,Tape.mk₂ (false::false::left) (false::suffix)⟩,
   ⟨3,Tape.mk₂ (false::false::left) (true::suffix)⟩,
   ⟨4,Tape.mk₂ (false::left) (false::true::suffix)⟩,
   ⟨5,Tape.mk₂ left (false::false::true::suffix)⟩]
theorem plant_bounded (left suffix : List Bool) :
    BoundedRun plantCode (Tape.mk₂ left (false::false::false::suffix)) 5
      (Tape.mk₂ left (false::false::true::suffix)) 6 := by
  refine ⟨plantTrace left suffix,⟨rfl,?_,rfl,?_⟩,by rfl⟩
  · simp [plantTrace,List.isChain_cons_cons,TM0.step,plantCode,Tape.mk₂]
  · simp [TM0.step,plantCode]

def clampBackCode : Machine 6 := PSTRTMSeq005.seqMachine clampCode backOneMachine
def prepareCode : Machine 10 := PSTRTMSeq005.seqMachine clampBackCode PSTRTMMulRewind085.rewindMachine
def shiftCode : Machine 20 := PSTRTMSeq005.seqMachine prepareCode NatSplice.shiftMachine
def plantShiftCode : Machine 26 := PSTRTMSeq005.seqMachine shiftCode plantCode
def returnCode : Machine 32 := PSTRTMSeq005.seqMachine plantShiftCode fieldBackMachine
def encodeCode : Machine 52 := PSTRTMSeq005.seqMachine returnCode PA17TMRatArithmeticUnblock004.markerMachine
def code : Machine 57 := PSTRTMSeq005.seqMachine encodeCode Uncapped.Steps.prefixCode

theorem integer_left (base : List Bool) (n : ℕ) :
    ratLeft base (n : Rat)=false::true::true::false::
      (PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload n).reverse++false::false::base) := by
  have zeroSign : sign (n : Rat)=false := by
    simp only [sign,decide_eq_false_iff_not]
    exact not_lt.mpr (Nat.cast_nonneg n)
  have num : numeratorDigits (n : Rat)=PSTRTMNatValue017.rawPayload n := by
    simp [numeratorDigits]
  have den : denominatorDigits (n : Rat)=[true] := by
    simp only [denominatorDigits,Rat.den_natCast]
    decide
  rw [ratLeft,bothLeft,firstLeft,firstLeft,zeroSign,num,den]
  rfl

/-- Physical RIGHT1 repair of the integer factor. The sole intervening
FALSE is consumed by the actual Den1 write. Every arbitrary WEST cell
and every suffix cell survive, including the following risk Rat. -/
theorem actual_bounded (base suffix : List Bool) (n : ℕ) :
    BoundedRun code (Tape.mk₂ (ratLeft base (n : Rat)) (false::suffix)) 57
      (Tape.mk₂ (false::base) (encodeDatum (.rational (n : Rat))++suffix))
      (128*(natBits n+1)^2) := by
  let digits:=PSTRTMNatValue017.rawPayload n
  have width : digits.length=natBits n := by
    simp only [digits,PSTRTMNatValue017.rawPayload,List.length_ofFn]
  have clamped:=clamp_bounded (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::false::base)) suffix
  have backed : BoundedRun backOneMachine
      (Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::false::base))
        (false::true::false::false::suffix)) 1
      (Tape.mk₂ (PSTRTMRawNat010.leftBlocks digits.reverse++false::false::base)
        (false::false::true::false::false::suffix)) 2 :=
    ⟨backOneTrace (PSTRTMRawNat010.leftBlocks digits.reverse++false::false::base) false
      (false::true::false::false::suffix),backOne_runsFrom _ _ _,by rfl⟩
  have rewound : BoundedRun PSTRTMMulRewind085.rewindMachine
      (Tape.mk₂ (PSTRTMRawNat010.leftBlocks digits.reverse++false::false::base)
        (false::false::true::false::false::suffix)) 3
      (Tape.mk₂ (false::false::base)
        (PSTRTMIncrement009.blocks digits++false::false::true::false::false::suffix))
      (2*digits.length+3) :=
    ⟨PSTRTMPairRewind105.fullTrace (false::base) digits.reverse (false::false::true::false::false::suffix),
      PSTRTMPairRewind105.rewind_runsFrom _ _ _,
      by rw [PSTRTMPairRewind105.full_length,List.length_reverse]⟩
  have shifted : BoundedRun NatSplice.shiftMachine
      (Tape.mk₂ (false::false::base)
        (PSTRTMIncrement009.blocks digits++false::false::true::false::false::suffix)) 9
      (Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::false::false::base))
        (false::false::false::suffix)) (4*digits.length+6) :=
    ⟨NatSplice.shiftTrace false (false::false::base) (false::false::suffix) digits,
      NatSplice.shift_runsFrom _ _ _,by rw [NatSplice.shift_length]⟩
  have planted:=plant_bounded
    (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::false::false::base)) suffix
  have returned : BoundedRun fieldBackMachine
      (Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::false::false::base))
        (false::false::true::suffix)) 5
      (Tape.mk₂ (false::false::false::base)
        (PSTRTMIncrement009.blocks digits++false::false::false::true::suffix)) (2*digits.length+5) := by
    refine ⟨fieldBackTrace (false::false::base) digits (false::false::true::suffix),?_,
      by rw [fieldBackTrace_length]⟩
    have actual:=fieldBack_runsFrom (false::false::base) digits (false::false::true::suffix)
    have lastEq : fieldBackFinal (false::false::base) digits (false::false::true::suffix)=
        (⟨5,Tape.mk₂ (false::false::false::base)
          (PSTRTMIncrement009.blocks digits++false::false::false::true::suffix)⟩ : MachineState 5) := by
      change (⟨PSTRTMSeq005.rightLabel (a:=1) (3 : Fin 4),_⟩ : MachineState 5)=_
      have labelEq : PSTRTMSeq005.rightLabel (a:=1) (3 : Fin 4)=(5 : Fin 6) := by decide
      rw [labelEq]
      rfl
    rw [lastEq] at actual
    exact actual
  have encoded : BoundedRun PA17TMRatArithmeticUnblock004.markerMachine
      (Tape.mk₂ (false::false::false::base)
        (PSTRTMIncrement009.blocks digits++false::false::false::true::suffix)) 19
      (Tape.mk₂ (false::false::false::base) (encodeNat n++true::false::true::suffix))
      (digits.length^2+11*digits.length+6) :=
    ⟨PA17TMRatArithmeticUnblock004.markerTrace (false::false::base) digits (false::true::suffix),
      PA17TMRatArithmeticUnblock004.marker_originalNat_runsFrom n (false::false::base) (false::true::suffix),
      by rw [PA17TMRatArithmeticUnblock004.marker_length]⟩
  have tagged : BoundedRun Uncapped.Steps.prefixCode
      (Tape.mk₂ (false::false::false::base) (encodeNat n++true::false::true::suffix)) 4
      (Tape.mk₂ (false::base) (encodeDatum (.rational (n : Rat))++suffix)) 5 := by
    have nonnegative : ¬(n : Rat)<0 := not_lt.mpr (Nat.cast_nonneg n)
    have datum : encodeDatum (.rational (n : Rat))++suffix=
        true::false::(encodeNat n++true::false::true::suffix) := by
      simp [encodeDatum,nonnegative,encodeNat,natBits]
    rw [datum]
    exact ⟨Uncapped.Steps.prefixTrace (false::base) false false (encodeNat n++true::false::true::suffix),
      Uncapped.Steps.prefix_runsFrom _ _ _ _,by rfl⟩
  have actual:=((((((clamped.seq backed).seq rewound).seq shifted).seq planted).seq returned).seq encoded).seq tagged
  rw [←integer_left base n] at actual
  exact actual.mono (by rw [width];nlinarith [Nat.zero_le ((natBits n)^2)])

end RootB23.Threshold.FactorGap
