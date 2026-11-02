module
public import Structure.RootB23_Threshold_FactorSource_003
public import Common.PSTR_TM_ThresholdCursor_115
public import Common.PSTR_TM_ThresholdCounterSeek_169

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.FactorWalk
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002

def markedLeft (left digits : List Bool) : List Bool :=
  false::true::false::false::(PSTRTMRawNat010.leftBlocks digits.reverse++left)
def marker (suffix : List Bool) : List Bool := false::false::true::false::suffix
def sourceSkipCode : Machine 5 := PSTRTMSeq005.seqMachine PSTRTMThresholdCursor115.cursorMachine tagMachine

theorem source_skip (left digits suffix : List Bool) :
    BoundedRun sourceSkipCode (Tape.mk₂ left (PSTRTMIncrement009.blocks digits++marker suffix)) 5
      (Tape.mk₂ (markedLeft left digits) suffix) (2*digits.length+6) := by
  have scan : BoundedRun PSTRTMThresholdCursor115.cursorMachine
      (Tape.mk₂ left (PSTRTMIncrement009.blocks digits++marker suffix)) 2
      (Tape.mk₂ (false::false::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) (true::false::suffix))
      (2*digits.length+3) :=
    ⟨PSTRTMThresholdCursor115.cursorTrace left digits (true::false::suffix),
      PSTRTMThresholdCursor115.cursor_runsFrom _ _ _,by rw [PSTRTMThresholdCursor115.cursor_length]⟩
  have two : BoundedRun tagMachine
      (Tape.mk₂ (false::false::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) (true::false::suffix)) 2
      (Tape.mk₂ (markedLeft left digits) suffix) 3 :=
    ⟨tagTrace _ true false suffix,tag_runsFrom _ true false suffix,by rfl⟩
  exact (scan.seq two).mono (by omega)

def bBase (left depth b : List Bool) (gap : ℕ) : List Bool :=
  PSTRTMRawNat010.leftBlocks b.reverse++List.replicate (2*gap+2) false++
    (PSTRTMRawNat010.leftBlocks depth.reverse++left)
def bRight (b : List Bool) (q : Rat) (suffix : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks b++encodeDatum (.rational q)++false::suffix
def depthRight (depth b : List Bool) (gap : ℕ) (q : Rat) (suffix : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks depth++List.replicate (2*gap+2) false++bRight b q suffix

def depthSeekCode : Machine 5 := PSTRTMSeq005.seqMachine
  PSTRTMThresholdCursor115.cursorMachine PSTRTMThresholdCounterSeek169.seekMachine
def bScanCode : Machine 7 := PSTRTMSeq005.seqMachine depthSeekCode PA17TMRatArithmeticWidth018.scanMachine
def factorEntryCode : Machine 9 := PSTRTMSeq005.seqMachine bScanCode backOneMachine
def commonCode : Machine 55 := PSTRTMSeq005.seqMachine factorEntryCode ratMachine
def denCode : Machine 61 := PSTRTMSeq005.seqMachine sourceSkipCode commonCode
def numCode : Machine 67 := PSTRTMSeq005.seqMachine sourceSkipCode denCode

private theorem parse_cost (n d : ℕ) : n^2+d^2+9*(n+d)+11 ≤ 64*(n+d+1)^2 := by
  nlinarith only [Nat.zero_le (n^2),Nat.zero_le (d^2),Nat.zero_le (n*d)]

theorem rational_scan (left suffix : List Bool) (q : Rat) :
    BoundedRun ratMachine (Tape.mk₂ left (encodeDatum (.rational q)++suffix)) 45
      (Tape.mk₂ (ratLeft left q) suffix) (64*(natBits q.num.natAbs+natBits q.den+1)^2) := by
  have endpoint : ratFinal left (sign q) (numeratorDigits q) (denominatorDigits q) suffix=
      (⟨45,Tape.mk₂ (ratLeft left q) suffix⟩ : MachineState 45) := by
    change (⟨PSTRTMSeq005.rightLabel (a:=9)
      (PSTRTMSeq005.rightLabel (a:=17) (17 : Fin 18)),_⟩ : MachineState 45)=_
    have labelEq : PSTRTMSeq005.rightLabel (a:=9)
        (PSTRTMSeq005.rightLabel (a:=17) (17 : Fin 18))=(45 : Fin 46) := by decide
    rw [labelEq]
    rfl
  refine ⟨ratTrace left (sign q) (numeratorDigits q) (denominatorDigits q) suffix,?_,?_⟩
  · rw [←endpoint]
    exact encodeDatum_rat_runsFrom left suffix q
  · rw [ratTrace_length,numeratorDigits_length,denominatorDigits_length]
    exact parse_cost _ _

/-- Real forward route through the exhausted depth, every aligned gap
pair and the saved B field. B's first DATA bit may be either Boolean.
The factor Rat is parsed physically; the inverse route will restore it. -/
theorem common_bounded (left depth b suffix : List Bool) (gap : ℕ) (q : Rat)
    (nonnegative : 0 ≤ q) (nonempty : b≠[]) :
    BoundedRun commonCode (Tape.mk₂ left (depthRight depth b gap q suffix)) 55
      (Tape.mk₂ (ratLeft (bBase left depth b gap) q) (false::suffix))
      (2*depth.length+2*gap+2*b.length+64*(natBits q.num.natAbs+natBits q.den+1)^2+10) := by
  cases b with
  | nil => exact False.elim (nonempty rfl)
  | cons bit later =>
    have zeroSign : sign q=false := by
      simp only [sign,decide_eq_false_iff_not]
      exact not_lt.mpr nonnegative
    have datum : encodeDatum (.rational q)=true::false::(encodeNat q.num.natAbs++encodeNat q.den) := by
      rw [encodeDatum,show decide (q<0)=false from zeroSign]
      rfl
    let depthLeft:=false::false::(PSTRTMRawNat010.leftBlocks depth.reverse++left)
    have gapEq : List.replicate (2*gap+2) false=false::false::PSTRTMThresholdCounterSeek169.gaps gap := by
      rw [PSTRTMThresholdCounterSeek169.gaps_replicate,
        show 2*gap+2=2+2*gap by omega,List.replicate_add]
      rfl
    have first : BoundedRun PSTRTMThresholdCursor115.cursorMachine
        (Tape.mk₂ left (depthRight depth (bit::later) gap q suffix)) 2
        (Tape.mk₂ depthLeft (PSTRTMThresholdCounterSeek169.gaps gap++bRight (bit::later) q suffix))
        (2*depth.length+3) := by
      rw [depthRight,gapEq]
      refine ⟨PSTRTMThresholdCursor115.cursorTrace left depth
        (PSTRTMThresholdCounterSeek169.gaps gap++bRight (bit::later) q suffix),?_,
        by rw [PSTRTMThresholdCursor115.cursor_length]⟩
      simpa only [PSTRTMThresholdCursor115.state,depthLeft,List.append_assoc,List.cons_append] using
        PSTRTMThresholdCursor115.cursor_runsFrom left depth
          (PSTRTMThresholdCounterSeek169.gaps gap++bRight (bit::later) q suffix)
    have seek : BoundedRun PSTRTMThresholdCounterSeek169.seekMachine
        (Tape.mk₂ depthLeft (PSTRTMThresholdCounterSeek169.gaps gap++bRight (bit::later) q suffix)) 2
        (Tape.mk₂ (PSTRTMThresholdCounterSeek169.gapLeft gap depthLeft) (bRight (bit::later) q suffix))
        (2*gap+3) :=
      ⟨PSTRTMThresholdCounterSeek169.seekTrace bit (PSTRTMIncrement009.blocks later++encodeDatum (.rational q)++false::suffix) gap depthLeft,
        PSTRTMThresholdCounterSeek169.seek_runsFrom _ _ _ _,by rw [PSTRTMThresholdCounterSeek169.seek_length]⟩
    have gapLeftEq : PSTRTMThresholdCounterSeek169.gapLeft gap depthLeft=
        List.replicate (2*gap+2) false++(PSTRTMRawNat010.leftBlocks depth.reverse++left) := by
      rw [PSTRTMThresholdCounterSeek169.gapLeft_eq,PSTRTMThresholdCounterSeek169.gaps_replicate]
      rw [List.replicate_add]
      simp only [depthLeft,List.append_assoc,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
    have scanned : BoundedRun PA17TMRatArithmeticWidth018.scanMachine
        (Tape.mk₂ (PSTRTMThresholdCounterSeek169.gapLeft gap depthLeft) (bRight (bit::later) q suffix)) 1
        (Tape.mk₂ (true::bBase left depth (bit::later) gap) (false::(encodeNat q.num.natAbs++encodeNat q.den++false::suffix)))
        (2*(bit::later).length+2) := by
      have raw:=PA17TMRatArithmeticWidth018.scan_runsFrom
        (PSTRTMThresholdCounterSeek169.gapLeft gap depthLeft) (bit::later) true
        (encodeNat q.num.natAbs++encodeNat q.den++false::suffix)
      refine ⟨PA17TMRatArithmeticWidth018.scanTrace
        (PSTRTMThresholdCounterSeek169.gapLeft gap depthLeft) (bit::later) true
        (encodeNat q.num.natAbs++encodeNat q.den++false::suffix),?_,
        by rw [PA17TMRatArithmeticWidth018.scanTrace_length]⟩
      simpa only [bRight,datum,List.append_assoc,List.cons_append,List.nil_append,gapLeftEq,bBase,
        PA17TMRatArithmeticWidth018.scanState] using raw
    have back : BoundedRun backOneMachine
        (Tape.mk₂ (true::bBase left depth (bit::later) gap) (false::(encodeNat q.num.natAbs++encodeNat q.den++false::suffix))) 1
        (Tape.mk₂ (bBase left depth (bit::later) gap) (encodeDatum (.rational q)++false::suffix)) 2 := by
      refine ⟨backOneTrace (bBase left depth (bit::later) gap) true
        (false::(encodeNat q.num.natAbs++encodeNat q.den++false::suffix)),?_,by rfl⟩
      simpa only [datum,List.cons_append,List.append_assoc,cursorState] using
        backOne_runsFrom (bBase left depth (bit::later) gap) true
          (false::(encodeNat q.num.natAbs++encodeNat q.den++false::suffix))
    have parsed:=rational_scan (bBase left depth (bit::later) gap) (false::suffix) q
    exact ((((first.seq seek).seq scanned).seq back).seq parsed).mono (by omega)

def denRight (den depth b : List Bool) (gap : ℕ) (q : Rat) (suffix : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks den++marker (depthRight depth b gap q suffix)
def numRight (num den depth b : List Bool) (gap : ℕ) (q : Rat) (suffix : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks num++marker (denRight den depth b gap q suffix)

theorem denominator_bounded (left den depth b suffix : List Bool) (gap : ℕ) (q : Rat)
    (nonnegative : 0 ≤ q) (nonempty : b≠[]) :
    BoundedRun denCode (Tape.mk₂ left (denRight den depth b gap q suffix)) 61
      (Tape.mk₂ (ratLeft (bBase (markedLeft left den) depth b gap) q) (false::suffix))
      (2*den.length+2*depth.length+2*gap+2*b.length+64*(natBits q.num.natAbs+natBits q.den+1)^2+16) := by
  have source:=source_skip left den (depthRight depth b gap q suffix)
  have later:=common_bounded (markedLeft left den) depth b suffix gap q nonnegative nonempty
  exact (source.seq later).mono (by omega)

theorem numerator_bounded (left num den depth b suffix : List Bool) (gap : ℕ) (q : Rat)
    (nonnegative : 0 ≤ q) (nonempty : b≠[]) :
    BoundedRun numCode (Tape.mk₂ left (numRight num den depth b gap q suffix)) 67
      (Tape.mk₂ (ratLeft (bBase (markedLeft (markedLeft left num) den) depth b gap) q) (false::suffix))
      (2*num.length+2*den.length+2*depth.length+2*gap+2*b.length+64*(natBits q.num.natAbs+natBits q.den+1)^2+22) := by
  have source:=source_skip left num (denRight den depth b gap q suffix)
  have later:=denominator_bounded (markedLeft left num) den depth b suffix gap q nonnegative nonempty
  exact (source.seq later).mono (by omega)

end RootB23.Threshold.FactorWalk
