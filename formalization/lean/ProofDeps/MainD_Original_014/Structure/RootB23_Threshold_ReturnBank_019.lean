module
public import Structure.RootB23_Threshold_Window_PhysicalReserve_014
public import Structure.RootB23_Threshold_BarePacket_017

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnBank
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticBookmark014 PA17TMRatArithmeticFarLoad031
open PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

def innerArchive (base : List Bool) (x y : Rat) : List Bool :=
  false::counterArchive
    (PhysicalReserve.preservedArchive (sign x::base) (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail) (List.replicate (fieldWidth x y) false) 4
def archive (base : List Bool) (x y : Rat) : List Bool := true::innerArchive base x y
def counterWord (digits suffix : List Bool) : List Bool :=
  PA17TMRatArithmeticCopy006.workspace digits++PA17TMRatArithmeticCopy006.workspace digits++
    PA17TMRatArithmeticCopy006.workspace digits++PA17TMRatArithmeticCopy006.workspace digits++suffix
def sourceRight (x y : Rat) (east : List Bool) : List Bool :=
  fieldWord (nxContext (denominatorDigits x).tail (numeratorDigits y).tail (denominatorDigits y).tail)
    (false::(numeratorDigits x).tail)
    (true::false::counterWord (List.replicate (fieldWidth x y) false) (true::east))

def leftCode : Machine 3 := CountAppend.fromDestinationMachine
def leftTrace (left word : List Bool) : List (MachineState 3) :=
  [⟨0,Tape.mk₂ (false::false::false::left) word⟩,
   ⟨1,Tape.mk₂ (false::false::left) (false::word)⟩,
   ⟨2,Tape.mk₂ (false::left) (false::false::word)⟩,
   ⟨3,Tape.mk₂ left (false::false::false::word)⟩]
theorem left_bounded (left word : List Bool) :
    BoundedRun leftCode (Tape.mk₂ (false::false::false::left) word) 3
      (Tape.mk₂ left (false::false::false::word)) 4 := by
  refine ⟨leftTrace left word,⟨rfl,?_,rfl,?_⟩,by rfl⟩
  · simp [leftTrace,List.isChain_cons_cons,TM0.step,leftCode,CountAppend.fromDestinationMachine,Tape.mk₂]
  · simp [TM0.step,leftCode,CountAppend.fromDestinationMachine]

def counterBankCode : Machine 35 := PSTRTMSeq005.seqMachine counterFourBackMachine CountAppend.fromDestinationMachine
def sourceCode : Machine 62 := PSTRTMSeq005.seqMachine counterBankCode nxRoute.back
def eofCode : Machine 66 := PSTRTMSeq005.seqMachine sourceCode leftCode
def code : Machine 70 := PSTRTMSeq005.seqMachine eofCode PSTRTMMulRewind085.rewindMachine

def originalSource (risk : Rat) : List Bool :=
  FactorWalk.markedLeft (FactorWalk.markedLeft [false] (PSTRTMThresholdRiskSource233.numerator risk))
    (PSTRTMThresholdRiskSource233.denominator risk)
def bArchive (risk : Rat) (depth : ℕ) : List Bool :=
  List.replicate (2*(PSTRTMThresholdBBackupEntry188.result risk depth).gap+1) false++
    (PSTRTMRawNat010.leftBlocks (PSTRTMThresholdBBackupEntry188.result risk depth).depth.reverse++originalSource risk)
def bRight (risk : Rat) (depth : ℕ) (y : Rat) (east : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks (FactorSource.bDigits risk depth)++false::false::false::
    sourceRight (FactorSource.factorValue risk depth : Rat) y east

private theorem width_eq (x y : Rat) :
    TotalWidth.width (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=fieldWidth x y := by
  change (clampFirst (numeratorDigits x)).length+(clampFirst (denominatorDigits x)).length+
    (clampFirst (numeratorDigits y)).length+(clampFirst (denominatorDigits y)).length=fieldWidth x y
  rw [clampFirst_length _ (numerator_ne_nil x),clampFirst_length _ (denominator_ne_nil x),
    clampFirst_length _ (numerator_ne_nil y),clampFirst_length _ (denominator_ne_nil y)]
  rfl

/-- The true gap anchor is physically crossed, then the four retained
equal counters and the bookmarked original bank are actually rewound.
Three real LEFTs and a real flagged rewind finally enter the ORIGINAL B,
preserving every arbitrary east cell containing the actual cap result. -/
theorem actual_bounded (risk : Rat) (depth : ℕ) (y : Rat) (east : List Bool) :
    BoundedRun code
      (Tape.mk₂ (innerArchive (BarePacket.west risk depth) (FactorSource.factorValue risk depth : Rat) y)
        (true::east)) 70
      (Tape.mk₂ (false::bArchive risk depth) (bRight risk depth y east))
      (10*fieldWidth (FactorSource.factorValue risk depth : Rat) y+
        2*(FactorSource.bDigits risk depth).length+64) := by
  let x:=(FactorSource.factorValue risk depth : Rat)
  let base:=BarePacket.west risk depth
  let nx:=(numeratorDigits x).tail
  let dx:=(denominatorDigits x).tail
  let ny:=(numeratorDigits y).tail
  let dy:=(denominatorDigits y).tail
  let digits:=List.replicate (fieldWidth x y) false
  let kept:=PhysicalReserve.preservedArchive (false::base) nx dx ny dy
  let words:=counterWord digits (true::east)
  have counters:=counterFourBack_bounded kept digits (true::east)
  have fromBank:=CountAppend.fromDestination_bounded (TotalWidth.bankLeft (false::base) nx dx ny dy) words
  have routes:=nx_route_correct dx ny dy
  have source:=routes.back_run (false::base) (false::nx) (true::false::words)
  have zeroSign : sign x=false := by
    simp only [sign,decide_eq_false_iff_not]
    exact not_lt.mpr (Nat.cast_nonneg (FactorSource.factorValue risk depth))
  let stored:=FactorWalk.bBase (originalSource risk)
    (PSTRTMThresholdBBackupEntry188.result risk depth).depth (FactorSource.bDigits risk depth)
    (PSTRTMThresholdBBackupEntry188.result risk depth).gap
  have three:=left_bounded stored (sourceRight x y east)
  have sourceTape : false::false::base=false::false::false::stored := rfl
  rw [sourceTape] at source
  have bShape : stored=PSTRTMRawNat010.leftBlocks (FactorSource.bDigits risk depth).reverse++false::bArchive risk depth := by
    dsimp only [stored,FactorWalk.bBase,bArchive]
    rw [show 2*(PSTRTMThresholdBBackupEntry188.result risk depth).gap+2=
      1+(2*(PSTRTMThresholdBBackupEntry188.result risk depth).gap+1) by omega,List.replicate_add]
    simp only [List.append_assoc,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
  have rewind : BoundedRun PSTRTMMulRewind085.rewindMachine
      (Tape.mk₂ stored (false::false::false::sourceRight x y east)) 3
      (Tape.mk₂ (false::bArchive risk depth) (bRight risk depth y east))
      (2*(FactorSource.bDigits risk depth).length+3) := by
    rw [bShape]
    exact ⟨PSTRTMPairRewind105.fullTrace (bArchive risk depth) (FactorSource.bDigits risk depth).reverse
      (false::false::false::sourceRight x y east),PSTRTMPairRewind105.rewind_runsFrom _ _ _,
      by rw [PSTRTMPairRewind105.full_length,List.length_reverse]⟩
  have actual:=(((counters.seq fromBank).seq source).seq three).seq rewind
  have port : PSTRTMSeq005.rightLabel (a:=66) (3 : Fin 4)=(70 : Fin 71) := by decide
  rw [port] at actual
  have widths:=width_eq x y
  have fee : (8*digits.length+28)+4+(2*(false::nx).length+TotalWidth.numCost dx ny dy)+4+
      (2*(FactorSource.bDigits risk depth).length+3)≤
      10*fieldWidth x y+2*(FactorSource.bDigits risk depth).length+64 := by
    simp only [digits,List.length_replicate,TotalWidth.numCost]
    change (false::nx).length+(false::dx).length+(false::ny).length+(false::dy).length=fieldWidth x y at widths
    omega
  simpa only [code,eofCode,sourceCode,counterBankCode,innerArchive,kept,digits,
    nx,dx,ny,dy,base,x,zeroSign] using actual.mono fee

end RootB23.Threshold.ReturnBank
