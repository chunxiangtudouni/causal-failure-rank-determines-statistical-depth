module
public import Structure.RootB23_Threshold_ReturnBank_019
public import Structure.RootB23_Threshold_Window_MarshalAnchor_016

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnTraverse
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticBookmark014 PA17TMRatArithmeticFarLoad031
open PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

/-- The B-copy source is allowed to be halfway through its actual data.
Its temporary FALSE flag is part of left, rather than a reset home cursor. -/
def stored (left digits : List Bool) : List Bool := PSTRTMRawNat010.leftBlocks digits.reverse++left
def base (left digits : List Bool) : List Bool := false::stored left digits
def word (x y : Rat) (digits east : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks digits++false::false::false::ReturnBank.sourceRight x y east

def rightCode : Machine 3 := fun q _ =>
  match q.val with
  | 0=>some (1,.move .right)
  | 1=>some (2,.move .right)
  | 2=>some (3,.move .right)
  | _=>none
def rightTrace (left suffix : List Bool) (a b c : Bool) : List (MachineState 3) :=
  [⟨0,Tape.mk₂ left (a::b::c::suffix)⟩,
   ⟨1,Tape.mk₂ (a::left) (b::c::suffix)⟩,
   ⟨2,Tape.mk₂ (b::a::left) (c::suffix)⟩,
   ⟨3,Tape.mk₂ (c::b::a::left) suffix⟩]
theorem right_bounded (left suffix : List Bool) (a b c : Bool) :
    BoundedRun rightCode (Tape.mk₂ left (a::b::c::suffix)) 3
      (Tape.mk₂ (c::b::a::left) suffix) 4 := by
  refine ⟨rightTrace left suffix a b c,⟨rfl,?_,rfl,?_⟩,by rfl⟩
  · simp [rightTrace,List.isChain_cons_cons,TM0.step,rightCode,Tape.mk₂]
  · simp [TM0.step,rightCode]

def outBCode : Machine 4 := PSTRTMSeq005.seqMachine PA17TMRatArithmeticWidth018.scanMachine tagMachine
def outBankCode : Machine 15 := PSTRTMSeq005.seqMachine outBCode nxRoute.out
def outCounterEntryCode : Machine 19 := PSTRTMSeq005.seqMachine outBankCode rightCode
def outCode : Machine 35 := PSTRTMSeq005.seqMachine outCounterEntryCode MarshalAnchor.counterFourForwardMachine

theorem width_eq (x y : Rat) :
    TotalWidth.width (numeratorDigits x).tail (denominatorDigits x).tail
      (numeratorDigits y).tail (denominatorDigits y).tail=fieldWidth x y := by
  change (clampFirst (numeratorDigits x)).length+(clampFirst (denominatorDigits x)).length+
    (clampFirst (numeratorDigits y)).length+(clampFirst (denominatorDigits y)).length=fieldWidth x y
  rw [clampFirst_length _ (numerator_ne_nil x),clampFirst_length _ (denominator_ne_nil x),
    clampFirst_length _ (numerator_ne_nil y),clampFirst_length _ (denominator_ne_nil y)]
  rfl

/-- Real B EOF, three guard cells, all four bookmarked original fields,
the count-work marker and all four actual counters are crossed. The exact
permanent TRUE gap anchor is the resulting head, for arbitrary east. -/
theorem out_bounded (x y : Rat) (nonnegative : 0≤x) (left digits east : List Bool) :
    BoundedRun outCode (Tape.mk₂ left (word x y digits east)) 35
      (Tape.mk₂ (ReturnBank.innerArchive (base left digits) x y) (true::east))
      (2*digits.length+10*fieldWidth x y+48) := by
  let nx:=(numeratorDigits x).tail
  let dx:=(denominatorDigits x).tail
  let ny:=(numeratorDigits y).tail
  let dy:=(denominatorDigits y).tail
  let counter:=List.replicate (fieldWidth x y) false
  let words:=ReturnBank.counterWord counter (true::east)
  let kept:=PhysicalReserve.preservedArchive (false::base left digits) nx dx ny dy
  have scan : BoundedRun PA17TMRatArithmeticWidth018.scanMachine (Tape.mk₂ left (word x y digits east)) 1
      (Tape.mk₂ (false::stored left digits) (false::false::ReturnBank.sourceRight x y east))
      (2*digits.length+2) :=
    ⟨PA17TMRatArithmeticWidth018.scanTrace left digits false (false::ReturnBank.sourceRight x y east),
      PA17TMRatArithmeticWidth018.scan_runsFrom _ _ _ _,by rw [PA17TMRatArithmeticWidth018.scanTrace_length]⟩
  have two : BoundedRun tagMachine
      (Tape.mk₂ (false::stored left digits) (false::false::ReturnBank.sourceRight x y east)) 2
      (Tape.mk₂ (false::false::false::stored left digits) (ReturnBank.sourceRight x y east)) 3 :=
    ⟨tagTrace (false::stored left digits) false false (ReturnBank.sourceRight x y east),
      tag_runsFrom _ _ _ _,by rfl⟩
  have routes:=nx_route_correct dx ny dy
  have bank:=routes.out_run (false::false::false::stored left digits) (false::nx) (true::false::words)
  have three:=right_bounded (nxFinish dx ny dy (false::false::false::stored left digits) (false::nx)) words false true false
  have counters:=MarshalAnchor.counterFourForward_bounded kept counter (true::east)
  have counterStage : BoundedRun MarshalAnchor.counterFourForwardMachine
      (Tape.mk₂ (false::true::false::nxFinish dx ny dy
        (false::false::false::stored left digits) (false::nx)) words) 15
      (Tape.mk₂ (false::counterArchive kept counter 4) (true::east)) (8*counter.length+16) := by
    simpa only [kept,PhysicalReserve.preservedArchive,TotalWidth.bankLeft,base,
      words,ReturnBank.counterWord,List.append_assoc] using counters
  have actual:=(((scan.seq two).seq bank).seq three).seq counterStage
  have port : PSTRTMSeq005.rightLabel (a:=19) (15 : Fin 16)=(35 : Fin 36) := by decide
  rw [port] at actual
  have zeroSign : sign x=false := by
    simp only [sign,decide_eq_false_iff_not]
    exact not_lt.mpr nonnegative
  have widths:=width_eq x y
  have fee : (2*digits.length+2)+3+(2*(false::nx).length+TotalWidth.numCost dx ny dy)+4+
      (8*counter.length+16)≤2*digits.length+10*fieldWidth x y+48 := by
    simp only [counter,List.length_replicate,TotalWidth.numCost]
    change (false::nx).length+(false::dx).length+(false::ny).length+(false::dy).length=fieldWidth x y at widths
    omega
  simpa only [outCode,outCounterEntryCode,outBankCode,outBCode,ReturnBank.innerArchive,
    ReturnBank.sourceRight,ReturnBank.counterWord,PhysicalReserve.preservedArchive,TotalWidth.bankLeft,
    kept,words,counter,base,nx,dx,ny,dy,zeroSign,List.append_assoc] using actual.mono fee

/-- The same fixed backward table also stops at the actual temporary
FALSE flag inside B. It does not assume that the source cursor is home. -/
theorem back_bounded (x y : Rat) (nonnegative : 0≤x) (archive digits east : List Bool) :
    BoundedRun ReturnBank.code
      (Tape.mk₂ (ReturnBank.innerArchive (base (false::archive) digits) x y) (true::east)) 70
      (Tape.mk₂ (false::archive) (word x y digits east))
      (10*fieldWidth x y+2*digits.length+64) := by
  let nx:=(numeratorDigits x).tail
  let dx:=(denominatorDigits x).tail
  let ny:=(numeratorDigits y).tail
  let dy:=(denominatorDigits y).tail
  let counter:=List.replicate (fieldWidth x y) false
  let kept:=PhysicalReserve.preservedArchive (false::base (false::archive) digits) nx dx ny dy
  let words:=ReturnBank.counterWord counter (true::east)
  have counters:=counterFourBack_bounded kept counter (true::east)
  have fromBank:=CountAppend.fromDestination_bounded
    (TotalWidth.bankLeft (false::base (false::archive) digits) nx dx ny dy) words
  have routes:=nx_route_correct dx ny dy
  have source:=routes.back_run (false::base (false::archive) digits) (false::nx) (true::false::words)
  have three:=ReturnBank.left_bounded (stored (false::archive) digits) (ReturnBank.sourceRight x y east)
  have rewind : BoundedRun PSTRTMMulRewind085.rewindMachine
      (Tape.mk₂ (stored (false::archive) digits) (false::false::false::ReturnBank.sourceRight x y east)) 3
      (Tape.mk₂ (false::archive) (word x y digits east)) (2*digits.length+3) :=
    ⟨PSTRTMPairRewind105.fullTrace archive digits.reverse (false::false::false::ReturnBank.sourceRight x y east),
      PSTRTMPairRewind105.rewind_runsFrom _ _ _,by rw [PSTRTMPairRewind105.full_length,List.length_reverse]⟩
  have actual:=(((counters.seq fromBank).seq source).seq three).seq rewind
  have port : PSTRTMSeq005.rightLabel (a:=66) (3 : Fin 4)=(70 : Fin 71) := by decide
  rw [port] at actual
  have zeroSign : sign x=false := by
    simp only [sign,decide_eq_false_iff_not]
    exact not_lt.mpr nonnegative
  have widths:=width_eq x y
  have fee : (8*counter.length+28)+4+(2*(false::nx).length+TotalWidth.numCost dx ny dy)+4+
      (2*digits.length+3)≤10*fieldWidth x y+2*digits.length+64 := by
    simp only [counter,List.length_replicate,TotalWidth.numCost]
    change (false::nx).length+(false::dx).length+(false::ny).length+(false::dy).length=fieldWidth x y at widths
    omega
  simpa only [ReturnBank.code,ReturnBank.eofCode,ReturnBank.sourceCode,ReturnBank.counterBankCode,
    ReturnBank.innerArchive,kept,words,counter,base,nx,dx,ny,dy,zeroSign,List.append_assoc]
    using actual.mono fee

theorem base_cons (left digits : List Bool) (bit : Bool) :
    base (true::bit::left) digits=base left (bit::digits) := by
  simp [base,stored,PSTRTMRawNat010.leftBlocks,List.reverse_cons,List.flatMap_append,List.append_assoc]

end RootB23.Threshold.ReturnTraverse
