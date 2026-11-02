module
public import Structure.RootB23_Threshold_ReturnScratch_025
public import Structure.RootB23_Threshold_ReturnActual_022

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnRoute
open PaperProofs.Common.Native.RationalControllerComputation Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002

def markedNum (q : Rat) : List Bool := true::(ReturnAnchor.numerator q).tail
def blank (q : Rat) (left : ℕ) : ℕ := left-(PSTRTMThresholdBReblock195.savedLeft q 1).length
def scratchLeft (q : Rat) : List Bool := ReturnScratch.oldLeft (markedNum q) (ReturnAnchor.denominator q)
  (PSTRTMThresholdBBackupEntry188.result q 1).depth (ReturnAnchor.bDigits q)
  (PSTRTMThresholdBBackupEntry188.result q 1).gap
def result : Bool → Rat → Rat
  | false,q=>q
  | true,_=>(1/4 : Rat)
def bridge : Bool → Rat → ℕ → List Bool
  | false,_,left=>List.replicate left false
  | true,q,left=>List.replicate (blank q left) false++false::ReturnAnchor.markedSourceRight q []
def east (capped : Bool) (q : Rat) (left : ℕ) (suffix : List Bool) : List Bool :=
  bridge capped q left++(encodeDatum (.rational (result capped q))++false::suffix)
def nearLeft : Bool → Rat → ℕ → List Bool → List Bool
  | false,_,left,archive=>List.replicate left false++archive
  | true,q,left,archive=>scratchLeft q++(List.replicate (blank q left) false++archive)
def context (capped : Bool) (x y q : Rat) (left : ℕ) : List Bool :=
  false::false::ReturnBank.sourceRight x y (bridge capped q left++encodeDatum (.rational (result capped q)))
def finish (capped : Bool) (x y q : Rat) (left : ℕ) (sourceLeft digits : List Bool) : List Bool :=
  ratLeft (nearLeft capped q left (ReturnBank.archive (ReturnTraverse.base sourceLeft digits) x y)) (result capped q)
def scratchFee (q : Rat) : ℕ :=
  2*(ReturnAnchor.bDigits q).length+2*(PSTRTMThresholdBBackupEntry188.result q 1).gap+
  2*(PSTRTMThresholdBBackupEntry188.result q 1).depth.length+
  2*((markedNum q).length+(ReturnAnchor.denominator q).length)+40
def restoreFee (capped : Bool) (q : Rat) : ℕ :=
  128*(natBits (result capped q).num.natAbs+natBits (result capped q).den+1)^2
def cost (capped : Bool) (x y q : Rat) (left : ℕ) : ℕ :=
  10*fieldWidth x y+left+scratchFee q+restoreFee capped q+256

def anchorCode : Machine 37 := PSTRTMSeq005.seqMachine ReturnTraverse.outCode
  (PA17TMRatArithmeticAllocate013.gapSeekMachine .right)
def outFalseCode : Machine 83 := PSTRTMSeq005.seqMachine anchorCode ratMachine
def outTruePrefixCode : Machine 67 := PSTRTMSeq005.seqMachine anchorCode ReturnScratch.outCode
def outTrueCode : Machine 113 := PSTRTMSeq005.seqMachine outTruePrefixCode ratMachine
def backFalsePrefixCode : Machine 62 := PSTRTMSeq005.seqMachine FactorBack.restoreCode ReturnAnchor.falseCode
def backFalseCode : Machine 133 := PSTRTMSeq005.seqMachine backFalsePrefixCode ReturnBank.code
def backTruePrefixCode : Machine 97 := PSTRTMSeq005.seqMachine FactorBack.restoreCode ReturnScratch.backCode
def backTrueCode : Machine 168 := PSTRTMSeq005.seqMachine backTruePrefixCode ReturnBank.code
def out : Bool → Machine 192
  | false=>padMachine (by decide : 83≤192) outFalseCode
  | true=>padMachine (by decide : 113≤192) outTrueCode
def back : Bool → Machine 192
  | false=>padMachine (by decide : 133≤192) backFalseCode
  | true=>padMachine (by decide : 168≤192) backTrueCode
def outPort : Bool → Fin 193
  | false=>padLabel (by decide : 83≤192) 83
  | true=>padLabel (by decide : 113≤192) 113
def backPort : Bool → Fin 193
  | false=>padLabel (by decide : 133≤192) 133
  | true=>padLabel (by decide : 168≤192) 168

theorem source_word (capped : Bool) (x y q : Rat) (left : ℕ) (digits suffix : List Bool) :
    RoutedCopy.fieldWord (context capped x y q left) digits suffix=
      ReturnTraverse.word x y digits (east capped q left suffix) := by
  simp only [RoutedCopy.fieldWord,context,ReturnTraverse.word,east,ReturnBank.sourceRight,
    ReturnBank.counterWord,PA17TMRatArithmeticFarLoad031.fieldWord,List.append_assoc,List.cons_append]

theorem true_east (q : Rat) (left : ℕ) (suffix : List Bool) :
    east true q left suffix=List.replicate (blank q left) false++false::
      ReturnScratch.word (markedNum q) (ReturnAnchor.denominator q)
        (PSTRTMThresholdBBackupEntry188.result q 1).depth (ReturnAnchor.bDigits q)
        (PSTRTMThresholdBBackupEntry188.result q 1).gap
        (PSTRTMThresholdCapLiteral242.quarterBits++false::suffix) := by
  rw [PSTRTMThresholdCapLiteral242.quarter_codec]
  simp only [east,bridge,result,ReturnAnchor.markedSourceRight,ReturnAnchor.depthRight,
    ReturnScratch.word,ReturnScratch.depthWord,markedNum,FactorWalk.marker,
    PSTRTMThresholdRiskMarkers232.markerTail,List.append_assoc,List.cons_append,List.nil_append]

theorem markedGap_bounded (archive word : List Bool) (head : word=true::word.tail) (gap : ℕ) :
    BoundedRun (PA17TMRatArithmeticAllocate013.gapSeekMachine .right)
      (Tape.mk₂ archive (true::(List.replicate gap false++false::word))) 1
      (Tape.mk₂ (false::(List.replicate gap false++true::archive)) word) (gap+3) := by
  have actual : BoundedRun (PA17TMRatArithmeticAllocate013.gapSeekMachine .right)
      (Tape.mk₂ archive (true::(List.replicate (gap+1) false++true::word.tail))) 1
      (Tape.mk₂ (List.replicate (gap+1) false++true::archive) (true::word.tail)) (gap+1+2) :=
    ⟨PA17TMRatArithmeticAllocate013.forwardGapTrace (gap+1) archive word.tail,
      PA17TMRatArithmeticAllocate013.forwardGap_runsFrom _ _ _,
      by rw [PA17TMRatArithmeticAllocate013.forwardGap_length]⟩
  have startWord : List.replicate (gap+1) false++true::word.tail=List.replicate gap false++false::word := by
    rw [List.replicate_succ']
    simp only [List.append_assoc,List.singleton_append,←head]
  have lastLeft : List.replicate (gap+1) false++true::archive=false::(List.replicate gap false++true::archive) := by
    rw [List.replicate_succ]
    rfl
  rw [startWord,lastLeft,←head] at actual
  exact actual.mono (by omega)

theorem outFalse_bounded (x y q : Rat) (nonnegative : 0≤x) (left : ℕ) (sourceLeft digits suffix : List Bool) :
    BoundedRun outFalseCode
      (Tape.mk₂ sourceLeft (RoutedCopy.fieldWord (context false x y q left) digits suffix)) 83
      (Tape.mk₂ (finish false x y q left sourceLeft digits) (false::suffix))
      (2*digits.length+cost false x y q left) := by
  let arc:=ReturnBank.innerArchive (ReturnTraverse.base sourceLeft digits) x y
  let value:=encodeDatum (.rational q)++false::suffix
  have valueHead : value=true::value.tail := rfl
  have first:=ReturnTraverse.out_bounded x y nonnegative sourceLeft digits (east false q left suffix)
  have seek : BoundedRun (PA17TMRatArithmeticAllocate013.gapSeekMachine .right)
      (Tape.mk₂ arc (true::(List.replicate left false++value))) 1
      (Tape.mk₂ (List.replicate left false++true::arc) value) (left+2) := by
    have actual : BoundedRun (PA17TMRatArithmeticAllocate013.gapSeekMachine .right)
        (Tape.mk₂ arc (true::(List.replicate left false++true::value.tail))) 1
        (Tape.mk₂ (List.replicate left false++true::arc) (true::value.tail)) (left+2) :=
      ⟨PA17TMRatArithmeticAllocate013.forwardGapTrace left arc value.tail,
        PA17TMRatArithmeticAllocate013.forwardGap_runsFrom _ _ _,
        by rw [PA17TMRatArithmeticAllocate013.forwardGap_length]⟩
    rw [←valueHead] at actual
    exact actual
  have parsed:=FactorWalk.rational_scan (List.replicate left false++true::arc) (false::suffix) q
  have actual:=(first.seq seek).seq parsed
  have port : PSTRTMSeq005.rightLabel (a:=37) (45 : Fin 46)=(83 : Fin 84) := by decide
  rw [port] at actual
  rw [source_word]
  simpa only [outFalseCode,anchorCode,finish,nearLeft,result,ReturnBank.archive,arc] using
    actual.mono (by dsimp only [cost,restoreFee,result];omega)

theorem outTrue_bounded (x y q : Rat) (nonnegative : 0≤x) (left : ℕ) (sourceLeft digits suffix : List Bool) :
    BoundedRun outTrueCode
      (Tape.mk₂ sourceLeft (RoutedCopy.fieldWord (context true x y q left) digits suffix)) 113
      (Tape.mk₂ (finish true x y q left sourceLeft digits) (false::suffix))
      (2*digits.length+cost true x y q left) := by
  let arc:=ReturnBank.innerArchive (ReturnTraverse.base sourceLeft digits) x y
  let num:=markedNum q
  let den:=ReturnAnchor.denominator q
  let dep:=(PSTRTMThresholdBBackupEntry188.result q 1).depth
  let b:=ReturnAnchor.bDigits q
  let gap:=(PSTRTMThresholdBBackupEntry188.result q 1).gap
  let tail:=encodeDatum (.rational (1/4 : Rat))++false::suffix
  let source:=ReturnScratch.word num den dep b gap tail
  have sourceHead : source=true::source.tail := rfl
  have first:=ReturnTraverse.out_bounded x y nonnegative sourceLeft digits (east true q left suffix)
  rw [true_east,PSTRTMThresholdCapLiteral242.quarter_codec] at first
  have seek:=markedGap_bounded arc source sourceHead (blank q left)
  have bNonempty : b≠[] := PSTRTMThresholdUnitColumnsCost160.rawPayload_ne_nil _
  have crossed:=ReturnScratch.out_bounded (List.replicate (blank q left) false++true::arc)
    num den dep b (false::suffix) gap bNonempty
  rw [PSTRTMThresholdCapLiteral242.quarter_codec] at crossed
  have parsed:=FactorWalk.rational_scan
    (scratchLeft q++(List.replicate (blank q left) false++true::arc)) (false::suffix) (1/4 : Rat)
  have actual:=((first.seq seek).seq crossed).seq parsed
  have port : PSTRTMSeq005.rightLabel (a:=67) (45 : Fin 46)=(113 : Fin 114) := by decide
  rw [port] at actual
  rw [source_word,true_east,PSTRTMThresholdCapLiteral242.quarter_codec]
  have small : blank q left≤left := Nat.sub_le _ _
  simpa only [outTrueCode,outTruePrefixCode,anchorCode,finish,nearLeft,result,ReturnBank.archive,
    arc,List.append_assoc] using actual.mono (b:=2*digits.length+cost true x y q left)
      (by dsimp only [cost,scratchFee,restoreFee,result,num,den,dep,b,gap];omega)

theorem backFalse_bounded (x y q : Rat) (nonnegative : 0≤x) (qNonnegative : 0≤q)
    (left : ℕ) (archive digits suffix : List Bool) :
    BoundedRun backFalseCode
      (Tape.mk₂ (finish false x y q left (false::archive) digits) (false::suffix)) 133
      (Tape.mk₂ (false::archive) (RoutedCopy.fieldWord (context false x y q left) digits suffix))
      (2*digits.length+cost false x y q left) := by
  let arc:=ReturnBank.innerArchive (ReturnTraverse.base (false::archive) digits) x y
  let value:=encodeDatum (.rational q)++false::suffix
  have valueHead : value=true::value.tail := rfl
  have restored:=FactorBack.restore_bounded (List.replicate left false++true::arc) suffix q qNonnegative
  have seek:=ReturnAnchor.false_bounded arc value.tail left
  rw [←valueHead] at seek
  have returned:=ReturnTraverse.back_bounded x y nonnegative archive digits (east false q left suffix)
  have actual:=(restored.seq seek).seq returned
  have port : PSTRTMSeq005.rightLabel (a:=62) (70 : Fin 71)=(133 : Fin 134) := by decide
  rw [port] at actual
  rw [source_word]
  simpa only [backFalseCode,backFalsePrefixCode,finish,nearLeft,result,ReturnBank.archive,arc] using
    actual.mono (by dsimp only [cost,restoreFee,result];omega)

theorem backTrue_bounded (x y q : Rat) (nonnegative : 0≤x)
    (left : ℕ) (archive digits suffix : List Bool) :
    BoundedRun backTrueCode
      (Tape.mk₂ (finish true x y q left (false::archive) digits) (false::suffix)) 168
      (Tape.mk₂ (false::archive) (RoutedCopy.fieldWord (context true x y q left) digits suffix))
      (2*digits.length+cost true x y q left) := by
  let arc:=ReturnBank.innerArchive (ReturnTraverse.base (false::archive) digits) x y
  let num:=markedNum q
  let den:=ReturnAnchor.denominator q
  let dep:=(PSTRTMThresholdBBackupEntry188.result q 1).depth
  let b:=ReturnAnchor.bDigits q
  let gap:=(PSTRTMThresholdBBackupEntry188.result q 1).gap
  have restored:=FactorBack.restore_bounded
    (scratchLeft q++(List.replicate (blank q left) false++true::arc)) suffix (1/4 : Rat) (by norm_num)
  have nonempty : dep≠[] := PSTRTMThresholdRiskReturnBudget230.result_depth_ne_nil q 1 (by decide)
  have seek:=ReturnScratch.back_bounded arc num den dep b
    (PSTRTMThresholdCapLiteral242.quarterBits++false::suffix) gap (blank q left) nonempty
  rw [PSTRTMThresholdCapLiteral242.quarter_codec] at seek
  simp only [List.append_assoc] at seek
  have returned:=ReturnTraverse.back_bounded x y nonnegative archive digits (east true q left suffix)
  rw [true_east,PSTRTMThresholdCapLiteral242.quarter_codec] at returned
  have actual:=(restored.seq seek).seq returned
  have port : PSTRTMSeq005.rightLabel (a:=97) (70 : Fin 71)=(168 : Fin 169) := by decide
  rw [port] at actual
  rw [source_word,true_east,PSTRTMThresholdCapLiteral242.quarter_codec]
  have small : blank q left≤left := Nat.sub_le _ _
  simpa only [backTrueCode,backTruePrefixCode,finish,nearLeft,result,ReturnBank.archive,arc,
    List.append_assoc] using actual.mono (b:=2*digits.length+cost true x y q left)
      (by dsimp only [cost,scratchFee,restoreFee,result,num,den,dep,b,gap];omega)

theorem finish_cons (capped : Bool) (x y q : Rat) (left : ℕ) (sourceLeft later : List Bool) (bit : Bool) :
    finish capped x y q left (true::bit::sourceLeft) later=finish capped x y q left sourceLeft (bit::later) := by
  simp only [finish,ReturnTraverse.base_cons]

end RootB23.Threshold.ReturnRoute
