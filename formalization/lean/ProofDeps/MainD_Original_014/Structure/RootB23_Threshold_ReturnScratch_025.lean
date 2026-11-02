module
public import Structure.RootB23_Threshold_ReturnQuarter_023
public import Structure.RootB23_Threshold_ReturnTraverse_024

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnScratch
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticParse002

/-- This is the actual marked cap scratch, whose first NUM data bit was
paid TRUE by ReturnAnchor020. No canonical-q equation is assumed here. -/
def fieldsLeft (outer num den : List Bool) : List Bool :=
  PSTRTMThresholdRiskMarkers232.markerLeft (PSTRTMThresholdDenPrepare141.denArchive outer num) den
def oldLeft (num den depth b : List Bool) (gap : ℕ) : List Bool :=
  false::(PSTRTMRawNat010.leftBlocks b.reverse++List.replicate (2*gap+2) false++
    (PSTRTMRawNat010.leftBlocks depth.reverse++fieldsLeft [] num den))
def depthWord (depth b : List Bool) (gap : ℕ) (tail : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks depth++List.replicate (2*gap+2) false++
    PSTRTMIncrement009.blocks b++false::tail
def word (num den depth b : List Bool) (gap : ℕ) (tail : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks num++FactorWalk.marker
    (PSTRTMIncrement009.blocks den++FactorWalk.marker (depthWord depth b gap tail))

def depthCode : Machine 17 := PSTRTMSeq005.seqMachine FactorWalk.depthSeekCode ReturnQuarter.code
def denCode : Machine 23 := PSTRTMSeq005.seqMachine FactorWalk.sourceSkipCode depthCode
def outCode : Machine 29 := PSTRTMSeq005.seqMachine FactorWalk.sourceSkipCode denCode
def prepareBackCode : Machine 34 := PSTRTMSeq005.seqMachine ReturnAnchor.fieldsCode backOneMachine
def backCode : Machine 36 := PSTRTMSeq005.seqMachine prepareBackCode (PA17TMRatArithmeticAllocate013.gapSeekMachine .left)

theorem depth_bounded (left depth b suffix : List Bool) (gap : ℕ) (bNonempty : b≠[]) :
    BoundedRun depthCode
      (Tape.mk₂ left (depthWord depth b gap (PSTRTMThresholdCapLiteral242.quarterBits++suffix))) 17
      (Tape.mk₂ (false::FactorWalk.bBase left depth b gap) (PSTRTMThresholdCapLiteral242.quarterBits++suffix))
      (2*depth.length+2*gap+2*b.length+26) := by
  cases b with
  | nil=>exact False.elim (bNonempty rfl)
  | cons bit later=>
    let depthLeft:=false::false::(PSTRTMRawNat010.leftBlocks depth.reverse++left)
    let endWord:=PSTRTMIncrement009.blocks (bit::later)++false::(PSTRTMThresholdCapLiteral242.quarterBits++suffix)
    have gapEq : List.replicate (2*gap+2) false=false::false::PSTRTMThresholdCounterSeek169.gaps gap := by
      rw [PSTRTMThresholdCounterSeek169.gaps_replicate,
        show 2*gap+2=2+2*gap by omega,List.replicate_add]
      rfl
    have first : BoundedRun PSTRTMThresholdCursor115.cursorMachine
        (Tape.mk₂ left (depthWord depth (bit::later) gap (PSTRTMThresholdCapLiteral242.quarterBits++suffix))) 2
        (Tape.mk₂ depthLeft (PSTRTMThresholdCounterSeek169.gaps gap++endWord)) (2*depth.length+3) := by
      rw [depthWord,gapEq]
      refine ⟨PSTRTMThresholdCursor115.cursorTrace left depth
        (PSTRTMThresholdCounterSeek169.gaps gap++endWord),?_,by rw [PSTRTMThresholdCursor115.cursor_length]⟩
      simpa only [PSTRTMThresholdCursor115.state,depthLeft,endWord,List.append_assoc,List.cons_append] using
        PSTRTMThresholdCursor115.cursor_runsFrom left depth (PSTRTMThresholdCounterSeek169.gaps gap++endWord)
    have seek : BoundedRun PSTRTMThresholdCounterSeek169.seekMachine
        (Tape.mk₂ depthLeft (PSTRTMThresholdCounterSeek169.gaps gap++endWord)) 2
        (Tape.mk₂ (PSTRTMThresholdCounterSeek169.gapLeft gap depthLeft) endWord) (2*gap+3) :=
      ⟨PSTRTMThresholdCounterSeek169.seekTrace bit
        (PSTRTMIncrement009.blocks later++false::(PSTRTMThresholdCapLiteral242.quarterBits++suffix)) gap depthLeft,
        PSTRTMThresholdCounterSeek169.seek_runsFrom _ _ _ _,by rw [PSTRTMThresholdCounterSeek169.seek_length]⟩
    have connector:=ReturnQuarter.actual_bounded (PSTRTMThresholdCounterSeek169.gapLeft gap depthLeft) (bit::later) suffix
    have actual:=(first.seq seek).seq connector
    have port : PSTRTMSeq005.rightLabel (a:=5) (11 : Fin 12)=(17 : Fin 18) := by decide
    rw [port] at actual
    have gapLeftEq : PSTRTMThresholdCounterSeek169.gapLeft gap depthLeft=
        List.replicate (2*gap+2) false++(PSTRTMRawNat010.leftBlocks depth.reverse++left) := by
      rw [PSTRTMThresholdCounterSeek169.gapLeft_eq,PSTRTMThresholdCounterSeek169.gaps_replicate,
        List.replicate_add]
      simp only [depthLeft,List.append_assoc,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append]
    simpa only [depthCode,FactorWalk.depthSeekCode,FactorWalk.bBase,gapLeftEq,List.append_assoc]
      using actual.mono (by omega)

/-- Fixed forward connector across both actual0010 markers, exhausted
depth, its aligned gap and the actual cap-B/quarter EOF01. -/
theorem out_bounded (outer num den depth b suffix : List Bool) (gap : ℕ) (bNonempty : b≠[]) :
    BoundedRun outCode
      (Tape.mk₂ (false::outer) (word num den depth b gap (PSTRTMThresholdCapLiteral242.quarterBits++suffix))) 29
      (Tape.mk₂ (oldLeft num den depth b gap++outer) (PSTRTMThresholdCapLiteral242.quarterBits++suffix))
      (2*num.length+2*den.length+2*depth.length+2*gap+2*b.length+38) := by
  have numRun:=FactorWalk.source_skip (false::outer) num
    (PSTRTMIncrement009.blocks den++FactorWalk.marker (depthWord depth b gap (PSTRTMThresholdCapLiteral242.quarterBits++suffix)))
  have denRun:=FactorWalk.source_skip (FactorWalk.markedLeft (false::outer) num) den
    (depthWord depth b gap (PSTRTMThresholdCapLiteral242.quarterBits++suffix))
  have depthRun:=depth_bounded (FactorWalk.markedLeft (FactorWalk.markedLeft (false::outer) num) den)
    depth b suffix gap bNonempty
  have actual:=numRun.seq (denRun.seq depthRun)
  have port : PSTRTMSeq005.rightLabel (a:=5) (PSTRTMSeq005.rightLabel (a:=5) (17 : Fin 18))=(29 : Fin 30) := by decide
  rw [port] at actual
  simpa only [outCode,denCode,word,oldLeft,FactorWalk.bBase,FactorWalk.markedLeft,fieldsLeft,
    PSTRTMThresholdRiskMarkers232.markerLeft,PSTRTMThresholdDenPrepare141.denArchive,
    List.append_assoc,List.cons_append,List.nil_append] using actual.mono (by omega)

theorem prepareBack_bounded (outer num den depth b tail : List Bool) (gap : ℕ) (depthNonempty : depth≠[]) :
    BoundedRun prepareBackCode (Tape.mk₂ (oldLeft num den depth b gap++outer) tail) 34
      (Tape.mk₂ outer (false::word num den depth b gap tail))
      (2*b.length+2*gap+2*depth.length+2*(num.length+den.length)+35) := by
  let arc:=List.replicate (2*gap+1) false++(PSTRTMRawNat010.leftBlocks depth.reverse++fieldsLeft outer num den)
  have geometry : oldLeft num den depth b gap++outer=
      PA17TMRatArithmeticCopy006.sourceLeft arc b := by
    rw [oldLeft,PA17TMRatArithmeticCopy006.sourceLeft]
    have rep : List.replicate (2*gap+2) false=false::List.replicate (2*gap+1) false := by
      rw [show 2*gap+2=(2*gap+1)+1 by omega,List.replicate_succ]
    simp only [arc,rep,fieldsLeft,PSTRTMThresholdRiskMarkers232.markerLeft,
      PSTRTMThresholdDenPrepare141.denArchive,List.append_assoc,List.cons_append,List.nil_append]
  have bBack : BoundedRun fieldBackMachine (Tape.mk₂ (oldLeft num den depth b gap++outer) tail) 5
      (Tape.mk₂ (false::arc) (PSTRTMIncrement009.blocks b++false::tail)) (2*b.length+5) := by
    rw [geometry]
    refine ⟨fieldBackTrace arc b tail,?_,by rw [fieldBackTrace_length]⟩
    have actual:=fieldBack_runsFrom arc b tail
    have port : PSTRTMSeq005.rightLabel (a:=1) (3 : Fin 4)=(5 : Fin 6) := by decide
    simpa only [PA17TMRatArithmeticCopy006.sourceLeft,fieldBackFinal,PSTRTMSeq005.rightCfg,
      PSTRTMMulRewind085.state,port] using actual
  have depthRun : BoundedRun PSTRTMThresholdRiskReturn228.depthMachine
      (Tape.mk₂ (false::arc) (PSTRTMIncrement009.blocks b++false::tail)) 8
      (Tape.mk₂ (fieldsLeft outer num den) (depthWord depth b gap tail))
      (2*gap+2*depth.length+12) := by
    cases found : depth.reverse with
    | nil=>
      have equal:=congrArg List.reverse found
      simp only [List.reverse_reverse,List.reverse_nil] at equal
      exact False.elim (depthNonempty equal)
    | cons bit earlier=>
      have original : (bit::earlier).reverse=depth := by rw [←found,List.reverse_reverse]
      have length:=congrArg List.length found
      simp only [List.length_reverse,List.length_cons] at length
      let inner:=(fieldsLeft outer num den).tail
      have fieldsShape : fieldsLeft outer num den=false::inner := rfl
      have input : false::arc=List.replicate (2*gap+2) false++
          (PSTRTMRawNat010.leftBlocks (bit::earlier)++false::inner) := by
        rw [show 2*gap+2=(2*gap+1)+1 by omega,List.replicate_succ]
        simp only [arc,found,fieldsShape,List.cons_append]
      rw [input]
      refine ⟨PSTRTMThresholdRiskReturn228.depthTrace inner bit earlier
        (PSTRTMIncrement009.blocks b++false::tail) (2*gap+2),?_,?_⟩
      · have actual:=PSTRTMThresholdRiskReturn228.depth_runsFrom inner bit earlier
          (PSTRTMIncrement009.blocks b++false::tail) (2*gap+2)
        have port : PSTRTMSeq005.rightLabel (a:=4) (3 : Fin 4)=(8 : Fin 9) := by decide
        simpa only [PSTRTMThresholdRiskReturn228.depthFinal,PSTRTMSeq005.rightCfg,PSTRTMMulRewind085.state,
          port,original,depthWord,fieldsShape,List.append_assoc] using actual
      · rw [PSTRTMThresholdRiskReturn228.depth_length]
        omega
  have fields : BoundedRun PSTRTMThresholdRiskMarkers232.riskFieldsMachine
      (Tape.mk₂ (fieldsLeft outer num den) (depthWord depth b gap tail)) 17
      (Tape.mk₂ (false::outer) (word num den depth b gap tail)) (2*(num.length+den.length)+16) := by
    refine ⟨PSTRTMThresholdRiskMarkers232.riskFieldsTrace outer num den (depthWord depth b gap tail),?_,
      by rw [PSTRTMThresholdRiskMarkers232.riskFields_length]⟩
    have actual:=PSTRTMThresholdRiskMarkers232.riskFields_runsFrom outer num den (depthWord depth b gap tail)
    have port : PSTRTMSeq005.rightLabel (a:=8) (PSTRTMSeq005.rightLabel (a:=4) (3 : Fin 4))=(17 : Fin 18) := by decide
    simpa only [fieldsLeft,PSTRTMThresholdRiskMarkers232.riskFieldsFinal,PSTRTMThresholdRiskMarkers232.markerFinal,
      PSTRTMSeq005.rightCfg,PSTRTMMulRewind085.state,port,word,FactorWalk.marker,
      PSTRTMThresholdRiskMarkers232.markerTail] using actual
  have back : BoundedRun backOneMachine
      (Tape.mk₂ (false::outer) (word num den depth b gap tail)) 1
      (Tape.mk₂ outer (false::word num den depth b gap tail)) 2 :=
    ⟨backOneTrace outer false (word num den depth b gap tail),backOne_runsFrom _ _ _,by rfl⟩
  have actual:=((bBack.seq depthRun).seq fields).seq back
  have port : PSTRTMSeq005.rightLabel (a:=32) (1 : Fin 2)=(34 : Fin 35) := by decide
  rw [port] at actual
  simpa only [prepareBackCode,ReturnAnchor.fieldsCode,ReturnAnchor.depthCode] using actual.mono (by omega)

theorem back_bounded (archive num den depth b tail : List Bool) (gap blank : ℕ) (depthNonempty : depth≠[]) :
    BoundedRun backCode
      (Tape.mk₂ (oldLeft num den depth b gap++List.replicate blank false++true::archive) tail) 36
      (Tape.mk₂ archive (true::(List.replicate blank false++false::word num den depth b gap tail)))
      (2*b.length+2*gap+2*depth.length+2*(num.length+den.length)+blank+37) := by
  have first:=prepareBack_bounded (List.replicate blank false++true::archive) num den depth b tail gap depthNonempty
  have seek : BoundedRun (PA17TMRatArithmeticAllocate013.gapSeekMachine .left)
      (Tape.mk₂ (List.replicate blank false++true::archive) (false::word num den depth b gap tail)) 1
      (Tape.mk₂ archive (true::(List.replicate blank false++false::word num den depth b gap tail))) (blank+2) :=
    ⟨Uncapped.Steps.returnTrace false blank archive (word num den depth b gap tail),
      Uncapped.Steps.return_runsFrom _ _ _ _,by rw [Uncapped.Steps.return_length]⟩
  have actual:=first.seq seek
  have port : PSTRTMSeq005.rightLabel (a:=34) (1 : Fin 2)=(36 : Fin 37) := by decide
  rw [port] at actual
  simpa only [backCode,List.append_assoc] using actual.mono (by omega)

end RootB23.Threshold.ReturnScratch
