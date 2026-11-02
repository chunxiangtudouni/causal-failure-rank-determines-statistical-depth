module
public import Structure.RootB23_Threshold_ReturnCredit_018

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnAnchor
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PSTRTMThresholdBBackupEntry188

def bDigits (q : Rat) : List Bool := PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB q 1)
def numerator (q : Rat) : List Bool := PSTRTMNatValue017.rawPayload q.num.natAbs
def denominator (q : Rat) : List Bool := PSTRTMNatValue017.rawPayload q.den
def depthRight (q : Rat) (tail : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks (result q 1).depth++List.replicate (2*(result q 1).gap+2) false++
    PSTRTMIncrement009.blocks (bDigits q)++false::tail
def sourceRight (q : Rat) (tail : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks (numerator q)++PSTRTMThresholdRiskMarkers232.markerTail
    (PSTRTMIncrement009.blocks (denominator q)++PSTRTMThresholdRiskMarkers232.markerTail (depthRight q tail))
def markedSourceRight (q : Rat) (tail : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks (true::(numerator q).tail)++PSTRTMThresholdRiskMarkers232.markerTail
    (PSTRTMIncrement009.blocks (denominator q)++PSTRTMThresholdRiskMarkers232.markerTail (depthRight q tail))

def depthCode : Machine 14 := PSTRTMSeq005.seqMachine PA17TMRatArithmeticParse002.fieldBackMachine
  PSTRTMThresholdRiskReturn228.depthMachine
def fieldsCode : Machine 32 := PSTRTMSeq005.seqMachine depthCode PSTRTMThresholdRiskMarkers232.riskFieldsMachine
def markCode : Machine 34 := PSTRTMSeq005.seqMachine fieldsCode (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
def prepareCode : Machine 36 := PSTRTMSeq005.seqMachine markCode PA17TMRatArithmeticParse002.backOneMachine
def trueCode : Machine 38 := PSTRTMSeq005.seqMachine prepareCode (PA17TMRatArithmeticAllocate013.gapSeekMachine .left)
def falseCode : Machine 1 := PA17TMRatArithmeticAllocate013.gapSeekMachine .left

theorem prepare_bounded (outer tail : List Bool) (q : Rat) :
    BoundedRun prepareCode (Tape.mk₂ (PSTRTMThresholdBReblock195.savedLeft q 1++outer) tail) 36
      (Tape.mk₂ outer (false::markedSourceRight q tail))
      (2*(bDigits q).length+2*(result q 1).gap+2*(result q 1).depth.length+
        2*((numerator q).length+(denominator q).length)+37) := by
  have bBack : BoundedRun PA17TMRatArithmeticParse002.fieldBackMachine
      (Tape.mk₂ (PSTRTMThresholdBReblock195.savedLeft q 1++outer) tail) 5
      (Tape.mk₂ (false::(sourceArchive q 1++outer))
        (PSTRTMIncrement009.blocks (bDigits q)++false::tail)) (2*(bDigits q).length+5) := by
    refine ⟨PA17TMRatArithmeticParse002.fieldBackTrace (sourceArchive q 1++outer) (bDigits q) tail,?_,
      by rw [PA17TMRatArithmeticParse002.fieldBackTrace_length]⟩
    have actual:=PA17TMRatArithmeticParse002.fieldBack_runsFrom (sourceArchive q 1++outer) (bDigits q) tail
    have port : PSTRTMSeq005.rightLabel (a:=1) (3 : Fin 4)=(5 : Fin 6) := by decide
    simpa only [PSTRTMThresholdBReblock195.savedLeft,PA17TMRatArithmeticCopy006.sourceLeft,bDigits,
      PA17TMRatArithmeticParse002.fieldBackFinal,PSTRTMSeq005.rightCfg,PSTRTMMulRewind085.state,
      port,List.append_assoc,List.cons_append] using actual
  have depth : BoundedRun PSTRTMThresholdRiskReturn228.depthMachine
      (Tape.mk₂ (false::(sourceArchive q 1++outer))
        (PSTRTMIncrement009.blocks (bDigits q)++false::tail)) 8
      (Tape.mk₂ (false::(PSTRTMThresholdDepthSource184.riskArchive q++outer)) (depthRight q tail))
      (2*(result q 1).gap+2*(result q 1).depth.length+12) := by
    have nonempty:=PSTRTMThresholdRiskReturnBudget230.result_depth_ne_nil q 1 (by decide)
    cases found : (result q 1).depth.reverse with
    | nil=>
      have equal:=congrArg List.reverse found
      simp only [List.reverse_reverse,List.reverse_nil] at equal
      exact False.elim (nonempty equal)
    | cons bit earlier=>
      have original : (bit::earlier).reverse=(result q 1).depth := by rw [←found,List.reverse_reverse]
      have length:=congrArg List.length found
      simp only [List.length_reverse,List.length_cons] at length
      let right:=PSTRTMIncrement009.blocks (bDigits q)++false::tail
      have input : false::(sourceArchive q 1++outer)=
          List.replicate (2*(result q 1).gap+2) false++
            (PSTRTMRawNat010.leftBlocks (bit::earlier)++false::(PSTRTMThresholdDepthSource184.riskArchive q++outer)) := by
        rw [show 2*(result q 1).gap+2=2+2*(result q 1).gap by omega,List.replicate_add]
        simp only [sourceArchive,PSTRTMThresholdCounterSeek169.gaps_replicate,found,
          List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc]
      rw [input]
      refine ⟨PSTRTMThresholdRiskReturn228.depthTrace (PSTRTMThresholdDepthSource184.riskArchive q++outer)
        bit earlier right (2*(result q 1).gap+2),?_,?_⟩
      · have actual:=PSTRTMThresholdRiskReturn228.depth_runsFrom
          (PSTRTMThresholdDepthSource184.riskArchive q++outer) bit earlier right (2*(result q 1).gap+2)
        have port : PSTRTMSeq005.rightLabel (a:=4) (3 : Fin 4)=(8 : Fin 9) := by decide
        simpa only [PSTRTMThresholdRiskReturn228.depthFinal,PSTRTMSeq005.rightCfg,PSTRTMMulRewind085.state,
          port,original,depthRight,right,List.append_assoc] using actual
      · rw [PSTRTMThresholdRiskReturn228.depth_length]
        omega
  have fields : BoundedRun PSTRTMThresholdRiskMarkers232.riskFieldsMachine
      (Tape.mk₂ (false::(PSTRTMThresholdDepthSource184.riskArchive q++outer)) (depthRight q tail)) 17
      (Tape.mk₂ (false::outer) (sourceRight q tail))
      (2*((numerator q).length+(denominator q).length)+16) := by
    refine ⟨PSTRTMThresholdRiskMarkers232.riskFieldsTrace outer (numerator q) (denominator q) (depthRight q tail),?_,
      by rw [PSTRTMThresholdRiskMarkers232.riskFields_length]⟩
    have actual:=PSTRTMThresholdRiskMarkers232.riskFields_runsFrom outer (numerator q) (denominator q) (depthRight q tail)
    have port : PSTRTMSeq005.rightLabel (a:=8) (PSTRTMSeq005.rightLabel (a:=4) (3 : Fin 4))=(17 : Fin 18) := by decide
    simpa only [PSTRTMThresholdDepthSource184.riskArchive,PSTRTMThresholdDenPrepare141.denArchive,
      PSTRTMThresholdRiskMarkers232.markerLeft,PSTRTMThresholdRiskMarkers232.riskFieldsFinal,
      PSTRTMThresholdRiskMarkers232.markerFinal,PSTRTMSeq005.rightCfg,PSTRTMMulRewind085.state,
      sourceRight,numerator,denominator,port,List.append_assoc,List.cons_append,List.nil_append] using actual
  have marked : BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
      (Tape.mk₂ (false::outer) (sourceRight q tail)) 1
      (Tape.mk₂ (false::outer) (markedSourceRight q tail)) 2 := by
    have nonempty : numerator q≠[] := PA17TMRatArithmeticBookmark014.numerator_ne_nil q
    cases found : numerator q with
    | nil=>exact False.elim (nonempty found)
    | cons bit later=>
      simpa only [sourceRight,markedSourceRight,found,List.tail_cons,PSTRTMIncrement009.blocks,
        List.flatMap_cons,List.cons_append,List.nil_append] using
        (show BoundedRun (PA17TMRatArithmeticAllocate013.setMarkerMachine true)
          (Tape.mk₂ (false::outer) (bit::true::(PSTRTMIncrement009.blocks later++
            PSTRTMThresholdRiskMarkers232.markerTail (PSTRTMIncrement009.blocks (denominator q)++
              PSTRTMThresholdRiskMarkers232.markerTail (depthRight q tail))))) 1
          (Tape.mk₂ (false::outer) (true::true::(PSTRTMIncrement009.blocks later++
            PSTRTMThresholdRiskMarkers232.markerTail (PSTRTMIncrement009.blocks (denominator q)++
              PSTRTMThresholdRiskMarkers232.markerTail (depthRight q tail))))) 2 from
          ⟨PA17TMRatArithmeticAllocate013.setMarkerTrace bit true (false::outer) _,
            PA17TMRatArithmeticAllocate013.setMarker_runsFrom _ _ _ _,by rfl⟩)
  have back : BoundedRun PA17TMRatArithmeticParse002.backOneMachine
      (Tape.mk₂ (false::outer) (markedSourceRight q tail)) 1
      (Tape.mk₂ outer (false::markedSourceRight q tail)) 2 :=
    ⟨PA17TMRatArithmeticParse002.backOneTrace outer false (markedSourceRight q tail),
      PA17TMRatArithmeticParse002.backOne_runsFrom _ _ _,by rfl⟩
  have actual:=(((bBack.seq depth).seq fields).seq marked).seq back
  have port : PSTRTMSeq005.rightLabel (a:=34) (1 : Fin 2)=(36 : Fin 37) := by decide
  rw [port] at actual
  simpa only [prepareCode,markCode,fieldsCode,depthCode] using actual.mono (by omega)

def trueEast (q : Rat) (left : ℕ) (tail : List Bool) : List Bool :=
  List.replicate (left-(PSTRTMThresholdBReblock195.savedLeft q 1).length) false++false::markedSourceRight q tail

/-- TRUE consumes the complete structured cap archive before scanning
the remaining real FALSE window to the permanent outer TRUE anchor. The
distance is read by those tape structures, never supplied to this code. -/
theorem true_bounded (archive tail : List Bool) (q : Rat) (left : ℕ)
    (complete : (PSTRTMThresholdBReblock195.savedLeft q 1).length≤left) :
    BoundedRun trueCode
      (Tape.mk₂ (PA17TMRatArithmeticFrame005.windowPrefix left
        (ListBlank.mk (PSTRTMThresholdBReblock195.savedLeft q 1))++true::archive) tail) 38
      (Tape.mk₂ archive (true::trueEast q left tail)) (left+32) := by
  let gap:=left-(PSTRTMThresholdBReblock195.savedLeft q 1).length
  have first:=prepare_bounded (List.replicate gap false++true::archive) tail q
  have gapRun : BoundedRun (PA17TMRatArithmeticAllocate013.gapSeekMachine .left)
      (Tape.mk₂ (List.replicate gap false++true::archive) (false::markedSourceRight q tail)) 1
      (Tape.mk₂ archive (true::(List.replicate gap false++false::markedSourceRight q tail))) (gap+2) :=
    ⟨Uncapped.Steps.returnTrace false gap archive (markedSourceRight q tail),
      Uncapped.Steps.return_runsFrom _ _ _ _,by rw [Uncapped.Steps.return_length]⟩
  have actual:=first.seq gapRun
  have port : PSTRTMSeq005.rightLabel (a:=36) (1 : Fin 2)=(38 : Fin 39) := by decide
  rw [port] at actual
  rw [PA17TMRatArithmeticFrame005.windowPrefix_mk_of_length _ _ complete]
  have length:=ReturnCredit.savedLeft_length q
  simp only [bDigits,numerator,denominator,PSTRTMNatValue017.rawPayload,List.length_ofFn] at actual
  simpa only [trueCode,trueEast,gap,List.append_assoc] using actual.mono (by omega)

theorem false_bounded (archive tail : List Bool) (left : ℕ) :
    BoundedRun falseCode (Tape.mk₂ (List.replicate left false++true::archive) (true::tail)) 1
      (Tape.mk₂ archive (true::(List.replicate left false++true::tail))) (left+2) :=
  ⟨Uncapped.Steps.returnTrace true left archive tail,Uncapped.Steps.return_runsFrom _ _ _ _,
    by rw [Uncapped.Steps.return_length]⟩

end RootB23.Threshold.ReturnAnchor
