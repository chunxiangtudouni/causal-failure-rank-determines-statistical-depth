module
public import Structure.RootB23_Threshold_Uncapped_Serialize_008
public import Structure.RootB23_Threshold_Uncapped_Clean_009
public import Common.PSTR_TM_ThresholdRiskMarkers_232

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section
namespace RootB23.Threshold.Uncapped.Export
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMIncrement009 PSTRTMRawNat010
open PA17TMRatArithmeticPairEncode017

def walkCode : Machine 10 := PSTRTMSeq005.seqMachine Serialize.locateCode Walk.code
def cleanCode : Machine 71 := PSTRTMSeq005.seqMachine walkCode Clean.code
def rewindCode : Machine 75 := PSTRTMSeq005.seqMachine cleanCode PSTRTMMulRewind085.rewindMachine
def code : Machine 84 := PSTRTMSeq005.seqMachine rewindCode PSTRTMThresholdRiskMarkers232.markerMachine
def bareCode : Machine 180 := PSTRTMSeq005.seqMachine code Serialize.code

def tailCost (depth : List Bool) (gap n a b : Nat) : Nat :=
  (payload n).length^2+21*(payload n).length+8*depth.length+4*gap+
    4*((payload a).length+(payload b).length)+61

theorem input_tail_blank (archive : List Bool) (a b : Nat) :
    Turing.Tape.mk₂ (false::false::archive) (Serialize.inputRight a b []) =
      Turing.Tape.mk₂ (false::false::archive)
        (blocks (payload a)++Serialize.marker (blocks (payload b))) := by
  have word : Serialize.inputRight a b [] =
      (blocks (payload a)++Serialize.marker (blocks (payload b)))++List.replicate 2 false := by
    simp only [Serialize.inputRight,Serialize.marker,List.replicate_succ,List.replicate_zero,
      List.cons_append,List.append_assoc]
  rw [word]
  simp only [Turing.Tape.mk₂]
  rw [Clean.blank_false_tail]

/-- Every cell after DEN's old0010 is physically erased by Clean009.
The remaining NUM0010 is then actually crossed/rewound to the NUM head.
Both incoming guards and every earlier archive cell are preserved. -/
theorem cleanup_contract (archive depth : List Bool) (gap n a b : Nat) :
    ∃ states, PSTRTMSeq005.RunsFrom code
      ⟨0,Turing.Tape.mk₂ (false::false::archive)
        (Serialize.inputRight a b (true::false::Clean.gapRight depth gap n))⟩ states
      ⟨84,Turing.Tape.mk₂ (false::false::archive) (Serialize.inputRight a b [])⟩ ∧
      states.length ≤ tailCost depth gap n a b := by
  let scratch := Clean.gapRight depth gap n
  let input := Turing.Tape.mk₂ (false::false::archive) (Serialize.inputRight a b (true::false::scratch))
  let atDen := Turing.Tape.mk₂ (Serialize.denominatorLeft archive a)
    (blocks (payload b)++false::false::true::false::scratch)
  let denLeft := leftBlocks (payload b).reverse++Serialize.denominatorLeft archive a
  let atEnd := Turing.Tape.mk₂ denLeft (false::false::true::false::scratch)
  let cleanEnd := Turing.Tape.mk₂ denLeft []
  let cleanDen := Turing.Tape.mk₂ (Serialize.denominatorLeft archive a) (blocks (payload b))
  let cleanNum := Turing.Tape.mk₂ (false::false::archive) (Serialize.inputRight a b [])
  have r0 : ∃ states, PSTRTMSeq005.RunsFrom Serialize.locateCode ⟨0,input⟩ states ⟨7,atDen⟩ ∧
      states.length ≤ 2*(payload a).length+8 := by
    refine ⟨Serialize.locateTrace archive a b (true::false::scratch),Serialize.locate_runsFrom _ _ _ _,?_⟩
    simp only [Serialize.locateTrace,List.length_append,List.length_map,Walk.actual_length,
      Steps.fourRightTrace,List.length_cons,List.length_nil]
    omega
  have r1 : ∃ states, PSTRTMSeq005.RunsFrom Walk.code ⟨0,atDen⟩ states ⟨2,atEnd⟩ ∧
      states.length ≤ 2*(payload b).length+3 :=
    ⟨Walk.actualTrace (Serialize.denominatorLeft archive a) (payload b) (true::false::scratch),
      Walk.field_runsFrom _ _ _,(Walk.actual_length _ _ _).le⟩
  have r01 := Clean.joined_bounded Serialize.locateCode Walk.code input atDen atEnd
    (2*(payload a).length+8) (2*(payload b).length+3) r0 r1
  have r2 : ∃ states, PSTRTMSeq005.RunsFrom Clean.code ⟨0,atEnd⟩ states ⟨60,cleanEnd⟩ ∧
      states.length ≤ (payload n).length^2+21*(payload n).length+8*depth.length+4*gap+39 :=
    Clean.scratch_contract denLeft depth gap n
  have r02 := Clean.joined_bounded walkCode Clean.code input atEnd cleanEnd
    (2*(payload a).length+8+(2*(payload b).length+3))
    ((payload n).length^2+21*(payload n).length+8*depth.length+4*gap+39) r01 r2
  have r3 : ∃ states, PSTRTMSeq005.RunsFrom PSTRTMMulRewind085.rewindMachine
      ⟨0,cleanEnd⟩ states ⟨3,cleanDen⟩ ∧ states.length ≤ 2*(payload b).length+3 := by
    let earlier := true::false::false::Serialize.numeratorLeft archive a
    refine ⟨PSTRTMPairRewind105.fullTrace earlier (payload b).reverse [],?_,?_⟩
    · simpa only [List.append_nil,PSTRTMMulRewind085.state,cleanEnd,cleanDen,denLeft,earlier,Serialize.denominatorLeft] using PSTRTMPairRewind105.rewind_runsFrom earlier (payload b) []
    · simpa only [List.length_reverse] using (PSTRTMPairRewind105.full_length earlier (payload b).reverse []).le
  have r03 := Clean.joined_bounded cleanCode PSTRTMMulRewind085.rewindMachine input cleanEnd cleanDen
    (2*(payload a).length+8+(2*(payload b).length+3)+
      ((payload n).length^2+21*(payload n).length+8*depth.length+4*gap+39))
    (2*(payload b).length+3) r02 r3
  have r4 : ∃ states, PSTRTMSeq005.RunsFrom PSTRTMThresholdRiskMarkers232.markerMachine
      ⟨0,cleanDen⟩ states ⟨8,cleanNum⟩ ∧ states.length ≤ 2*(payload a).length+8 := by
    refine ⟨PSTRTMThresholdRiskMarkers232.markerTrace (false::archive) (payload a) (blocks (payload b)),?_,?_⟩
    · have real := PSTRTMThresholdRiskMarkers232.marker_runsFrom (false::archive) (payload a) (blocks (payload b))
      change PSTRTMSeq005.RunsFrom PSTRTMThresholdRiskMarkers232.markerMachine ⟨0,cleanDen⟩ _
        ⟨8,Turing.Tape.mk₂ (false::false::archive) (blocks (payload a)++Serialize.marker (blocks (payload b)))⟩ at real
      rw [←input_tail_blank] at real
      exact real
    · exact (PSTRTMThresholdRiskMarkers232.marker_length _ _ _).le
  obtain ⟨states,actual,time⟩ := Clean.joined_bounded rewindCode PSTRTMThresholdRiskMarkers232.markerMachine
    input cleanDen cleanNum
    (2*(payload a).length+8+(2*(payload b).length+3)+
      ((payload n).length^2+21*(payload n).length+8*depth.length+4*gap+39)+(2*(payload b).length+3))
    (2*(payload a).length+8) r03 r4
  refine ⟨states,actual,?_⟩
  dsimp only [tailCost]
  omega

theorem positive_final_blank (archive : List Bool) (q : Rat) (hq : 0 < q) :
    Serialize.final archive q.num.natAbs q.den [] =
      (⟨95,Turing.Tape.mk₂ archive (encodeDatum (.rational q))⟩ : MachineState 95) := by
  change (⟨95,Turing.Tape.mk₂ archive
    (true::false::(encodeNat q.num.natAbs++encodeNat q.den++Serialize.remainder []))⟩ : MachineState 95) = _
  have nonnegative : ¬q < 0 := not_lt.mpr (le_of_lt hq)
  have word : true::false::(encodeNat q.num.natAbs++encodeNat q.den++Serialize.remainder []) =
      encodeDatum (.rational q)++List.replicate 4 false := by
    simp only [encodeDatum,nonnegative,decide_false,Serialize.remainder,List.replicate_succ,
      List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc]
  rw [word]
  simp only [Turing.Tape.mk₂]
  rw [Clean.blank_false_tail]

/-- The actual cleaned source feeds the SAME fixed serializer with a
genuinely blank DEN tail. The final FALSE padding descriptor is the blank
tape quotient of cells that were actually cleared, never a free erasure. -/
theorem bare_contract (archive depth : List Bool) (gap n : Nat) (q : Rat) (hq : 0 < q) :
    ∃ states, PSTRTMSeq005.RunsFrom bareCode
      ⟨0,Turing.Tape.mk₂ (false::false::archive)
        (Serialize.inputRight q.num.natAbs q.den (true::false::Clean.gapRight depth gap n))⟩ states
      ⟨180,Turing.Tape.mk₂ archive (encodeDatum (.rational q))⟩ ∧
      states.length ≤ tailCost depth gap n q.num.natAbs q.den+
        128*(natBits q.num.natAbs+natBits q.den+1)^2 := by
  let input := Turing.Tape.mk₂ (false::false::archive)
    (Serialize.inputRight q.num.natAbs q.den (true::false::Clean.gapRight depth gap n))
  let middle := Turing.Tape.mk₂ (false::false::archive) (Serialize.inputRight q.num.natAbs q.den [])
  have firstRun := cleanup_contract archive depth gap n q.num.natAbs q.den
  have secondRun : ∃ states, PSTRTMSeq005.RunsFrom Serialize.code ⟨0,middle⟩ states
      ⟨95,Turing.Tape.mk₂ archive (encodeDatum (.rational q))⟩ ∧
      states.length ≤ 128*(natBits q.num.natAbs+natBits q.den+1)^2 := by
    refine ⟨Serialize.actualTrace archive q.num.natAbs q.den [],?_,?_⟩
    · have real := Serialize.actual_runsFrom archive q.num.natAbs q.den []
      rw [positive_final_blank archive q hq] at real
      exact real
    · simpa only [payload_length] using Serialize.actual_time_le archive q.num.natAbs q.den []
  exact Clean.joined_bounded code Serialize.code input middle
    (Turing.Tape.mk₂ archive (encodeDatum (.rational q)))
    (tailCost depth gap n q.num.natAbs q.den)
    (128*(natBits q.num.natAbs+natBits q.den+1)^2) firstRun secondRun

end RootB23.Threshold.Uncapped.Export
