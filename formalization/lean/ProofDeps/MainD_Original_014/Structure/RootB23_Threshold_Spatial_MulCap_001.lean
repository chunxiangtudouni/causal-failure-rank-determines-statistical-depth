module
public import Structure.RootB23_Threshold_Spatial_MulFrame_001
public import Structure.RootB23_Threshold_ProductPacket_005
public import Structure.RootB23_Threshold_Uncapped_Actual_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section
namespace RootB23.Threshold.Spatial.MulCap
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticMulController057 PA17TMRatArithmeticMulSuffix063
open PA17TMRatArithmeticFrame005 PA17TMRatArithmeticFrameBudget008
open PaperProofs.Common.Native.RationalControllerComputation.RootB23.Threshold.Spatial
open RootB23.Threshold.Uncapped

abbrev packetCap : Nat := controllerCap+135+1
abbrev cap : Nat := packetCap+1582+1
def packetMachine : Machine packetCap := PSTRTMSeq005.seqMachine mulMachine ProductPacket.machine
def code : Machine cap := PSTRTMSeq005.seqMachine packetMachine Actual.code
def final (x y : Rat) : MachineState cap :=
  PSTRTMSeq005.rightCfg (a:=packetCap) (Actual.final (x*y))
def inputLength (x y : Rat) : Nat := (encode [.rational x,.rational y]).length
def timeCoefficient : Nat := mulTimeCoefficient+256+134217728*512
def time (x y : Rat) : Nat := timeCoefficient*(inputLength x y+1)^4
def output (x y : Rat) : List Bool := encodeDatum (.rational (min (1/4 : Rat) (x*y)))
def oldLeft (x y : Rat) : List Bool :=
  if (1/4 : Rat) ≤ x*y then PSTRTMThresholdBReblock195.savedLeft (x*y) 1 else []
def window (x y : Rat) (spare : Nat) : Nat := time x y+2*inputLength x y+spare+2

theorem timeCoefficient_pos : 0 < timeCoefficient := by unfold timeCoefficient; omega

theorem product_width_le (x y : Rat) :
    natBits (x*y).num.natAbs+natBits (x*y).den+1 ≤ inputLength x y := by
  have fields := PA17TMRatArithmeticMulFields048.pipeline_fields x y
  have bits := PA17TMRatArithmeticMulFields048.normalized_bits x y
  rw [fields.1,fields.2.1] at bits
  have size : inputLength x y=2*PA17TMRatArithmeticParse002.fieldWidth x y+14 :=
    PA17TMRatArithmeticParse002.pair_length x y
  omega

theorem cap_packet_length (q : Rat) :
    (encode [.rational q,.natural 1]).length=(encode [.rational q]).length+6 := by
  have oneBits : natBits 1=1 := by decide
  have twoBits : natBits 2=2 := by decide
  simp only [PSTRTMLength004.encode_length,List.length_cons,List.length_nil,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,PSTRTMLength004.datumBits,
    oneBits,twoBits]
  omega

/-- FF/FFFF are genuinely blank cells of RAW64's exact mk1 output. -/
private theorem packet_empty_input (q : Rat) :
    Tape.mk₂ [false,false] (encode [.rational q]++[false,false,false,false]) =
      Tape.mk₁ (encode [.rational q]) := by
  have left : ListBlank.mk [false,false] = ListBlank.mk ([] : List Bool) := by
    apply Quotient.sound
    exact Or.inr ⟨2,by rfl⟩
  have right : ListBlank.mk (encode [.rational q]++[false,false,false,false]) =
      ListBlank.mk (encode [.rational q]) := by
    apply Quotient.sound
    exact Or.inr ⟨4,by rfl⟩
  simp only [Tape.mk₁,Tape.mk₂,left,right]

theorem final_tape (x y : Rat) (positive : 0 < x*y) :
    (final x y).Tape=Actual.finalTape (x*y) := Actual.final_tape (x*y) positive

theorem final_tape_split (x y : Rat) :
    Actual.finalTape (x*y)=Tape.mk₂ (oldLeft x y) (output x y) := by
  by_cases capped : (1/4 : Rat) ≤ x*y
  · simp only [Actual.finalTape,oldLeft,output,capped,ite_true,min_eq_left capped]
  · simp only [Actual.finalTape,oldLeft,output,capped,ite_false,
      min_eq_right (le_of_not_ge capped),Tape.mk₁]

theorem final_right (x y : Rat) (positive : 0 < x*y) :
    (final x y).Tape.right₀=ListBlank.mk (output x y) := Actual.final_right (x*y) positive

theorem final_control (x y : Rat) (positive : 0 < x*y) :
    (final x y).q.val=packetCap+1+(if (1/4 : Rat) ≤ x*y then 1365 else 1582) := by
  by_cases capped : (1/4 : Rat) ≤ x*y
  · simp only [final,Actual.final,capped,ite_true,Actual.trueFinal,
      PSTRTMSeq005.rightCfg,PSTRTMSeq005.leftCfg,PSTRTMSeq005.rightLabel,PSTRTMSeq005.leftLabel]
    rw [PSTRTMThresholdDynamicCap245.final_control (x*y) positive]
    simp only [capped,ite_true]
  · simp only [final,Actual.final,capped,ite_false,Actual.falseFinal,
      PSTRTMSeq005.rightCfg,PSTRTMSeq005.rightLabel]
    rw [show (216 : Fin 217).val=216 by decide]

theorem output_length_le (x y : Rat) : (output x y).length ≤ 2*inputLength x y := by
  have original := PA17TMRatArithmeticParse002.pair_length x y
  have raw := raw_product_length_le x y
  change (encode [.rational (x*y)]).length ≤ 2*inputLength x y at raw
  by_cases capped : (1/4 : Rat) ≤ x*y
  · have quarter : (encodeDatum (.rational (1/4 : Rat))).length=12 := by
      rw [←PSTRTMThresholdCapLiteral242.quarter_codec]
      rfl
    simp only [output,min_eq_left capped,quarter]
    unfold inputLength
    omega
  · have oneBits : natBits 1=1 := by decide
    simp only [PSTRTMLength004.encode_length,List.length_singleton,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,PSTRTMLength004.datumBits,oneBits,Nat.add_zero] at raw
    simp only [output,min_eq_right (le_of_not_ge capped),PSTRTMLength004.encodeDatum_rational_length]
    omega

/-- One fixed compound table: genuine RAW64, actual 136-label packet
conversion, then the genuine fixed minquarter program. Both HALT transfers
are actual Seq005 write-self steps, with no reset or answer reloading. -/
theorem original_contract (x y : Rat) (positive : 0 < x*y) :
    ∃ trace, Runs code (encode [.rational x,.rational y]) trace (final x y) ∧
      trace.length ≤ time x y ∧
      ∀ clock chargedInputLength, visitedSpace code chargedInputLength (trace.take clock) ≤
        chargedInputLength+2*time x y+1 := by
  obtain ⟨rawTrace,rawLast,rawRun,rawWhole,rawTime⟩ := original_mul_runs x y
  obtain ⟨packetTrace,packetRun,packetTime,_packetSpace⟩ :=
    ProductPacket.packet_contract (x*y) positive [] [] (inputLength x y)
  have packetFrom : PSTRTMSeq005.RunsFrom ProductPacket.machine ⟨0,rawLast.Tape⟩ packetTrace
      ⟨135,Tape.mk₁ (encode [.rational (x*y),.natural 1])⟩ := by
    rw [rawWhole]
    simpa only [List.append_nil,packet_empty_input,Tape.mk₁] using packetRun
  let frontTrace := rawTrace.map (PSTRTMSeq005.leftCfg (b:=135)) ++
    packetTrace.map (PSTRTMSeq005.rightCfg (a:=controllerCap))
  let packetLast : MachineState 135 := ⟨135,Tape.mk₁ (encode [.rational (x*y),.natural 1])⟩
  have prefixRun : Runs packetMachine (encode [.rational x,.rational y]) frontTrace
      (PSTRTMSeq005.rightCfg (a:=controllerCap) packetLast) :=
    PSTRTMSeq005.seq_runs mulMachine ProductPacket.machine _ rawLast packetLast rawTrace packetTrace rawRun packetFrom
  obtain ⟨capTrace,capRun,capTime,_capSpace⟩ := Actual.original_minquarter_contract (x*y) positive
  have capFrom : PSTRTMSeq005.RunsFrom Actual.code
      ⟨0,(PSTRTMSeq005.rightCfg (a:=controllerCap) packetLast).Tape⟩ capTrace (Actual.final (x*y)) :=
    ⟨capRun.1,capRun.2.1,capRun.2.2.1,capRun.2.2.2.1⟩
  let trace := frontTrace.map (PSTRTMSeq005.leftCfg (b:=1582)) ++
    capTrace.map (PSTRTMSeq005.rightCfg (a:=packetCap))
  have actual : Runs code (encode [.rational x,.rational y]) trace (final x y) :=
    PSTRTMSeq005.seq_runs packetMachine Actual.code _ _ _ frontTrace capTrace prefixRun capFrom
  have one : 1 ≤ inputLength x y+1 := by omega
  have twoFour : (inputLength x y+1)^2 ≤ (inputLength x y+1)^4 :=
    Nat.pow_le_pow_right one (by decide : 2 ≤ 4)
  have threeFour : (inputLength x y+1)^3 ≤ (inputLength x y+1)^4 :=
    Nat.pow_le_pow_right one (by decide : 3 ≤ 4)
  have width := product_width_le x y
  have packetPower : (natBits (x*y).num.natAbs+natBits (x*y).den+1)^2 ≤
      (inputLength x y+1)^4 :=
    (Nat.pow_le_pow_left (by omega : natBits (x*y).num.natAbs+natBits (x*y).den+1 ≤ inputLength x y+1) 2).trans twoFour
  have packetBound := packetTime.trans (Nat.mul_le_mul_left 256 packetPower)
  have size : Restore.inputSize (x*y)+2 ≤ 8*(inputLength x y+1) := by
    have outputSize := raw_product_length_le x y
    have packetSize := cap_packet_length (x*y)
    change (encode [.rational (x*y)]).length ≤ 2*inputLength x y at outputSize
    unfold Restore.inputSize
    omega
  have capPower : (Restore.inputSize (x*y)+2)^3 ≤ 512*(inputLength x y+1)^4 := by
    have bound := Nat.pow_le_pow_left size 3
    have cube : (Restore.inputSize (x*y)+2)^3 ≤ 512*(inputLength x y+1)^3 := by
      simpa only [Nat.mul_pow,show (8 : Nat)^3=512 by decide] using bound
    exact cube.trans (Nat.mul_le_mul_left 512 threeFour)
  have capBound := capTime.trans (Nat.mul_le_mul_left 134217728 capPower)
  change rawTrace.length ≤ mulTimeCoefficient*(inputLength x y+1)^4 at rawTime
  have totalTime : trace.length ≤ time x y := by
    simp only [trace,frontTrace,List.length_append,List.length_map]
    calc
      rawTrace.length+packetTrace.length+capTrace.length ≤
          (mulTimeCoefficient*(inputLength x y+1)^4+256*(inputLength x y+1)^4)+
            134217728*(512*(inputLength x y+1)^4) :=
        Nat.add_le_add (Nat.add_le_add rawTime packetBound) capBound
      _ = time x y := by unfold time timeCoefficient; ring
  refine ⟨trace,actual,totalTime,?_⟩
  intro clock chargedInputLength
  have space := PSTRTMTrace002.visitedSpace_le code chargedInputLength (trace.take clock)
  have taken : (trace.take clock).length ≤ trace.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  omega

theorem window_original_bound (x y : Rat) (spare : Nat) :
    window x y spare ≤ (timeCoefficient+spare+2)*(inputLength x y+1)^4 := by
  have power : inputLength x y+1 ≤ (inputLength x y+1)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ inputLength x y+1) (by decide : 1 ≤ 4)
  have margin : 2*inputLength x y+spare+2 ≤ (spare+2)*(inputLength x y+1) := by
    nlinarith [Nat.zero_le (spare*inputLength x y)]
  calc
    window x y spare = time x y+(2*inputLength x y+spare+2) := by unfold window; omega
    _ ≤ time x y+(spare+2)*(inputLength x y+1) := Nat.add_le_add_left margin _
    _ ≤ time x y+(spare+2)*(inputLength x y+1)^4 := Nat.add_le_add_left (Nat.mul_le_mul_left _ power) _
    _ = (timeCoefficient+spare+2)*(inputLength x y+1)^4 := by unfold time; ring

/-- Frame the ENTIRE compound once. The same finite code preserves external
archive/suffix at their physical boundaries. Left credit is a windowPrefix of
the actual old cap tape (TRUE retains savedLeft); it is not called blank. -/
theorem framed_contract (x y : Rat) (positive : 0 < x*y) (archive suffix : List Bool)
    (spare left right : Nat) (leftRoom : window x y spare ≤ left) (rightRoom : window x y spare ≤ right) :
    ∃ (finalLeft finalRight : Nat) (trace : List (MachineState cap)) (last : MachineState cap),
      PSTRTMSeq005.RunsFrom code
        ⟨0,Tape.mk₂ (List.replicate left false++archive)
          (encode [.rational x,.rational y]++List.replicate (right+1-inputLength x y) false++suffix)⟩ trace last ∧
      last.q=(final x y).q ∧
      last.Tape=Tape.mk₂ (windowPrefix finalLeft (ListBlank.mk (oldLeft x y))++archive)
        (output x y++List.replicate (finalRight+1-(output x y).length) false++suffix) ∧
      spare ≤ finalLeft ∧ spare ≤ finalRight+1-(output x y).length ∧
      finalLeft+finalRight=left+right ∧ trace.length ≤ time x y ∧
      ∀ clock chargedInputLength, visitedSpace code chargedInputLength (trace.take clock) ≤
        chargedInputLength+2*time x y+1 := by
  obtain ⟨oldTrace,oldRun,oldTime,_oldSpace⟩ := original_contract x y positive
  have runFrom : PSTRTMSeq005.RunsFrom code (TM0.init (encode [.rational x,.rational y])) oldTrace (final x y) :=
    ⟨oldRun.1,oldRun.2.1,oldRun.2.2.1,oldRun.2.2.2.1⟩
  have leftBound : oldTrace.length ≤ left := by unfold window at leftRoom; omega
  have rightBound : oldTrace.length ≤ right := by unfold window at rightRoom; omega
  obtain ⟨finalLeft,finalRight,trace,run,length,_sameDisplacements,sum,leftSpent,rightSpent⟩ :=
    frame_runsFrom_budget code archive suffix oldTrace (TM0.init (encode [.rational x,.rational y]))
      (final x y) left right runFrom leftBound rightBound
  have inputFits : (encode [.rational x,.rational y]).length ≤ right+1 := by
    change inputLength x y ≤ right+1
    unfold window at rightRoom
    omega
  have outputLength := output_length_le x y
  have outputFits : (output x y).length ≤ finalRight+1 := by
    unfold window at rightRoom
    omega
  have initialTape : frameCfg left right archive suffix (TM0.init (encode [.rational x,.rational y])) =
      (⟨0,Tape.mk₂ (List.replicate left false++archive)
        (encode [.rational x,.rational y]++List.replicate (right+1-inputLength x y) false++suffix)⟩ : MachineState cap) := by
    unfold frameCfg TM0.init
    rw [frameTape_mk₁ _ _ _ _ _ inputFits]
    rfl
  rw [initialTape] at run
  refine ⟨finalLeft,finalRight,trace,frameCfg finalLeft finalRight archive suffix (final x y),run,rfl,?_,?_,?_,sum,?_,?_⟩
  · change frameTape (final x y).Tape finalLeft finalRight archive suffix = _
    rw [final_tape x y positive,final_tape_split,frameTape_mk₂,
      windowPrefix_mk_of_length (finalRight+1) (output x y) outputFits]
  · unfold window at leftRoom
    omega
  · unfold window at rightRoom
    omega
  · omega
  · intro clock chargedInputLength
    have space := PSTRTMTrace002.visitedSpace_le code chargedInputLength (trace.take clock)
    have taken : (trace.take clock).length ≤ trace.length := by rw [List.length_take]; exact Nat.min_le_right _ _
    omega

end RootB23.Threshold.Spatial.MulCap
