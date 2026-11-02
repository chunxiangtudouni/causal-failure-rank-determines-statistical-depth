module
public import Common.PSTR_TM_ThresholdCursor_115
public import Common.PSTR_TM_ThresholdDepthTrace_117

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdFields118
open PaperProofs.Common.Native.RationalControllerComputation

def numeratorLeft (risk : Rat) : List Bool :=
  false::true::false::false::PSTRTMRawNat010.leftBlocks (PSTRTMThresholdRisk114.first risk).reverse
def depthContext (risk : Rat) : List Bool := false::
  (PSTRTMRawNat010.leftBlocks (PSTRTMThresholdRisk114.second risk).reverse++numeratorLeft risk)
def cursorTrace (risk : Rat) (depth : Nat) : List (MachineState 2) :=
  PSTRTMThresholdCursor115.cursorTrace (numeratorLeft risk) (PSTRTMThresholdRisk114.second risk) (encodeNat depth++[true])
def cursorFinal (risk : Rat) (depth : Nat) : MachineState 2 :=
  PSTRTMThresholdCursor115.state 2 (false::depthContext risk) (encodeNat depth++[true])
def preparationMachine : Machine 146 := PSTRTMSeq005.seqMachine PSTRTMThresholdRisk114.riskMachine PSTRTMThresholdCursor115.cursorMachine
/-- ONE fixed167-label ORIGINAL threshold-input parser. Numerator and
denominator survive in the actual left archive; the natural depth field is
actually decoded and the original list-end true ACTUALLY cleared to00.
This is a real front end for the original threshold machine, NOT a change
of its input to supplied arithmetic fields or a five-Datum output claim. -/
def fieldsMachine : Machine 166 := PSTRTMSeq005.seqMachine preparationMachine PSTRTMThresholdDepthCode116.depthMachine
def preparationTrace (risk : Rat) (depth : Nat) : List (MachineState 146) :=
  (PSTRTMThresholdRisk114.riskTrace risk depth).map (PSTRTMSeq005.leftCfg (b:=2)) ++
    (cursorTrace risk depth).map (PSTRTMSeq005.rightCfg (a:=143))
def preparationFinal (risk : Rat) (depth : Nat) : MachineState 146 := PSTRTMSeq005.rightCfg (a:=143) (cursorFinal risk depth)
def fieldsTrace (risk : Rat) (depth : Nat) : List (MachineState 166) :=
  (preparationTrace risk depth).map (PSTRTMSeq005.leftCfg (b:=19)) ++
    (PSTRTMThresholdDepthTrace117.depthTrace (depthContext risk) [] (PSTRTMNatValue017.rawPayload depth) []).map (PSTRTMSeq005.rightCfg (a:=146))
def fieldsFinal (risk : Rat) (depth : Nat) : MachineState 166 := PSTRTMSeq005.rightCfg (a:=146)
  (PSTRTMThresholdDepthCode116.state 16 (false::depthContext risk)
    (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload depth)++[false,false]))

theorem preparation_runs (risk : Rat) (depth : Nat) (hr : 0<risk) :
    Runs preparationMachine (encode [.rational risk,.natural depth]) (preparationTrace risk depth) (preparationFinal risk depth) := by
  apply PSTRTMSeq005.seq_runs PSTRTMThresholdRisk114.riskMachine PSTRTMThresholdCursor115.cursorMachine
    (encode [.rational risk,.natural depth]) (PSTRTMThresholdRisk114.riskFinal risk depth) (cursorFinal risk depth)
    (PSTRTMThresholdRisk114.riskTrace risk depth) (cursorTrace risk depth) (PSTRTMThresholdRisk114.risk_runs risk depth hr)
  have h := PSTRTMThresholdCursor115.cursor_runsFrom (numeratorLeft risk) (PSTRTMThresholdRisk114.second risk) (encodeNat depth++[true])
  rw [PSTRTMThresholdRisk114.risk_final_tape]
  exact h

theorem preparation_final_tape (risk : Rat) (depth : Nat) : (preparationFinal risk depth).Tape=
    Turing.Tape.mk₂ (false::depthContext risk) (encodeNat depth++[true]) := rfl

theorem raw_depth_encoding (depth : Nat) : PSTRTMTwoRawOperands029.rawInput (PSTRTMNatValue017.rawPayload depth)=encodeNat depth := by
  simp [PSTRTMTwoRawOperands029.rawInput,PSTRTMNatValue017.rawPayload,encodeNat,List.append_assoc]

theorem fields_runs (risk : Rat) (depth : Nat) (hr : 0<risk) :
    Runs fieldsMachine (encode [.rational risk,.natural depth]) (fieldsTrace risk depth) (fieldsFinal risk depth) := by
  apply PSTRTMSeq005.seq_runs preparationMachine PSTRTMThresholdDepthCode116.depthMachine
    (encode [.rational risk,.natural depth]) (preparationFinal risk depth)
    (PSTRTMThresholdDepthCode116.state 16 (false::depthContext risk)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload depth)++[false,false]))
    (preparationTrace risk depth)
    (PSTRTMThresholdDepthTrace117.depthTrace (depthContext risk) [] (PSTRTMNatValue017.rawPayload depth) [])
    (preparation_runs risk depth hr)
  have h := PSTRTMThresholdDepthTrace117.depth_runsFrom (depthContext risk) (PSTRTMNatValue017.rawPayload depth) []
  rw [preparation_final_tape]
  simpa only [raw_depth_encoding,List.append_nil,PSTRTMThresholdDepthCode116.state] using h

/-- ENTIRE real tape: the retained risk fields/markers are explicit left
data, and depth has a genuine blank right tail. This00 comes from the
actual original-list-end write in116, not a textual one-false delimiter. -/
theorem fields_final_tape (risk : Rat) (depth : Nat) : (fieldsFinal risk depth).Tape=
    Turing.Tape.mk₂ (false::depthContext risk) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload depth)) := by
  have hz (bits : List Bool) : Turing.ListBlank.mk (bits++[false,false])=Turing.ListBlank.mk bits := by
    calc
      _ = Turing.ListBlank.mk ((bits++[false])++[false]) := by rw [List.append_assoc]; rfl
      _ = Turing.ListBlank.mk (bits++[false]) := PSTRTMRawNat010.blank_append_false _
      _ = Turing.ListBlank.mk bits := PSTRTMRawNat010.blank_append_false _
  simp only [fieldsFinal,PSTRTMSeq005.rightCfg,PSTRTMThresholdDepthCode116.state,Turing.Tape.mk₂,hz]

theorem field_values (risk : Rat) (depth : Nat) :
    PSTRTMIncrement009.valueDigits (PSTRTMThresholdRisk114.first risk)=risk.num.natAbs ∧
    PSTRTMIncrement009.valueDigits (PSTRTMThresholdRisk114.second risk)=risk.den ∧
    PSTRTMIncrement009.valueDigits (PSTRTMNatValue017.rawPayload depth)=depth :=
  ⟨PSTRTMNatValue017.valueDigits_rawPayload _,PSTRTMNatValue017.valueDigits_rawPayload _,PSTRTMNatValue017.valueDigits_rawPayload _⟩

private theorem payload_length (value : Nat) : (PSTRTMNatValue017.rawPayload value).length=natBits value := by
  simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn]
theorem depth_bits_le (risk : Rat) (depth : Nat) (hr : 0<risk) :
    natBits depth ≤ (encode [.rational risk,.natural depth]).length+1 := by
  rw [PSTRTMThresholdStrip113.original_input risk depth hr]
  simp only [PSTRTMThresholdStrip113.headerBits,PSTRTMThresholdStrip113.rawSuffix,List.length_append,List.length_cons,
    List.length_nil,PSTRTMLength004.encodeNat_length]
  omega

private theorem arithmetic_length_bound (riskTime denominator depth input : Nat)
    (hp : riskTime≤512*(input+1)^2) (hn : denominator≤ input+1) (hd : depth≤ input+1) :
    (riskTime+(2*denominator+3))+(depth^2+11*depth+6) ≤ 2048*(input+1)^2 := by
  have hd2 := Nat.pow_le_pow_left hd 2
  nlinarith

private theorem arithmetic_space_bound (input time space : Nat)
    (ht : time≤2048*(input+1)^2) (hs : space≤ input+2*time+1) : space≤8192*(input+1)^2 := by
  nlinarith

theorem fields_length_le (risk : Rat) (depth : Nat) (hr : 0<risk) :
    (fieldsTrace risk depth).length ≤ 2048*((encode [.rational risk,.natural depth]).length+1)^2 := by
  have hp := PSTRTMThresholdRisk114.risk_length_le risk depth hr
  have hw := PSTRTMThresholdRisk114.original_widths_le risk depth hr
  have hn : natBits risk.den ≤ (encode [.rational risk,.natural depth]).length+1 := by omega
  have hd := depth_bits_le risk depth hr
  simp only [fieldsTrace,preparationTrace,List.length_append,List.length_map,cursorTrace,
    PSTRTMThresholdCursor115.cursor_length,PSTRTMThresholdRisk114.second_length,
    PSTRTMThresholdDepthTrace117.depth_length,List.length_nil,Nat.mul_zero,Nat.add_zero,payload_length]
  exact arithmetic_length_bound _ _ _ _ hp hn hd

theorem fields_visitedSpace_le (risk : Rat) (depth : Nat) (hr : 0<risk) :
    visitedSpace fieldsMachine (encode [.rational risk,.natural depth]).length (fieldsTrace risk depth) ≤
      8192*((encode [.rational risk,.natural depth]).length+1)^2 := by
  have hs := PSTRTMTrace002.visitedSpace_le fieldsMachine (encode [.rational risk,.natural depth]).length (fieldsTrace risk depth)
  have ht := fields_length_le risk depth hr
  exact arithmetic_space_bound _ _ _ ht hs

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdFields118
