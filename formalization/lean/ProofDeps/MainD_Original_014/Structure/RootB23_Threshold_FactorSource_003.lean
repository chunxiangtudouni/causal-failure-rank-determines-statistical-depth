module
public import Structure.RootB23_Threshold_NatSplice_001
public import Common.PSTR_TM_ThresholdIntegerDatum_217
public import Common.PSTR_TM_ThresholdRiskSource_233

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
@[expose] public section
namespace RootB23.Threshold.FactorSource
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)

def factorValue (risk : Rat) (depth : ℕ) : ℕ := PSTRTMThresholdBadFactor226.factor risk depth
def archive (risk : Rat) (depth : ℕ) : List Bool :=
  PSTRTMThresholdBackupReturn227.sourceLeft (PSTRTMThresholdBBackupEntry188.sourceArchive risk depth)
    (PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth))
def factorDatum (risk : Rat) (depth : ℕ) : List Bool := encodeDatum (.rational (factorValue risk depth : Rat))

/-- The integer factor is physically computed, normalized and serialized.
Both original near guards are consumed by the real Rat tag/sign writes. -/
def factorMachine : Machine 1370 := PSTRTMSeq005.seqMachine
  PSTRTMThresholdBadFactor226.factorMachine PSTRTMThresholdIntegerDatum217.integerDatumMachine

def factorFinal (risk : Rat) (depth : ℕ) : MachineState 1370 :=
  PSTRTMSeq005.rightCfg (a:=1330)
    (PSTRTMThresholdIntegerDatum217.integerDatumFinal (archive risk depth) (factorValue risk depth))

private theorem weighted_square (amount width scale : ℕ)
    (cost : amount ≤ 64*(width+1)^2) (room : width+1 ≤ 7*scale) :
    amount ≤ 3136*scale^2 := by
  have square:=Nat.pow_le_pow_left room 2
  nlinarith only [cost,square]

theorem factor_actual (risk : Rat) (depth : ℕ) (hr : 0<risk) (hd : 1 ≤ depth) :
    ∃ trace, Runs factorMachine (encode [.rational risk,.natural depth]) trace (factorFinal risk depth) ∧
      (factorFinal risk depth).Tape=Tape.mk₂ (archive risk depth) (factorDatum risk depth) ∧
      trace.length ≤ 67108864*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
  let first:=PSTRTMThresholdBadFactor226.factorTrace risk depth
  let later:=PSTRTMThresholdIntegerDatum217.integerDatumTrace (archive risk depth) (factorValue risk depth)
  let trace:=first.map (PSTRTMSeq005.leftCfg (b:=39))++later.map (PSTRTMSeq005.rightCfg (a:=1330))
  have actual : Runs factorMachine (encode [.rational risk,.natural depth]) trace (factorFinal risk depth) := by
    apply PSTRTMSeq005.seq_runs PSTRTMThresholdBadFactor226.factorMachine
      PSTRTMThresholdIntegerDatum217.integerDatumMachine _
      (PSTRTMThresholdBadFactor226.factorFinal risk depth)
      (PSTRTMThresholdIntegerDatum217.integerDatumFinal (archive risk depth) (factorValue risk depth))
      first later (PSTRTMThresholdBadFactor226.factor_runs risk depth hr hd)
    rw [PSTRTMThresholdBackupReturn227.original_factor_entry]
    exact PSTRTMThresholdIntegerDatum217.integerDatum_runsFrom _ _
  have firstTime:=PSTRTMThresholdBadFactor226.factor_time_le risk depth hr hd
  have laterTime:=PSTRTMThresholdIntegerDatum217.integerDatum_time_le (archive risk depth) (factorValue risk depth)
  have width:=PSTRTMThresholdBadFactor226.factor_bits_le risk depth hr hd
  let scale:=(encode [.rational risk,.natural depth]).length+depth+1
  have positive : 1 ≤ scale := by dsimp only [scale];omega
  have widthScale : natBits (factorValue risk depth)+1 ≤ 7*scale := by
    change natBits (factorValue risk depth) ≤ _ at width
    dsimp only [scale];omega
  have cube : scale^2 ≤ scale^3 := Nat.pow_le_pow_right positive (by decide : 2 ≤ 3)
  have laterSmall : later.length ≤ 3136*scale^2 := weighted_square _ _ _ laterTime widthScale
  have laterCube:=laterSmall.trans (Nat.mul_le_mul_left 3136 cube)
  refine ⟨trace,actual,?_,?_⟩
  · change (PSTRTMThresholdIntegerDatum217.integerDatumFinal _ _).Tape=_
    exact PSTRTMThresholdIntegerDatum217.integerDatum_final_tape _ _
  · simp only [trace,List.length_append,List.length_map]
    change first.length+later.length ≤ 67108864*scale^3
    change first.length ≤ 33554432*scale^3 at firstTime
    omega

def bDigits (risk : Rat) (depth : ℕ) : List Bool :=
  PSTRTMNatValue017.rawPayload (PaperProofs.Statistics.controllerB risk depth)
def bSuffix (risk : Rat) (depth : ℕ) : List Bool :=
  PSTRTMIncrement009.blocks (bDigits risk depth)++factorDatum risk depth
def depthSuffix (risk : Rat) (depth : ℕ) : List Bool :=
  PSTRTMIncrement009.blocks (PSTRTMThresholdBBackupEntry188.result risk depth).depth++
    List.replicate (2*(PSTRTMThresholdBBackupEntry188.result risk depth).gap+2) false++bSuffix risk depth
def sourceRight (risk : Rat) (depth : ℕ) : List Bool :=
  PSTRTMIncrement009.blocks (PSTRTMThresholdRiskSource233.numerator risk)++
    PSTRTMThresholdRiskMarkers232.markerTail
      (PSTRTMIncrement009.blocks (PSTRTMThresholdRiskSource233.denominator risk)++
        PSTRTMThresholdRiskMarkers232.markerTail (depthSuffix risk depth))

/-- Unlike227, no two FALSE guards are pretended to survive the Rat
writer. The exact nearest-field EOF is already under the current head. -/
def bDepthMachine : Machine 12 := PSTRTMSeq005.seqMachine
  PSTRTMMulRewind085.rewindMachine PSTRTMThresholdRiskReturn228.depthMachine
def returnMachine : Machine 30 := PSTRTMSeq005.seqMachine
  bDepthMachine PSTRTMThresholdRiskMarkers232.riskFieldsMachine

theorem return_actual (risk : Rat) (depth : ℕ) (hd : 1 ≤ depth) :
    BoundedRun returnMachine (Tape.mk₂ (archive risk depth) (factorDatum risk depth)) 30
      (Tape.mk₂ [false] (sourceRight risk depth))
      (2*(bDigits risk depth).length+2*(PSTRTMThresholdBBackupEntry188.result risk depth).gap+
        2*(PSTRTMThresholdBBackupEntry188.result risk depth).depth.length+
        2*((PSTRTMThresholdRiskSource233.numerator risk).length+
          (PSTRTMThresholdRiskSource233.denominator risk).length)+31) := by
  have nonempty:=PSTRTMThresholdRiskReturnBudget230.result_depth_ne_nil risk depth hd
  cases reversed : (PSTRTMThresholdBBackupEntry188.result risk depth).depth.reverse with
  | nil =>
    have equal:=congrArg List.reverse reversed
    simp only [List.reverse_reverse,List.reverse_nil] at equal
    exact False.elim (nonempty equal)
  | cons bit earlier =>
    have original : (bit::earlier).reverse=(PSTRTMThresholdBBackupEntry188.result risk depth).depth := by
      rw [←reversed,List.reverse_reverse]
    have reverseLength:=congrArg List.length reversed
    simp only [List.length_reverse,List.length_cons] at reverseLength
    have rewind : BoundedRun PSTRTMMulRewind085.rewindMachine
        (Tape.mk₂ (archive risk depth) (factorDatum risk depth)) 3
        (Tape.mk₂ (false::PSTRTMThresholdBBackupEntry188.sourceArchive risk depth) (bSuffix risk depth))
        (2*(bDigits risk depth).length+3) :=
      ⟨PSTRTMPairRewind105.fullTrace (PSTRTMThresholdBBackupEntry188.sourceArchive risk depth)
        (bDigits risk depth).reverse (factorDatum risk depth),
        PSTRTMPairRewind105.rewind_runsFrom _ _ _,by rw [PSTRTMPairRewind105.full_length,List.length_reverse]⟩
    have depthRun:=PSTRTMThresholdRiskReturn228.depth_runsFrom
      (PSTRTMThresholdDepthSource184.riskArchive risk) bit earlier (bSuffix risk depth)
      (2*(PSTRTMThresholdBBackupEntry188.result risk depth).gap+2)
    have entry : false::PSTRTMThresholdBBackupEntry188.sourceArchive risk depth=
        List.replicate (2*(PSTRTMThresholdBBackupEntry188.result risk depth).gap+2) false++
          (PSTRTMRawNat010.leftBlocks (bit::earlier)++false::PSTRTMThresholdDepthSource184.riskArchive risk) := by
      rw [←reversed,PSTRTMThresholdBBackupEntry188.sourceArchive,
        PSTRTMThresholdCounterSeek169.gaps_replicate]
      rw [show 2*(PSTRTMThresholdBBackupEntry188.result risk depth).gap+2=
        2+2*(PSTRTMThresholdBBackupEntry188.result risk depth).gap by omega,List.replicate_add]
      rfl
    rw [←entry] at depthRun
    have finalEq : PSTRTMThresholdRiskReturn228.depthFinal
        (PSTRTMThresholdDepthSource184.riskArchive risk) bit earlier (bSuffix risk depth)
        (2*(PSTRTMThresholdBBackupEntry188.result risk depth).gap+2)=
        (⟨8,Tape.mk₂ (false::PSTRTMThresholdDepthSource184.riskArchive risk) (depthSuffix risk depth)⟩ : MachineState 8) := by
      change (⟨PSTRTMSeq005.rightLabel (a:=4) (3 : Fin 4),_⟩ : MachineState 8)=_
      have labelEq : PSTRTMSeq005.rightLabel (a:=4) (3 : Fin 4)=(8 : Fin 9) := by decide
      rw [labelEq]
      simp only [depthSuffix,original]
      rfl
    rw [finalEq] at depthRun
    have back : BoundedRun PSTRTMThresholdRiskReturn228.depthMachine
        (Tape.mk₂ (false::PSTRTMThresholdBBackupEntry188.sourceArchive risk depth) (bSuffix risk depth)) 8
        (Tape.mk₂ (false::PSTRTMThresholdDepthSource184.riskArchive risk) (depthSuffix risk depth))
        (2*(PSTRTMThresholdBBackupEntry188.result risk depth).gap+2*earlier.length+12) :=
      ⟨_,depthRun,by rw [PSTRTMThresholdRiskReturn228.depth_length];omega⟩
    have fieldsRun:=PSTRTMThresholdRiskMarkers232.riskFields_runsFrom []
      (PSTRTMThresholdRiskSource233.numerator risk) (PSTRTMThresholdRiskSource233.denominator risk)
      (depthSuffix risk depth)
    rw [←PSTRTMThresholdRiskSource233.original_marker_entry] at fieldsRun
    have fieldsEq : PSTRTMThresholdRiskMarkers232.riskFieldsFinal []
        (PSTRTMThresholdRiskSource233.numerator risk) (PSTRTMThresholdRiskSource233.denominator risk)
        (depthSuffix risk depth)=
        (⟨17,Tape.mk₂ [false] (sourceRight risk depth)⟩ : MachineState 17) := by
      change (⟨PSTRTMSeq005.rightLabel (a:=8)
        (PSTRTMSeq005.rightLabel (a:=4) (3 : Fin 4)),_⟩ : MachineState 17)=_
      have labelEq : PSTRTMSeq005.rightLabel (a:=8)
          (PSTRTMSeq005.rightLabel (a:=4) (3 : Fin 4))=(17 : Fin 18) := by decide
      rw [labelEq]
      rfl
    rw [fieldsEq] at fieldsRun
    have fields : BoundedRun PSTRTMThresholdRiskMarkers232.riskFieldsMachine
        (Tape.mk₂ (false::PSTRTMThresholdDepthSource184.riskArchive risk) (depthSuffix risk depth)) 17
        (Tape.mk₂ [false] (sourceRight risk depth))
        (2*((PSTRTMThresholdRiskSource233.numerator risk).length+
          (PSTRTMThresholdRiskSource233.denominator risk).length)+16) := by
      exact ⟨PSTRTMThresholdRiskMarkers232.riskFieldsTrace []
        (PSTRTMThresholdRiskSource233.numerator risk) (PSTRTMThresholdRiskSource233.denominator risk)
        (depthSuffix risk depth),fieldsRun,by rw [PSTRTMThresholdRiskMarkers232.riskFields_length]⟩
    have actual:=(rewind.seq back).seq fields
    exact actual.mono (by omega)

def machine : Machine 1401 := PSTRTMSeq005.seqMachine factorMachine returnMachine

/-- Original risk/depth produce the canonical multiplication factor and
return to the SAME retained risk NUM/DEN. This is a packet precursor,
not a supplied packet or an assertion that RawMul has an archive ABI. -/
theorem original_source_actual (risk : Rat) (depth : ℕ) (hr : 0<risk) (hd : 1 ≤ depth) :
    ∃ trace final, Runs machine (encode [.rational risk,.natural depth]) trace final ∧
      final.Tape=Tape.mk₂ [false] (sourceRight risk depth) ∧
      trace.length ≤ 134217728*((encode [.rational risk,.natural depth]).length+depth+1)^3 ∧
      ∀ clock, visitedSpace machine (encode [.rational risk,.natural depth]).length (trace.take clock) ≤ 
        536870912*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
  obtain ⟨front,first,whole,firstTime⟩:=factor_actual risk depth hr hd
  obtain ⟨tail,second,tailTime⟩:=return_actual risk depth hd
  let final : MachineState 1401:=PSTRTMSeq005.rightCfg (a:=1370)
    (⟨30,Tape.mk₂ [false] (sourceRight risk depth)⟩ : MachineState 30)
  let trace:=front.map (PSTRTMSeq005.leftCfg (b:=30))++tail.map (PSTRTMSeq005.rightCfg (a:=1370))
  have actual : Runs machine (encode [.rational risk,.natural depth]) trace final := by
    apply PSTRTMSeq005.seq_runs factorMachine returnMachine _ (factorFinal risk depth)
      ⟨30,Tape.mk₂ [false] (sourceRight risk depth)⟩ front tail first
    rw [whole]
    exact second
  let scale:=(encode [.rational risk,.natural depth]).length+depth+1
  have positive : 1 ≤ scale := by dsimp only [scale];omega
  have inputSquare : (encode [.rational risk,.natural depth]).length+1 ≤ scale^2 := by
    have power:=Nat.pow_le_pow_right positive (by decide : 1 ≤ 2)
    simp only [pow_one] at power
    dsimp only [scale] at power ⊢
    omega
  have bWidth:=PSTRTMThresholdBBackupCost189.controllerB_bits_le risk depth hr hd
  have depthWidth:=PSTRTMThresholdBackup139.original_width_le risk depth hr
  rw [PSTRTMThresholdDepthSource184.depth_length] at depthWidth
  have depthLength:=PSTRTMThresholdRiskReturnBudget230.result_depth_length risk depth hd
  have riskWidth:=PSTRTMThresholdRisk114.original_widths_le risk depth hr
  have gap:=PSTRTMThresholdRiskReturnBudget230.result_gap_le risk depth hr hd
  have bLength : (bDigits risk depth).length=natBits (PaperProofs.Statistics.controllerB risk depth) := by
    simp only [bDigits,PSTRTMNatValue017.rawPayload,List.length_ofFn]
  have ndLength : (PSTRTMThresholdRiskSource233.numerator risk).length+
      (PSTRTMThresholdRiskSource233.denominator risk).length=natBits risk.num.natAbs+natBits risk.den := by
    simp only [PSTRTMThresholdRiskSource233.numerator,PSTRTMThresholdRiskSource233.denominator,
      PSTRTMNatValue017.rawPayload,List.length_ofFn]
  have tailSmall : tail.length ≤ 256*scale^2 := by
    rw [bLength,depthLength,ndLength] at tailTime
    change (PSTRTMThresholdBBackupEntry188.result risk depth).gap ≤ 64*scale^2 at gap
    have squarePos : 1 ≤ scale^2 := by simpa only [one_pow] using Nat.pow_le_pow_left positive 2
    omega
  have cube : scale^2 ≤ scale^3 := Nat.pow_le_pow_right positive (by decide : 2 ≤ 3)
  have tailCube:=tailSmall.trans (Nat.mul_le_mul_left 256 cube)
  have time : trace.length ≤ 134217728*scale^3 := by
    simp only [trace,List.length_append,List.length_map]
    change front.length ≤ 67108864*scale^3 at firstTime
    omega
  refine ⟨trace,final,actual,rfl,time,?_⟩
  intro clock
  have space:=PSTRTMTrace002.visitedSpace_le machine (encode [.rational risk,.natural depth]).length (trace.take clock)
  have taken : (trace.take clock).length ≤ trace.length := by
    rw [List.length_take];exact Nat.min_le_right _ _
  have inputCube:=inputSquare.trans cube
  change _ ≤ 536870912*scale^3
  omega

end RootB23.Threshold.FactorSource
