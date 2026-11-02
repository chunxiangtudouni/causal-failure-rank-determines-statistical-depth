module
public import Structure.RootB23_Threshold_RiskSerialize_015
public import Structure.RootB23_Threshold_FactorGap_016

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.BarePacket
open PaperProofs.Common.Native.RationalControllerComputation Turing
open PA17TMRatArithmeticWidth018 (BoundedRun)

def denRiskCode : Machine 1574 := PSTRTMSeq005.seqMachine DenominatorCopy.code RiskSerialize.code
def factorEntryCode : Machine 1576 := PSTRTMSeq005.seqMachine denRiskCode PA17TMRatArithmeticParse002.backOneMachine
def tailCode : Machine 1634 := PSTRTMSeq005.seqMachine factorEntryCode FactorGap.code
def machine : Machine 4405 := PSTRTMSeq005.seqMachine NumeratorCopy.machine tailCode

def tailCost (risk : Rat) (depth b : List Bool) (gap n : ℕ) : ℕ :=
  DenominatorCopy.cost (PSTRTMNatValue017.rawPayload risk.num.natAbs)
    (PSTRTMNatValue017.rawPayload risk.den) depth b gap (n : Rat)+
    (2*natBits risk.num.natAbs+14+128*(natBits risk.num.natAbs+natBits risk.den+1)^2)+2+
    128*(natBits n+1)^2

theorem tail_bounded (archive depth b : List Bool) (gap n : ℕ) (risk : Rat)
    (positive : 0<risk) (depthNonempty : depth≠[]) (bNonempty : b≠[]) :
    BoundedRun tailCode
      (Tape.mk₂ (RoutedCopy.destinationLeft 0
        (SourceRoutes.numFinish (PSTRTMNatValue017.rawPayload risk.den) depth b gap (n : Rat)
          (false::archive) (PSTRTMNatValue017.rawPayload risk.num.natAbs)))
        (PA17TMRatArithmeticCopy006.workspace (PSTRTMNatValue017.rawPayload risk.num.natAbs))) 1634
      (Tape.mk₂ (false::FactorWalk.bBase
        (FactorWalk.markedLeft (FactorWalk.markedLeft (false::archive)
          (PSTRTMNatValue017.rawPayload risk.num.natAbs)) (PSTRTMNatValue017.rawPayload risk.den)) depth b gap)
        (encodeDatum (.rational (n : Rat))++encodeDatum (.rational risk)++Uncapped.Serialize.remainder []))
      (tailCost risk depth b gap n) := by
  let num:=PSTRTMNatValue017.rawPayload risk.num.natAbs
  let den:=PSTRTMNatValue017.rawPayload risk.den
  let base:=SourceRoutes.numFinish den depth b gap (n : Rat) (false::archive) num
  have copied:=DenominatorCopy.actual_bounded archive num den depth b gap (n : Rat)
    (Nat.cast_nonneg n) depthNonempty bNonempty
  have serialized:=RiskSerialize.rational_bounded base risk positive
  have copiedTape : RoutedCopy.destinationLeft 0
      (DenominatorRoute.finish depth b num gap (n : Rat)
        (false::DenominatorCopy.sourceArchive archive num) den)=RiskSerialize.denLeft base num := rfl
  rw [copiedTape] at copied
  have backed : BoundedRun PA17TMRatArithmeticParse002.backOneMachine
      (Tape.mk₂ (false::base) (encodeDatum (.rational risk)++Uncapped.Serialize.remainder [])) 1
      (Tape.mk₂ base (false::(encodeDatum (.rational risk)++Uncapped.Serialize.remainder []))) 2 :=
    ⟨PA17TMRatArithmeticParse002.backOneTrace base false
        (encodeDatum (.rational risk)++Uncapped.Serialize.remainder []),
      PA17TMRatArithmeticParse002.backOne_runsFrom _ _ _,by rfl⟩
  have repaired:=FactorGap.actual_bounded
    (FactorWalk.bBase (FactorWalk.markedLeft (FactorWalk.markedLeft (false::archive) num) den) depth b gap)
    (encodeDatum (.rational risk)++Uncapped.Serialize.remainder []) n
  have actual:=((copied.seq serialized).seq backed).seq repaired
  have port : PSTRTMSeq005.rightLabel (a:=1576) (57 : Fin 58)=(1634 : Fin 1635) := by decide
  rw [port] at actual
  simpa only [tailCode,factorEntryCode,denRiskCode,tailCost,num,den,List.append_assoc] using actual

def west (risk : Rat) (depth : ℕ) : List Bool :=
  false::FactorWalk.bBase
    (FactorWalk.markedLeft (FactorWalk.markedLeft [false]
      (PSTRTMThresholdRiskSource233.numerator risk)) (PSTRTMThresholdRiskSource233.denominator risk))
    (PSTRTMThresholdBBackupEntry188.result risk depth).depth (FactorSource.bDigits risk depth)
    (PSTRTMThresholdBBackupEntry188.result risk depth).gap

theorem blank_remainder (left word : List Bool) :
    Tape.mk₂ left (word++Uncapped.Serialize.remainder [])=Tape.mk₂ left word := by
  change Tape.mk₂ left (word++[false,false,false,false])=Tape.mk₂ left word
  calc
    _=Tape.mk₂ left (word++[false,false,false]) := by
      simpa [List.append_assoc] using
        PA17TMRatArithmeticBankCopy024.tape_append_false left (word++[false,false,false])
    _=Tape.mk₂ left (word++[false,false]) := by
      simpa [List.append_assoc] using
        PA17TMRatArithmeticBankCopy024.tape_append_false left (word++[false,false])
    _=Tape.mk₂ left (word++[false]) := by
      simpa [List.append_assoc] using
        PA17TMRatArithmeticBankCopy024.tape_append_false left (word++[false])
    _=Tape.mk₂ left word := PA17TMRatArithmeticBankCopy024.tape_append_false left word

private theorem copy_cost_le (digits route scale : ℕ) (positive : 1≤scale)
    (width : digits≤scale) (cost : route≤16384*scale^2) :
    4*digits^2+(2*route+45)*digits+5*route+33≤131072*scale^3 := by
  have square:=Nat.pow_le_pow_left width 2
  have cube : scale^2≤scale^3 := Nat.pow_le_pow_right positive (by decide : 2≤3)
  have linear : scale≤scale^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤2)
  have multiply:=Nat.mul_le_mul cost width
  have identity : (16384*scale^2)*scale=16384*scale^3 := by ring
  rw [identity] at multiply
  have costCube:=cost.trans (Nat.mul_le_mul_left 16384 cube)
  have digitCube:=width.trans (linear.trans cube)
  have oneCube:=positive.trans (linear.trans cube)
  nlinarith only [square,cube,multiply,costCube,digitCube,oneCube]

private theorem extra_cost_le (risk : Rat) (depth : ℕ) (hr : 0<risk) (hd : 1≤depth) :
    NumeratorCopy.cost (PSTRTMThresholdRiskSource233.numerator risk)
        (PSTRTMThresholdRiskSource233.denominator risk) (PSTRTMThresholdBBackupEntry188.result risk depth).depth
        (FactorSource.bDigits risk depth) (PSTRTMThresholdBBackupEntry188.result risk depth).gap
        (FactorSource.factorValue risk depth : Rat)+
      tailCost risk (PSTRTMThresholdBBackupEntry188.result risk depth).depth (FactorSource.bDigits risk depth)
        (PSTRTMThresholdBBackupEntry188.result risk depth).gap (FactorSource.factorValue risk depth)
      ≤1048576*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
  let scale:=(encode [.rational risk,.natural depth]).length+depth+1
  let num:=PSTRTMThresholdRiskSource233.numerator risk
  let den:=PSTRTMThresholdRiskSource233.denominator risk
  let dep:=(PSTRTMThresholdBBackupEntry188.result risk depth).depth
  let b:=FactorSource.bDigits risk depth
  let gap:=(PSTRTMThresholdBBackupEntry188.result risk depth).gap
  let factor:=FactorSource.factorValue risk depth
  have positive : 1≤scale := by dsimp only [scale];omega
  have linear : scale≤scale^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤2)
  have cube : scale^2≤scale^3 := Nat.pow_le_pow_right positive (by decide : 2≤3)
  have numLength : num.length=natBits risk.num.natAbs := by
    simp only [num,PSTRTMThresholdRiskSource233.numerator,PSTRTMNatValue017.rawPayload,List.length_ofFn]
  have denLength : den.length=natBits risk.den := by
    simp only [den,PSTRTMThresholdRiskSource233.denominator,PSTRTMNatValue017.rawPayload,List.length_ofFn]
  have depLength : dep.length=natBits depth := PSTRTMThresholdRiskReturnBudget230.result_depth_length risk depth hd
  have bLength : b.length=natBits (PaperProofs.Statistics.controllerB risk depth) := by
    simp only [b,FactorSource.bDigits,PSTRTMNatValue017.rawPayload,List.length_ofFn]
  have riskWidth:=PSTRTMThresholdRisk114.original_widths_le risk depth hr
  have backupWidth:=PSTRTMThresholdBackup139.original_width_le risk depth hr
  rw [PSTRTMThresholdDepthSource184.depth_length] at backupWidth
  have bWidth:=PSTRTMThresholdBBackupCost189.controllerB_bits_le risk depth hr hd
  have factorWidth:=PSTRTMThresholdBadFactor226.factor_bits_le risk depth hr hd
  have gapWidth:=PSTRTMThresholdRiskReturnBudget230.result_gap_le risk depth hr hd
  have numSmall : num.length≤scale := by rw [numLength];dsimp only [scale];omega
  have denSmall : den.length≤scale := by rw [denLength];dsimp only [scale];omega
  have depSmall : dep.length≤scale := by rw [depLength];dsimp only [scale];omega
  have bSmall : b.length≤5*scale := by rw [bLength];dsimp only [scale];omega
  have factorSmall : natBits factor+2≤7*scale := by
    change natBits factor≤_ at factorWidth
    dsimp only [scale];omega
  have gapSmall : gap≤64*scale^2 := gapWidth
  have factorSquare:=Nat.pow_le_pow_left factorSmall 2
  have routeBase : SourceRoutes.denCost dep b gap (factor : Rat)≤8192*scale^2 := by
    have unitBits : natBits 1=1 := by decide
    simp only [SourceRoutes.denCost,Rat.num_natCast,Int.natAbs_natCast,Rat.den_natCast,unitBits]
    nlinarith only [depSmall,bSmall,gapSmall,factorSquare,positive,linear]
  have numRoute : SourceRoutes.numCost den dep b gap (factor : Rat)≤16384*scale^2 := by
    dsimp only [SourceRoutes.numCost]
    omega
  have denRoute : DenominatorRoute.cost dep b num gap (factor : Rat)≤16384*scale^2 := by
    dsimp only [DenominatorRoute.cost]
    omega
  have numCopy:=copy_cost_le num.length (SourceRoutes.numCost den dep b gap (factor : Rat)) scale
    positive numSmall numRoute
  have denCopy:=copy_cost_le den.length (DenominatorRoute.cost dep b num gap (factor : Rat)) scale
    positive denSmall denRoute
  have denRouteCube:=denRoute.trans (Nat.mul_le_mul_left 16384 cube)
  have numCube:=numSmall.trans (linear.trans cube)
  have denCube:=denSmall.trans (linear.trans cube)
  have oneCube:=positive.trans (linear.trans cube)
  have serializerWidth : natBits risk.num.natAbs+natBits risk.den+1≤2*scale := by
    dsimp only [scale];omega
  have serializerSquare:=Nat.pow_le_pow_left serializerWidth 2
  have serializer : 2*natBits risk.num.natAbs+14+
      128*(natBits risk.num.natAbs+natBits risk.den+1)^2≤1024*scale^3 := by
    rw [←numLength]
    rw [←numLength] at serializerSquare
    nlinarith only [serializerSquare,numCube,oneCube,cube]
  have repairWidth : natBits factor+1≤7*scale := by omega
  have repairSquare:=Nat.pow_le_pow_left repairWidth 2
  have repair : 128*(natBits factor+1)^2≤8192*scale^3 := by
    nlinarith only [repairSquare,cube]
  change (4*num.length^2+(2*SourceRoutes.numCost den dep b gap (factor : Rat)+45)*num.length+
      5*SourceRoutes.numCost den dep b gap (factor : Rat)+33)+
    ((2*den.length+2*num.length+DenominatorRoute.cost dep b num gap (factor : Rat)+2+
      (4*den.length^2+(2*DenominatorRoute.cost dep b num gap (factor : Rat)+45)*den.length+
        5*DenominatorRoute.cost dep b num gap (factor : Rat)+33))+
      (2*natBits risk.num.natAbs+14+128*(natBits risk.num.natAbs+natBits risk.den+1)^2)+2+
      128*(natBits factor+1)^2)≤1048576*scale^3
  omega

/-- ONE fixed Bool program produces the genuine continuous bare two-Rat
packet from the original risk/depth input. The original risk, exhausted
depth and B archive all remain on the very same WEST tape. No window,
width, room, numerical answer or control fuel is supplied as input. -/
theorem original_bare_actual (risk : Rat) (depth : ℕ) (hr : 0<risk) (hd : 1≤depth) :
    ∃ trace final, Runs machine (encode [.rational risk,.natural depth]) trace final ∧
      final.Tape=Tape.mk₂ (west risk depth)
        (encodeDatum (.rational (FactorSource.factorValue risk depth : Rat))++encodeDatum (.rational risk)) ∧
      trace.length≤268435456*((encode [.rational risk,.natural depth]).length+depth+1)^3 ∧
      ∀ clock, visitedSpace machine (encode [.rational risk,.natural depth]).length (trace.take clock)≤
        1073741824*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
  obtain ⟨front,before,first,whole,firstTime⟩:=NumeratorCopy.original_numerator_actual risk depth hr hd
  have depthNonempty:=PSTRTMThresholdRiskReturnBudget230.result_depth_ne_nil risk depth hd
  have bNonempty : FactorSource.bDigits risk depth≠[] := by
    intro equal
    have length:=congrArg List.length equal
    simp only [FactorSource.bDigits,PSTRTMNatValue017.rawPayload,List.length_ofFn,List.length_nil] at length
    have positive : 1≤natBits (PaperProofs.Statistics.controllerB risk depth) := by dsimp only [natBits];omega
    omega
  obtain ⟨part,second,partTime⟩:=tail_bounded [] (PSTRTMThresholdBBackupEntry188.result risk depth).depth
    (FactorSource.bDigits risk depth) (PSTRTMThresholdBBackupEntry188.result risk depth).gap
    (FactorSource.factorValue risk depth) risk hr depthNonempty bNonempty
  let output:=encodeDatum (.rational (FactorSource.factorValue risk depth : Rat))++encodeDatum (.rational risk)
  have lastTape : Tape.mk₂ (west risk depth) (output++Uncapped.Serialize.remainder [])=
      Tape.mk₂ (west risk depth) output := blank_remainder _ _
  have second' : PSTRTMSeq005.RunsFrom tailCode ⟨0,before.Tape⟩ part
      ⟨1634,Tape.mk₂ (west risk depth) output⟩ := by
    rw [whole]
    rw [←lastTape]
    exact second
  let trace:=front.map (PSTRTMSeq005.leftCfg (b:=1634))++part.map (PSTRTMSeq005.rightCfg (a:=2770))
  let final : MachineState 4405:=PSTRTMSeq005.rightCfg (a:=2770)
    (⟨1634,Tape.mk₂ (west risk depth) output⟩ : MachineState 1634)
  have actual : Runs machine (encode [.rational risk,.natural depth]) trace final :=
    PSTRTMSeq005.seq_runs NumeratorCopy.machine tailCode _ before _ front part first second'
  have extra:=extra_cost_le risk depth hr hd
  have time : trace.length≤268435456*((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
    simp only [trace,List.length_append,List.length_map]
    omega
  refine ⟨trace,final,actual,rfl,time,?_⟩
  intro clock
  have space:=PSTRTMTrace002.visitedSpace_le machine (encode [.rational risk,.natural depth]).length (trace.take clock)
  have taken : (trace.take clock).length≤trace.length := by rw [List.length_take];exact Nat.min_le_right _ _
  have inputCube : (encode [.rational risk,.natural depth]).length+1≤
      ((encode [.rational risk,.natural depth]).length+depth+1)^3 := by
    have positive : 1≤(encode [.rational risk,.natural depth]).length+depth+1 := by omega
    have power:=Nat.pow_le_pow_right positive (by decide : 1≤3)
    simp only [pow_one] at power
    omega
  omega

end RootB23.Threshold.BarePacket
