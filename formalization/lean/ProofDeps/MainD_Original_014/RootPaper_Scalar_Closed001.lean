module
public import RootB23_WordOddsBits_Public_003
public import Structure.RootB23_Threshold_ReturnOriginalActual_057
public import B23_4_WordTM0_Public002
public import Common.PSTR_TM_NativeLe_060
public import PSTR_WordBool_RatAddSub_Callees_001
public import PSTR_WordBool_RatCmp_API_001

/-! Paper price-proofs:294--297. Closed concrete binary primitives, with
explicit encoded input-copy and result-read lengths. This module constructs
no machine and assumes no per-call cost, width, window, or room oracle.
Numeric depth remains in the original threshold scale. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace RootPaper.Scalar
open Turing PaperProofs.Common.Native PaperProofs.Statistics
open RationalControllerComputation PSTRWordBool

def pairInput (x y : Rat) : List Bool := encode [.rational x,.rational y]

private theorem pay_copy (c input output : Nat) (short : output≤2*input) :
    c*(input+1)^4+input+output≤(c+3)*(input+1)^4 := by
  have power : input≤(input+1)^4 := (Nat.le_succ input).trans
    (by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ input+1) (by decide : 1 ≤ 4))
  rw [Nat.add_mul]
  omega

/-- Both actual signed branches, including cancellation and zero inputs.
The coefficient is from the concrete proved binary algorithm. -/
theorem add_sub_closed (subtract : Bool) (x y : Rat) :
    let result := if subtract then x-y else x+y
    computes (PA17TMRatArithmeticAddSubController075.addSubMachine subtract) (pairInput x y)
      (encode [.rational result])
      (RatAddSub.addSubCoefficient*((pairInput x y).length+1)^4)
      (RatAddSub.addSubCoefficient*((pairInput x y).length+1)^4) ∧
    (encode [.rational result]).length≤2*(pairInput x y).length ∧
    RatAddSub.addSubCoefficient*((pairInput x y).length+1)^4+
      (pairInput x y).length+(encode [.rational result]).length≤
      (RatAddSub.addSubCoefficient+3)*((pairInput x y).length+1)^4 := by
  dsimp only
  have run : computes (PA17TMRatArithmeticAddSubController075.addSubMachine subtract) (pairInput x y)
      (encode [.rational (if subtract then x-y else x+y)])
      (RatAddSub.addSubCoefficient*((pairInput x y).length+1)^4)
      (RatAddSub.addSubCoefficient*((pairInput x y).length+1)^4) := by
    cases subtract
    · exact PA17TMRatArithmeticAddSubFull079.original_add_computes x y
    · exact PA17TMRatArithmeticAddSubFull079.original_sub_computes x y
  have short : (encode [.rational (if subtract then x-y else x+y)]).length≤2*(pairInput x y).length := by
    cases subtract
    · exact PA17TMRatArithmeticNativeSize007.add_output_length_le x y
    · exact PA17TMRatArithmeticNativeSize007.sub_output_length_le x y
  exact ⟨run,short,pay_copy _ _ _ short⟩

theorem mul_closed (x y : Rat) :
    computes RatMulDiv.mulSource (pairInput x y) (encode [.rational (x*y)])
      (RatMulDiv.mulCoefficient*((pairInput x y).length+1)^4)
      (RatMulDiv.mulCoefficient*((pairInput x y).length+1)^4) ∧
    (encode [.rational (x*y)]).length≤2*(pairInput x y).length ∧
    RatMulDiv.mulCoefficient*((pairInput x y).length+1)^4+
      (pairInput x y).length+(encode [.rational (x*y)]).length≤
      (RatMulDiv.mulCoefficient+3)*((pairInput x y).length+1)^4 := by
  have run : computes RatMulDiv.mulSource (pairInput x y) (encode [.rational (x*y)])
      (RatMulDiv.mulCoefficient*((pairInput x y).length+1)^4)
      (RatMulDiv.mulCoefficient*((pairInput x y).length+1)^4) :=
    PA17TMRatArithmeticMulSuffix063.original_mul_computes x y
  have short := PA17TMRatArithmeticNativeSize007.mul_output_length_le x y
  exact ⟨run,short,pay_copy _ _ _ short⟩

/-- The original total Rat division semantics includes a zero divisor. -/
theorem div_closed (x y : Rat) :
    computes RatMulDiv.divSource (pairInput x y) (encode [.rational (x/y)])
      (RatMulDiv.divCoefficient*((pairInput x y).length+1)^4)
      (RatMulDiv.divCoefficient*((pairInput x y).length+1)^4) ∧
    (encode [.rational (x/y)]).length≤2*(pairInput x y).length ∧
    RatMulDiv.divCoefficient*((pairInput x y).length+1)^4+
      (pairInput x y).length+(encode [.rational (x/y)]).length≤
      (RatMulDiv.divCoefficient+3)*((pairInput x y).length+1)^4 := by
  have run : computes RatMulDiv.divSource (pairInput x y) (encode [.rational (x/y)])
      (RatMulDiv.divCoefficient*((pairInput x y).length+1)^4)
      (RatMulDiv.divCoefficient*((pairInput x y).length+1)^4) :=
    PA17TMRatArithmeticRatDivController070.original_div_computes x y
  have short := PA17TMRatArithmeticNativeSize007.div_output_length_le x y
  exact ⟨run,short,pay_copy _ _ _ short⟩

theorem pair_input_bits (x y : Rat) :
    (pairInput x y).length=2*PA17TMRatArithmeticNativeSize007.inputBits x y+14 :=
  PA17TMRatArithmeticNativeSize007.input_length x y

/-- Exact canonical Nat width, including zero. Measuring the digits requires
only traversing these digits; no loop over the represented numerical value. -/
theorem nat_input_bits (n : Nat) :
    (PSTRTMNatValue017.rawPayload n).length=natBits n ∧ (encodeNat n).length=2*natBits n+1 :=
  ⟨by simp only [PSTRTMNatValue017.rawPayload,List.length_ofFn],PSTRTMLength004.encodeNat_length n⟩

/-- A closed binary comparison run with copy/read costs paid explicitly. -/
theorem nat_le_closed (a b : Nat) :
    computes PSTRTMNativeLe060.nativeLeMachine (encodeNat a++encodeNat b)
      (encodeNat (if decide (a≤b) then 1 else 0))
      (4096*(natBits a+natBits b+1)^2) (16384*(natBits a+natBits b+1)^2) ∧
    (PSTRTMNativeLe060.nativeTrace a b).length+(encodeNat a++encodeNat b).length+
      (encodeNat (if decide (a≤b) then 1 else 0)).length≤4101*(natBits a+natBits b+1)^2 := by
  refine ⟨PSTRTMNativeLe060.encodeNat_le_computes a b,?_⟩
  have time:=PSTRTMNativeLe060.native_length_le a b
  have input : (encodeNat a++encodeNat b).length=2*(natBits a+natBits b+1) := by
    simp only [List.length_append,PSTRTMLength004.encodeNat_length]
    omega
  have output : (encodeNat (if decide (a≤b) then 1 else 0)).length=3 := by
    rw [PSTRTMNativeLe060.encodeNat_bool]
    rfl
  have positive : 1≤natBits a+natBits b+1 := by omega
  have square : natBits a+natBits b+1≤(natBits a+natBits b+1)^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤2)
  rw [input,output]
  omega

def comparisonClock (current : RatCmp.State Unit) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (RatCmp.program .halt point) current.var current.stk

private theorem sum_cap {α : Type*} (weight : α→Nat) (xs : List α) (cap : Nat)
    (each : ∀ x∈xs,weight x≤cap) : (xs.map weight).sum≤xs.length*cap := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have one:=each x List.mem_cons_self
    have later:=ih (fun y member=>each y (List.mem_cons_of_mem _ member))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def comparisonCoefficient : Nat := (RatCmp.coefficient+1024)*(16*(RatCmp.coefficient+1028)+1)+1

/-- Standalone signed rational comparison. The actual primitive-clock sum,
the canonical operand copy and the one-bit result are all paid. -/
theorem rational_le_closed (x y : Rat) :
    ∃ (path : List (RatCmp.State Unit)) (final : RatCmp.State Unit),
      RatCmp.Facts (RatCmp.program .halt) RatCmp.coefficient RatCmp.degree ()
        default default default (fun _=>[]) x y path final ∧
      final.stk 3=[decide (x≤y)] ∧
      path.length+(path.dropLast.map comparisonClock).sum+(pairInput x y).length+1≤
        comparisonCoefficient*((pairInput x y).length+1)^8 := by
  obtain ⟨path,final,facts⟩:=RatCmp.actual_le (.halt : RatCmp.Statement Unit) () default default default (fun _=>[]) x y
  let S:=(pairInput x y).length+1
  let Q:=S^4
  have positive : 1≤S := by dsimp only [S];omega
  have oneQ : 1≤Q := Nat.one_le_pow _ _ positive
  have small : S≤Q := by simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤4)
  have outside : IsolatedRat.outside (fun _ : RatInput.Stack=>[]) = 0 := by
    rfl
  have cap : RatCmp.scale RatCmp.coefficient RatCmp.degree (fun _=>[]) x y≤(RatCmp.coefficient+1024)*Q := by
    simp only [RatCmp.scale,outside,Nat.zero_add,Nat.mul_one,RatCmp.degree_eq_four]
    change 1024+RatCmp.coefficient*Q≤_
    rw [Nat.add_mul]
    omega
  have localClock : 16*(RatCmp.scale RatCmp.coefficient RatCmp.degree (fun _=>[]) x y+4)+1≤
      (16*(RatCmp.coefficient+1028)+1)*Q := by
    have four:=Nat.mul_le_mul_left 4 oneQ
    nlinarith only [cap,four,oneQ]
  have sum : (path.dropLast.map comparisonClock).sum≤
      path.length*(16*(RatCmp.scale RatCmp.coefficient RatCmp.degree (fun _=>[]) x y+4)) := by
    have each : ∀ current∈path.dropLast,comparisonClock current≤
        16*(RatCmp.scale RatCmp.coefficient RatCmp.degree (fun _=>[]) x y+4) := by
      intro current member
      cases active : current.l with
      | none => simp only [comparisonClock,active];exact Nat.zero_le _
      | some point =>
        simpa only [comparisonClock,active] using (facts.proper current member).2 point active |>.2
    exact (sum_cap comparisonClock path.dropLast _ each).trans
      (Nat.mul_le_mul_right _ (by rw [List.length_dropLast];omega))
  have time:=facts.time.trans cap
  have product:=Nat.mul_le_mul time localClock
  have paid : path.length+(path.dropLast.map comparisonClock).sum≤
      ((RatCmp.coefficient+1024)*(16*(RatCmp.coefficient+1028)+1))*S^8 := by
    calc
      _≤path.length*(16*(RatCmp.scale RatCmp.coefficient RatCmp.degree (fun _=>[]) x y+4)+1) := by
        rw [Nat.mul_add,Nat.mul_one]
        omega
      _≤((RatCmp.coefficient+1024)*Q)*((16*(RatCmp.coefficient+1028)+1)*Q) := product
      _=_ := by dsimp only [Q];ring
  have scale8 : S≤S^8 := by simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤8)
  refine ⟨path,final,facts,facts.result,?_⟩
  change path.length+(path.dropLast.map comparisonClock).sum+S≤comparisonCoefficient*S^8
  unfold comparisonCoefficient
  rw [Nat.add_mul,Nat.one_mul]
  exact Nat.add_le_add paid scale8

theorem word_output_length (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    (wordOutput E target word).length=2*RootB23.WordOddsBits.width (E.rationalWordOdds word)+18 := by
  have boolWidth (bit : Bool) : PSTRTMLength004.datumBits (boolDatum bit)=4 := by cases bit <;> rfl
  simp only [wordOutput,PSTRTMLength004.encode_length,List.length_cons,List.length_nil,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil]
  rw [boolWidth,boolWidth]
  simp only [PSTRTMLength004.datumBits]
  change 2*natBits 3+2+(2*RootB23.WordOddsBits.width (E.rationalWordOdds word)+4+(4+(4+0)))=_
  have three : natBits 3=2 := rfl
  rw [three]
  omega

theorem word_output_copy_bound (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    (wordInput E target word).length+(wordOutput E target word).length≤
      29*((wordInput E target word).length+word.1+1)^2 := by
  have odds:=RootB23.WordOddsBits.original_odds_width_le_input E target word
  rw [word_output_length]
  let B:=(wordInput E target word).length
  let S:=B+word.1+1
  have positive : 1≤S := by dsimp only [S];omega
  have input : B≤S := by dsimp only [S];omega
  have depth : word.1≤S := by dsimp only [S];omega
  have wide : RootB23.WordOddsBits.width (E.rationalWordOdds word)≤5*S^2 := by
    have first : (2*word.1+3)*B≤(2*S+3)*S := Nat.mul_le_mul (by omega) input
    have square : S≤S^2 := by simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤2)
    nlinarith only [odds,first,square]
  change B+(2*RootB23.WordOddsBits.width (E.rationalWordOdds word)+18)≤29*S^2
  have square : S≤S^2 := by simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤2)
  nlinarith only [wide,input,square,positive]

/-- Strongest existing original WORD entry; no new source is constructed.
Positive constants come from the proved complete original algorithm. -/
theorem word_closed :
    ∃ states : Nat,∃ code : Machine states,∃ port : Fin (states+1),∃ coefficient degree : Nat,
      0<coefficient ∧ 0<degree ∧
      ∀ (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord),
        ∃ trace final,Runs code (wordInput E target word) trace final ∧ final.q=port ∧
          TM0.step code final=none ∧ final.Tape.right₀=ListBlank.mk (wordOutput E target word) ∧
          trace.length+(wordInput E target word).length+(wordOutput E target word).length≤
            coefficient*((wordInput E target word).length+word.1+1)^degree ∧
          ∀ clock,visitedSpace code (wordInput E target word).length (trace.take clock)≤
            coefficient*((wordInput E target word).length+word.1+1)^degree := by
  obtain ⟨states,code,port,c,d,hc,hd,runs⟩:=B23_4_WordTM0.Public.original_actual
  refine ⟨states,code,port,c+29,d+2,by omega,by omega,?_⟩
  intro E target word
  obtain ⟨trace,final,run,atPort,halted,output,time,space⟩:=runs E target word
  let S:=(wordInput E target word).length+word.1+1
  have positive : 1≤S := by dsimp only [S];omega
  have oldPower : S^d≤S^(d+2) := Nat.pow_le_pow_right positive (by omega)
  have twoPower : S^2≤S^(d+2) := Nat.pow_le_pow_right positive (by omega)
  have time':=time.trans (Nat.mul_le_mul_left c oldPower)
  have copy':=(word_output_copy_bound E target word).trans (Nat.mul_le_mul_left 29 twoPower)
  refine ⟨trace,final,run,atPort,halted,output,?_,?_⟩
  · rw [Nat.add_mul]
    simpa only [S,Nat.add_assoc] using Nat.add_le_add time' copy'
  · intro clock
    exact (space clock).trans (Nat.mul_le_mul (by omega : c≤c+29) oldPower)

theorem threshold_output_length (risk : Rat) (depth : Nat) :
    (thresholdOutput risk depth).length=2*RootB23.Threshold.FinalSerialize.totalWidth (controllerB risk depth)
      (controllerTarget risk depth) (controllerBadRisk risk (controllerTarget risk depth))
      ((1-controllerTarget risk depth)/controllerTarget risk depth) (controllerTarget risk depth/(1-controllerTarget risk depth))+26 := by
  simp only [thresholdOutput,PSTRTMLength004.encode_length,List.length_cons,List.length_nil,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,PSTRTMLength004.datumBits,
    RootB23.Threshold.FinalSerialize.totalWidth,RootB23.Threshold.FinalSerialize.nineFields,
    PA17TMRatArithmeticParse002.numeratorDigits_length,PA17TMRatArithmeticParse002.denominatorDigits_length,
    PSTRTMNatValue017.rawPayload,List.length_ofFn]
  have five : natBits 5=3 := rfl
  rw [five]
  omega

/-- Full original THRESHOLD: risk>0 and depth>=1 are the mathematical
domain. Numeric depth, not just log depth, remains in the cost scale. -/
theorem threshold_closed (risk : Rat) (depth : Nat) (positive : 0<risk) (depthPositive : 1≤depth) :
    computes RootB23.Threshold.ReturnOriginalPacket.code (encode [.rational risk,.natural depth])
      (thresholdOutput risk depth)
      (RootB23.Threshold.ReturnOriginalPacket.timeCoefficient*RootB23.Threshold.OriginalBridge.scale risk depth^10)
      (RootB23.Threshold.ReturnOriginalPacket.spaceCoefficient*RootB23.Threshold.OriginalBridge.scale risk depth^10) ∧
    (thresholdOutput risk depth).length≤282*RootB23.Threshold.OriginalBridge.scale risk depth ∧
    RootB23.Threshold.ReturnOriginalPacket.timeCoefficient*RootB23.Threshold.OriginalBridge.scale risk depth^10+
      (encode [.rational risk,.natural depth]).length+(thresholdOutput risk depth).length≤
      (RootB23.Threshold.ReturnOriginalPacket.timeCoefficient+283)*RootB23.Threshold.OriginalBridge.scale risk depth^10 := by
  have width:=RootB23.Threshold.FinalSemantics.nine_width_le risk depth positive depthPositive
  have size : (thresholdOutput risk depth).length≤282*RootB23.Threshold.OriginalBridge.scale risk depth := by
    rw [threshold_output_length]
    change _≤128*RootB23.Threshold.OriginalBridge.scale risk depth at width
    have one:=RootB23.Threshold.OriginalBridge.scale_positive risk depth
    omega
  have input : (encode [.rational risk,.natural depth]).length≤RootB23.Threshold.OriginalBridge.scale risk depth := by
    unfold RootB23.Threshold.OriginalBridge.scale
    omega
  have power : RootB23.Threshold.OriginalBridge.scale risk depth≤RootB23.Threshold.OriginalBridge.scale risk depth^10 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (RootB23.Threshold.OriginalBridge.scale_positive risk depth) (by decide : 1≤10)
  refine ⟨RootB23.Threshold.ReturnOriginalPacket.computes_uniform risk depth positive depthPositive,size,?_⟩
  rw [Nat.add_mul]
  have copies : (encode [.rational risk,.natural depth]).length+(thresholdOutput risk depth).length≤
      283*RootB23.Threshold.OriginalBridge.scale risk depth^10 :=
    (by omega : _≤283*RootB23.Threshold.OriginalBridge.scale risk depth).trans (Nat.mul_le_mul_left 283 power)
  omega

end RootPaper.Scalar

#print axioms RootPaper.Scalar.add_sub_closed
#print axioms RootPaper.Scalar.mul_closed
#print axioms RootPaper.Scalar.div_closed
#print axioms RootPaper.Scalar.nat_le_closed
#print axioms RootPaper.Scalar.rational_le_closed
#print axioms RootPaper.Scalar.word_closed
#print axioms RootPaper.Scalar.threshold_closed
