module

public import RootPaper_Prep_Qualification004

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

open scoped BigOperators
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Common.Native.PSTRWordBool

namespace RootPaper.Prep

def driftEndOps (E : BinaryExperiment) : List Operation :=
  [.rational .mul (sumAbs E) (sumAbs E), .rational .div (sumAbs E*sumAbs E) 2]

def stageOps (E : BinaryExperiment) (e : Nat) : List Operation :=
  let r := E.priorOne/(1-E.priorOne)
  let b := ratioSearch r 0
  let m := channelMax E
  let d := drift E
  let positive : 0 < d := by change 0 < drift E; rw [drift_eq]; exact E.channelDriftLower_pos
  [.rational .sub 1 E.priorOne, .rational .div E.priorOne (1-E.priorOne)] ++
    ratioOps r 0 ++ channelOps E ++ sumAbsOps E ++ driftEndOps E ++ quotaOps e b m d positive 0

theorem stageOps_bounded (E : BinaryExperiment) (e S : Nat) (positive : 1 ≤ S)
    (prior : field E.priorOne ≤ S)
    (ratio : field (E.priorOne/(1-E.priorOne)) ≤ S)
    (eBound : e ≤ S) (bBound : E.priorIntegerMax ≤ S) (mBound : E.channelIntegerMax ≤ S)
    (dBound : field E.channelDriftLower ≤ S) (qBound : E.rationalQuota e ≤ S)
    (fields : ∀ truth y, field (E.channel truth y) ≤ S)
    (ratios : ∀ y, field (E.channel true y/E.channel false y) ≤ S)
    (limits : ∀ y, BinaryExperiment.ratioIntegerBound (E.channel true y/E.channel false y) ≤ S)
    (prefixes : ∀ k, field (RootB234.ChannelWidth.reversePrefixAbs E k) ≤ S) :
    Bounded (stageOps E e) ((E.alphabetSize+1)*128*S^2) (128*S) := by
  have priorBound : BinaryExperiment.ratioIntegerBound (E.priorOne/(1-E.priorOne)) ≤ S := by
    change E.priorIntegerMax ≤ S
    exact bBound
  have complement := field_sub 1 E.priorOne
  rw [field_one] at complement
  have start : Bounded [.rational .sub 1 E.priorOne, .rational .div E.priorOne (1-E.priorOne)] 2 (128*S) := by
    constructor
    · rfl
    · intro op member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp only [Operation.width, field_one] <;> omega
  have bscan := ratioOps_bounded (E.priorOne/(1-E.priorOne)) 0 S positive ratio priorBound (Nat.zero_le _)
  have channel := channelOpsAux_bounded E S positive fields ratios limits (List.finRange E.alphabetSize) 0 (Nat.zero_le _)
  simp only [List.length_finRange] at channel
  have sum := sumAbsOps_bounded E S positive fields prefixes
  have sf : field (sumAbs E) ≤ S := by rw [sumAbs_eq]; exact prefixes _
  have sq := field_mul (sumAbs E) (sumAbs E)
  have finish : Bounded (driftEndOps E) 2 (128*S) := by
    constructor
    · rfl
    · intro op member
      simp only [driftEndOps, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp only [Operation.width, field_two] <;> omega
  have qLimit : RootB234.Quota.quota e E.priorIntegerMax E.channelIntegerMax E.channelDriftLower ≤ S := qBound
  have quota := quotaOps_bounded e E.priorIntegerMax E.channelIntegerMax E.channelDriftLower E.channelDriftLower_pos
    0 S positive eBound bBound mBound dBound qLimit (Nat.zero_le _)
  have all := bounded_append (bounded_append (bounded_append (bounded_append (bounded_append start
    (bounded_mono bscan (Nat.le_refl _) (by omega)))
    (bounded_mono channel (Nat.le_refl _) (by omega)))
    (bounded_mono sum (Nat.le_refl _) (by omega))) finish) quota
  have countBound :
      2+((BinaryExperiment.ratioIntegerBound (E.priorOne/(1-E.priorOne))-0+1)*(S+8))+
        E.alphabetSize*(32*S^2)+E.alphabetSize*5+2+
        (RootB234.Quota.quota e E.priorIntegerMax E.channelIntegerMax E.channelDriftLower-0+1)*19 ≤
          (E.alphabetSize+1)*128*S^2 := by
    have first := Nat.mul_le_mul_right (S+8) (Nat.add_le_add_right priorBound 1)
    have second := Nat.mul_le_mul_right 19 (Nat.add_le_add_right qLimit 1)
    have square : S ≤ S^2 := by nlinarith
    have alph : E.alphabetSize ≤ E.alphabetSize*S^2 := by
      exact Nat.le_mul_of_pos_right _ (by positivity)
    simp only [Nat.sub_zero]
    nlinarith
  have allBound := bounded_mono all countBound (Nat.le_refl _)
  have priorEq : BinaryExperiment.ratioIntegerBound (E.priorOne/(1-E.priorOne)) = E.priorIntegerMax := rfl
  simpa only [stageOps, ratioSearch_eq, Nat.zero_max, priorEq, channelMax_eq, drift_eq, channelOps] using allBound

theorem original_stageOps_bounded (I : Instance) (input : StatisticalInput I) (C : Contract I)
    (budget : Rat) (stage : I.Stage) :
    Bounded (stageOps (input.experiment stage) (computedExponent (I:=I) budget))
      (262144*(arithmeticScale input C budget)^3) (4096*arithmeticScale input C budget) := by
  let P := arithmeticScale input C budget
  let S := 32*P
  have posP : 1 ≤ P := by unfold P arithmeticScale; omega
  have posS : 1 ≤ S := by unfold S; omega
  have prior := input_prior_field I input C budget stage
  have complement := field_sub 1 (input.experiment stage).priorOne
  rw [field_one] at complement
  have ratio := field_div (input.experiment stage).priorOne (1-(input.experiment stage).priorOne)
  have counters := RootB23.PrepScalar.original_stage_counters_bounded I input C budget stage
  have eb := counters.1
  have bb := counters.2.1
  have mb := counters.2.2.1
  have qb := counters.2.2.2
  have quotaBound : (input.experiment stage).rationalQuota (computedExponent (I:=I) budget) ≤ P := by
    simpa only [computedQuotas, referenceQuota] using qb
  have all := stageOps_bounded (input.experiment stage) (computedExponent (I:=I) budget) S posS
    (by dsimp [S,P]; omega) (by dsimp [S,P]; omega)
    (by dsimp [S,P]; omega) (by dsimp [S,P]; omega) (by dsimp [S,P]; omega)
    (original_drift_field I input C budget stage) (by dsimp [S,P]; omega)
    (by intro truth y; have h := input_channel_field I input C budget stage truth y; dsimp [S,P]; omega)
    (by intro y
        have f0 := input_channel_field I input C budget stage false y
        have f1 := input_channel_field I input C budget stage true y
        have d := field_div ((input.experiment stage).channel true y) ((input.experiment stage).channel false y)
        dsimp [S,P]; omega)
    (by intro y
        have h := RootB23.PrepScalar.original_channel_ratio_scan_bounded I input C budget stage y
        dsimp [S,P]; omega)
    (by intro k
        have h := original_prefix_field I input C budget stage k
        dsimp [S,P]; omega)
  have alphabet : (input.experiment stage).alphabetSize ≤ P :=
    (RootB23.PrepScalar.each_alphabet_le_total I input stage).trans
      (RootB23.PrepScalar.alphabet_total_le_scale I input C budget)
  apply bounded_mono all
  · dsimp only [S]
    have multiplier : (input.experiment stage).alphabetSize+1 ≤ 2*P := by omega
    have bound := Nat.mul_le_mul_right (128*(32*P)^2) multiplier
    nlinarith
  · dsimp only [S]
    omega

def inputCopyOps {I : Instance} (input : StatisticalInput I) (C : Contract I) (budget : Rat) : List Operation :=
  (originalData input C budget).map (fun datum => match datum with
    | .natural n => .natural n
    | .rational q => .rational .add q 0)

theorem inputCopyOps_bounded (I : Instance) (input : StatisticalInput I) (C : Contract I) (budget : Rat) :
    Bounded (inputCopyOps input C budget) (arithmeticScale input C budget) (4*arithmeticScale input C budget) := by
  have count := RootB23.PrepScalar.datum_list_length_le_bits (originalData input C budget)
  have inputBits := original_bits_le_scale I input C budget
  have positive : 1 ≤ arithmeticScale input C budget := by unfold arithmeticScale; omega
  constructor
  · simp only [inputCopyOps, List.length_map]
    exact count.trans inputBits
  · intro op member
    obtain ⟨datum, present, rfl⟩ := List.mem_map.mp member
    cases datum with
    | natural n =>
      have h := input_nat_field I input C budget n present
      simp only [Operation.width]
      omega
    | rational q =>
      have h := input_rat_field I input C budget q present
      have zero : field (0 : Rat) = 2 := rfl
      simp only [Operation.width, zero]
      omega

def preparationOps {I : Instance} (input : StatisticalInput I) (C : Contract I)
    (budget : Rat) (positive : 0 < budget) : List Operation :=
  let e := exponentSearch budget positive I.stageCount 1
  let rows := (List.finRange I.stageCount).map (fun stage => (stage, prepareStage (input.experiment stage) e))
  inputCopyOps input C budget ++ exponentOps budget positive I.stageCount 1 ++
    (List.finRange I.stageCount).flatMap (fun stage => stageOps (input.experiment stage) e) ++
    qualificationOps C rows

theorem original_preparationOps_bounded (I : Instance) (input : StatisticalInput I) (C : Contract I)
    (budget : Rat) (hbudget : 0 < budget) :
    Bounded (preparationOps input C budget hbudget)
      (1000000*(arithmeticScale input C budget)^4) (4096*arithmeticScale input C budget) := by
  let P := arithmeticScale input C budget
  have positive : 1 ≤ P := by unfold P arithmeticScale; omega
  have stages : I.stageCount ≤ P := by unfold P arithmeticScale inputSize; omega
  have exponent := RootB23.PrepScalar.original_global_exponent_bounded I input C budget
  have epositive : 1 ≤ BinaryExperiment.quotaExponent budget I.stageCount := le_max_left _ _
  have budgetField : field budget ≤ P := by
    apply input_rat_field I input C budget
    simp [originalData]
  have eOps := exponentOps_bounded budget hbudget I.stageCount 1 (32*P) (by omega)
    (by omega) (by omega) (by exact exponent.trans (by omega)) epositive
  have eOps' : Bounded (exponentOps budget hbudget I.stageCount 1)
      ((BinaryExperiment.quotaExponent budget I.stageCount-1+1)*(2*(32*P)+20)) (4096*P) := by
    convert eOps using 1; ring
  have stagesOps := bounded_flatMap (List.finRange I.stageCount)
    (fun stage => stageOps (input.experiment stage) (computedExponent (I:=I) budget))
    (262144*P^3) (4096*P) (by intro stage _; exact original_stageOps_bounded I input C budget stage)
  simp only [List.length_finRange] at stagesOps
  have copy := inputCopyOps_bounded I input C budget
  have qual := original_qualificationOps_bounded I input C budget
  have copies : Bounded (inputCopyOps input C budget) P (4096*P) :=
    bounded_mono copy (Nat.le_refl _) (by change 4*P ≤ 4096*P; omega)
  have qualification : Bounded (qualificationOps C (originalRows input budget)) (I.stageCount*8+16) (4096*P) :=
    bounded_mono qual (Nat.le_refl _) (by change 128*P ≤ 4096*P; omega)
  have joined := bounded_append (bounded_append (bounded_append copies eOps') stagesOps) qualification
  have result := bounded_mono joined (show _ ≤ 1000000*P^4 from by
    have ecount : BinaryExperiment.quotaExponent budget I.stageCount-1+1 ≤ 2*P := by
      change BinaryExperiment.quotaExponent budget I.stageCount ≤ P at exponent
      omega
    have factor : 2*(32*P)+20 ≤ 84*P := by omega
    have eproduct : (BinaryExperiment.quotaExponent budget I.stageCount-1+1)*(2*(32*P)+20) ≤
        168*P^2 := (Nat.mul_le_mul ecount factor).trans_eq (by ring)
    have sproduct : I.stageCount*(262144*P^3) ≤ 262144*P^4 :=
      (Nat.mul_le_mul_right (262144*P^3) stages).trans_eq (by ring)
    have ps : P ≤ P^4 := by
      simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1 ≤ 4)
    have p2 : P^2 ≤ P^4 := Nat.pow_le_pow_right positive (by decide : 2 ≤ 4)
    have e4 := eproduct.trans (Nat.mul_le_mul_left 168 p2)
    have qlinear : I.stageCount*8+16 ≤ 24*P := by omega
    have q4 := qlinear.trans (Nat.mul_le_mul_left 24 ps)
    omega) (Nat.le_refl _)
  have exactE : exponentSearch budget hbudget I.compatibility.length 1 = computedExponent (I:=I) budget := by
    change exponentSearch budget hbudget I.stageCount 1 = _
    rw [exponentSearch_eq, max_eq_right epositive]
    rfl
  unfold preparationOps
  simp only [Instance.stageCount]
  rw [exactE]
  simpa only [originalRows, Instance.stageCount] using result

theorem original_preparation_bitCost (I : Instance) (input : StatisticalInput I) (C : Contract I)
    (budget : Rat) (positive : 0 < budget) :
    bitCost (preparationOps input C budget positive) ≤
      (1000000*primitiveRate*4097^4)*(arithmeticScale input C budget)^8 := by
  let P := arithmeticScale input C budget
  have one : 1 ≤ P := by unfold P arithmeticScale; omega
  have bound := bounded_bitCost (original_preparationOps_bounded I input C budget positive)
  have linear : 4096*P+1 ≤ 4097*P := by omega
  have powered := Nat.pow_le_pow_left linear 4
  exact bound.trans ((Nat.mul_le_mul_left (1000000*P^4*primitiveRate) powered).trans_eq (by
    dsimp only [P]
    ring))

end RootPaper.Prep
