module

public import RootB23_PrepScalarAggregate_001
public import RootB234_ChannelWidth_Public003
public import RootB234_Quota_FirstSuccess003

/-! The paper preparation algorithm. The three searches have no supplied
fuel: the original closed formulas occur only in their erased termination
proofs. Arithmetic charging is supplied by the separate paper cost consumer.
This module makes no claim about the optional bit-machine implementation. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

open scoped BigOperators
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open PaperProofs.Common.Native.RationalControllerComputation

namespace RootPaper.Prep

def ratioTest (r : Rat) (n : Nat) : Bool :=
  decide (r ≤ (2 : Rat)^n) && decide (1/r ≤ (2 : Rat)^n)

theorem ratioTest_iff (r : Rat) (n : Nat) :
    ratioTest r n = true ↔ BinaryExperiment.ratioIntegerBound r ≤ n := by
  simp only [ratioTest, Bool.and_eq_true, decide_eq_true_eq]
  exact (RootB23.PrepScalar.ratio_bound_le_iff r n).symm

def ratioSearch (r : Rat) (n : Nat) : Nat :=
  if ratioTest r n then n else ratioSearch r (n+1)
termination_by BinaryExperiment.ratioIntegerBound r - n
decreasing_by
  have before : n < BinaryExperiment.ratioIntegerBound r := by
    have failed : ¬BinaryExperiment.ratioIntegerBound r ≤ n := by
      intro bounded
      exact (by assumption : ratioTest r n ≠ true) ((ratioTest_iff r n).2 bounded)
    omega
  omega

theorem ratioSearch_eq (r : Rat) (n : Nat) :
    ratioSearch r n = max n (BinaryExperiment.ratioIntegerBound r) := by
  fun_induction ratioSearch r n with
  | case1 n passed =>
    rw [max_eq_left ((ratioTest_iff r n).1 passed)]
  | case2 n failed ih =>
    have before : n < BinaryExperiment.ratioIntegerBound r := by
      have : ¬BinaryExperiment.ratioIntegerBound r ≤ n := fun bounded =>
        failed ((ratioTest_iff r n).2 bounded)
      omega
    rw [ih, max_eq_right (by omega), max_eq_right (by omega)]

def exponentTest (budget : Rat) (N n : Nat) : Bool :=
  decide (1 ≤ n) && decide ((2*N*referenceQuotaConstant N : Rat) ≤ (2 : Rat)^n*budget)

theorem exponentTest_iff (budget : Rat) (positive : 0 < budget) (N n : Nat) :
    exponentTest budget N n = true ↔ BinaryExperiment.quotaExponent budget N ≤ n := by
  simp only [exponentTest, Bool.and_eq_true, decide_eq_true_eq]
  exact (RootB23.PrepScalar.exponent_le_iff budget positive N n).symm

def exponentSearch (budget : Rat) (positive : 0 < budget) (N n : Nat) : Nat :=
  if exponentTest budget N n then n else exponentSearch budget positive N (n+1)
termination_by BinaryExperiment.quotaExponent budget N - n
decreasing_by
  have : n < BinaryExperiment.quotaExponent budget N := by
    have failed : ¬BinaryExperiment.quotaExponent budget N ≤ n := by
      intro bounded
      exact (by assumption : exponentTest budget N n ≠ true)
        ((exponentTest_iff budget positive N n).2 bounded)
    omega
  omega

theorem exponentSearch_eq (budget : Rat) (positive : 0 < budget) (N n : Nat) :
    exponentSearch budget positive N n = max n (BinaryExperiment.quotaExponent budget N) := by
  fun_induction exponentSearch budget positive N n with
  | case1 n passed => rw [max_eq_left ((exponentTest_iff budget positive N n).1 passed)]
  | case2 n failed ih =>
    have before : n < BinaryExperiment.quotaExponent budget N := by
      have : ¬BinaryExperiment.quotaExponent budget N ≤ n := fun bounded =>
        failed ((exponentTest_iff budget positive N n).2 bounded)
      omega
    rw [ih, max_eq_right (by omega), max_eq_right (by omega)]

def quotaTest (e b m : Nat) (d : Rat) (n : Nat) : Bool :=
  decide (2*((e : Rat)+b) ≤ d*(n : Rat)) &&
    decide ((e : Rat)*(8*((m : Rat)*m)) ≤ (d*d)*(n : Rat))

theorem quotaTest_iff (e b m : Nat) (d : Rat) (positive : 0 < d) (n : Nat) :
    quotaTest e b m d n = true ↔ RootB234.Quota.quota e b m d ≤ n := by
  rw [←RootB234.Quota.successful_iff e b m n d positive]
  simp only [quotaTest, Bool.and_eq_true, decide_eq_true_eq,
    RootB234.Quota.Successful, RootB234.Quota.firstDifference,
    RootB234.Quota.secondDifference, sub_nonneg]

def quotaSearch (e b m : Nat) (d : Rat) (positive : 0 < d) (n : Nat) : Nat :=
  if quotaTest e b m d n then n else quotaSearch e b m d positive (n+1)
termination_by RootB234.Quota.quota e b m d - n
decreasing_by
  have : n < RootB234.Quota.quota e b m d := by
    have failed : ¬RootB234.Quota.quota e b m d ≤ n := by
      intro bounded
      exact (by assumption : quotaTest e b m d n ≠ true)
        ((quotaTest_iff e b m d positive n).2 bounded)
    omega
  omega

theorem quotaSearch_eq (e b m : Nat) (d : Rat) (positive : 0 < d) (n : Nat) :
    quotaSearch e b m d positive n = max n (RootB234.Quota.quota e b m d) := by
  fun_induction quotaSearch e b m d positive n with
  | case1 n passed => rw [max_eq_left ((quotaTest_iff e b m d positive n).1 passed)]
  | case2 n failed ih =>
    have before : n < RootB234.Quota.quota e b m d := by
      have : ¬RootB234.Quota.quota e b m d ≤ n := fun bounded =>
        failed ((quotaTest_iff e b m d positive n).2 bounded)
      omega
    rw [ih, max_eq_right (by omega), max_eq_right (by omega)]

def channelMax (E : BinaryExperiment) : Nat :=
  ((List.finRange E.alphabetSize).map (fun y => ratioSearch (E.channel true y/E.channel false y) 0)).foldl max 0

theorem foldl_max_eq_sup (xs : List Nat) (n : Nat) :
    xs.foldl max n = max n (xs.toFinset.sup id) := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih => simp [ih, max_assoc]

theorem channelMax_eq (E : BinaryExperiment) : channelMax E = E.channelIntegerMax := by
  simp only [channelMax, ratioSearch_eq, Nat.zero_max, foldl_max_eq_sup, Nat.zero_max]
  unfold BinaryExperiment.channelIntegerMax
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro n member
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    exact Finset.le_sup (f := fun y : Fin E.alphabetSize =>
      BinaryExperiment.ratioIntegerBound (E.channel true y/E.channel false y)) (Finset.mem_univ y)
  · apply Finset.sup_le
    intro y _
    exact Finset.le_sup (f := (id : Nat → Nat))
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨y, List.mem_finRange y, rfl⟩))

def sumAbs (E : BinaryExperiment) : Rat :=
  ((List.finRange E.alphabetSize).reverse).foldl
    (fun total y => total+|E.channel true y-E.channel false y|) 0

theorem sumAbs_eq (E : BinaryExperiment) :
    sumAbs E = RootB234.ChannelWidth.reversePrefixAbs E E.alphabetSize := by
  have fold (ys : List (Fin E.alphabetSize)) (total : Rat) :
      ys.foldl (fun a y => a+|E.channel true y-E.channel false y|) total =
        total+(ys.map (fun y => |E.channel true y-E.channel false y|)).sum := by
    induction ys generalizing total with
    | nil => simp
    | cons y ys ih => simp [ih, add_assoc]
  simp only [sumAbs, fold, zero_add, RootB234.ChannelWidth.reversePrefixAbs]
  rw [List.take_of_length_le (by simp)]

def drift (E : BinaryExperiment) : Rat := sumAbs E * sumAbs E / 2

theorem drift_eq (E : BinaryExperiment) : drift E = E.channelDriftLower := by
  rw [RootB234.ChannelWidth.channelDriftLower_formula, drift, sumAbs_eq, pow_two]

structure StageResult where
  drift : Rat
  channels : Nat
  prior : Nat
  quota : Nat
  deriving DecidableEq

def prepareStage (E : BinaryExperiment) (e : Nat) : StageResult :=
  let b := ratioSearch (E.priorOne/(1-E.priorOne)) 0
  let m := channelMax E
  let d := drift E
  let positive : 0 < d := by change 0 < drift E; rw [drift_eq]; exact E.channelDriftLower_pos
  ⟨d, m, b, quotaSearch e b m d positive 0⟩

theorem prepareStage_eq (E : BinaryExperiment) (e : Nat) :
    prepareStage E e = ⟨E.channelDriftLower, E.channelIntegerMax, E.priorIntegerMax, E.rationalQuota e⟩ := by
  simp only [prepareStage, ratioSearch_eq, Nat.zero_max, channelMax_eq, drift_eq,
    quotaSearch_eq]
  have prior : E.priorOne/(1-E.priorOne) = E.prior true/E.prior false := by
    simp [BinaryExperiment.prior]
  simp only [prior, BinaryExperiment.priorIntegerMax]
  rfl

def qualify {I : Instance} (C : Contract I) (rows : List (I.Stage × StageResult)) : Bool :=
  rows.all (fun row => decide (row.2.quota ≤ C.reviewQuota row.1)) &&
    decide (C.normalCallBound + (rows.map (fun row => row.2.quota)).sum +
      min I.stageCount I.toolCount ≤ C.totalCallCap)

def stageData (row : StageResult) : List Datum :=
  [.rational row.drift, .natural row.channels, .natural row.prior, .natural row.quota]

def preparation {I : Instance} (input : StatisticalInput I) (C : Contract I)
    (budget : Rat) (positive : 0 < budget) : List Bool :=
  let e := exponentSearch budget positive I.stageCount 1
  let rows := (List.finRange I.stageCount).map (fun stage => (stage, prepareStage (input.experiment stage) e))
  encode ([.natural e, boolDatum (qualify C rows)] ++ rows.flatMap (fun row => stageData row.2))

theorem qualification_eq (I : Instance) (input : StatisticalInput I) (C : Contract I) (budget : Rat) :
    qualify C ((List.finRange I.stageCount).map (fun stage =>
      (stage, prepareStage (input.experiment stage) (computedExponent (I:=I) budget)))) =
      numericQualification input C budget := by
  simp only [qualify, prepareStage_eq, Instance.stageCount]
  have quotas : ∀ stage : I.Stage,
      (input.experiment stage).rationalQuota (computedExponent (I:=I) budget) = computedQuotas input budget stage :=
    fun _ => rfl
  simp_rw [quotas]
  simp only [List.all_map, List.map_map, Function.comp_def]
  rw [←List.ofFn_eq_map, List.sum_ofFn]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, numericQualification]
  constructor
  · rintro ⟨reviews, cap⟩
    exact ⟨fun stage => reviews stage (List.mem_finRange stage), cap⟩
  · rintro ⟨reviews, cap⟩
    exact ⟨fun stage _ => reviews stage, cap⟩

theorem preparation_eq (I : Instance) (input : StatisticalInput I) (C : Contract I)
    (budget : Rat) (positive : 0 < budget) :
    preparation input C budget positive = preparationOutput input C budget := by
  have epositive : 1 ≤ BinaryExperiment.quotaExponent budget I.stageCount := le_max_left _ _
  have exactE : exponentSearch budget positive I.compatibility.length 1 = computedExponent (I:=I) budget := by
    change exponentSearch budget positive I.stageCount 1 = _
    rw [exponentSearch_eq, max_eq_right epositive]
    rfl
  have qualified := qualification_eq I input C budget
  simp only [Instance.stageCount] at qualified
  simp only [preparation, Instance.stageCount]
  rw [exactE, qualified]
  simp only [List.flatMap_map, prepareStage_eq, stageData,
    preparationOutput, computedQuotas, referenceQuota, Instance.stageCount]

theorem zero_stage_exponent (budget : Rat) (positive : 0 < budget) :
    exponentSearch budget positive 0 1 = 1 := by
  rw [exponentSearch_eq, RootB23.PrepScalar.exponent_zero_stages, max_self]

end RootPaper.Prep
