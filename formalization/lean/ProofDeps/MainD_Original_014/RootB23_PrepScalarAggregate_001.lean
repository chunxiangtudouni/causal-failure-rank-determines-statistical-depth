module

public import RootB23_PrepScalarPublic_001

/-! The alphabet multiplicity is charged explicitly. This is a polynomial
bound on the mathematical scan counts, not a supplied runtime fuel or a
claim that the fixed Bool implementation has already been constructed. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open PaperProofs.Common.Native.RationalControllerComputation

namespace RootB23.PrepScalar

theorem datum_length_positive (datum : Datum) : 1 ≤ (encodeDatum datum).length := by
  cases datum <;> simp only [encodeDatum,List.length_cons,List.length_append] <;> omega

theorem datum_list_length_le_bits (data : List Datum) : data.length ≤ (encode data).length := by
  have fields (items : List Datum) : items.length ≤ (items.flatMap encodeDatum).length := by
    induction items with
    | nil => simp
    | cons first rest ih =>
      have positive := datum_length_positive first
      simp only [List.length_cons,List.flatMap_cons,List.length_append]
      omega
  have enough := fields data
  simp only [encode,List.length_append,List.length_cons,List.length_nil]
  omega

theorem experiment_alphabet_le_fields (E : BinaryExperiment) : E.alphabetSize ≤ (rawExperiment E).length := by
  simp [rawExperiment]
  omega

def alphabetTotal {I : Instance} (input : StatisticalInput I) : Nat :=
  ((List.finRange I.stageCount).map (fun stage => (input.experiment stage).alphabetSize)).sum

theorem alphabet_total_le_input (I : Instance) (input : StatisticalInput I) (C : Contract I) (budget : Rat) :
    alphabetTotal input ≤ (preparationInput input C budget).length := by
  have fields (stages : List I.Stage) :
      (stages.map (fun stage => (input.experiment stage).alphabetSize)).sum ≤
        (stages.flatMap (fun stage => rawExperiment (input.experiment stage))).length := by
    induction stages with
    | nil => simp
    | cons stage rest ih =>
      have head := experiment_alphabet_le_fields (input.experiment stage)
      simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append]
      omega
  have room : ((List.finRange I.stageCount).flatMap (fun stage => rawExperiment (input.experiment stage))).length ≤
      (rawInstance input ++ rawContract C ++ [Datum.rational budget]).length := by
    simp only [rawInstance,List.length_append,List.length_cons,List.length_nil]
    omega
  exact (fields (List.finRange I.stageCount)).trans (room.trans (datum_list_length_le_bits _))

theorem alphabet_total_le_scale (I : Instance) (input : StatisticalInput I) (C : Contract I) (budget : Rat) :
    alphabetTotal input ≤ arithmeticScale input C budget := by
  have encoded := alphabet_total_le_input I input C budget
  unfold arithmeticScale inputSize
  omega

theorem each_alphabet_le_total (I : Instance) (input : StatisticalInput I) (stage : I.Stage) :
    (input.experiment stage).alphabetSize ≤ alphabetTotal input := by
  apply List.single_le_sum
  · intro _ _
    exact Nat.zero_le _
  · exact List.mem_map.mpr ⟨stage,List.mem_finRange _,rfl⟩

def channelScanTotal {I : Instance} (input : StatisticalInput I) (stage : I.Stage) : Nat :=
  ∑ symbol : Fin (input.experiment stage).alphabetSize,
    BinaryExperiment.ratioIntegerBound
      ((input.experiment stage).channel true symbol/(input.experiment stage).channel false symbol)

theorem channel_scan_le (I : Instance) (input : StatisticalInput I) (C : Contract I) (budget : Rat) (stage : I.Stage) :
    channelScanTotal input stage ≤ (input.experiment stage).alphabetSize*arithmeticScale input C budget := by
  have each := Finset.sum_le_sum (s:=Finset.univ) (fun symbol _ =>
    original_channel_ratio_scan_bounded I input C budget stage symbol)
  simpa only [channelScanTotal,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using each

def stageScanCount {I : Instance} (input : StatisticalInput I) (budget : Rat) (stage : I.Stage) : Nat :=
  (input.experiment stage).priorIntegerMax+computedQuotas input budget stage+
    channelScanTotal input stage+(input.experiment stage).alphabetSize+2

def scanCount {I : Instance} (input : StatisticalInput I) (budget : Rat) : Nat :=
  computedExponent (I:=I) budget+
    ((List.finRange I.stageCount).map (stageScanCount input budget)).sum+1

theorem original_scan_count_polynomial (I : Instance) (input : StatisticalInput I) (C : Contract I) (budget : Rat) :
    scanCount input budget ≤ 8*(arithmeticScale input C budget)^3 := by
  let S := arithmeticScale input C budget
  have one : 1 ≤ S := by dsimp [S,arithmeticScale];omega
  have stages : I.stageCount ≤ S := by dsimp [S,arithmeticScale,inputSize];omega
  have alphabet : ∀ stage : I.Stage, (input.experiment stage).alphabetSize ≤ S :=
    fun stage => (each_alphabet_le_total I input stage).trans (alphabet_total_le_scale I input C budget)
  have each (stage : I.Stage) : stageScanCount input budget stage ≤ S^2+3*S+2 := by
    have counters := original_stage_counters_bounded I input C budget stage
    have channel := channel_scan_le I input C budget stage
    have product := Nat.mul_le_mul_right S (alphabet stage)
    dsimp only [stageScanCount]
    dsimp only [S] at product ⊢
    nlinarith [alphabet stage,counters.2.1,counters.2.2.2]
  have summed (items : List I.Stage) :
      (items.map (stageScanCount input budget)).sum ≤ items.length*(S^2+3*S+2) := by
    induction items with
    | nil => simp
    | cons stage rest ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      have added := Nat.add_le_add (each stage) ih
      omega
  have total := summed (List.finRange I.stageCount)
  have total_count : ((List.finRange I.stageCount).map (stageScanCount input budget)).sum ≤
      I.stageCount*(S^2+3*S+2) := by
    calc
      _ ≤ (List.finRange I.stageCount).length*(S^2+3*S+2) := total
      _ = I.stageCount*(S^2+3*S+2) :=
        congrArg (fun n : Nat => n*(S^2+3*S+2)) (List.length_finRange (n:=I.stageCount))
  have number := Nat.mul_le_mul_right (S^2+3*S+2) stages
  have exponent := original_global_exponent_bounded I input C budget
  have square : S ≤ S^2 := by nlinarith
  have cube : S^2 ≤ S^3 := by nlinarith [Nat.mul_le_mul_left (S*S) one]
  change computedExponent (I:=I) budget+_+1 ≤ 8*S^3
  change computedExponent (I:=I) budget ≤ S at exponent
  nlinarith

end RootB23.PrepScalar
