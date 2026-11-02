module

public import RootPaper_Prep_Channel003

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

def quotaSumOps {α : Type*} (rows : List (α × StageResult)) (current : Nat) : List Operation :=
  match rows with
  | [] => []
  | row::rows => naturalAdd current row.2.quota ++ quotaSumOps rows (current+row.2.quota)

def qualificationOps {I : Instance} (C : Contract I) (rows : List (I.Stage × StageResult)) : List Operation :=
  let q := (rows.map (fun row => row.2.quota)).sum
  rows.flatMap (fun row => naturalLE row.2.quota (C.reviewQuota row.1)) ++
    quotaSumOps rows 0 ++ naturalLE I.stageCount I.toolCount ++
    naturalAdd C.normalCallBound q ++ naturalAdd (C.normalCallBound+q) (min I.stageCount I.toolCount) ++
    naturalLE (C.normalCallBound+q+min I.stageCount I.toolCount) C.totalCallCap

theorem quotaSumOps_bounded {α : Type*} (rows : List (α × StageResult)) (current S : Nat)
    (positive : 1 ≤ S) (total : current+(rows.map (fun row => row.2.quota)).sum ≤ S) :
    Bounded (quotaSumOps rows current) (rows.length*4) (64*S) := by
  induction rows generalizing current with
  | nil => exact bounded_nil _ _
  | cons row rows ih =>
    have currentBound : current ≤ S := by simp only [List.map_cons, List.sum_cons] at total; omega
    have rowBound : row.2.quota ≤ S := by simp only [List.map_cons, List.sum_cons] at total; omega
    have cf := field_nat current
    have rf := field_nat row.2.quota
    have add := naturalAdd_bounded current row.2.quota (4*S) (by omega) (by omega) (by omega)
    have rest := ih (current+row.2.quota) (by simp only [List.map_cons, List.sum_cons] at total; omega)
    exact bounded_mono (bounded_append (bounded_mono add (Nat.le_refl _) (by omega)) rest)
      (by simp only [List.length_cons]; omega) (Nat.le_refl _)

theorem qualificationOps_bounded (I : Instance) (C : Contract I) (rows : List (I.Stage × StageResult))
    (S : Nat) (positive : 1 ≤ S)
    (stages : I.stageCount ≤ S) (tools : I.toolCount ≤ S)
    (normal : field (C.normalCallBound : Rat) ≤ S) (cap : field (C.totalCallCap : Rat) ≤ S)
    (reviews : ∀ row ∈ rows, field (C.reviewQuota row.1 : Rat) ≤ S)
    (total : (rows.map (fun row => row.2.quota)).sum ≤ S) :
    Bounded (qualificationOps C rows) (rows.length*8+16) (128*S) := by
  let q := (rows.map (fun row => row.2.quota)).sum
  have qb : q ≤ S := total
  have qf := field_nat q
  have nf := field_nat I.stageCount
  have jf := field_nat I.toolCount
  have mf := field_nat (min I.stageCount I.toolCount)
  have mb : min I.stageCount I.toolCount ≤ S := (min_le_left _ _).trans stages
  have nq : field ((C.normalCallBound+q : Nat) : Rat) ≤ 8*S := by
    have add := field_add (C.normalCallBound : Rat) (q : Rat)
    push_cast
    omega
  have final : field ((C.normalCallBound+q+min I.stageCount I.toolCount : Nat) : Rat) ≤ 24*S := by
    have add := field_add ((C.normalCallBound+q : Nat) : Rat) ((min I.stageCount I.toolCount : Nat) : Rat)
    rw [←Nat.cast_add] at add
    omega
  have reviewCalls := bounded_flatMap rows (fun row => naturalLE row.2.quota (C.reviewQuota row.1)) 4 (128*S) (by
    intro row present
    have rowBound : row.2.quota ≤ q := List.le_sum_of_mem
      (List.mem_map.mpr ⟨row, present, rfl⟩)
    have rowField := field_nat row.2.quota
    have call := naturalLE_bounded row.2.quota (C.reviewQuota row.1) (4*S) (by omega)
      (by omega) (by have h := reviews row present; omega)
    exact bounded_mono call (Nat.le_refl _) (by omega))
  have sums := quotaSumOps_bounded rows 0 S positive (by simpa only [Nat.zero_add] using total)
  have minimum := naturalLE_bounded I.stageCount I.toolCount (4*S) (by omega) (by omega) (by omega)
  have firstAdd := naturalAdd_bounded C.normalCallBound q (4*S) (by omega) (by omega) (by omega)
  have secondAdd := naturalAdd_bounded (C.normalCallBound+q) (min I.stageCount I.toolCount)
    (8*S) (by omega) nq (by omega)
  have finalCompare := naturalLE_bounded (C.normalCallBound+q+min I.stageCount I.toolCount)
    C.totalCallCap (32*S) (by omega) (by omega) (by omega)
  have finalCompare' : Bounded (naturalLE (C.normalCallBound+q+min I.stageCount I.toolCount)
      C.totalCallCap) 4 (128*S) := by
    convert finalCompare using 1; ring
  have joined : Bounded
      (rows.flatMap (fun row => naturalLE row.2.quota (C.reviewQuota row.1)) ++
        quotaSumOps rows 0 ++ naturalLE I.stageCount I.toolCount ++
        naturalAdd C.normalCallBound q ++ naturalAdd (C.normalCallBound+q) (min I.stageCount I.toolCount) ++
        naturalLE (C.normalCallBound+q+min I.stageCount I.toolCount) C.totalCallCap)
      (rows.length*4+rows.length*4+4+4+4+4) (128*S) :=
    bounded_append (bounded_append (bounded_append (bounded_append (bounded_append reviewCalls
      (bounded_mono sums (Nat.le_refl _) (by omega)))
      (bounded_mono minimum (Nat.le_refl _) (by omega)))
      (bounded_mono firstAdd (Nat.le_refl _) (by omega)))
      (bounded_mono secondAdd (Nat.le_refl _) (by omega))) finalCompare'
  unfold qualificationOps
  exact bounded_mono joined (by omega) (Nat.le_refl _)

def originalRows {I : Instance} (input : StatisticalInput I) (budget : Rat) : List (I.Stage × StageResult) :=
  (List.finRange I.stageCount).map (fun stage =>
    (stage, prepareStage (input.experiment stage) (computedExponent (I:=I) budget)))

theorem originalRows_sum (I : Instance) (input : StatisticalInput I) (budget : Rat) :
    ((originalRows input budget).map (fun row => row.2.quota)).sum = numericalQuota input budget := by
  simp only [originalRows, Instance.stageCount, List.map_map, prepareStage_eq]
  change ((List.finRange I.compatibility.length).map (fun stage : Fin I.compatibility.length =>
    computedQuotas input budget stage)).sum = _
  rw [←List.ofFn_eq_map, List.sum_ofFn]
  rfl

theorem originalRows_length (I : Instance) (input : StatisticalInput I) (budget : Rat) :
    (originalRows input budget).length = I.stageCount := by
  simp only [originalRows, Instance.stageCount, List.length_map, List.length_finRange]

theorem original_qualificationOps_bounded (I : Instance) (input : StatisticalInput I) (C : Contract I) (budget : Rat) :
    Bounded (qualificationOps C (originalRows input budget))
      (I.stageCount*8+16) (128*arithmeticScale input C budget) := by
  let P := arithmeticScale input C budget
  have positive : 1 ≤ P := by unfold P arithmeticScale; omega
  have stages : I.stageCount ≤ P := by unfold P arithmeticScale inputSize; omega
  have tools : I.toolCount ≤ P := by unfold P arithmeticScale inputSize; omega
  have normal : field (C.normalCallBound : Rat) ≤ P := by
    apply input_nat_field I input C budget
    simp [originalData, rawContract]
  have cap : field (C.totalCallCap : Rat) ≤ P := by
    apply input_nat_field I input C budget
    simp [originalData, rawContract]
  have reviews : ∀ row ∈ originalRows input budget, field (C.reviewQuota row.1 : Rat) ≤ P := by
    intro row present
    apply input_nat_field I input C budget
    unfold originalData
    apply List.mem_append.mpr
    left
    apply List.mem_append.mpr
    right
    unfold rawContract
    apply List.mem_append.mpr
    right
    exact List.mem_map.mpr ⟨row.1, List.mem_finRange row.1, rfl⟩
  have total : ((originalRows input budget).map (fun row => row.2.quota)).sum ≤ P := by
    rw [originalRows_sum]
    unfold P arithmeticScale
    omega
  have all := qualificationOps_bounded I C (originalRows input budget) P positive stages tools normal cap reviews total
  simpa only [originalRows_length] using all

end RootPaper.Prep
