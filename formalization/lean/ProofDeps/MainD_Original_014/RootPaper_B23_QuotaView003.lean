module

public import RootPaper_B23_Preparation002
import Lean.Util.CollectAxioms

/-! The controller reads its quotas from the ACTUAL prepared row list.
This adapter supplies no quota formula or answer as runtime input. The
counter below measures linked-record visits only; controller accounting
also pays the index/field bit work rather than treating this as bit time. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootPaper.B23

open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RationalControllerComputation

variable {I : Instance}

def readQuota : List (I.Stage × RootPaper.Prep.StageResult) → Nat → Nat × Nat
  | [], _ => (0, 1)
  | row :: _, 0 => (row.2.quota, 1)
  | _ :: rows, index + 1 =>
      let found := readQuota rows index
      (found.1, found.2 + 1)

theorem readQuota_value (rows : List (I.Stage × RootPaper.Prep.StageResult)) (index : Nat) :
    (readQuota rows index).1 = (rows.map (fun row => row.2.quota)).getD index 0 := by
  induction rows generalizing index with
  | nil => cases index <;> rfl
  | cons row rows ih =>
      cases index with
      | zero => rfl
      | succ index => exact ih index

theorem readQuota_visits (rows : List (I.Stage × RootPaper.Prep.StageResult)) (index : Nat) :
    (readQuota rows index).2 ≤ rows.length + 1 := by
  induction rows generalizing index with
  | nil => simp [readQuota]
  | cons row rows ih =>
      cases index with
      | zero => simp [readQuota]
      | succ index =>
          have earlier := ih index
          simp only [readQuota, List.length_cons]
          omega

def preparedQuotas (preparation : RootPaper.Prep.NumericalPreparation I) : I.Stage → Nat :=
  fun stage => (readQuota preparation.rows stage.val).1

theorem actual_prepared_quota_view (input : StatisticalInput I) (C : Contract I)
    (budget : Rat) (positive : 0 < budget) (stage : I.Stage) :
    let calculation := RootPaper.Prep.preparationCalculation input C budget positive
    (readQuota calculation.value.rows stage.val).1 = computedQuotas input budget stage ∧
      (readQuota calculation.value.rows stage.val).2 ≤ I.stageCount + 1 := by
  have calculation := RootPaper.Prep.preparationCalculation_spec I input C budget positive
  have original := calculation.1.trans (RootPaper.Prep.numericalPreparation_eq I input C budget positive)
  have rows := congrArg RootPaper.Prep.NumericalPreparation.rows original
  dsimp only at rows ⊢
  rw [rows]
  refine ⟨?_, ?_⟩
  · rw [readQuota_value, original_rows]
    dsimp only [qualifiedResources, Instance.stageCount]
    rw [List.map_map]
    change ((List.finRange I.compatibility.length).map (fun index : I.Stage =>
      referenceQuota input (computedExponent (I := I) budget) index)).getD stage.val 0 = _
    rw [← List.ofFn_eq_map]
    have valid : stage.val < (List.ofFn (fun index : I.Stage =>
        referenceQuota input (computedExponent (I := I) budget) index)).length := by
      simpa only [List.length_ofFn] using stage.isLt
    rw [List.getD_eq_getElem _ _ valid, List.getElem_ofFn]
    rfl
  · exact (readQuota_visits _ _).trans_eq (by rw [RootPaper.Prep.originalRows_length])

theorem preparedQuotas_eq (input : StatisticalInput I) (C : Contract I)
    (budget : Rat) (positive : 0 < budget) :
    preparedQuotas (RootPaper.Prep.preparationCalculation input C budget positive).value =
      computedQuotas input budget := by
  funext stage
  exact (actual_prepared_quota_view input C budget positive stage).1

end RootPaper.B23

#print axioms RootPaper.B23.actual_prepared_quota_view
#print axioms RootPaper.B23.preparedQuotas_eq

open Lean Elab Command
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`RootPaper.B23.actual_prepared_quota_view, `RootPaper.B23.preparedQuotas_eq] do
    for ax in ← collectAxioms name do
      unless allowed.contains ax do throwError m!"ROOT_PAPER_QUOTA_VIEW_STD3_FAIL forbidden={ax} declaration={name}"
  logInfo "ROOT_PAPER_QUOTA_VIEW_STD3_PASS endpoints=2 forbidden=0"
