module

public import Common.PSTR_SYM_ExperimentBits_002

/-! Source-only original input/output budget. Runtime experiments and the
available bitmap are paid by their actual raw Bool codec, never an oracle. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.CompactPrice.PSTRSymbolicBits

open PaperProofs.Common.SymbolicPrice PaperProofs.Statistics PaperProofs.Structure
open RationalControllerComputation RationalControllerComputation.PSTRTMLength004

theorem datumMass_flatMap {α : Type} (items : List α) (encodeItem : α → List Datum) :
    datumMass (items.flatMap encodeItem) = (items.map (fun x => datumMass (encodeItem x))).sum := by
  induction items with
  | nil => rfl
  | cons first later ih =>
    simp only [List.flatMap_cons, datumMass_append, List.map_cons, List.sum_cons, ih]

def scheduleMass {Tool : Type} (stages : ExperimentSchedule Tool) : Nat :=
  (stages.map (fun stage => datumMass (rawExperiment stage.2))).sum

theorem heads_expression_bits {Tool : Type} [DecidableEq Tool]
    (stages : ExperimentSchedule Tool) (remaining : Finset Tool) (target : ENat) (offset : Nat) :
    exprBits (sumExpr ((heads stages remaining target offset).map (fun head => localCoefficientExpr head.2))) ≤
      12 + 16 * scheduleMass stages := by
  induction stages generalizing offset with
  | nil => simp [heads, sumExpr, exprBits_zero, scheduleMass]
  | cons stage later ih =>
    rcases stage with ⟨eligible, experiment⟩
    have current := localCoefficient_bits_le_raw experiment
    have tail := ih (offset + 1)
    by_cases chosen : executableBadRank eligible later remaining + 1 = target
    · simp only [heads, chosen, ite_true, List.map_cons, sumExpr, exprBits_add]
      change _ ≤ 12 + 16 * (datumMass (rawExperiment experiment) + scheduleMass later)
      omega
    · simp only [heads, chosen, ite_false]
      change _ ≤ 12 + 16 * (datumMass (rawExperiment experiment) + scheduleMass later)
      omega

def originalExperimentMass {I : Instance} (input : StatisticalInput I) : Nat :=
  ((List.finRange I.compatibility.length).map (fun stage => datumMass (rawExperiment (input.experiment stage)))).sum

def originalInputMass {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool) : Nat :=
  datumMass (rawInstance input ++ rawSet available)

theorem inputSchedule_mass {I : Instance} (input : StatisticalInput I) :
    scheduleMass (inputSchedule input) = originalExperimentMass input := by
  simp only [scheduleMass, inputSchedule, List.ofFn_eq_map, List.map_map,
    Function.comp_def, originalExperimentMass]

theorem originalExperimentMass_le {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool) :
    originalExperimentMass input ≤ originalInputMass input available := by
  have block :
      datumMass ((List.finRange I.compatibility.length).flatMap (fun stage => rawExperiment (input.experiment stage))) =
        originalExperimentMass input := by
    exact datumMass_flatMap _ _
  unfold originalInputMass rawInstance
  simp only [Instance.stageCount, datumMass_append]
  rw [block]
  omega

theorem originalInputMass_le_length {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool) :
    originalInputMass input available ≤ (symbolicInput input available).length :=
  datumMass_le_encoded_length _

theorem stageCount_le_input_length {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool) :
    I.stageCount ≤ (symbolicInput input available).length := by
  have lower := sum_map_ge_const (List.finRange I.compatibility.length)
    (fun stage => datumMass (rawExperiment (input.experiment stage))) 1
    (by intro stage _; exact (by omega : 1 ≤ 4).trans (rawExperiment_mass_ge_four _))
  simp only [List.length_finRange, Nat.one_mul] at lower
  change I.stageCount ≤ originalExperimentMass input at lower
  exact lower.trans ((originalExperimentMass_le input available).trans (originalInputMass_le_length input available))

theorem rawSet_mass {q : Nat} (available : Finset (Fin q)) : datumMass (rawSet available) = 4 * q := by
  have item (tool : Fin q) : datumBits (boolDatum (decide (tool ∈ available))) = 4 := by
    cases membership : decide (tool ∈ available) <;>
      norm_num [membership, boolDatum, datumBits, natBits]
  simp only [rawSet, datumMass, List.map_map, Function.comp_def, item]
  simp [Nat.mul_comm]

theorem toolCount_le_input_length {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool) :
    I.toolCount ≤ (symbolicInput input available).length := by
  have mass := originalInputMass_le_length input available
  unfold originalInputMass at mass
  rw [datumMass_append, rawSet_mass] at mass
  omega

/-- The exact original Expr TREE mass is linear in the ORIGINAL Bool input.
There is no runtime head list, leaf maximum or coefficient among the inputs. -/
theorem original_expression_bits {I : Instance}
    (input : StatisticalInput I) (available : Finset I.Tool) :
    exprBits (inputExpression input available) ≤ 12 + 16 * (symbolicInput input available).length := by
  have experimentBound := (originalExperimentMass_le input available).trans (originalInputMass_le_length input available)
  unfold inputExpression leadingExpression
  split
  · rw [exprBits_zero]
    omega
  · unfold headExpression
    have headsBound := heads_expression_bits (inputSchedule input) available
      (genericRank (compatibility (inputSchedule input)) available) 0
    rw [inputSchedule_mass] at headsBound
    omega

end PaperProofs.Common.Native.CompactPrice.PSTRSymbolicBits
