module

public import PaperProofs.Common.AvailableValue
public import PaperProofs.Common.NativeAccountingIrrelevance
public import PaperProofs.Common.NativeContractMetadata
public import PaperProofs.Common.NativeEmpty
public import PaperProofs.Common.SuffixInput
public import Mathlib.Data.Finset.Lattice.Fold
import Lean.Elab.Tactic.Omega

/-!
The healthy current-window penalty value is an independent real-policy infimum
on the fresh suffix with only R available. The original binary experiments are
pulled back whole, and unavailable tools are enforced by reached-action legality.
Caps and normal-call bookkeeping are canonically fixed only after their actual
uncapped equivalences have been proved. The old-history/pending-ledger bridge
and Bellman recursion remain separate obligations, not defining equations.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PaperProofs.Common

def Instance.freshSuffix (I : Instance) (next : ℕ) : Instance where
  toolCount := I.toolCount
  compatibility := I.compatibility.drop next

@[simp] theorem Instance.freshSuffix_zero (I : Instance) : I.freshSuffix 0 = I := rfl

theorem Instance.freshSuffix_stageCount (I : Instance) (next : ℕ) :
    (I.freshSuffix next).stageCount = I.stageCount - next := by
  simp only [Instance.freshSuffix, Instance.stageCount, List.length_drop]

theorem Instance.freshSuffix_isEmpty_stage (I : Instance) (next : ℕ) (hnext : I.stageCount ≤ next) :
    IsEmpty (I.freshSuffix next).Stage := by
  refine ⟨fun stage => ?_⟩
  have hs := stage.isLt
  change stage.val < (I.freshSuffix next).stageCount at hs
  rw [Instance.freshSuffix_stageCount, Nat.sub_eq_zero_of_le hnext] at hs
  exact Nat.not_lt_zero _ hs

theorem Instance.freshSuffix_eq_suffixRestricted (I : Instance) (next : ℕ) :
    I.freshSuffix next = I.suffixRestricted next I.tools := by
  cases I
  simp [Instance.freshSuffix, Instance.suffixRestricted, Instance.tools]

def Instance.freshStageLift (I : Instance) (next : ℕ) (stage : (I.freshSuffix next).Stage) : I.Stage :=
  ⟨next + stage.val, by
    have hs : stage.val < I.compatibility.length - next := by
      simpa only [Instance.freshSuffix, List.length_drop] using stage.isLt
    omega⟩

theorem Instance.freshSuffix_eligible (I : Instance) (next : ℕ)
    (stage : (I.freshSuffix next).Stage) :
    (I.freshSuffix next).eligible stage = I.eligible (I.freshStageLift next stage) := by
  have hl : stage.val < (I.compatibility.drop next).length := stage.isLt
  have ho : next + stage.val < I.compatibility.length := (I.freshStageLift next stage).isLt
  change (I.compatibility.drop next)[stage.val]'hl = I.compatibility[next + stage.val]'ho
  simp only [List.getElem_drop]

def StatisticalInput.freshSuffix {I : Instance} (input : StatisticalInput I) :
    (next : ℕ) → StatisticalInput (I.freshSuffix next)
  | 0 => input
  | next + 1 => {
      experiment stage := input.experiment (I.freshStageLift (next + 1) stage)
      correctionFee stage tool := input.correctionFee (I.freshStageLift (next + 1) stage) tool
      correctionFee_nonneg stage tool :=
        input.correctionFee_nonneg (I.freshStageLift (next + 1) stage) tool }

@[simp] theorem StatisticalInput.freshSuffix_zero {I : Instance} (input : StatisticalInput I) :
    input.freshSuffix 0 = input := rfl

theorem StatisticalInput.freshSuffix_experiment {I : Instance} (input : StatisticalInput I)
    (next : ℕ) (stage : (I.freshSuffix next).Stage) :
    (input.freshSuffix next).experiment stage = input.experiment (I.freshStageLift next stage) := by
  cases next with
  | zero =>
    congr 1
    apply Fin.ext
    simp [Instance.freshStageLift]
  | succ next => rfl

def zeroNormalAccounting (I : Instance) : Native.NormalAccounting I := fun _ _ _ => 0

/-- Fresh-suffix full-policy value; it is not the solution of a recurrence. -/
noncomputable def StatisticalInput.healthyPenalty {I : Instance} (input : StatisticalInput I)
    (next : ℕ) (available : Finset I.Tool) (penalty : ℝ≥0∞) : ℝ≥0∞ :=
  Native.availablePenaltyValue (input.freshSuffix next) (currentRelaxedContract (I.freshSuffix next))
    (zeroNormalAccounting (I.freshSuffix next)) available penalty

theorem StatisticalInput.healthyPenalty_le_penalty {I : Instance} (input : StatisticalInput I)
    (next : ℕ) (available : Finset I.Tool) (penalty : ℝ≥0∞) :
    input.healthyPenalty next available penalty ≤ penalty :=
  Native.availablePenaltyValue_le_penalty _ _ _ _ _

theorem StatisticalInput.healthyPenalty_antitone {I : Instance} (input : StatisticalInput I)
    (next : ℕ) (penalty : ℝ≥0∞) : Antitone (fun available => input.healthyPenalty next available penalty) := by
  intro smaller larger hsub
  exact Native.availablePenaltyValue_antitone (input.freshSuffix next)
    (currentRelaxedContract (I.freshSuffix next)) (zeroNormalAccounting (I.freshSuffix next)) penalty hsub

theorem StatisticalInput.healthyPenalty_ne_top {I : Instance} (input : StatisticalInput I)
    (next : ℕ) (available : Finset I.Tool) {penalty : ℝ≥0∞} (hfinite : penalty ≠ ⊤) :
    input.healthyPenalty next available penalty ≠ ⊤ := by
  intro htop
  exact hfinite (top_le_iff.mp (htop ▸ input.healthyPenalty_le_penalty next available penalty))

theorem StatisticalInput.healthyPenalty_zero {I : Instance} (input : StatisticalInput I)
    (next : ℕ) (available : Finset I.Tool) : input.healthyPenalty next available 0 = 0 :=
  le_antisymm (input.healthyPenalty_le_penalty next available 0) zero_le

theorem StatisticalInput.healthyPenalty_terminal {I : Instance} (input : StatisticalInput I)
    (next : ℕ) (hnext : I.stageCount ≤ next) (available : Finset I.Tool) (penalty : ℝ≥0∞) :
    input.healthyPenalty next available penalty = 0 := by
  let : IsEmpty (I.freshSuffix next).Stage := I.freshSuffix_isEmpty_stage next hnext
  exact Native.availablePenaltyValue_empty _ _ _ _ _

/-- Real conversion is safe here because the independently defined value is
already proved finite at every finite penalty. -/
noncomputable def StatisticalInput.healthyPenaltyReal {I : Instance} (input : StatisticalInput I)
    (next : ℕ) (available : Finset I.Tool) (penalty : ℝ) : ℝ :=
  (input.healthyPenalty next available (ENNReal.ofReal penalty)).toReal

theorem StatisticalInput.healthyPenaltyReal_nonneg {I : Instance} (input : StatisticalInput I)
    (next : ℕ) (available : Finset I.Tool) (penalty : ℝ) :
    0 ≤ input.healthyPenaltyReal next available penalty := ENNReal.toReal_nonneg

theorem StatisticalInput.healthyPenaltyReal_terminal {I : Instance} (input : StatisticalInput I)
    (next : ℕ) (hnext : I.stageCount ≤ next) (available : Finset I.Tool) (penalty : ℝ) :
    input.healthyPenaltyReal next available penalty = 0 := by
  simp only [StatisticalInput.healthyPenaltyReal, input.healthyPenalty_terminal next hnext,
    ENNReal.toReal_zero]

theorem StatisticalInput.healthyPenaltyReal_le_penalty {I : Instance} (input : StatisticalInput I)
    (next : ℕ) (available : Finset I.Tool) (penalty : ℝ) (hpenalty : 0 ≤ penalty) :
    input.healthyPenaltyReal next available penalty ≤ penalty := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (input.healthyPenalty_le_penalty next available (ENNReal.ofReal penalty))
  simpa only [StatisticalInput.healthyPenaltyReal, ENNReal.toReal_ofReal hpenalty] using h

theorem StatisticalInput.healthyPenaltyReal_antitone {I : Instance} (input : StatisticalInput I)
    (next : ℕ) (penalty : ℝ) : Antitone (fun available => input.healthyPenaltyReal next available penalty) := by
  intro smaller larger hsub
  exact ENNReal.toReal_mono (input.healthyPenalty_ne_top next smaller ENNReal.ofReal_ne_top)
    (input.healthyPenalty_antitone next (ENNReal.ofReal penalty) hsub)

theorem StatisticalInput.healthyPenalty_initial {I : Instance} (input : StatisticalInput I)
    (C : Contract I) (hC : C.IsCurrentAllocation) (accounting : Native.NormalAccounting I)
    (penalty : ℝ≥0∞) :
    input.healthyPenalty 0 I.tools penalty = Native.penaltyValue input C.deferExecution accounting penalty := by
  change Native.availablePenaltyValue input (currentRelaxedContract I) (zeroNormalAccounting I)
    Finset.univ penalty = _
  rw [Native.availablePenaltyValue_univ,
    Native.penaltyValue_reaccount_eq input (currentRelaxedContract I) accounting (zeroNormalAccounting I),
    Native.penaltyValue_currentContract input C hC accounting penalty]

theorem StatisticalInput.healthyPenalty_initial_observation_lower {I : Instance} (input : StatisticalInput I)
    (C : Contract I) (hC : C.IsCurrentAllocation) (accounting : Native.NormalAccounting I)
    {Seed : Type*} [MeasurableSpace Seed] (policy : Native.Policy input C .native accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (δ : ℝ≥0∞)
    (hsafe : Native.risk input C .native accounting policy.rule ν ≤ δ) :
    input.healthyPenalty 0 I.tools δ⁻¹ - 1 ≤
      Native.expectedObservationBill input C .native accounting policy.rule ν := by
  rw [input.healthyPenalty_initial C hC accounting]
  exact Native.inverseRisk_deferredPenalty_le_observation input C accounting policy ν δ hsafe

theorem StatisticalInput.healthyPenalty_initial_value_lower {I : Instance} (input : StatisticalInput I)
    (C : Contract I) (hC : C.IsCurrentAllocation) (accounting : Native.NormalAccounting I)
    (δ : ℝ≥0∞) :
    input.healthyPenalty 0 I.tools δ⁻¹ - 1 ≤ Native.value input C .native accounting δ := by
  rw [input.healthyPenalty_initial C hC accounting]
  exact Native.inverseRisk_deferredPenalty_lower input C accounting δ

noncomputable def StatisticalInput.goodPenaltyReal {I : Instance} (input : StatisticalInput I)
    (stage : I.Stage) (available : Finset I.Tool) (penalty : ℝ) : ℝ :=
  input.healthyPenaltyReal (stage.val + 1) available penalty

noncomputable def StatisticalInput.badPenaltyReal {I : Instance} (input : StatisticalInput I)
    (stage : I.Stage) (available : Finset I.Tool) (penalty : ℝ) : ℝ := by
  classical
  exact if h : (I.eligible stage ∩ available).Nonempty then
    (I.eligible stage ∩ available).inf' h
      (fun tool => input.healthyPenaltyReal (stage.val + 1) (available.erase tool) penalty)
  else penalty

theorem StatisticalInput.penalty_successor_order {I : Instance} (input : StatisticalInput I)
    (stage : I.Stage) (available : Finset I.Tool) (penalty : ℝ) (hpenalty : 0 ≤ penalty) :
    0 ≤ input.goodPenaltyReal stage available penalty ∧
      input.goodPenaltyReal stage available penalty ≤ input.badPenaltyReal stage available penalty ∧
        input.badPenaltyReal stage available penalty ≤ penalty := by
  classical
  refine ⟨input.healthyPenaltyReal_nonneg _ _ _, ?_, ?_⟩
  · unfold StatisticalInput.badPenaltyReal
    split_ifs with h
    · apply Finset.le_inf'
      intro tool _
      exact input.healthyPenaltyReal_antitone (stage.val + 1) penalty (Finset.erase_subset _ _)
    · exact input.healthyPenaltyReal_le_penalty _ _ _ hpenalty
  · unfold StatisticalInput.badPenaltyReal
    split_ifs with h
    · exact (Finset.inf'_le _ h.choose_spec).trans
        (input.healthyPenaltyReal_le_penalty _ _ _ hpenalty)
    · exact le_rfl

/-- Exact outstanding Bellman statement for the independent native infimum.
It has no recurrence or optimal-continuation oracle as an input. -/
def StatisticalInput.CurrentPenaltyRecursion {I : Instance} (input : StatisticalInput I) : Prop :=
  ∀ (stage : I.Stage) (available : Finset I.Tool) (penalty : ℝ), 0 < penalty →
    input.healthyPenaltyReal stage.val available penalty =
      min penalty (input.goodPenaltyReal stage available penalty +
        (input.experiment stage).localValueReal
          (input.badPenaltyReal stage available penalty - input.goodPenaltyReal stage available penalty))

end PaperProofs.Common
