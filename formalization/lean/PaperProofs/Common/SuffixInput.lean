module

public import PaperProofs.Common.Input
public import Mathlib.Data.List.TakeDrop
import Lean.Elab.Tactic.Omega

/-!
The same original finite input restricted to a suffix and a remaining-tool
set. Tool numbers are unchanged. Each local stage lifts to the original stage
n+j, including arbitrary n: if n is past the terminal state no local stage
exists. Statistical data are pulled back from that exact original stage.
-/

@[expose] public section

namespace PaperProofs.Common

def Instance.suffixRestricted (I : Instance) (next : Nat) (remaining : Finset I.Tool) : Instance where
  toolCount := I.toolCount
  compatibility := (I.compatibility.drop next).map (fun eligible => eligible ∩ remaining)

theorem Instance.suffixRestricted_toolCount (I : Instance) (next : Nat)
    (remaining : Finset I.Tool) : (I.suffixRestricted next remaining).toolCount = I.toolCount := rfl

theorem Instance.suffixRestricted_stageCount (I : Instance) (next : Nat)
    (remaining : Finset I.Tool) :
    (I.suffixRestricted next remaining).stageCount = I.stageCount - next := by
  simp only [Instance.stageCount, Instance.suffixRestricted, List.length_map, List.length_drop]

/-- A local stage exists only when n+j is a genuine original stage; no bound
on n is assumed by the definition. -/
def Instance.suffixStageLift (I : Instance) (next : Nat) (remaining : Finset I.Tool)
    (stage : (I.suffixRestricted next remaining).Stage) : I.Stage :=
  ⟨next + stage.val, by
    have hstage : stage.val < I.compatibility.length - next := by
      simpa only [Instance.suffixRestricted, List.length_map, List.length_drop] using stage.isLt
    omega⟩

theorem Instance.suffixStageLift_val (I : Instance) (next : Nat) (remaining : Finset I.Tool)
    (stage : (I.suffixRestricted next remaining).Stage) :
    (I.suffixStageLift next remaining stage).val = next + stage.val := rfl

theorem Instance.suffixStageLift_injective (I : Instance) (next : Nat)
    (remaining : Finset I.Tool) : Function.Injective (I.suffixStageLift next remaining) := by
  intro left right heq
  apply Fin.ext
  have hval := congrArg Fin.val heq
  change next + left.val = next + right.val at hval
  omega

theorem Instance.suffixRestricted_eligible (I : Instance) (next : Nat) (remaining : Finset I.Tool)
    (stage : (I.suffixRestricted next remaining).Stage) :
    (I.suffixRestricted next remaining).eligible stage =
      I.eligible (I.suffixStageLift next remaining stage) ∩ remaining := by
  have hlocal : stage.val <
      ((I.compatibility.drop next).map (fun eligible => eligible ∩ remaining)).length := stage.isLt
  have horiginal : next + stage.val < I.compatibility.length :=
    (I.suffixStageLift next remaining stage).isLt
  change ((I.compatibility.drop next).map (fun eligible => eligible ∩ remaining))[stage.val]'hlocal =
    I.compatibility[next + stage.val]'horiginal ∩ remaining
  simp only [List.getElem_map, List.getElem_drop]

theorem Instance.suffixRestricted_eligible_subset (I : Instance) (next : Nat)
    (remaining : Finset I.Tool) (stage : (I.suffixRestricted next remaining).Stage) :
    (I.suffixRestricted next remaining).eligible stage ⊆ remaining := by
  rw [I.suffixRestricted_eligible]
  exact Finset.inter_subset_right

theorem Instance.suffixRestricted_terminal (I : Instance) (next : Nat)
    (remaining : Finset I.Tool) (hterminal : I.stageCount ≤ next) :
    (I.suffixRestricted next remaining).compatibility = [] := by
  simp only [Instance.suffixRestricted, List.drop_eq_nil_of_le hterminal, List.map_nil]

theorem Instance.suffixRestricted_no_stage (I : Instance) (next : Nat)
    (remaining : Finset I.Tool) (hterminal : I.stageCount ≤ next) :
    IsEmpty (I.suffixRestricted next remaining).Stage := by
  refine ⟨fun stage => ?_⟩
  have hstage := stage.isLt
  have hlength : (I.suffixRestricted next remaining).compatibility.length = 0 :=
    congrArg List.length (I.suffixRestricted_terminal next remaining hterminal)
  have hstage' : stage.val < 0 := hlength ▸ hstage
  exact Nat.not_lt_zero _ hstage'

/-- Reuse the entire original experiment, rather than reconstructing priors,
channels or observation prices as separate data. -/
def StatisticalInput.suffixRestricted {I : Instance} (input : StatisticalInput I)
    (next : Nat) (remaining : Finset I.Tool) : StatisticalInput (I.suffixRestricted next remaining) where
  experiment stage := input.experiment (I.suffixStageLift next remaining stage)
  correctionFee stage tool := input.correctionFee (I.suffixStageLift next remaining stage) tool
  correctionFee_nonneg stage tool :=
    input.correctionFee_nonneg (I.suffixStageLift next remaining stage) tool

theorem StatisticalInput.suffixRestricted_experiment {I : Instance} (input : StatisticalInput I)
    (next : Nat) (remaining : Finset I.Tool) (stage : (I.suffixRestricted next remaining).Stage) :
    (input.suffixRestricted next remaining).experiment stage =
      input.experiment (I.suffixStageLift next remaining stage) := rfl

theorem StatisticalInput.suffixRestricted_prior {I : Instance} (input : StatisticalInput I)
    (next : Nat) (remaining : Finset I.Tool) (stage : (I.suffixRestricted next remaining).Stage)
    (fact : Bool) :
    ((input.suffixRestricted next remaining).experiment stage).prior fact =
      (input.experiment (I.suffixStageLift next remaining stage)).prior fact := rfl

theorem StatisticalInput.suffixRestricted_channel {I : Instance} (input : StatisticalInput I)
    (next : Nat) (remaining : Finset I.Tool) (stage : (I.suffixRestricted next remaining).Stage)
    (fact : Bool) (symbol : Fin (input.experiment (I.suffixStageLift next remaining stage)).alphabetSize) :
    ((input.suffixRestricted next remaining).experiment stage).channel fact symbol =
      (input.experiment (I.suffixStageLift next remaining stage)).channel fact symbol := rfl

theorem StatisticalInput.suffixRestricted_observationFee {I : Instance} (input : StatisticalInput I)
    (next : Nat) (remaining : Finset I.Tool) (stage : (I.suffixRestricted next remaining).Stage) :
    (input.suffixRestricted next remaining).fees.observation stage =
      input.fees.observation (I.suffixStageLift next remaining stage) := rfl

theorem StatisticalInput.suffixRestricted_correctionFee {I : Instance} (input : StatisticalInput I)
    (next : Nat) (remaining : Finset I.Tool) (stage : (I.suffixRestricted next remaining).Stage)
    (tool : I.Tool) :
    (input.suffixRestricted next remaining).fees.correction stage tool =
      input.fees.correction (I.suffixStageLift next remaining stage) tool := rfl

theorem StatisticalInput.suffixRestricted_observationCharge {I : Instance} (input : StatisticalInput I)
    (next : Nat) (remaining : Finset I.Tool) (stage : (I.suffixRestricted next remaining).Stage)
    (samples : ℕ∞) :
    ((input.suffixRestricted next remaining).experiment stage).observationCharge samples =
      (input.experiment (I.suffixStageLift next remaining stage)).observationCharge samples := rfl

end PaperProofs.Common
