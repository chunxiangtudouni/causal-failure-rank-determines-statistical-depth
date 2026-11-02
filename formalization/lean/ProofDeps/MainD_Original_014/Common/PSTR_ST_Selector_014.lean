module

public import Common.PSTR_ST_TableInfinite_009
public import PaperProofs.Common.ReferenceSuffixReplay

/-! Proof-only maximizing selector interface for the uniform variable-fee
induction. This is not a new runtime input or an uncharged machine oracle.
The actual table selector is explicitly instantiated from proved callbacks;
suffixes inherit the ambient selector rather than rebuilding a new tree tie. -/

@[expose] public section

namespace PaperProofs.Common.Native.PSTRStatistics.MaxSelector

open PaperProofs.Structure PaperProofs.Structure.LaminarTree
open CompactPrice TableAlignment TableInfinite

abbrev Selector (I : Instance) := I.Stage → Finset I.Tool → Option I.Tool

structure Spec (I : Instance) (available : Finset I.Tool) (choose : Selector I) : Prop where
  none : ∀ (stage : I.Stage) (used : Finset I.Tool),
    choose stage used = none ↔ I.eligible stage ∩ (available \ used) = ∅
  some : ∀ (stage : I.Stage) (used : Finset I.Tool) (tool : I.Tool),
    choose stage used = some tool →
      tool ∈ I.eligible stage ∩ (available \ used) ∧
      errorRank (I.compatibility.drop (stage.val + 1)) ((available \ used).erase tool) =
        badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1)) (available \ used)

def table (I : Instance) (available : Finset I.Tool) : Selector I :=
  fun stage used => (tableReply I available stage used).tool

theorem table_spec (I : Instance) (hlaminar : LaminarSchedule I.compatibility)
    (available : Finset I.Tool) : Spec I available (table I available) := by
  constructor
  · intro stage used
    exact tableRepairTool_eq_none I hlaminar available stage used
  · intro stage used tool htool
    exact tableRepairTool_spec I hlaminar available stage used tool htool

def restrict (I : Instance) (choose : Selector I) (first : ℕ) (pastUsed : Finset I.Tool) :
    Selector (I.freshSuffix first) :=
  fun stage used => choose (I.freshStageLift first stage) (pastUsed ∪ used)

/-- Uniform max-selector semantics survives a genuine fresh suffix with old
used tools removed from initial availability, while preserving the AMBIENT tie. -/
theorem Spec.restrict {I : Instance} {available : Finset I.Tool} {choose : Selector I}
    (spec : Spec I available choose) (first : ℕ) (pastUsed : Finset I.Tool) :
    Spec (I.freshSuffix first) (available \ pastUsed) (restrict I choose first pastUsed) := by
  have remaining (used : Finset I.Tool) : (available \ pastUsed) \ used = available \ (pastUsed ∪ used) := by
    ext tool
    simp [and_assoc]
  constructor
  · intro stage used
    change choose (I.freshStageLift first stage) (pastUsed ∪ used) = Option.none ↔ _
    rw [I.freshSuffix_eligible]
    change choose (I.freshStageLift first stage) (pastUsed ∪ used) = Option.none ↔
      I.eligible (I.freshStageLift first stage) ∩ ((available \ pastUsed) \ used) = ∅
    rw [remaining used]
    exact spec.none (I.freshStageLift first stage) (pastUsed ∪ used)
  · intro stage used tool htool
    have hs := spec.some (I.freshStageLift first stage) (pastUsed ∪ used) tool htool
    rw [I.freshSuffix_eligible, freshSuffix_drop_after_stage]
    change tool ∈ I.eligible (I.freshStageLift first stage) ∩ ((available \ pastUsed) \ used) ∧
      errorRank (I.compatibility.drop ((I.freshStageLift first stage).val + 1))
        (((available \ pastUsed) \ used).erase tool) =
          badChildRank (I.eligible (I.freshStageLift first stage))
            (I.compatibility.drop ((I.freshStageLift first stage).val + 1)) ((available \ pastUsed) \ used)
    rw [remaining used]
    exact hs

theorem restrict_table_spec (I : Instance) (hlaminar : LaminarSchedule I.compatibility)
    (available : Finset I.Tool) (first : ℕ) (pastUsed : Finset I.Tool) :
    Spec (I.freshSuffix first) (available \ pastUsed)
      (restrict I (table I available) first pastUsed) :=
  (table_spec I hlaminar available).restrict first pastUsed

end PaperProofs.Common.Native.PSTRStatistics.MaxSelector
