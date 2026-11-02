module

public import PaperProofs.Paid.PDROC_FailureCharacterization_001
public import PaperProofs.Paid.PDROC_Reachability_001
public import PaperProofs.Paid.PDROC_FirstFailure_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem currentCorrectionExtension_existingCorrect {s next : State I} {stage : I.Stage}
    (hext : CurrentCorrectionExtension s next stage) (hstage : stage.val = s.cursor)
    (hcu : CursorInvariant next) (hpast : ∀ i : I.Stage, ¬ PastUnrepairedError s i) :
    ExistingPhysicallyCorrect next := by
  rcases hext with ⟨_ha, hcursor, hwritten, htruth, hexecutions, hcorrect⟩
  apply existingCorrect_of_noPast_current next hcu
  · intro i hi
    apply hpast i
    rcases hi with ⟨hlt, hw, he⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hcursor] using hlt
    · simpa only [hwritten, htruth] using hw
    · intro e hm
      exact he e (hexecutions.subset hm)
  · intro i hi _hw
    have heq : i = stage := Fin.ext (hi.trans (hcursor.trans hstage.symm))
    exact Or.inr (by simpa only [heq] using hcorrect)

/-- A real current repair followed by truthful suffix completion witnesses
non-permanent failure. This preserves all original executions and uses only
genuine legal uncapped Steps in the semantic feasibility comparison. -/
theorem prefix_not_permanentlyFailed_of_currentRepair (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (world : input.World)
    {n : ℕ} {s next : State I} (stage : I.Stage)
    (hp : Prefix input C mode accounting rule seed (input.truthAt world) (worldTapes input world) n s)
    (hstage : stage.val = s.cursor) (hpast : ∀ i : I.Stage, ¬ PastUnrepairedError s i)
    (hpath : Relation.ReflTransGen (fun before after => ∃ action,
      Step input C .uncapped accounting (worldTapes input world) before action after) s next)
    (hext : CurrentCorrectionExtension s next stage) :
    ¬ PermanentlyFailed input C accounting world s := by
  have hcu := reachable_cursorInvariant input C accounting (worldTapes input world) hpath
    (prefix_cursorInvariant input C mode accounting rule seed _ _ hp)
  obtain ⟨final, hfinal, hhalt, hsuccess⟩ := truthfulContinuation_exists input C accounting
    (worldTapes input world) next
    (reachable_invariant input C accounting (worldTapes input world) hpath
      (prefix_invariant input C mode accounting rule seed _ _ hp))
    (reachable_deadlineInvariant input C accounting (worldTapes input world) hpath
      (prefix_deadlineInvariant input C mode accounting rule seed _ _ hp)) hcu hext.1
    (reachable_pastPortsWritten input C accounting (worldTapes input world) hpath
      (prefix_pastPortsWritten input C mode accounting rule seed _ _ hp))
    (currentCorrectionExtension_existingCorrect hext hstage hcu hpast)
  exact not_not_intro ⟨final, hpath.trans hfinal, hhalt, hsuccess⟩

end PDROC
