module

public import PaperProofs.Star.PStarLR_ReportedBarrier_008

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Star.Parameters

namespace PStarLR

variable {I : Instance}

theorem prefix_complete_error_or_correct (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {state : State I} (path : Prefix input C mode accounting policy seed truth tapes n state)
    (complete : allWritten state.ledger) (stage : I.Stage) :
    reportedError state.history stage = true ∨ reportedCorrect state.history stage = true := by
  have reported := prefix_allWritten_reported input C mode accounting policy seed truth tapes path complete stage
  unfold reportedError reportedCorrect
  rw [prefix_historyWritten input C mode accounting policy seed truth tapes path,
    prefix_historyReport_all_contracts input C mode accounting policy seed truth tapes path]
  cases hw : state.ledger.written stage with
  | none => exact (complete stage hw).elim
  | some bit =>
    cases hr : state.ledger.reportTime stage with
    | none => exact (reported hr).elim
    | some time => cases ht : state.ledger.truth stage <;> cases bit <;> simp

theorem retainedToolChoice_exists_of_complete (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (complete : ∀ stage, reportedError history stage = true ∨ reportedCorrect history stage = true)
    (size : (Finset.univ.filter fun stage => reportedError history stage).card ≤ P.tools)
    (stage : (starInstance P.tools order).Stage) (wrong : reportedError history stage = true) :
    ∃ tool, P.retainedToolChoice order history stage = some tool := by
  classical
  cases label : stageLabel P.tools order stage with
  | some tool => exact ⟨tool, by simp only [Parameters.retainedToolChoice, label]⟩
  | none =>
    let errors := Finset.univ.filter fun i : (starInstance P.tools order).Stage => reportedError history i
    have htotal : (Finset.univ : Finset (starInstance P.tools order).Stage).card = P.tools+1 := by
      simp only [Finset.card_univ, Instance.Stage, Fintype.card_fin]
      exact stageCount_eq P.tools order
    have hsmall : errors.card < (Finset.univ : Finset (starInstance P.tools order).Stage).card := by
      rw [htotal]
      exact Nat.lt_succ_of_le size
    obtain ⟨missing, _member, outside⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
    have notError : reportedError history missing ≠ true := by
      intro isError
      exact outside (Finset.mem_filter.mpr ⟨Finset.mem_univ missing, isError⟩)
    have correct : reportedCorrect history missing = true := (complete missing).resolve_left notError
    cases missingLabel : stageLabel P.tools order missing with
    | none =>
      have heq : missing = stage := stageLabel_injective P.tools order (missingLabel.trans label.symm)
      exact (notError (heq.symm ▸ wrong)).elim
    | some tool =>
      have heq : missing = singletonStage P.tools order tool :=
        stageLabel_injective P.tools order (missingLabel.trans (stageLabel_singleton P.tools order tool).symm)
      have candidates : (Finset.univ.filter fun candidate : Fin P.tools =>
          reportedCorrect history (singletonStage P.tools order candidate)).Nonempty := by
        exact ⟨tool, Finset.mem_filter.mpr ⟨Finset.mem_univ tool, by rwa [← heq]⟩⟩
      obtain ⟨chosen, hchosen, _membership⟩ := firstOfFinset_exists _ candidates
      refine ⟨chosen, ?_⟩
      change @Eq (Option (Fin P.tools)) (P.retainedToolChoice order history stage) (some chosen)
      unfold Parameters.retainedToolChoice
      rw [label]
      exact hchosen

theorem retainedToolChoice_exists_at_barrier (P : PaperProofs.Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (mode : ResourceMode)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (policy : PolicyRule (starInstance P.tools order) Seed) (seed : Seed)
    (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C mode accounting policy seed truth tapes n state)
    (complete : allWritten state.ledger)
    (size : (PaperProofs.Retained.ordinaryMismatches state.ledger).card ≤ P.tools)
    (stage : (starInstance P.tools order).Stage) (wrong : reportedError state.history stage = true) :
    ∃ tool, P.retainedToolChoice order state.history stage = some tool := by
  apply retainedToolChoice_exists_of_complete P order state.history
    (prefix_complete_error_or_correct (P.input order) C mode accounting policy seed truth tapes path complete)
    _ stage wrong
  rw [prefix_complete_errors (P.input order) C mode accounting policy seed truth tapes path complete]
  exact size

end PStarLR
