module

public import PaperProofs.Star.PStarLR_ActionShape_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Star.Parameters

namespace PStarLR

theorem firstOfFinset_mem {n : ℕ} (items : Finset (Fin n)) (tool : Fin n)
    (chosen : firstOfFinset items = some tool) : tool ∈ items := by
  classical
  unfold firstOfFinset at chosen
  split_ifs at chosen with nonempty
  · have heq := Option.some.inj chosen
    rw [← heq]
    exact Finset.min'_mem items nonempty

theorem firstOfFinset_exists {n : ℕ} (items : Finset (Fin n)) (nonempty : items.Nonempty) :
    ∃ tool, firstOfFinset items = some tool ∧ tool ∈ items := by
  classical
  exact ⟨items.min' nonempty, by simp [firstOfFinset, nonempty], Finset.min'_mem items nonempty⟩

theorem reportedCorrect_not_error {I : Instance} (history : List (VisibleEvent I)) (stage : I.Stage)
    (correct : reportedCorrect history stage = true) : reportedError history stage = false := by
  cases hw : historyWritten history stage with
  | none => simp [reportedCorrect, hw] at correct
  | some bit =>
    cases hr : historyReport history stage with
    | none => simp [reportedCorrect, hw, hr] at correct
    | some pair =>
      obtain ⟨truth, serial⟩ := pair
      cases bit <;> cases truth <;> simp [reportedCorrect, reportedError, hw, hr] at *

theorem retainedToolChoice_compatible (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) (tool : Fin P.tools)
    (chosen : P.retainedToolChoice order history stage = some tool) :
    tool ∈ (starInstance P.tools order).eligible stage := by
  classical
  change @Eq (Option (Fin P.tools)) (P.retainedToolChoice order history stage) (some tool) at chosen
  rw [eligible_formula]
  cases label : stageLabel P.tools order stage with
  | none => exact Finset.mem_univ tool
  | some own =>
    have heq : own = tool := by
      unfold Parameters.retainedToolChoice at chosen
      rw [label] at chosen
      exact Option.some.inj chosen
    rw [heq]
    exact Finset.mem_singleton_self tool

theorem retainedUniversalToolChoice_correct (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) (tool : Fin P.tools)
    (universal : stageLabel P.tools order stage = none)
    (chosen : P.retainedToolChoice order history stage = some tool) :
    reportedCorrect history (singletonStage P.tools order tool) = true := by
  classical
  change @Eq (Option (Fin P.tools)) (P.retainedToolChoice order history stage) (some tool) at chosen
  unfold Parameters.retainedToolChoice at chosen
  rw [universal] at chosen
  have member := firstOfFinset_mem (Finset.univ.filter fun candidate =>
    reportedCorrect history (singletonStage P.tools order candidate)) tool chosen
  exact (Finset.mem_filter.mp member).2

theorem retainedToolChoice_injective_on_errors (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (left right : (starInstance P.tools order).Stage) (tool : Fin P.tools)
    (leftError : reportedError history left = true) (rightError : reportedError history right = true)
    (leftChoice : P.retainedToolChoice order history left = some tool)
    (rightChoice : P.retainedToolChoice order history right = some tool) : left = right := by
  classical
  change @Eq (Option (Fin P.tools)) (P.retainedToolChoice order history left) (some tool) at leftChoice
  change @Eq (Option (Fin P.tools)) (P.retainedToolChoice order history right) (some tool) at rightChoice
  cases hl : stageLabel P.tools order left with
  | none =>
    cases hr : stageLabel P.tools order right with
    | none => exact stageLabel_injective P.tools order (hl.trans hr.symm)
    | some own =>
      have heq : own = tool := by
        unfold Parameters.retainedToolChoice at rightChoice
        rw [hr] at rightChoice
        exact Option.some.inj rightChoice
      have hstage : right = singletonStage P.tools order tool :=
        stageLabel_injective P.tools order (by rw [hr, heq, stageLabel_singleton])
      have correct := retainedUniversalToolChoice_correct P order history left tool hl leftChoice
      have wrongFalse := reportedCorrect_not_error history _ correct
      rw [← hstage, rightError] at wrongFalse
      cases wrongFalse
  | some own =>
    have heq : own = tool := by
      unfold Parameters.retainedToolChoice at leftChoice
      rw [hl] at leftChoice
      exact Option.some.inj leftChoice
    cases hr : stageLabel P.tools order right with
    | none =>
      have hstage : left = singletonStage P.tools order tool :=
        stageLabel_injective P.tools order (by rw [hl, heq, stageLabel_singleton])
      have correct := retainedUniversalToolChoice_correct P order history right tool hr rightChoice
      have wrongFalse := reportedCorrect_not_error history _ correct
      rw [← hstage, leftError] at wrongFalse
      cases wrongFalse
    | some other =>
      have heqOther : other = tool := by
        unfold Parameters.retainedToolChoice at rightChoice
        rw [hr] at rightChoice
        exact Option.some.inj rightChoice
      exact stageLabel_injective P.tools order (by rw [hl, hr, heq, heqOther])

end PStarLR
