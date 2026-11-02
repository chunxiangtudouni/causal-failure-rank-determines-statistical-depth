module

public import PaperProofs.Star.RootStarOverflow_002
public import PaperProofs.Common.NativeCapTransfer

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace RootStarOverflow

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Star.Parameters

theorem prefix_halted_or_ideal {I : Instance} {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (bounded ideal : PolicyRule I Seed)
    (hcoupled : ∀ seed history, bounded seed history = ideal seed history ∨ bounded seed history = .abandon)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting bounded seed truth tapes n s) :
    s.halted = true ∨ Prefix input C mode accounting ideal seed truth tapes n s := by
  induction hp with
  | initial => exact Or.inr .initial
  | @next n s next earlier step ih =>
    have ha := step_source_active input C mode accounting tapes step
    rcases ih with hh | hpideal
    · simp only [hh, Bool.true_eq_false] at ha
    · rcases hcoupled seed s.history with hs | habandon
      · exact Or.inr (.next hpideal (by rwa [← hs]))
      · have hstep : Step input C mode accounting tapes s .abandon next := by rwa [habandon] at step
        have heq := step_deterministic input C mode accounting tapes hstep (Step.abandon s ha)
        exact Or.inl (by rw [heq]; rfl)

theorem legalRule_of_abandon_coupling {I : Instance} {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (bounded ideal : PolicyRule I Seed)
    (hcoupled : ∀ seed history, bounded seed history = ideal seed history ∨ bounded seed history = .abandon)
    (hlegal : LegalRule input C mode accounting ideal) : LegalRule input C mode accounting bounded := by
  intro seed truth tapes n s hp ha
  rcases prefix_halted_or_ideal input C mode accounting bounded ideal hcoupled seed truth tapes hp with hh | hideal
  · simp only [ha, Bool.false_eq_true] at hh
  · rcases hcoupled seed s.history with hs | habandon
    · rw [hs]
      exact hlegal seed truth tapes n s hideal ha
    · exact ⟨stopState s true, by rw [habandon]; exact Step.abandon s ha⟩

theorem referenceLegality_bounded (P : Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (quota : ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order))
    (hlegal : P.ReferenceLegality order kind r none C accounting) :
    P.ReferenceLegality order kind r (some quota) C accounting := by
  obtain ⟨ideal, heq⟩ := hlegal
  refine ⟨⟨P.starReferenceRule order kind r (some quota),
    P.measurable_starReferenceRule order kind r (some quota), ?_⟩, rfl⟩
  apply legalRule_of_abandon_coupling (P.input order) C .uncapped accounting _ _
    (starRule_quota_coupling P order kind r quota)
  rw [← heq]
  exact ideal.legal

end RootStarOverflow
