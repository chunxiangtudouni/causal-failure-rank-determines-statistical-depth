module

public import PaperProofs.Star.RootStarOverflow_008
public import PaperProofs.Common.BoundedNormalIO

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCompletedQualification045

open Common Common.Native Parameters Statistics

/-- The TRUE original bounded Star script halts on EVERY sample, for any
real target and quota. This uses actual all-prefix legality/quota proofs,
not risk, expected cost, a.e. stopping, H0, or qualification as a premise. -/
theorem starBounded_halted (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (quota : ℕ) (C : Contract (starInstance P.tools order)) (qualified : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) (sample : Unit × (P.input order).World) :
    (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r (some quota)) sample
      (quotaActionBound (starInstance P.tools order) (fun _ => quota)+1)).halted = true :=
  run_halted_of_reviewQuotaCertificate (P.input order) C accounting _
    (RootStarOverflow.star_legal_uncapped P order kind r (some quota) C qualified accounting)
    (fun _ => quota) (RootStarOverflow.reviewQuotaCertificate P order kind r quota C qualified accounting) sample

/-- Exactly the SAME H0: complete-run normal calls are equivalent to the
existing prefix bound for THIS actual fixed Star script. -/
theorem starBounded_normalCalls_iff_completed (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (quota : ℕ) (C : Contract (starInstance P.tools order)) (qualified : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) (H0 : ℕ) :
    (∀ sample n, (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r (some quota) (Seed := Unit)) sample n).ledger.normalCalls ≤ (H0 : ℕ∞)) ↔
    CompletedNormalCallBound (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r (some quota) (Seed := Unit)) H0 := by
  let policy : Policy (P.input order) C .uncapped accounting Unit :=
    ⟨P.starReferenceRule order kind r (some quota), P.measurable_starReferenceRule order kind r (some quota),
      RootStarOverflow.star_legal_uncapped P order kind r (some quota) C qualified accounting⟩
  change NormalCallCertificate (P.input order) C .uncapped accounting policy H0 ↔
    CompletedNormalCallBound (P.input order) C .uncapped accounting policy.rule H0
  apply normalCallCertificate_iff_completed_of_halts
  intro sample
  exact ⟨_, starBounded_halted P order kind r quota C qualified accounting sample⟩

/-- The manuscript's complete-run H0 formulation, with EXACTLY the
original E*, Q*, review windows and total-call inequality. -/
structure CompletedOriginalStarQualification (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (delta : ℝ) (exponent : ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) : Prop where
  minimal_exponent : IsMinimalDyadicExponent (20*(P.tools+1 : ℕ)) delta exponent
  stage_quota : ∀ i, P.commonQuota exponent ≤ C.reviewQuota i
  total_calls : C.normalCallBound+(P.tools+1)*P.commonQuota exponent+P.tools ≤ C.totalCallCap
  normal_calls : CompletedNormalCallBound (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind (delta/2) (some (P.commonQuota exponent)) (Seed := Unit)) C.normalCallBound

/-- No new resource hypothesis: the original complete-run qualification is
EQUIVALENT to the original formal qualifier, under the same kind contract. -/
theorem completedOriginalStarQualification_iff (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (delta : ℝ) (exponent : ℕ) (C : Contract (starInstance P.tools order)) (qualified : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) :
    CompletedOriginalStarQualification P order kind delta exponent C accounting ↔
      P.OriginalStarQualification order kind delta exponent C accounting := by
  constructor
  · intro h
    exact ⟨h.minimal_exponent, h.stage_quota, h.total_calls,
      (starBounded_normalCalls_iff_completed P order kind (delta/2) (P.commonQuota exponent)
        C qualified accounting C.normalCallBound).mpr h.normal_calls⟩
  · intro h
    exact ⟨h.minimal_exponent, h.stage_quota, h.total_calls,
      (starBounded_normalCalls_iff_completed P order kind (delta/2) (P.commonQuota exponent)
        C qualified accounting C.normalCallBound).mp h.normal_calls⟩

end PaperProofs.Star.PStarCompletedQualification045

