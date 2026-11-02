module

public import PaperProofs.Star.RootStarOverflow_007
public import PaperProofs.Common.ReferenceControllerQuota
public import PaperProofs.Star.PStarLR_ActionShape_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace RootStarOverflow

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Star.Parameters
open scoped ENNReal

theorem testing_review_lt_quota (P : Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (quota : ℕ) (history : List (VisibleEvent (starInstance P.tools order)))
    (stage review : (starInstance P.tools order).Stage)
    (h : P.testingActionReal order kind r (some quota) history stage = .review review) :
    (historyObservations history review).length < quota := by
  classical
  unfold testingActionReal at h
  split at h
  · cases h
  · split at h
    · dsimp only at h
      split at h
      · cases h
      · split at h
        · have heq := Action.review.inj h
          subst review
          assumption
        · cases h
    · cases h

theorem star_review_lt_quota {Seed : Type*} (P : Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (quota : ℕ) (seed : Seed) (history : List (VisibleEvent (starInstance P.tools order)))
    (review : (starInstance P.tools order).Stage)
    (h : P.starReferenceRule order kind r (some quota) seed history = .review review) :
    (historyObservations history review).length < quota := by
  cases kind with
  | current =>
    unfold starReferenceRule candidateWithTesting at h
    split at h
    · cases h
    · split at h
      · dsimp only at h
        split at h
        · exact testing_review_lt_quota P order .current r quota history _ review h
        · split at h
          · cases h
          · split at h
            · exact ((PStarLR.repairAction_ne_review P order history _ _ _ review (by simp)) h).elim
            · cases h
      · split at h <;> cases h
  | earlyRetained | lateRetained =>
    unfold starReferenceRule candidateWithTesting at h
    split at h
    · cases h
    · split at h
      · dsimp only at h
        split at h
        · exact testing_review_lt_quota P order _ r quota history _ review h
        · cases h
      · split at h
        · exact ((PStarLR.barrierAction_ne_review P order history review) h).elim
        · cases h

private theorem reportedWrite_reviews {I : Instance} (C : Contract I) (s : State I) (stage : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s stage bit).reviews = s.ledger.reviews := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

theorem prefix_reviews_le_quota {Seed : Type*} (P : Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (quota : ℕ) (C : Contract (starInstance P.tools order)) (mode : ResourceMode)
    (accounting : NormalAccounting (starInstance P.tools order)) (seed : Seed)
    (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {s : State (starInstance P.tools order)}
    (hp : Prefix (P.input order) C mode accounting (P.starReferenceRule order kind r (some quota)) seed truth tapes n s) :
    ∀ stage, s.ledger.reviews stage ≤ (quota : ℕ∞) := by
  induction hp with
  | initial => intro stage; exact bot_le
  | @next n s result earlier step ih =>
    generalize haction : P.starReferenceRule order kind r (some quota) seed s.history = action at step
    cases step with
    | review current live port resources =>
      have hgate := star_review_lt_quota P order kind r quota seed s.history current haction
      intro stage
      by_cases heq : stage = current
      · subst stage
        simp only [record, reviewLedger, Function.update_self]
        rw [← prefix_historyObservations_length (P.input order) C mode accounting
          (P.starReferenceRule order kind r (some quota)) seed truth tapes earlier current]
        exact_mod_cast Nat.succ_le_of_lt hgate
      · simpa only [record, reviewLedger, Function.update_of_ne heq] using ih stage
    | write current bit live port resources =>
      intro stage
      simpa only [record, reportedWrite_reviews] using ih stage
    | allocate | execute | advance | stop | abandon => exact ih

theorem reviewQuotaCertificate {Seed : Type*} (P : Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (quota : ℕ) (C : Contract (starInstance P.tools order)) (hC : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) :
    ReviewQuotaCertificate (P.input order) C accounting
      (P.starReferenceRule order kind r (some quota) (Seed := Seed)) (fun _ => quota) := by
  intro sample n stage
  obtain ⟨_, _, hp⟩ := run_has_prefix (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r (some quota)) (star_legal_uncapped P order kind r (some quota) C hC accounting) sample n
  exact prefix_reviews_le_quota P order kind r quota C .uncapped accounting sample.1
    ((P.input order).truthAt sample.2) (worldTapes (P.input order) sample.2) hp stage

theorem referenceAllPathCharges (P : Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order)) (hC : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) :
    P.ReferenceAllPathCharges order kind r limit C accounting := by
  have hlegal := star_legal_uncapped (Seed := Unit) P order kind r limit C hC accounting
  have hmin : min (starInstance P.tools order).stageCount (starInstance P.tools order).toolCount = P.tools := by
    rw [stageCount_eq]
    change min (P.tools + 1) P.tools = P.tools
    omega
  have hmax : (P.input order).fees.maxCorrection ≤ ENNReal.ofReal (P.correctionFee : ℝ) := by
    apply Finset.sup_le
    intro pair _
    exact le_rfl
  intro sample
  constructor
  · intro n
    simpa only [hmin] using run_actualCorrections_le (P.input order) C .uncapped accounting _ hlegal sample n
  · have hbill := runActualBill_le_observation_add (P.input order) C .uncapped accounting _ hlegal sample
    rw [hmin] at hbill
    exact hbill.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hmax zero_le))

end RootStarOverflow
