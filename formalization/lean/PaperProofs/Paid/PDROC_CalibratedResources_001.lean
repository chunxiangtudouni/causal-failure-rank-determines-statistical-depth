module

public import PaperProofs.Paid.CalibratedBackend

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC.CalibratedResources

theorem menuRepairAction_ne_review (P : Parameters) (N K : ℕ)
    (history : List (VisibleEvent (freshInstance N K)))
    (stage reviewed : (freshInstance N K).Stage) :
    P.menuRepairAction N K history stage ≠ .review reviewed := by
  intro selected
  unfold Parameters.menuRepairAction at selected
  split at selected
  · cases selected
  · split at selected
    · cases selected
    · split at selected <;> cases selected

theorem cappedTestingAction_review_lt (P : Parameters) (level : ℕ) (tie : Bool)
    (history : List (VisibleEvent P.sharedInstance)) (stage reviewed : P.sharedInstance.Stage)
    (selected : P.cappedTestingAction level tie history stage = .review reviewed) :
    stage = reviewed ∧ (historyObservations history reviewed).length < P.certificate.Q := by
  unfold Parameters.cappedTestingAction at selected
  dsimp only at selected
  split at selected
  · split at selected
    · cases selected
    · rename_i before
      have same : stage = reviewed := Action.review.inj selected
      refine ⟨same, ?_⟩
      rw [← same]
      exact Nat.lt_of_not_ge (fun quota => before (Or.inr quota))
  · cases selected

theorem calibratedTestingAction_review_lt (P : Parameters) (level : ℕ)
    (seed : P.CalibratedMenuSeed) (history : List (VisibleEvent P.sharedInstance))
    (stage reviewed : P.sharedInstance.Stage)
    (selected : P.calibratedTestingAction level seed history stage = .review reviewed) :
    stage = reviewed ∧ (historyObservations history reviewed).length < P.certificate.Q := by
  unfold Parameters.calibratedTestingAction at selected
  split at selected
  · cases selected
  · split at selected
    · split at selected
      · exact cappedTestingAction_review_lt P level (seed.1 stage) history stage reviewed selected
      · cases selected
    · cases selected

theorem calibratedMenuCandidate_review_lt (P : Parameters) (table : MenuTable)
    (seed : P.CalibratedMenuSeed) (history : List (VisibleEvent P.sharedInstance))
    (reviewed : P.sharedInstance.Stage)
    (selected : P.calibratedMenuCandidate table seed history = .review reviewed) :
    (historyObservations history reviewed).length < P.certificate.Q := by
  unfold Parameters.calibratedMenuCandidate at selected
  split at selected
  · cases selected
  · split at selected
    · rename_i hcursor
      dsimp only at selected
      let current : P.sharedInstance.Stage :=
        ⟨historyCursor history, by simpa [Parameters.sharedInstance] using hcursor⟩
      cases written : historyWrite history current with
      | none =>
        rw [written] at selected
        cases action : (Parameters.menuEntryAt table (P.certificate.stages - current.val)
            (P.menuEntryTools P.certificate.stages P.tools history current)).action with
        | finish => rw [action] at selected; cases selected
        | abandon => rw [action] at selected; cases selected
        | test level bad =>
          rw [action] at selected
          exact (calibratedTestingAction_review_lt P level seed history current reviewed selected).2
      | some packet =>
        obtain ⟨bit, serial⟩ := packet
        rw [written] at selected
        dsimp only at selected
        cases report : historyReport history current with
        | none => rw [report] at selected; cases selected
        | some packet =>
          obtain ⟨truth, reportedSerial⟩ := packet
          rw [report] at selected
          dsimp only at selected
          by_cases serialMismatch : (serial != reportedSerial) = true
          · simp only [serialMismatch, ite_true] at selected
            cases selected
          · simp only [serialMismatch] at selected
            by_cases correct : (bit == truth) = true
            · simp only [correct, ite_true] at selected
              cases selected
            · simp only [correct] at selected
              cases action : (Parameters.menuEntryAt table (P.certificate.stages - current.val)
                  (P.menuEntryTools P.certificate.stages P.tools history current)).action with
              | finish => rw [action] at selected; cases selected
              | abandon => rw [action] at selected; cases selected
              | test level bad =>
                cases bad with
                | abandon => rw [action] at selected; cases selected
                | repair =>
                  rw [action] at selected
                  exact (menuRepairAction_ne_review P _ _ history current reviewed selected).elim
    · split at selected <;> cases selected

theorem zeroChargeCandidateRule_ne_review (P : Parameters) (fee : ℚ)
    (seed : MenuSeed P.certificate.stages P.tools) (history : List (VisibleEvent P.sharedInstance))
    (reviewed : P.sharedInstance.Stage) : P.zeroChargeCandidateRule fee seed history ≠ .review reviewed := by
  intro selected
  unfold Parameters.zeroChargeCandidateRule at selected
  split at selected
  · cases selected
  · split at selected
    · rename_i hcursor
      dsimp only at selected
      let current : P.sharedInstance.Stage :=
        ⟨historyCursor history, by simpa [Parameters.sharedInstance] using hcursor⟩
      cases written : historyWrite history current with
      | none => rw [written] at selected; cases selected
      | some packet =>
        obtain ⟨bit, serial⟩ := packet
        rw [written] at selected
        dsimp only at selected
        cases report : historyReport history current with
        | none => rw [report] at selected; cases selected
        | some packet =>
          obtain ⟨truth, reportedSerial⟩ := packet
          rw [report] at selected
          dsimp only at selected
          by_cases serialMismatch : (serial != reportedSerial) = true
          · simp only [serialMismatch, ite_true] at selected
            cases selected
          · simp only [serialMismatch] at selected
            by_cases correct : (bit == truth) = true
            · simp only [correct, ite_true] at selected
              cases selected
            · simp only [correct] at selected
              by_cases free : fee = 0
              · simp only [free] at selected
                exact menuRepairAction_ne_review P _ _ history current reviewed selected
              · simp only [free] at selected
                cases selected
    · split at selected <;> cases selected

theorem calibratedStateCandidate_review_lt (P : Parameters) (state : MultiplierState)
    (seed : P.CalibratedSearchSeed) (history : List (VisibleEvent P.sharedInstance))
    (reviewed : P.sharedInstance.Stage)
    (selected : P.calibratedStateCandidate state seed history = .review reviewed) :
    (historyObservations history reviewed).length < P.certificate.Q := by
  cases state with
  | exact solution => exact calibratedMenuCandidate_review_lt P solution.table seed.2 history reviewed selected
  | bracket lower upper =>
    exact calibratedMenuCandidate_review_lt P (if seed.1 then lower.table else upper.table)
      seed.2 history reviewed selected

theorem calibratedAlgorithmCandidate_review_lt (P : Parameters) (fee : ℚ)
    (seed : P.CalibratedSearchSeed) (history : List (VisibleEvent P.sharedInstance))
    (reviewed : P.sharedInstance.Stage)
    (selected : P.calibratedAlgorithmCandidate fee seed history = .review reviewed) :
    (historyObservations history reviewed).length < P.certificate.Q := by
  unfold Parameters.calibratedAlgorithmCandidate at selected
  split at selected
  · exact (zeroChargeCandidateRule_ne_review P fee seed.2.1 history reviewed selected).elim
  · exact calibratedStateCandidate_review_lt P _ seed history reviewed selected

theorem calibratedAlgorithmRule_review_lt (P : Parameters) (fee : ℚ)
    (seed : P.CalibratedSearchSeed) (history : List (VisibleEvent P.sharedInstance))
    (reviewed : P.sharedInstance.Stage)
    (selected : P.calibratedAlgorithmRule fee seed history = .review reviewed) :
    (historyObservations history reviewed).length < P.certificate.Q := by
  unfold Parameters.calibratedAlgorithmRule searchGuardRule at selected
  dsimp only at selected
  split at selected
  · exact calibratedAlgorithmCandidate_review_lt P fee seed history reviewed selected
  · cases selected

end PDROC.CalibratedResources
