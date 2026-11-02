module

public import PaperProofs.Paid.PDLower_BlindZeroQuota_002
public import PaperProofs.Common.ReferenceMassFlow

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native

namespace PDLower

variable {I : Instance}

def TruthAgreesOnWritten (state : State I) (truth : I.Stage → Bool) : Prop :=
  ∀ stage, state.ledger.written stage ≠ none → truth stage = state.ledger.truth stage

theorem step_retarget_agree_written (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (tapes : ReviewTapes input) (truth : I.Stage → Bool)
    {state next : State I} {action : Action I}
    (step : Step input C mode accounting tapes state action next)
    (agreeSource : TruthAgreesOnWritten state truth)
    (agreeNext : TruthAgreesOnWritten next truth) :
    Step input C mode accounting tapes (retargetTruth state truth) action (retargetTruth next truth) := by
  cases step with
  | review stage live port resources =>
    have hr : withinResources C mode (record accounting (retargetTruth state truth) (.review stage)
        [.observation stage (tapes stage (state.ledger.reviews stage).toNat).val]
        (reviewLedger (retargetTruth state truth) stage) state.cursor false).ledger := by
      simpa only [withinResources, Ledger.obeysCaps, Ledger.totalCalls, record, retargetTruth,
        reviewLedger] using resources
    simpa only [retargetTruth_record, retargetTruth, reviewLedger, record] using
      (Step.review (input := input) (C := C) (mode := mode) (accounting := accounting)
        (tapes := tapes) (retargetTruth state truth) stage live port hr)
  | write stage bit live port resources =>
    have hw : (reportedWriteLedger C state stage bit).written stage = some bit := by
      simp only [reportedWriteLedger, hearly, ↓reduceIte, writeLedger, Function.update_self]
    have hsame := agreeNext stage (by change (reportedWriteLedger C state stage bit).written stage ≠ none; rw [hw]; simp)
    change truth stage = (reportedWriteLedger C state stage bit).truth stage at hsame
    rw [reportedWriteLedger_truth] at hsame
    have hrsp : writeResponses C (retargetTruth state truth) stage bit =
        writeResponses C state stage bit := by
      simp only [writeResponses, hearly, ↓reduceIte, writeLedger, retargetTruth, hsame]
    have hr : withinResources C mode (record accounting (retargetTruth state truth) (.write stage bit)
        (writeResponses C (retargetTruth state truth) stage bit)
        (reportedWriteLedger C (retargetTruth state truth) stage bit) state.cursor false).ledger := by
      rw [hrsp, reportedWriteLedger_retargetTruth]
      simpa only [withinResources, Ledger.obeysCaps, Ledger.totalCalls, record, retargetTruth] using resources
    have hs := Step.write (input := input) (C := C) (mode := mode) (accounting := accounting)
      (tapes := tapes) (retargetTruth state truth) stage bit live port hr
    rw [hrsp, reportedWriteLedger_retargetTruth] at hs
    rw [retargetTruth_record]
    exact hs
  | allocate handle tool active valid compatible unused unallocated window resources =>
    have hsame := agreeSource handle.stage (by rw [valid.1]; simp)
    have hv : validHandle (retargetTruth state truth) handle := by
      simpa only [validHandle, retargetTruth, hsame] using valid
    have hr : withinResources C mode (record accounting (retargetTruth state truth) (.allocate handle tool)
        [.committed handle tool] (allocateLedger (retargetTruth state truth) handle tool) state.cursor false).ledger := by
      simpa only [withinResources, Ledger.obeysCaps, Ledger.totalCalls, record, retargetTruth,
        allocateLedger] using resources
    simpa only [retargetTruth_record, retargetTruth, allocateLedger, record] using
      (Step.allocate (input := input) (C := C) (mode := mode) (accounting := accounting)
        (tapes := tapes) (retargetTruth state truth) handle tool active hv compatible unused unallocated window hr)
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    have hsame := agreeSource handle.stage (by rw [valid.1]; simp)
    have hv : validHandle (retargetTruth state truth) handle := by
      simpa only [validHandle, retargetTruth, hsame] using valid
    have hr : withinResources C mode (record accounting (retargetTruth state truth) (.execute handle tool)
        [.executed handle tool] (executeLedger (retargetTruth state truth) handle tool) state.cursor false).ledger := by
      simpa only [withinResources, Ledger.obeysCaps, Ledger.totalCalls, record, retargetTruth,
        executeLedger] using resources
    simpa only [retargetTruth_record, retargetTruth, executeLedger, record] using
      (Step.execute (input := input) (C := C) (mode := mode) (accounting := accounting)
        (tapes := tapes) (retargetTruth state truth) handle tool active hv compatible committed unused uncorrected window hr)
  | advance stage live written resources =>
    have hr : withinResources C mode (record accounting (retargetTruth state truth) (.advance stage)
        [.advanced stage] (advanceLedger (retargetTruth state truth) stage) (state.cursor + 1) false).ledger := by
      simpa only [withinResources, Ledger.obeysCaps, Ledger.totalCalls, record, retargetTruth,
        advanceLedger] using resources
    simpa only [retargetTruth_record, retargetTruth, advanceLedger, record] using
      (Step.advance (input := input) (C := C) (mode := mode) (accounting := accounting)
        (tapes := tapes) (retargetTruth state truth) stage live written hr)
  | stop active =>
    simpa only [retargetTruth_stopState] using
      (Step.stop (input := input) (C := C) (mode := mode) (accounting := accounting)
        (tapes := tapes) (retargetTruth state truth) active)
  | abandon active =>
    simpa only [retargetTruth_stopState] using
      (Step.abandon (input := input) (C := C) (mode := mode) (accounting := accounting)
        (tapes := tapes) (retargetTruth state truth) active)

theorem truthAgreesOnWritten_source (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {state next : State I} {action : Action I}
    (step : Step input C mode accounting tapes state action next) (truth : I.Stage → Bool)
    (agreeNext : TruthAgreesOnWritten next truth) : TruthAgreesOnWritten state truth := by
  intro stage hwritten
  obtain ⟨bit, hbit⟩ := Option.ne_none_iff_exists'.mp hwritten
  have hnext := step_written_some input C mode accounting tapes step stage bit hbit
  have heq := agreeNext stage (by rw [hnext]; simp)
  rw [step_truth_unchanged input C mode accounting tapes step] at heq
  exact heq

theorem prefix_retarget_agree_written (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (seed : Seed) (truth truth' : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {state : State I}
    (path : Prefix input C mode accounting rule seed truth tapes n state)
    (agree : TruthAgreesOnWritten state truth') :
    Prefix input C mode accounting rule seed truth' tapes n (retargetTruth state truth') := by
  revert agree
  induction path with
  | initial => intro _agree; exact .initial
  | next earlier step ih =>
    intro agreeNext
    have agreeSource := truthAgreesOnWritten_source input C mode accounting tapes step truth' agreeNext
    exact .next (ih agreeSource)
      (step_retarget_agree_written input C hearly mode accounting tapes truth' step agreeSource agreeNext)

end PDLower
