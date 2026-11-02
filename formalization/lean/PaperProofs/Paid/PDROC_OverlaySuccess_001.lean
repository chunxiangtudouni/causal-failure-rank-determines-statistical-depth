module

public import PaperProofs.Paid.PDROC_OverlaySimulator_020
public import PaperProofs.Paid.PDROC_OverlaySimulator_021
public import PaperProofs.Common.HistorySuffixSuccess

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u v w

variable {I : Instance}

theorem overlaySuccess_ghostEvents_cursor (calls : List (OverlayGhostCall I)) :
    historyCursor (overlayGhostEvents calls) = 0 := by
  induction calls with
  | nil => rfl
  | cons call rest ih =>
    rcases call with ⟨reserve, handle, tool⟩
    cases reserve <;> simp [historyCursor, overlayGhostEvents, List.filterMap_cons, eventAdvance]

theorem overlaySuccess_written_append_ghost (history : List (VisibleEvent I))
    (calls : List (OverlayGhostCall I)) (stage : I.Stage) :
    historyWritten (history ++ overlayGhostEvents calls) stage = historyWritten history stage := by
  have hz : (overlayGhostEvents calls).filterMap (eventWrite stage) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro event he
    obtain ⟨call, _, rfl⟩ := List.mem_map.mp he
    rcases call with ⟨reserve, handle, tool⟩
    cases reserve <;> rfl
  simp only [historyWritten, historyWrite, List.filterMap_append, hz, List.append_nil]

theorem overlaySuccess_validHandle_written (history : List (VisibleEvent I))
    (handle : MismatchHandle I) (hv : historyValidHandle history handle) :
    historyWritten history handle.stage ≠ none := by
  intro hn
  unfold historyValidHandle at hv
  cases hr : historyReport history handle.stage with
  | none => rw [hr] at hv; exact hv
  | some pair =>
    rw [hr] at hv
    rw [hn] at hv
    cases hv.1

/-- Checked ghost calls stay on the current virtual cursor and require an
already written virtual port. Previous ghosts change neither fact. -/
theorem overlaySuccess_ghostTrace_member {Source : Type u}
    (source : PolicyRule I Source) (seed : Source) (virtual : List (VisibleEvent I))
    (calls : List (OverlayGhostCall I)) (ht : OverlayGhostTrace source seed virtual calls)
    (call : OverlayGhostCall I) (hm : call ∈ calls) :
    call.2.1.stage.val = historyCursor virtual ∧ historyWritten virtual call.2.1.stage ≠ none := by
  induction calls generalizing virtual with
  | nil => cases hm
  | cons first rest ih =>
    rcases ht with ⟨haction, hallow, hrest⟩
    rcases List.mem_cons.mp hm with rfl | hm
    · rw [haction] at hallow
      have hc : historyCursor virtual = call.2.1.stage.val ∧ historyValidHandle virtual call.2.1 := by
        rcases call with ⟨reserve, handle, tool⟩
        cases reserve <;> exact ⟨hallow.1, hallow.2.1⟩
      exact ⟨hc.1.symm, overlaySuccess_validHandle_written virtual call.2.1 hc.2⟩
    · have h := ih _ hrest hm
      rw [historyCursor_append, overlaySuccess_ghostEvents_cursor, add_zero,
        overlaySuccess_written_append_ghost] at h
      exact h

/-- A real early prefix with an erroneous actual write keeps its genuine
mismatch handle even after physical repair. -/
theorem overlaySuccess_prefix_validHandle_of_wrong
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Actual : Type v}
    (rule : PolicyRule I Actual) (seed : Actual) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (stage : I.Stage) (hw : s.ledger.written stage = some (!s.ledger.truth stage)) :
    historyValidHandle s.history ⟨stage, historyWriteSerial s.history stage⟩ := by
  obtain ⟨time, ht⟩ := prefix_early_written_reported input C hearly mode accounting rule seed truth tapes hp stage
    (by rw [hw]; simp)
  have hr := prefix_historyReport_early input C hearly mode accounting rule seed truth tapes hp stage
  rw [ht] at hr
  unfold historyValidHandle
  rw [hr]
  simp only [Option.map_some]
  rw [prefix_historyWritten input C mode accounting rule seed truth tapes hp stage,
    prefix_historyWriteSerial input C mode accounting rule seed truth tapes hp stage]
  exact ⟨hw, rfl, trivial⟩

/-- A ghost can only occur at an actually correct written stage. This is
pointwise on every genuine early Native prefix, with no source-law, risk,
termination or finite-expectation hypothesis. -/
theorem overlaySuccess_ghost_member_correct
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Actual : Type v} {Source : Type u}
    (rule : PolicyRule I Actual) (seed : Actual) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (source : PolicyRule I Source) (oldSeed : Source) (cache : SimulatorCache I)
    (hseen : cache.seen = s.history) (hproj : OverlayHistoryProjection s.history cache.shadow)
    (call : OverlayGhostCall I) (hm : call ∈ overlayGhostAtCache source oldSeed cache) :
    s.ledger.written call.2.1.stage = some (s.ledger.truth call.2.1.stage) := by
  classical
  have hnot : overlayHasActualMismatch cache.seen ≠ true := by
    intro ht
    rw [overlayGhostAtCache_actualMismatch source oldSeed cache ht] at hm
    cases hm
  have hfalse : overlayHasActualMismatch cache.seen = false := Bool.eq_false_iff.mpr hnot
  have hcalls : call ∈ overlayGhostCalls 2 source oldSeed cache.shadow := by
    simpa only [overlayGhostAtCache, hfalse, Bool.false_eq_true, ite_false] using hm
  obtain ⟨hstage, hw⟩ := overlaySuccess_ghostTrace_member source oldSeed cache.shadow _
    (overlayGhostCalls_trace 2 source oldSeed cache.shadow) call hcalls
  have hactual : historyWritten s.history call.2.1.stage ≠ none :=
    fun hn => hw ((hproj.2.1 call.2.1.stage).mp hn)
  have hledger : s.ledger.written call.2.1.stage ≠ none := by
    rwa [prefix_historyWritten input C mode accounting rule seed truth tapes hp call.2.1.stage] at hactual
  by_contra hc
  obtain ⟨bit, hb⟩ := Option.ne_none_iff_exists.mp hledger
  have hne : bit ≠ s.ledger.truth call.2.1.stage := by
    intro he
    exact hc (hb.symm.trans (congrArg some he))
  have hwrong : s.ledger.written call.2.1.stage = some (!s.ledger.truth call.2.1.stage) :=
    hb.symm.trans (congrArg some (Bool.eq_not_iff.mpr hne))
  have hv := overlaySuccess_prefix_validHandle_of_wrong input C hearly mode accounting rule seed truth tapes hp call.2.1.stage hwrong
  have hcursor : historyCursor cache.seen = call.2.1.stage.val := by
    rw [hseen]
    exact hproj.1.trans hstage.symm
  have hs := simulatorStageAt_some cache.seen call.2.1.stage hcursor
  apply hnot
  simp only [overlayHasActualMismatch, hs, decide_eq_true_eq]
  simpa only [hseen] using hv

end PDROC
