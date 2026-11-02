module

public import PaperProofs.Retained.PRet_EntrySaturation_059
public import PaperProofs.Retained.PRet_OutputCompletion_049
public import PaperProofs.Retained.PRet_PrebarrierProgress_028

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetEntryProgress061

open Common Common.Native PRetInformationPackets006 PRetEntryReplay045 PRetEntryInvariant050
open PRetEntrySaturation059 PRetOutputCompletion049 PRetPrebarrierProgress028 PRetPastWritten015

variable {I : Instance}

/-- Every genuine prefix has a legal raw continuation; a completed source
cannot induce public-guard rejection or false abandonment. Only actual
ordinary completion is assumed, separately from any matching condition. -/
theorem raw_step {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (first start : ℕ) (hentry : FirstEntryAt input C mode accounting source first start sample)
    (hcomplete : ∃ last, (run input C mode accounting source sample last).halted = true ∧
      (run input C mode accounting source sample last).ledger.finished = true ∧
      (run input C mode accounting source sample last).ledger.abandoned = false)
    {n : ℕ} {target : State (I.freshSuffix first)}
    (hp : Prefix (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) (PRetFreshExtractionPolicy047.rule first accounting source
        (publicStartup (run input C mode accounting source sample start)))
      sample.1 ((input.freshSuffix first).truthAt (input.restrictFreshWorld first sample.2))
      (worldTapes (input.freshSuffix first) (input.restrictFreshWorld first sample.2)) n target)
    (hi : EntryInvariant input C mode accounting source sample first start
      (publicStartup (run input C mode accounting source sample start)) target)
    (ha : target.halted = false) :
    ∃ next, Step (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first))
      (worldTapes (input.freshSuffix first) (input.restrictFreshWorld first sample.2)) target
      (PRetFreshExtractionPolicy047.raw first accounting source
        (publicStartup (run input C mode accounting source sample start)) sample.1 target.history) next ∧
      (next.halted = true → next.ledger.finished = true ∧ next.ledger.abandoned = false) := by
  classical
  obtain ⟨packets, oldClock, hclock, hinfo, hreplay, hr, hw⟩ := hi
  have hshadow : shadowFrom first accounting source (publicStartup (run input C mode accounting source sample start))
      sample.1 target.history = some (publicStartup (run input C mode accounting source sample oldClock)) := by
    unfold shadowFrom
    rw [hinfo, parse_packets]
    exact hreplay
  have hraw := PRetFreshExtractionPolicy047.raw_of_shadow first accounting source _ _ sample.1 target.history hshadow
  change PRetFreshExtractionPolicy047.raw first accounting source _ sample.1 target.history =
    PRetFreshExtractionPolicy047.candidate first (publicStartup (run input C mode accounting source sample oldClock))
      (source sample.1 (run input C mode accounting source sample oldClock).history) target.history at hraw
  rw [hraw]
  obtain ⟨sourceClock, _, sourcePrefix⟩ := run_has_prefix input C mode accounting source hlegal sample oldClock
  by_cases hh : (run input C mode accounting source sample oldClock).halted = true
  · obtain ⟨hf, hab, hall⟩ := halted_completed_prefix input C mode accounting source hlegal sample hcomplete oldClock hh
    have hcursor := prefix_historyCursor (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) _ sample.1 _ _ hp
    have hbound := (prefix_cursorInvariant (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) _ sample.1 _ _ hp).bound
    have htargetAll : allWritten target.ledger := by
      intro stage
      rw [hw]
      exact hall (I.freshStageLift first stage)
    by_cases hlt : target.cursor < (I.freshSuffix first).stageCount
    · let stage : (I.freshSuffix first).Stage := ⟨target.cursor, hlt⟩
      have haction : PRetFreshExtractionPolicy047.candidate first
          (publicStartup (run input C mode accounting source sample oldClock))
          (source sample.1 (run input C mode accounting source sample oldClock).history) target.history = .advance stage := by
        simp only [PRetFreshExtractionPolicy047.candidate, publicStartup, hh, hf, hab, Bool.false_eq_true,
          ↓reduceIte, PRetDelayedPolicy010.catchUp, hcursor, hlt, ↓reduceDIte]
        rfl
      refine ⟨record (zeroNormalAccounting (I.freshSuffix first)) target (.advance stage) [.advanced stage]
        (advanceLedger target stage) (target.cursor + 1) false, ?_, ?_⟩
      · rw [haction]
        exact Step.advance target stage ⟨ha, rfl⟩ (htargetAll stage) (.inl rfl)
      · intro hn
        cases hn
    · have heq : target.cursor = (I.freshSuffix first).stageCount := by omega
      have haction : PRetFreshExtractionPolicy047.candidate first
          (publicStartup (run input C mode accounting source sample oldClock))
          (source sample.1 (run input C mode accounting source sample oldClock).history) target.history = .stop := by
        simp only [PRetFreshExtractionPolicy047.candidate, publicStartup, hh, hf, hab, Bool.false_eq_true,
          ↓reduceIte, PRetDelayedPolicy010.catchUp, hcursor, heq, Nat.lt_irrefl]
      refine ⟨stopState target false, ?_, ?_⟩
      · rw [haction]
        exact Step.stop target ha
      · intro _
        exact ⟨by simpa only [stopState, decide_eq_true_eq] using htargetAll, rfl⟩
  · have hactive := Bool.eq_false_iff.mpr hh
    obtain ⟨original, hreview | ⟨bit, hwrite⟩⟩ := active_replayFrom_information input C mode accounting source hlegal sample
      _ _ oldClock hreplay hactive
    · obtain ⟨sourceNext, hs⟩ := hlegal sample.1 _ _ sourceClock _ sourcePrefix hactive
      rw [hreview] at hs
      cases hs with
      | review _ live port resources =>
        have hfuture := source_cursor_ge_entry input C mode accounting source hlegal sample first start oldClock hentry hclock
        rw [live.2] at hfuture
        let stage := suffixStageOf first original hfuture
        have hlift : I.freshStageLift first stage = original := freshStageLift_suffixStageOf first original hfuture
        have hport : target.ledger.written stage = none := by
          rw [hw]
          change (run input C mode accounting source sample oldClock).ledger.written (I.freshStageLift first stage) = none
          rw [hlift]
          exact port
        have hle : target.cursor ≤ stage.val := by
          by_contra hn
          exact (prefix_past_written (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
            (zeroNormalAccounting (I.freshSuffix first)) _ sample.1 _ _ hp stage (by omega)) hport
        have hbound : target.cursor < (I.freshSuffix first).stageCount := lt_of_le_of_lt hle stage.isLt
        simp only [PRetFreshExtractionPolicy047.candidate, publicStartup, hactive, Bool.false_eq_true,
          ↓reduceIte, hreview, hfuture]
        obtain ⟨next, hstep, hnot⟩ := catchUp_step (input.freshSuffix first) (freshContract (I.freshSuffix first))
          (zeroNormalAccounting (I.freshSuffix first)) _ sample.1 _ _ hp ha hbound stage.val (.review stage) hle
          (by
            intro before hb
            rw [hw]
            apply prefix_past_written input C mode accounting source sample.1 _ _ sourcePrefix
            have hv := congrArg Fin.val hlift
            change first + stage.val = original.val at hv
            change first + before.val < (run input C mode accounting source sample oldClock).cursor
            rw [live.2]
            omega)
          (by
            intro heq
            exact ⟨_, Step.review target stage ⟨ha, heq⟩ hport (.inl rfl), rfl⟩)
        exact ⟨next, hstep, by intro hn; rw [hnot] at hn; cases hn⟩
    · obtain ⟨sourceNext, hs⟩ := hlegal sample.1 _ _ sourceClock _ sourcePrefix hactive
      rw [hwrite] at hs
      cases hs with
      | write _ _ live port resources =>
        have hfuture := source_cursor_ge_entry input C mode accounting source hlegal sample first start oldClock hentry hclock
        rw [live.2] at hfuture
        let stage := suffixStageOf first original hfuture
        have hlift : I.freshStageLift first stage = original := freshStageLift_suffixStageOf first original hfuture
        have hport : target.ledger.written stage = none := by
          rw [hw]
          change (run input C mode accounting source sample oldClock).ledger.written (I.freshStageLift first stage) = none
          rw [hlift]
          exact port
        have hle : target.cursor ≤ stage.val := by
          by_contra hn
          exact (prefix_past_written (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
            (zeroNormalAccounting (I.freshSuffix first)) _ sample.1 _ _ hp stage (by omega)) hport
        have hbound : target.cursor < (I.freshSuffix first).stageCount := lt_of_le_of_lt hle stage.isLt
        simp only [PRetFreshExtractionPolicy047.candidate, publicStartup, hactive, Bool.false_eq_true,
          ↓reduceIte, hwrite, hfuture]
        obtain ⟨next, hstep, hnot⟩ := catchUp_step (input.freshSuffix first) (freshContract (I.freshSuffix first))
          (zeroNormalAccounting (I.freshSuffix first)) _ sample.1 _ _ hp ha hbound stage.val (.write stage bit) hle
          (by
            intro before hb
            rw [hw]
            apply prefix_past_written input C mode accounting source sample.1 _ _ sourcePrefix
            have hv := congrArg Fin.val hlift
            change first + stage.val = original.val at hv
            change first + before.val < (run input C mode accounting source sample oldClock).cursor
            rw [live.2]
            omega)
          (by
            intro heq
            exact ⟨_, Step.write target stage bit ⟨ha, heq⟩ hport (.inl rfl), rfl⟩)
        exact ⟨next, hstep, by intro hn; rw [hnot] at hn; cases hn⟩

end PaperProofs.Retained.PRetEntryProgress061


