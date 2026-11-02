module

public import PaperProofs.Paid.PDROC_SimulatorLaw_009

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {Seed : Type u}

/-- A finite, visible stage condition suitable for transport under the
complete record/truth law. It contains no hidden-world existence predicate. -/
def sourceDrawGuardGood (source : PolicyRule I Seed) (stage : I.Stage)
    (sample : ((Seed × List (VisibleEvent I)) × SimulatorDraw I) × Bool) : Prop :=
  ((∃ bit, sample.1.2.action = .write stage bit) ∨
    sample.1.2.action = .stop ∨ sample.1.2.action = .abandon) ∧
  sourcePostwriteGuardGood source sample.1.1.1 stage
    (sourceDrawTerminalHistory stage sample.1.1.2 sample.1.2 sample.2)

theorem measurableSet_sourceDrawGuardGood [MeasurableSpace Seed]
    (source : PolicyRule I Seed) (hm : MeasurableRule source) (stage : I.Stage) :
    MeasurableSet {sample : ((Seed × List (VisibleEvent I)) × SimulatorDraw I) × Bool |
      sourceDrawGuardGood source stage sample} := by
  have ha : MeasurableSet {sample : ((Seed × List (VisibleEvent I)) × SimulatorDraw I) × Bool |
      (∃ bit, sample.1.2.action = .write stage bit) ∨
        sample.1.2.action = .stop ∨ sample.1.2.action = .abandon} :=
    ((Set.to_countable {draw : SimulatorDraw I | (∃ bit, draw.action = .write stage bit) ∨
      draw.action = .stop ∨ draw.action = .abandon}).measurableSet).preimage
        (measurable_snd.comp measurable_fst)
  have hh : Measurable (fun sample : ((Seed × List (VisibleEvent I)) × SimulatorDraw I) × Bool =>
      sourceDrawTerminalHistory stage sample.1.1.2 sample.1.2 sample.2) :=
    (measurable_of_countable (fun data : (List (VisibleEvent I) × SimulatorDraw I) × Bool =>
      sourceDrawTerminalHistory stage data.1.1 data.1.2 data.2)).comp
      ((((measurable_snd.comp measurable_fst).comp measurable_fst).prodMk
        (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  exact ha.inter ((measurableSet_sourcePostwriteGuardGood source hm stage).preimage
    ((((measurable_fst.comp measurable_fst).comp measurable_fst)).prodMk hh))

theorem sourceDrawTerminalHistory_written (stage : I.Stage) (entry : List (VisibleEvent I))
    (draw : SimulatorDraw I) (truth bit : Bool) (ha : draw.action = .write stage bit) :
    historyWritten (sourceDrawTerminalHistory stage entry draw truth) stage = some bit := by
  rw [sourceDrawTerminalHistory_write stage entry draw truth bit ha]
  let serial := (historyActions entry).length + draw.record.observations.length
  have h := historyWrite_append_report
    ((entry ++ simulatorReviewPacket stage draw.record) ++ [.wrote stage bit serial]) stage stage truth serial
  rw [historyWrite_append_wrote_same] at h
  unfold historyWritten
  simpa only [List.append_assoc, List.singleton_append, Option.map_some] using congrArg (Option.map Prod.fst) h

theorem sourceDrawTerminalHistory_halted (stage : I.Stage) (entry : List (VisibleEvent I))
    (draw : SimulatorDraw I) (truth : Bool) (ha : draw.action = .stop ∨ draw.action = .abandon) :
    historyHalted (sourceDrawTerminalHistory stage entry draw truth) = true := by
  rcases ha with hs | hs
  · rw [sourceDrawTerminalHistory_stop stage entry draw truth hs]
    simp [historyHalted, historyActions, List.filterMap_append, eventAction]
  · rw [sourceDrawTerminalHistory_abandon stage entry draw truth hs]
    simp [historyHalted, historyActions, List.filterMap_append, eventAction]

/-- Every finite actual source draw at an original first entry satisfies
the measurable stage guard condition, on all successful and failed paths. -/
theorem firstEntry_sourceDrawGuardGood (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (hl : LegalRule (P.input fee hfee) C.val .uncapped accounting source)
    (sample : Seed × (P.input fee hfee).World) (start : ℕ) (stage : P.sharedInstance.Stage)
    (he : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting source stage.val start sample)
    (draw : SimulatorDraw P.sharedInstance)
    (hd : simulatorDrawAt P fee hfee source stage sample.1
      (run (P.input fee hfee) C.val .uncapped accounting source sample start).history
        (worldTapes (P.input fee hfee) sample.2 stage) = some draw) :
    sourceDrawGuardGood source stage
      (((sample.1, (run (P.input fee hfee) C.val .uncapped accounting source sample start).history), draw),
        (P.input fee hfee).truthAt sample.2 stage) := by
  have hshape := firstEntry_simulatorDrawAt_action_cases P fee hfee C accounting source hl sample start stage he draw hd
  refine ⟨hshape, ?_⟩
  rcases hshape with ⟨bit, hw⟩ | hstop | habandon
  · let input := P.input fee hfee
    let finish := start + draw.record.observations.length + 1
    have hterminal := firstEntry_sourceDrawTerminalHistory P fee hfee C accounting source hl sample start stage he draw hd
    obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting source hl sample finish
    have hh := sourceDrawTerminalHistory_written stage (run input C.val .uncapped accounting source sample start).history
      draw (input.truthAt sample.2 stage) bit hw
    rw [hterminal, prefix_historyWritten input C.val .uncapped accounting source sample.1 _ _ hp stage] at hh
    have hwrite : (run input C.val .uncapped accounting source sample finish).ledger.written stage ≠ none := by
      rw [hh]
      simp only [ne_eq, reduceCtorEq, not_false_eq_true]
    have hg := sourcePostwriteGuardGood_of_run input C.val C.property .uncapped accounting source hl sample finish stage hwrite
    rw [hterminal]
    exact hg
  · exact sourcePostwriteGuardGood_of_halted source sample.1 stage _
      (sourceDrawTerminalHistory_halted stage _ draw _ (Or.inl hstop))
  · exact sourcePostwriteGuardGood_of_halted source sample.1 stage _
      (sourceDrawTerminalHistory_halted stage _ draw _ (Or.inr habandon))

end PDROC
