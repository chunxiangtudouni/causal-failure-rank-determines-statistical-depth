module

public import PaperProofs.Paid.PDROC_SourceTerminal_001
public import PaperProofs.Paid.PDROC_SimulatorFlow_010

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem sourceTerminal_minimal_exit_of_finite
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (stage : P.sharedInstance.Stage) (sample : Seed × (P.input fee hfee).World)
    (hs : (simulatorLocalTest P fee hfee (sourceForOptionalHistory source.rule)
      (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage).rule.stop
        (sourceEventualStageSample P fee hfee C accounting source stage sample).1
        (sourceEventualStageSample P fee hfee C accounting source stage sample).2.2 ≠ ⊤)
    (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting source.rule stage sample = some entry) :
    ∃ start offset : ℕ,
      FirstEntryAt (P.input fee hfee) C.val .uncapped accounting source.rule stage.val start sample ∧
      (∀ k < offset, (run (P.input fee hfee) C.val .uncapped accounting source.rule sample (start + k)).halted = false ∧
        (run (P.input fee hfee) C.val .uncapped accounting source.rule sample (start + k)).cursor = stage.val) ∧
      (sourceEventualStageExitSome P fee hfee C accounting source stage sample).2 =
        some (run (P.input fee hfee) C.val .uncapped accounting source.rule sample (start + offset)).history ∧
      ((run (P.input fee hfee) C.val .uncapped accounting source.rule sample (start + offset)).halted = true ∨
        (run (P.input fee hfee) C.val .uncapped accounting source.rule sample (start + offset)).cursor = stage.val + 1) := by
  obtain ⟨start, draw, hfirst, hhistory, hd, hreport⟩ :=
    sourceEventualReportedDraw_source_realization_of_finite P fee hfee C accounting source stage sample hs entry he
  obtain ⟨offset, hbefore, hexit, hstage⟩ := firstEntry_sourceDrawStageExit_minimal P fee hfee C accounting
    source.rule source.legal sample start stage hfirst draw hd
  have hstageHistory := congrArg Prod.snd hstage
  rw [hhistory] at hstageHistory
  refine ⟨start, offset, hfirst, hbefore, ?_, hexit⟩
  change some ((sourceDrawStageExit (sourceForOptionalHistory source.rule) stage
    (sourceEventualReportedDraw P fee hfee C accounting source stage sample)).2) = _
  rw [hreport, sourceDrawStageExit_optionalHistory_some]
  exact congrArg some hstageHistory.symm

/-- The original source's complete cursor-N component is the measurable
tail of its genuine minimal last-stage exit, under only original full-bill
finiteness. No source success or entry normalization is used. -/
theorem source_finalCursorCapture_ae
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hlast : stage.val + 1 = P.sharedInstance.stageCount)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
      cursorCompletedNatProjection P.sharedInstance.stageCount
        (sample.1, completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule sample) =
      finalCursorTailProjection P.sharedInstance.stageCount source.rule
        (sourceEventualStageExitSome P fee hfee C accounting source stage sample) := by
  filter_upwards [sourceEventualStageSample_finite_ae P fee hfee C accounting source ν stage hfinite] with sample hs
  have hcursor (clock : ℕ) : historyCursor (id (run (P.input fee hfee) C.val .uncapped accounting source.rule sample clock).history) =
      (run (P.input fee hfee) C.val .uncapped accounting source.rule sample clock).cursor := by
    obtain ⟨n, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting source.rule source.legal sample clock
    exact prefix_historyCursor (P.input fee hfee) C.val .uncapped accounting source.rule sample.1 _ _ hp
  have hhalt (clock : ℕ) : historyHalted (id (run (P.input fee hfee) C.val .uncapped accounting source.rule sample clock).history) =
      (run (P.input fee hfee) C.val .uncapped accounting source.rule sample clock).halted := by
    obtain ⟨n, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting source.rule source.legal sample clock
    exact prefix_historyHalted (P.input fee hfee) C.val .uncapped accounting source.rule sample.1 _ _ hp
  have hcatch := sourceTerminal_minimal_exit_of_finite P fee hfee C accounting source stage sample hs
  have h := finalCursorHistory_eq_tailProjection_of_minimal_exit (P.input fee hfee) C.val .uncapped accounting
    source.rule source.legal sample stage hlast id hcursor hhalt source.rule sample.1
      (sourceEventualStageExitSome P fee hfee C accounting source stage sample).2 hcatch
        (fun _ clock _ _ _ hc => by
          simpa only [Option.map_id, id_eq] using
            terminalCursorTail_eq_completedHistory (P.input fee hfee) C.val C.property .uncapped accounting source.rule source.legal sample clock hc)
  have hseed := sourceEventualStageExitSome_seed P fee hfee C accounting source stage sample
  have hp := congrArg (fun prior => finalCursorTailProjection P.sharedInstance.stageCount source.rule
    (prior, (sourceEventualStageExitSome P fee hfee C accounting source stage sample).2)) hseed
  simp only [Option.map_id, id_eq] at h
  exact h.trans hp.symm

end PDROC
