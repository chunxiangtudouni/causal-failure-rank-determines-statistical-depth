module

public import PaperProofs.Paid.PDROC_SourceTerminal_001
public import PaperProofs.Paid.PDROC_SimulatorFlow_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- The ORIGINAL source's completed terminal component is its exact
eventual-stage exit component almost surely, without conditioning on
successful histories or a measurable range of semantic source worlds. -/
theorem sourceEventualStageExit_terminalCapture_ae
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
      cursorCompletedProjection stage
        (sample.1, completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule sample) =
      terminalExitProjection stage (sourceEventualStageExitSome P fee hfee C accounting source stage sample) := by
  filter_upwards [sourceEventualStageSample_finite_ae P fee hfee C accounting source ν stage hfinite] with sample hs
  have hcursor (clock : ℕ) : historyCursor (id (run (P.input fee hfee) C.val .uncapped accounting source.rule sample clock).history) =
      (run (P.input fee hfee) C.val .uncapped accounting source.rule sample clock).cursor := by
    obtain ⟨n, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting source.rule source.legal sample clock
    exact prefix_historyCursor (P.input fee hfee) C.val .uncapped accounting source.rule sample.1 _ _ hp
  have hhalt (clock : ℕ) : historyHalted (id (run (P.input fee hfee) C.val .uncapped accounting source.rule sample clock).history) =
      (run (P.input fee hfee) C.val .uncapped accounting source.rule sample clock).halted := by
    obtain ⟨n, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting source.rule source.legal sample clock
    exact prefix_historyHalted (P.input fee hfee) C.val .uncapped accounting source.rule sample.1 _ _ hp
  have hcatch := sourceEventualStageExitSome_actual_exit_of_finite P fee hfee C accounting source stage sample hs
  have h := cursorCompletedHistory_eq_terminalExitHistory (P.input fee hfee) C.val .uncapped accounting
    source.rule source.legal sample stage id hcursor hhalt
      (sourceEventualStageExitSome P fee hfee C accounting source stage sample).2 hcatch
  have hseed := sourceEventualStageExitSome_seed P fee hfee C accounting source stage sample
  apply Prod.ext
  · exact (congrArg Prod.fst hseed).symm
  · change cursorCompletedHistory stage (completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule sample) =
      terminalExitHistory stage (sourceEventualStageExitSome P fee hfee C accounting source stage sample).1.2
        (sourceEventualStageExitSome P fee hfee C accounting source stage sample).2
    rw [congrArg Prod.snd hseed]
    simpa only [Option.map_id, id_eq] using h

end PDROC
