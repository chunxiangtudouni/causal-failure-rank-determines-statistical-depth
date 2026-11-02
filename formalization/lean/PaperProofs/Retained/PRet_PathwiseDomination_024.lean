module

public import PaperProofs.Retained.PRet_RunReplay_023
public import PaperProofs.Retained.PRet_DelayedTerminalOnly_011

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetPathwiseDomination024

open Common Common.Native MeasureTheory PRetDelayedPolicy010 PRetDelayedTerminalOnly011
open PRetReplayConsequences017 PRetRunReplay023

variable {I : Instance}

theorem actualBill_domination {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) :
    runActualBill input C .uncapped accounting (rule accounting source) sample ≤
      runActualBill input C mode accounting source sample := by
  apply iSup_le
  intro n
  exact actualBill_le_of_replayInvariant input C mode accounting source sample _
    (run_replayInvariant input C hretained mode accounting source hlegal sample n)

theorem observationBill_domination {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) :
    runObservationBill input C .uncapped accounting (rule accounting source) sample ≤
      runObservationBill input C mode accounting source sample := by
  apply iSup_le
  intro n
  exact observationBill_le_of_replayInvariant input C mode accounting source sample _
    (run_replayInvariant input C hretained mode accounting source hlegal sample n)

theorem shadow_run {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (n : ℕ) :
    ∃ oldClock,
      shadowHistory accounting source sample.1
          (run input C .uncapped accounting (rule accounting source) sample n).history =
        (run input C mode accounting source sample oldClock).history ∧
      informationTrace (shadowHistory accounting source sample.1
          (run input C .uncapped accounting (rule accounting source) sample n).history) =
        informationTrace (run input C .uncapped accounting (rule accounting source) sample n).history :=
  shadow_of_replayInvariant input C mode accounting source sample _
    (run_replayInvariant input C hretained mode accounting source hlegal sample n)

/-- The actual constructed Policy, SAME original Seed, public measurable
whole-history shadow and all-path bills. Successful-source liveness, exact
eventual pairs and risk are deliberately still to be proved for R02. -/
theorem native_rearrangement_safety {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : Policy input C mode accounting Seed) :
    ∃ delayed : Policy input C .uncapped accounting Seed,
      TerminalOnly input C .uncapped accounting delayed.rule ∧
      ∃ shadow : Seed → List (VisibleEvent I) → List (VisibleEvent I),
        Measurable (fun p : Seed × List (VisibleEvent I) => shadow p.1 p.2) ∧
        (∀ sample n, ∃ oldClock,
          shadow sample.1 (run input C .uncapped accounting delayed.rule sample n).history =
            (run input C mode accounting source.rule sample oldClock).history ∧
          informationTrace (shadow sample.1 (run input C .uncapped accounting delayed.rule sample n).history) =
            informationTrace (run input C .uncapped accounting delayed.rule sample n).history) ∧
        (∀ sample,
          runObservationBill input C .uncapped accounting delayed.rule sample ≤
              runObservationBill input C mode accounting source.rule sample ∧
          runActualBill input C .uncapped accounting delayed.rule sample ≤
              runActualBill input C mode accounting source.rule sample) := by
  refine ⟨policy input C hretained accounting source.rule source.measurable_rule,
    delayed_terminalOnly input C accounting source.rule,
    shadowHistory accounting source.rule, measurable_shadowHistory accounting source.rule source.measurable_rule,
    ?_, ?_⟩
  · exact shadow_run input C hretained mode accounting source.rule source.legal
  · intro sample
    exact ⟨observationBill_domination input C hretained mode accounting source.rule source.legal sample,
      actualBill_domination input C hretained mode accounting source.rule source.legal sample⟩

end PaperProofs.Retained.PRetPathwiseDomination024
