module

public import PaperProofs.Paid.PDROC_CalibratedIdeal_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open PDMenu PDROC.CalibratedRuntime

namespace PDROC.CalibratedIdeal

/-- Strict remaining-stage induction for the unchanged actual ideal run.
Endpoint finiteness is only an internal sample condition, discharged below
on the original probability-one set. No continuation performance is assumed. -/
theorem entryTrace_induction (P : Parameters) (table : MenuTable) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : MenuSeed P.certificate.stages P.tools × (P.input fee hfee).World)
    (finite : MenuEndpointFiniteSample P P.certificate.stages P.tools fee hfee sample) :
    ∀ (n cursor clock : ℕ) (hfit : cursor + n = P.certificate.stages),
      FirstEntryAt (P.input fee hfee) C.val .uncapped accounting
        (P.compiledMenuRule P.certificate.stages P.tools table) cursor clock sample →
      EntryTrace P table fee hfee C accounting sample cursor n clock hfit := by
  intro n
  induction n with
  | zero =>
      intro cursor clock hfit hentry
      exact entryTrace_zero P table fee hfee C accounting sample cursor clock hfit hentry
  | succ n ih =>
      intro cursor clock hfit hentry
      let stage := menuSuffixStage P.certificate.stages P.tools cursor (n + 1) hfit 0
      have hstage : stage.val = cursor := by
        change cursor + 0 = cursor
        exact Nat.add_zero cursor
      have nextfit : cursor + 1 + n = P.certificate.stages := by omega
      let k := P.tools - (run (P.input fee hfee) C.val .uncapped accounting
        (P.compiledMenuRule P.certificate.stages P.tools table) sample clock).ledger.executions.length
      cases ha : (menuEntryAt table (n + 1) k).action with
      | finish =>
          exact entryTrace_abandon P table fee hfee C accounting sample cursor n clock hfit stage hstage hentry (.inr ha)
      | abandon =>
          exact entryTrace_abandon P table fee hfee C accounting sample cursor n clock hfit stage hstage hentry (.inl ha)
      | test level bad =>
          obtain ⟨reviews, stop⟩ := finite stage level (sample.1 stage)
          by_cases correct : (menuAnalysisTest P level).rule.decision (sample.1 stage)
              (menuOriginalTape P P.certificate.stages P.tools fee hfee stage
                (worldTapes (P.input fee hfee) sample.2 stage)) = (P.input fee hfee).truthAt sample.2 stage
          · exact entryTrace_correct P table fee hfee C accounting sample cursor n clock hfit nextfit stage hstage hentry
              level reviews bad ha stop correct (fun nextclock next => ih (cursor + 1) nextclock nextfit next)
          · cases bad with
            | abandon =>
                exact entryTrace_test_abort P table fee hfee C accounting sample cursor n clock hfit stage hstage hentry
                  level reviews .abandon ha stop correct (.inl rfl)
            | repair =>
                by_cases zero : k = 0
                · exact entryTrace_test_abort P table fee hfee C accounting sample cursor n clock hfit stage hstage hentry
                    level reviews .repair ha stop correct (.inr zero)
                · exact entryTrace_repair P table fee hfee C accounting sample cursor n clock hfit nextfit stage hstage hentry
                    level reviews ha stop correct (Nat.pos_of_ne_zero zero)
                    (fun nextclock next => ih (cursor + 1) nextclock nextfit next)

theorem rootTrace_of_finite (P : Parameters) (table : MenuTable) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (sample : MenuSeed P.certificate.stages P.tools × (P.input fee hfee).World)
    (finite : MenuEndpointFiniteSample P P.certificate.stages P.tools fee hfee sample) :
    ∃ ended,
      (run (P.input fee hfee) C.val .uncapped accounting
        (P.compiledMenuRule P.certificate.stages P.tools table) sample ended).halted = true ∧
      TraceLedgerMatch P 0 ∅
        (pathSummary P (idealFamily P) table P.certificate.stages P.tools
          (menuSeedFinEquiv P.certificate.stages P.tools sample.1)
          (menuWorldFinEquiv P P.certificate.stages P.tools fee hfee sample.2)).trace
        (initial ((P.input fee hfee).truthAt sample.2))
        (run (P.input fee hfee) C.val .uncapped accounting
          (P.compiledMenuRule P.certificate.stages P.tools table) sample ended) := by
  have first : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting
      (P.compiledMenuRule P.certificate.stages P.tools table) 0 0 sample := by
    exact ⟨rfl, by intro j hj; omega⟩
  obtain ⟨ended, _, halted, matched⟩ := entryTrace_induction P table fee hfee C accounting sample finite
    P.certificate.stages 0 0 (Nat.zero_add P.certificate.stages) first
  refine ⟨ended, halted, ?_⟩
  simp only [run, initial, historyUsed, historyCommitments, List.filterMap_nil,
    List.map_nil, List.toFinset_nil, List.length_nil, Nat.sub_zero,
    menuSuffixSeed_root P.certificate.stages P.tools sample.1,
    menuSuffixWorld_root P P.certificate.stages P.tools fee hfee sample.2] at matched ⊢
  with_unfolding_all exact matched

end PDROC.CalibratedIdeal
