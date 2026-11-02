module

public import PaperProofs.Paid.PDMenu_MenuCorrectEntryRecords_120
public import PaperProofs.Paid.PDMenu_MenuRepairEntryRecords_122
public import PaperProofs.Paid.PDMenu_MenuTerminalRecords_116
public import PaperProofs.Paid.PDMenu_MenuAbandonRecords_117

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- This explicit operational abort target has no future or IH premise.
It is kept separate so the finite-abort proof can be supplied independently.
It is not a Policy performance field or a proved Native refinement. -/
def MenuAbortEntryRecords (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K))
    (accounting : NormalAccounting (freshInstance N K))
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World) : Prop :=
  ∀ (cursor n clock : ℕ) (hfit : cursor + (n + 1) = N)
    (stage : (freshInstance N K).Stage), stage.val = cursor →
      FirstEntryAt (P.freshInput N K fee hfee) C .uncapped accounting
        (P.compiledMenuRule N K table) cursor clock sample →
      ∀ (level reviews : ℕ) (bad : MenuBadAction),
        (Parameters.menuEntryAt table (n + 1)
          (K - (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).ledger.executions.length)).action = .test level bad →
        (menuAnalysisTest P level).rule.stop (sample.1 stage)
          (menuOriginalTape P N K fee hfee stage (worldTapes (P.freshInput N K fee hfee) sample.2 stage)) = reviews →
        (menuAnalysisTest P level).rule.decision (sample.1 stage)
          (menuOriginalTape P N K fee hfee stage (worldTapes (P.freshInput N K fee hfee) sample.2 stage)) ≠
            (P.freshInput N K fee hfee).truthAt sample.2 stage →
        (bad = .abandon ∨ K - (run (P.freshInput N K fee hfee) C .uncapped accounting
          (P.compiledMenuRule N K table) sample clock).ledger.executions.length = 0) →
        MenuEntryRunRecords P N K table fee hfee C accounting sample cursor (n + 1) clock hfit

/-- Strict finite-stage induction. All true continuation IHs are discharged
here at strictly smaller n; only the separately named no-continuation abort
target remains to be instantiated by its real finite-path proof. -/
theorem menuEntryRunRecords_induction (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance N K))
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World)
    (hfinite : MenuEndpointFiniteSample P N K fee hfee sample)
    (habort : MenuAbortEntryRecords P N K table fee hfee C accounting sample) :
    ∀ (n cursor clock : ℕ) (hfit : cursor + n = N),
      FirstEntryAt (P.freshInput N K fee hfee) C .uncapped accounting
        (P.compiledMenuRule N K table) cursor clock sample →
      MenuEntryRunRecords P N K table fee hfee C accounting sample cursor n clock hfit := by
  intro n
  induction n with
  | zero =>
    intro cursor clock hfit hentry
    exact menuEntryRunRecords_zero P N K table fee hfee C hC.1.1 accounting sample cursor clock hfit hentry
  | succ n ih =>
    intro cursor clock hfit hentry
    let stage := menuSuffixStage N K cursor (n + 1) hfit 0
    have hstage : stage.val = cursor := by
      change cursor + 0 = cursor
      exact Nat.add_zero cursor
    have hnextfit : cursor + 1 + n = N := by omega
    let k := K - (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).ledger.executions.length
    cases ha : (Parameters.menuEntryAt table (n + 1) k).action with
    | finish =>
      exact menuEntryRunRecords_abandon P N K table fee hfee C hC.1.1 accounting sample cursor n clock hfit
        stage hstage hentry (.inr ha)
    | abandon =>
      exact menuEntryRunRecords_abandon P N K table fee hfee C hC.1.1 accounting sample cursor n clock hfit
        stage hstage hentry (.inl ha)
    | test level bad =>
      obtain ⟨reviews, hstop⟩ := hfinite stage level (sample.1 stage)
      by_cases hcorrect : (menuAnalysisTest P level).rule.decision (sample.1 stage)
          (menuOriginalTape P N K fee hfee stage (worldTapes (P.freshInput N K fee hfee) sample.2 stage)) =
            (P.freshInput N K fee hfee).truthAt sample.2 stage
      · exact menuEntryRunRecords_test_correct P N K table fee hfee C hC accounting sample cursor n clock hfit hnextfit
          stage hstage hentry level reviews bad ha hstop hcorrect
          (fun nextclock hnext => ih (cursor + 1) nextclock hnextfit hnext)
      · cases bad with
        | abandon =>
          exact habort cursor n clock hfit stage hstage hentry level reviews .abandon ha hstop hcorrect (.inl rfl)
        | repair =>
          by_cases hz : k = 0
          · exact habort cursor n clock hfit stage hstage hentry level reviews .repair ha hstop hcorrect (.inr hz)
          · exact menuEntryRunRecords_test_repair P N K table fee hfee C hC accounting sample cursor n clock hfit hnextfit
              stage hstage hentry level reviews ha hstop hcorrect (Nat.pos_of_ne_zero hz)
              (fun nextclock hnext => ih (cursor + 1) nextclock hnextfit hnext)

end PDMenu
