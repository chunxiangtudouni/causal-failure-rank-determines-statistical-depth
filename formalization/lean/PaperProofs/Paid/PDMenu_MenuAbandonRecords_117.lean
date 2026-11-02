module

public import PaperProofs.Paid.PDMenu_MenuEntryRecordTarget_115
public import PaperProofs.Paid.PDMenu_MenuNativeActionRun_103
public import PaperProofs.Paid.PDMenu_MenuPhysicalSnapshot_084

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem menuEntryRunRecords_abandon (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K))
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World)
    (cursor n clock : ℕ) (hfit : cursor + (n + 1) = N)
    (stage : (freshInstance N K).Stage) (hstage : stage.val = cursor)
    (hentry : FirstEntryAt (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) cursor clock sample)
    (ha : (Parameters.menuEntryAt table (n + 1)
      (K - (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).ledger.executions.length)).action = .abandon ∨
      (Parameters.menuEntryAt table (n + 1)
        (K - (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).ledger.executions.length)).action = .finish) :
    MenuEntryRunRecords P N K table fee hfee C accounting sample cursor (n + 1) clock hfit := by
  let input := P.freshInput N K fee hfee
  let rule := P.compiledMenuRule N K table
  let start := run input C .uncapped accounting rule sample clock
  have hlegal := P.compiledMenuRule_uncapped_legal N K table fee hfee C hearly accounting
  obtain ⟨hactive, hfresh⟩ := firstEntryAt_unborn input C .uncapped accounting rule hlegal sample cursor clock hentry
  have hc : start.cursor = stage.val := hentry.1.trans hstage.symm
  have hport : start.ledger.written stage = none := (hfresh stage (by omega)).1
  have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample clock hactive
  have hk := menuPrefix_entryTools_eq_physical_sub P N K table fee hfee C accounting sample.1
    (input.truthAt sample.2) (worldTapes input sample.2) hp stage hc hport
  have hrow : N - stage.val = n + 1 := by omega
  have haction : rule sample.1 start.history = .abandon := by
    apply compiledMenuRule_entry_abandon P N K table fee hfee C hearly accounting rule sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) hp sample.1 stage hactive hc hport
    rw [hrow, hk]
    exact ha
  have habandon := menu_run_abandon input C accounting rule hlegal sample clock hactive haction
  have hhalt : (run input C .uncapped accounting rule sample (clock + 1)).halted = true := by rw [habandon]; rfl
  have hfailure : ¬runSuccess input C .uncapped accounting rule sample := by
    intro hs
    have hsuccess := (menu_runSuccess_iff_of_halted input C .uncapped accounting rule sample (clock + 1) hhalt).mp hs
    have hbad := hsuccess.2.1
    rw [habandon] at hbad
    change true = false at hbad
    cases hbad
  have hsummary : menuPathSummary P table (n + 1) (K - start.ledger.executions.length)
      (menuSuffixSeed N K cursor (n + 1) hfit sample.1)
      (menuSuffixWorld P N K cursor (n + 1) hfit fee hfee sample.2) = menuPathAbandon := by
    rcases ha with ha | ha
    · exact menuPathSummary_abandon P table n _ _ _ ha
    · exact menuPathSummary_finish_positive P table n _ _ _ ha
  unfold MenuEntryRunRecords
  dsimp only
  rw [hsummary]
  refine ⟨clock + 1, Nat.le_succ clock, hhalt, ?_, ?_, ?_⟩
  · rw [habandon]
    exact (add_zero _).symm
  · rw [habandon]
    exact (Nat.add_zero _).symm
  · constructor
    · intro hs
      exact (hfailure hs).elim
    · intro hfalse
      cases hfalse

end PDMenu
