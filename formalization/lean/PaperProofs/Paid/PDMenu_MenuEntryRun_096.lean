module

public import PaperProofs.Paid.PDMenu_MenuEndpointRun_095
public import PaperProofs.Common.HistorySuffixRun

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance} {Seed : Type*}

/-- The visible testing frame facts follow from a genuine first entry.
In particular the earlier visible history contains no sample of this stage. -/
theorem menuFirstEntry_visible_fresh (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (stage : I.Stage) (clock : ℕ)
    (hentry : FirstEntryAt input C mode accounting rule stage.val clock sample) :
    let state := run input C mode accounting rule sample clock
    historyHalted state.history = false ∧ historyCursor state.history = stage.val ∧
      historyWrite state.history stage = none ∧ historyObservations state.history stage = [] := by
  obtain ⟨hactive, hfresh⟩ := firstEntryAt_unborn input C mode accounting rule hlegal sample stage.val clock hentry
  obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting rule hlegal sample clock
  obtain ⟨hport, hzero⟩ := hfresh stage le_rfl
  refine ⟨(prefix_historyHalted input C mode accounting rule sample.1 _ _ hp).trans hactive,
    (prefix_historyCursor input C mode accounting rule sample.1 _ _ hp).trans hentry.1, ?_, ?_⟩
  · rw [prefix_historyWrite input C mode accounting rule sample.1 _ _ hp stage, hport]
    rfl
  · have hlength := prefix_historyObservations_length input C mode accounting rule sample.1 _ _ hp stage
    rw [hzero] at hlength
    have hz : (historyObservations (run input C mode accounting rule sample clock).history stage).length = 0 := by
      exact_mod_cast hlength
    exact List.length_eq_zero_iff.mp hz

/-- Actual finite endpoint write from first entry. All frame, legal-rule,
empty-port and zero-review hypotheses are discharged from original steps. -/
theorem compiledMenu_run_writtenFrom_firstEntry (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K))
    (sample : MenuSeed N K × (P.freshInput N K fee hfee).World)
    (stage : (freshInstance N K).Stage) (clock level reviews : ℕ) (bad : MenuBadAction)
    (hentry : FirstEntryAt (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) stage.val clock sample)
    (ha : (Parameters.menuEntryAt table (N - stage.val)
      (P.menuEntryTools N K
        (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock).history stage)).action =
          .test level bad)
    (hstop : (menuAnalysisTest P level).rule.stop (sample.1 stage)
      (menuOriginalTape P N K fee hfee stage (worldTapes (P.freshInput N K fee hfee) sample.2 stage)) = reviews) :
    run (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) sample (clock + reviews + 1) =
        menuWrittenFrom (P.freshInput N K fee hfee) C accounting stage
          (run (P.freshInput N K fee hfee) C .uncapped accounting (P.compiledMenuRule N K table) sample clock)
          (worldTapes (P.freshInput N K fee hfee) sample.2 stage) reviews
          ((menuAnalysisTest P level).rule.decision (sample.1 stage)
            (menuOriginalTape P N K fee hfee stage (worldTapes (P.freshInput N K fee hfee) sample.2 stage))) := by
  have hlegal := P.compiledMenuRule_uncapped_legal N K table fee hfee C hearly accounting
  obtain ⟨hactive, hfresh⟩ := firstEntryAt_unborn (P.freshInput N K fee hfee) C .uncapped accounting
    (P.compiledMenuRule N K table) hlegal sample stage.val clock hentry
  obtain ⟨hport, hzero⟩ := hfresh stage le_rfl
  obtain ⟨hh, hc, hw, ho⟩ := menuFirstEntry_visible_fresh (P.freshInput N K fee hfee) C .uncapped accounting
    (P.compiledMenuRule N K table) hlegal sample stage clock hentry
  exact compiledMenu_run_writtenFrom P N K table fee hfee C accounting sample stage clock _ rfl
    hactive hentry.1 hport hzero hh hc hw ho level _ bad rfl ha reviews hstop

end PDMenu
