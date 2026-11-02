module

public import PaperProofs.Paid.PDMenu_MenuEntryRun_096
public import PaperProofs.Paid.PDMenu_MenuGuard_068
public import PaperProofs.Common.NativeHeadContinuation

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- The original public report packet selects the actual correct/error
branch at any written stage, independently of the earlier execution history. -/
theorem compiledMenuRule_writtenFrame (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K)) {Seed : Type*}
    (rule : PolicyRule (freshInstance N K) Seed) (seed : Seed)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : MenuSeed N K) (stage : (freshInstance N K).Stage) (bit : Bool)
    (hactive : state.halted = false) (hcursor : state.cursor = stage.val)
    (hbit : state.ledger.written stage = some bit) :
    P.compiledMenuRule N K table menuSeed state.history =
      if bit == state.ledger.truth stage then .advance stage else
        match (Parameters.menuEntryAt table (N - stage.val)
          (P.menuEntryTools N K state.history stage)).action with
        | .test _ .repair => P.menuRepairAction N K state.history stage
        | _ => .abandon := by
  rw [compiledMenuRule_eq_candidate_on_prefix P N K table fee hfee C hearly accounting rule seed truth tapes hp menuSeed]
  have hh : historyHalted state.history = false :=
    (prefix_historyHalted (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes hp).trans hactive
  have hc : historyCursor state.history = stage.val :=
    (prefix_historyCursor (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes hp).trans hcursor
  have hw : historyWrite state.history stage = some (bit, state.ledger.writeSerial stage) := by
    rw [prefix_historyWrite (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes hp stage, hbit]
    rfl
  obtain ⟨time, htime⟩ := prefix_early_written_reported (P.freshInput N K fee hfee) C hearly .uncapped accounting
    rule seed truth tapes hp stage (by rw [hbit]; exact Option.some_ne_none bit)
  have hr : historyReport state.history stage = some (state.ledger.truth stage, state.ledger.writeSerial stage) := by
    rw [prefix_historyReport_early (P.freshInput N K fee hfee) C hearly .uncapped accounting rule seed truth tapes hp stage, htime]
    rfl
  have hlt : historyCursor state.history < N := by
    rw [hc]
    simpa [freshInstance] using stage.isLt
  have hs : (⟨historyCursor state.history, by simpa [freshInstance] using hlt⟩ : (freshInstance N K).Stage) = stage :=
    Fin.ext hc
  simp only [Parameters.menuCandidateAction, hh, Bool.false_eq_true, ite_false, dite_eq_left hlt, hs,
    hw, hr, bne_self_eq_false]
  rw [hc]
  rfl

theorem compiledMenuRule_written_correct (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K)) {Seed : Type*}
    (rule : PolicyRule (freshInstance N K) Seed) (seed : Seed)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : MenuSeed N K) (stage : (freshInstance N K).Stage)
    (hactive : state.halted = false) (hcursor : state.cursor = stage.val)
    (hbit : state.ledger.written stage = some (state.ledger.truth stage)) :
    P.compiledMenuRule N K table menuSeed state.history = .advance stage := by
  rw [compiledMenuRule_writtenFrame P N K table fee hfee C hearly accounting rule seed truth tapes hp
    menuSeed stage (state.ledger.truth stage) hactive hcursor hbit]
  simp only [beq_self_eq_true, ite_true]

theorem compiledMenuRule_written_wrong (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K)) {Seed : Type*}
    (rule : PolicyRule (freshInstance N K) Seed) (seed : Seed)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : MenuSeed N K) (stage : (freshInstance N K).Stage) (bit : Bool)
    (hactive : state.halted = false) (hcursor : state.cursor = stage.val)
    (hbit : state.ledger.written stage = some bit) (hwrong : bit ≠ state.ledger.truth stage) :
    P.compiledMenuRule N K table menuSeed state.history =
      match (Parameters.menuEntryAt table (N - stage.val)
        (P.menuEntryTools N K state.history stage)).action with
      | .test _ .repair => P.menuRepairAction N K state.history stage
      | _ => .abandon := by
  rw [compiledMenuRule_writtenFrame P N K table fee hfee C hearly accounting rule seed truth tapes hp
    menuSeed stage bit hactive hcursor hbit]
  exact ite_eq_right (by simpa only [beq_iff_eq] using hwrong)

end PDMenu
