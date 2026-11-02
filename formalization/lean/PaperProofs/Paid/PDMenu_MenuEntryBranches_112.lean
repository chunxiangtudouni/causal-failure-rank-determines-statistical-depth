module

public import PaperProofs.Paid.PDMenu_MenuWrittenFrame_097

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {Seed : Type*}

theorem compiledMenuRule_entry_abandon (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K)) (rule : PolicyRule (freshInstance N K) Seed) (seed : Seed)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : MenuSeed N K) (stage : (freshInstance N K).Stage)
    (hactive : state.halted = false) (hcursor : state.cursor = stage.val)
    (hport : state.ledger.written stage = none)
    (ha : (Parameters.menuEntryAt table (N - stage.val) (P.menuEntryTools N K state.history stage)).action = .abandon ∨
      (Parameters.menuEntryAt table (N - stage.val) (P.menuEntryTools N K state.history stage)).action = .finish) :
    P.compiledMenuRule N K table menuSeed state.history = .abandon := by
  rw [compiledMenuRule_eq_candidate_on_prefix P N K table fee hfee C hearly accounting rule seed truth tapes hp menuSeed]
  have hh : historyHalted state.history = false :=
    (prefix_historyHalted (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes hp).trans hactive
  have hc : historyCursor state.history = stage.val :=
    (prefix_historyCursor (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes hp).trans hcursor
  have hw : historyWrite state.history stage = none := by
    rw [prefix_historyWrite (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes hp stage, hport]
    rfl
  have hlt : historyCursor state.history < N := by
    rw [hc]
    simpa [freshInstance] using stage.isLt
  have hs : (⟨historyCursor state.history, by simpa [freshInstance] using hlt⟩ : (freshInstance N K).Stage) = stage := Fin.ext hc
  simp only [Parameters.menuCandidateAction, hh, Bool.false_eq_true, ite_false, dite_eq_left hlt, hs, hw]
  rw [hc]
  rcases ha with ha | ha <;> rw [ha]

theorem compiledMenuRule_terminal_stop (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K)) (rule : PolicyRule (freshInstance N K) Seed) (seed : Seed)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : MenuSeed N K) (hactive : state.halted = false) (hcursor : state.cursor = N) :
    P.compiledMenuRule N K table menuSeed state.history = .stop := by
  rw [compiledMenuRule_eq_candidate_on_prefix P N K table fee hfee C hearly accounting rule seed truth tapes hp menuSeed]
  have hh : historyHalted state.history = false :=
    (prefix_historyHalted (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes hp).trans hactive
  have hc : historyCursor state.history = N :=
    (prefix_historyCursor (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes hp).trans hcursor
  simp only [Parameters.menuCandidateAction, hh, Bool.false_eq_true, ite_false, hc, Nat.lt_irrefl, dite_false, ite_true]

theorem compiledMenuRule_written_abandon (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K)) (rule : PolicyRule (freshInstance N K) Seed) (seed : Seed)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : MenuSeed N K) (stage : (freshInstance N K).Stage) (bit : Bool) (level : ℕ)
    (hactive : state.halted = false) (hcursor : state.cursor = stage.val)
    (hbit : state.ledger.written stage = some bit) (hwrong : bit ≠ state.ledger.truth stage)
    (hcell : (Parameters.menuEntryAt table (N - stage.val)
      (P.menuEntryTools N K state.history stage)).action = .test level .abandon) :
    P.compiledMenuRule N K table menuSeed state.history = .abandon := by
  rw [compiledMenuRule_written_wrong P N K table fee hfee C hearly accounting rule seed truth tapes hp
    menuSeed stage bit hactive hcursor hbit hwrong, hcell]

end PDMenu
