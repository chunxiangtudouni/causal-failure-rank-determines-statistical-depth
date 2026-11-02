module

public import PaperProofs.Paid.PDMenu_MenuAdvanceNative_074
public import PaperProofs.Common.NativeDeadlines
public import PaperProofs.Common.HistorySuffixSuccess

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- Every actually passed stage is physically correct, on all prefixes,
including failure and abandonment paths. Genuine execution deadlines are
then supplied by the original protocol's already-proved deadline invariant. -/
theorem menuPrefix_pastCorrect (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K)) (seed : MenuSeed N K)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) seed truth tapes clock state) :
    ∀ stage : (freshInstance N K).Stage, stage.val < state.cursor →
      state.ledger.written stage = some (state.ledger.truth stage) ∨
        ∃ execution ∈ state.ledger.executions, execution.handle.stage = stage := by
  induction hp with
  | initial => intro stage hs; exact (Nat.not_lt_zero _ hs).elim
  | @next clock state nextState hp step ih =>
    generalize haction : P.compiledMenuRule N K table seed state.history = action at step
    cases step with
    | review => exact ih
    | write current bit live port resources =>
      intro stage hs
      have hne : stage ≠ current := by
        intro heq
        subst stage
        change current.val < state.cursor at hs
        have hc := live.2
        omega
      simpa only [record, reportedWriteLedger, hearly, ite_true, writeLedger, Function.update_of_ne hne]
        using ih stage hs
    | allocate => exact ih
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      intro stage hs
      rcases ih stage hs with hgood | ⟨execution, he, heStage⟩
      · exact Or.inl hgood
      · exact Or.inr ⟨execution, List.mem_append_left _ he, heStage⟩
    | advance current live written resources =>
      intro stage hs
      by_cases hold : stage.val < state.cursor
      · exact ih stage hold
      · have heq : stage = current := by
          apply Fin.ext
          change stage.val < state.cursor + 1 at hs
          have hc := live.2
          omega
        subst stage
        exact menuPrefix_advance_good_or_executed P N K table fee hfee C hearly accounting
          (P.compiledMenuRule N K table) seed truth tapes hp seed current haction
    | stop | abandon => exact ih

theorem menuPrefix_terminal_allWritten (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K)) (seed : MenuSeed N K)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) seed truth tapes clock state)
    (hcursor : state.cursor = N) : allWritten state.ledger := by
  have hgood := menuPrefix_pastCorrect P N K table fee hfee C hearly accounting seed truth tapes hp
  have hwf := prefix_ledgerWellFormed (P.freshInput N K fee hfee) C .uncapped accounting
    (P.compiledMenuRule N K table) seed truth tapes hp
  intro stage
  have hs : stage.val < state.cursor := by
    rw [hcursor]
    simpa [freshInstance] using stage.isLt
  rcases hgood stage hs with hc | ⟨execution, he, hs⟩
  · rw [hc]
    exact Option.some_ne_none _
  · have hw := (hwf.genuine execution he).1
    rw [hs] at hw
    rw [hw]
    exact Option.some_ne_none _

theorem menuPrefix_terminal_success (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K)) (seed : MenuSeed N K)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) seed truth tapes clock state)
    (hcursor : state.cursor = N) (hhalt : state.halted = true) (habandoned : state.ledger.abandoned = false) :
    state.ledger.success C := by
  have hall := menuPrefix_terminal_allWritten P N K table fee hfee C hearly accounting seed truth tapes hp hcursor
  have hf := prefix_halted_allWritten_finished (P.freshInput N K fee hfee) C .uncapped accounting
    (P.compiledMenuRule N K table) seed truth tapes hp hhalt hall
  apply (prefix_success_iff_physical (P.freshInput N K fee hfee) C .uncapped accounting
    (P.compiledMenuRule N K table) seed truth tapes hp).mpr
  refine ⟨hf, habandoned, ?_⟩
  intro stage
  apply (finalOutput_correct_iff state.ledger stage).mpr
  apply menuPrefix_pastCorrect P N K table fee hfee C hearly accounting seed truth tapes hp stage
  rw [hcursor]
  simpa [freshInstance] using stage.isLt

end PDMenu
