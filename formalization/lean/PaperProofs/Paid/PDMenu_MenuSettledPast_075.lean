module

public import PaperProofs.Paid.PDMenu_MenuAdvanceNative_074

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

def MenuPastSettled {I : Instance} (state : State I) : Prop :=
  ∀ commitment ∈ state.ledger.commitments, commitment.handle.stage.val < state.cursor →
    ∃ execution ∈ state.ledger.executions,
      execution.handle = commitment.handle ∧ execution.tool = commitment.tool

/-- No commitment is carried unexecuted across a stage advance by the
literal compiler. The conclusion includes all failed finite prefixes. -/
theorem menuPrefix_pastSettled (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance N K)) (seed : MenuSeed N K)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting
      (P.compiledMenuRule N K table) seed truth tapes clock state) : MenuPastSettled state := by
  classical
  induction hp with
  | initial =>
    intro a ha
    cases ha
  | @next clock state nextState hp hstep ih =>
    generalize haction : P.compiledMenuRule N K table seed state.history = action at hstep
    cases hstep with
    | review => exact ih
    | write stage bit live port resources =>
      simpa only [MenuPastSettled, record, reportedWriteLedger, hC.1.1, ite_true, writeLedger] using ih
    | allocate handle tool active valid compatible unused unallocated window resources =>
      intro a ha hpast
      have hamem : a ∈ state.ledger.commitments ∨ a = ⟨handle, tool, state.clock⟩ := by
        simpa only [record, allocateLedger, List.mem_append, List.mem_singleton] using ha
      rcases hamem with hold | rfl
      · exact ih a hold hpast
      · have hcursor := window hC.1.2
        change handle.stage.val < state.cursor at hpast
        omega
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      intro a ha hpast
      obtain ⟨e, he, hh, ht⟩ := ih a ha hpast
      exact ⟨e, List.mem_append_left _ he, hh, ht⟩
    | advance stage live written resources =>
      intro a ha hpast
      change a ∈ state.ledger.commitments at ha
      change a.handle.stage.val < state.cursor + 1 at hpast
      by_cases hbefore : a.handle.stage.val < state.cursor
      · exact ih a ha hbefore
      · have hs : a.handle.stage = stage := Fin.ext (by have hc := live.2; omega)
        have hwf := prefix_ledgerWellFormed (P.freshInput N K fee hfee) C .uncapped accounting
          (P.compiledMenuRule N K table) seed truth tapes hp
        rcases menuPrefix_advance_good_or_executed P N K table fee hfee C hC.1.1 accounting
          (P.compiledMenuRule N K table) seed truth tapes hp seed stage haction with hgood | hex
        · have hg := (prefix_invariant (P.freshInput N K fee hfee) C .uncapped accounting
            (P.compiledMenuRule N K table) seed truth tapes hp).commitment_genuine a ha
          rw [hs, hgood] at hg
          have hfalse : state.ledger.truth stage = !state.ledger.truth stage := Option.some.inj hg.1
          exact False.elim ((Bool.eq_not_self _).mp hfalse)
        · obtain ⟨e, he, heStage⟩ := hex
          obtain ⟨b, hb, hhandle, htool, _⟩ := hwf.backed e he
          have hstage : b.handle.stage = a.handle.stage := (congrArg MismatchHandle.stage hhandle).trans (heStage.trans hs.symm)
          have hba : b = a := List.inj_on_of_nodup_map hwf.commitment_stages hb ha hstage
          subst b
          exact ⟨e, he, hhandle.symm, htool.symm⟩
    | stop | abandon => exact ih

end PDMenu
