module

public import PaperProofs.Retained.PRet_FreshContinuationPolicy_096
public import PaperProofs.Retained.PRet_FreshHeadRun_080

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshHeadAdvance097

open Common Common.Native PRetFreshContinuationPolicy096 PRetFreshHeadRun080

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- Both true head outcomes advance into the actual fresh continuation;
the old-H relaxed comparison does not make a premature current payment. -/
theorem run_advance_at (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad) (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n) :
    run input (freshContract I) .uncapped (zeroNormalAccounting I)
      (twoContinuationPolicy input head test good bad hgood hbad).rule sample (n + 2) =
      let written := bellmanHeadWrittenState input (freshContract I) (zeroNormalAccounting I) head (input.truthAt sample.2)
        (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
      record (zeroNormalAccounting I) written (.advance head) [.advanced head] (advanceLedger written head) 1 false := by
  let after := postHeadRaw head good bad
  let policy := twoContinuationPolicy input head test good bad hgood hbad
  let written := bellmanHeadWrittenState input (freshContract I) (zeroNormalAccounting I) head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hr : run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 1) = written :=
    run_write_at input head hhead test after sample n hstop
  obtain ⟨_, _, hp⟩ := run_has_prefix input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule policy.legal sample (n + 1)
  rw [hr] at hp
  have hc : written.cursor = 0 := bellmanHeadWrittenState_cursor input (freshContract I) (zeroNormalAccounting I) head _ _ n _
  have hw : written.ledger.written head = some (test.rule.decision sample.1 (worldTapes input sample.2 head)) :=
    bellmanHeadWrittenState_written input (freshContract I) rfl (zeroNormalAccounting I) head _ _ n _
  have hvisible := prefix_historyWritten input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample.1 _ _ hp head
  have hcursor := prefix_historyCursor input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample.1 _ _ hp
  have hraw : bellmanHeadThenRaw input head test after sample.1 written.history = .advance head := by
    simp only [bellmanHeadThenRaw, hvisible, hw, reduceCtorEq, ↓reduceIte]
    change postHeadRaw head good bad sample.1 written.history = .advance head
    simp only [postHeadRaw, hcursor, hc, ite_true]
  have hs : Step input (freshContract I) .uncapped (zeroNormalAccounting I) (worldTapes input sample.2) written (.advance head)
      (record (zeroNormalAccounting I) written (.advance head) [.advanced head] (advanceLedger written head) 1 false) := by
    have h := Step.advance (input := input) (C := freshContract I) (mode := .uncapped) (accounting := zeroNormalAccounting I)
      (tapes := worldTapes input sample.2) written head ⟨rfl, hc.trans hhead.symm⟩ (by rw [hw]; exact Option.some_ne_none _) (.inl rfl)
    simpa only [hc] using h
  have hguard := PRetRetainedGuard007.guarded_action_of_step input (freshContract I) rfl (zeroNormalAccounting I)
    (bellmanHeadThenRaw input head test after) sample.1 _ _ hp (by rw [hraw]; exact hs)
  change policy.rule sample.1 written.history = bellmanHeadThenRaw input head test after sample.1 written.history at hguard
  change run input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 1 + 1) = _
  apply run_succ_of_step input (freshContract I) .uncapped (zeroNormalAccounting I) policy.rule sample (n + 1) _
  · rw [hr]
    rfl
  · rw [hr, hguard, hraw]
    exact hs

end PaperProofs.Retained.PRetFreshHeadAdvance097
