module

public import PaperProofs.Paid.RootPaidToolRename010

@[expose] public section

namespace RootPaidToolRename

open MeasureTheory PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open scoped ENNReal

theorem action_allocate_image {I : Instance} (e : I.Tool ≃ I.Tool) (a : Action I)
    (available : Finset I.Tool) (hsource : ∀ handle tool, a = .allocate handle tool → tool ∈ available)
    (handle : MismatchHandle I) (tool : I.Tool) (ha : action e a = .allocate handle tool) :
    tool ∈ available.image e := by
  cases a <;> simp [action] at ha
  obtain ⟨rfl, rfl⟩ := ha
  exact Finset.mem_image.mpr ⟨_, hsource _ _ rfl, rfl⟩

theorem run_policy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (e : (freshInstance n k).Tool ≃ (freshInstance n k).Tool) (available : Finset (freshInstance n k).Tool)
    (source : AvailablePolicy (P.freshInput n k fee hfee) (paidRelaxedContract _) (zeroAccounting _) available Seed)
    (sample : Seed × (P.freshInput n k fee hfee).World) (time : ℕ) :
    run (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (policy P fee hfee n k e available source).val.rule sample time =
      state e (run (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) source.val.rule sample time) := by
  induction time with
  | zero => rfl
  | succ time ih =>
    let old := run (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) source.val.rule sample time
    let new := run (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (policy P fee hfee n k e available source).val.rule sample time
    have hv : new = state e old := ih
    by_cases hhalt : old.halted = true
    · have hn : new.halted = true := by rw [hv]; exact hhalt
      rw [run_succ_of_halted _ _ _ _ _ _ time hn, run_succ_of_halted _ _ _ _ _ _ time hhalt]
      exact ih
    · have ha : old.halted = false := Bool.eq_false_iff.mpr hhalt
      obtain ⟨oldTime, _, hp⟩ := run_has_prefix (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped
        (zeroAccounting _) source.val.rule source.val.legal sample time
      obtain ⟨next, hs⟩ := source.val.legal sample.1 ((P.freshInput n k fee hfee).truthAt sample.2)
        (worldTapes (P.freshInput n k fee hfee) sample.2) oldTime old hp ha
      obtain ⟨newTime, _, hpn⟩ := run_has_prefix (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped
        (zeroAccounting _) (policy P fee hfee n k e available source).val.rule
        (policy P fee hfee n k e available source).val.legal sample time
      have hraw : rawRule e source.val.rule sample.1 new.history = action e (source.val.rule sample.1 old.history) := by
        rw [hv]
        exact rawRule_on_history e source.val.rule sample.1 old.history
      have hsnew : Step (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
          (worldTapes (P.freshInput n k fee hfee) sample.2) new
          (rawRule e source.val.rule sample.1 new.history) (state e next) := by
        rw [hraw, hv]
        exact step P fee hfee n k e _ hs
      have havailable : ∀ handle tool, rawRule e source.val.rule sample.1 new.history = .allocate handle tool →
          tool ∈ available.image e := by
        intro handle tool heq
        exact action_allocate_image e _ available
          (source.property sample.1 ((P.freshInput n k fee hfee).truthAt sample.2)
            (worldTapes (P.freshInput n k fee hfee) sample.2) oldTime old hp ha)
          handle tool (hraw.symm.trans heq)
      have hguard := PDMenu.paidGuardedRule_eq_of_step (P.freshInput n k fee hfee) (paidRelaxedContract _)
        (paidRelaxedContract_rights _) (zeroAccounting _) (policy P fee hfee n k e available source).val.rule
        (rawRule e source.val.rule) sample.1 ((P.freshInput n k fee hfee).truthAt sample.2)
        (worldTapes (P.freshInput n k fee hfee) sample.2) hpn (available.image e) hsnew havailable
      have hsactual : Step (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
          (worldTapes (P.freshInput n k fee hfee) sample.2) new
          ((policy P fee hfee n k e available source).val.rule sample.1 new.history) (state e next) := by
        change Step _ _ _ _ _ _ (PDMenu.paidGuardedRule (available.image e) (rawRule e source.val.rule) sample.1 new.history) _
        rw [hguard]
        exact hsnew
      have han : new.halted = false := by rw [hv]; exact ha
      rw [run_succ_of_step _ _ _ _ _ _ time (state e next) han hsactual,
        run_succ_of_step _ _ _ _ _ _ time next ha hs]

theorem runActualBill_policy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (e : (freshInstance n k).Tool ≃ (freshInstance n k).Tool) (available : Finset (freshInstance n k).Tool)
    (source : AvailablePolicy (P.freshInput n k fee hfee) (paidRelaxedContract _) (zeroAccounting _) available Seed)
    (sample : Seed × (P.freshInput n k fee hfee).World) :
    runActualBill (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (policy P fee hfee n k e available source).val.rule sample =
      runActualBill (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) source.val.rule sample := by
  unfold runActualBill
  apply iSup_congr
  intro time
  rw [run_policy]
  exact ledger_actualBill P fee hfee n k e _

theorem runSuccess_policy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (e : (freshInstance n k).Tool ≃ (freshInstance n k).Tool) (available : Finset (freshInstance n k).Tool)
    (source : AvailablePolicy (P.freshInput n k fee hfee) (paidRelaxedContract _) (zeroAccounting _) available Seed)
    (sample : Seed × (P.freshInput n k fee hfee).World)
    (h : runSuccess (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) source.val.rule sample) :
    runSuccess (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (policy P fee hfee n k e available source).val.rule sample := by
  obtain ⟨time, hh, hs⟩ := h
  refine ⟨time, ?_, ?_⟩
  · rw [run_policy]
    exact hh
  · rw [run_policy]
    exact ledger_success e _ hs

theorem paidObjective_policy_le (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (e : (freshInstance n k).Tool ≃ (freshInstance n k).Tool) (available : Finset (freshInstance n k).Tool)
    (source : AvailablePolicy (P.freshInput n k fee hfee) (paidRelaxedContract _) (zeroAccounting _) available Seed)
    (ν : Measure Seed) (penalty : ℝ≥0∞) :
    paidPenaltyObjective (P.freshInput n k fee hfee) (paidRelaxedContract _) (zeroAccounting _)
      (policy P fee hfee n k e available source).val.rule ν penalty ≤
      paidPenaltyObjective (P.freshInput n k fee hfee) (paidRelaxedContract _) (zeroAccounting _) source.val.rule ν penalty := by
  have hb : expectedBill (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (policy P fee hfee n k e available source).val.rule ν =
      expectedBill (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) source.val.rule ν :=
    lintegral_congr (runActualBill_policy P fee hfee n k e available source)
  have hr : risk (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (policy P fee hfee n k e available source).val.rule ν ≤
      risk (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) source.val.rule ν :=
    measure_mono (fun sample hfail hsuccess => hfail (runSuccess_policy P fee hfee n k e available source sample hsuccess))
  unfold paidPenaltyObjective
  rw [hb]
  apply add_le_add le_rfl
  simpa only [mul_comm] using mul_le_mul_right hr penalty

end RootPaidToolRename
