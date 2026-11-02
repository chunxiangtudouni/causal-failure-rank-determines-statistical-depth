module

public import PaperProofs.Paid.RootPaidToolTransport003

@[expose] public section

namespace RootPaidToolTransport

open MeasureTheory PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open scoped ENNReal

def upWorld (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    (world : (P.freshInput n k fee hfee).World) : (P.freshInput n (k + 1) fee hfee).World :=
  fun stage => world (downStage n k stage)

theorem measurePreserving_upWorld (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) :
    MeasurePreserving (upWorld P fee hfee n k)
      (P.freshInput n k fee hfee).worldLaw (P.freshInput n (k + 1) fee hfee).worldLaw :=
  measurePreserving_piCongrLeft (fun stage => (P.freshInput n (k + 1) fee hfee).stageLaw stage) (stages n k)

def upSample (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) {Seed : Type*}
    (sample : Seed × (P.freshInput n k fee hfee).World) :
    Seed × (P.freshInput n (k + 1) fee hfee).World :=
  (sample.1, upWorld P fee hfee n k sample.2)

theorem measurePreserving_upSample (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (upSample P fee hfee n k (Seed := Seed))
      ((P.freshInput n k fee hfee).seededWorldLaw ν)
      ((P.freshInput n (k + 1) fee hfee).seededWorldLaw ν) :=
  (MeasurePreserving.id ν).prod (measurePreserving_upWorld P fee hfee n k)

theorem run_upPolicy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) Seed)
    (sample : Seed × (P.freshInput n k fee hfee).World) (time : ℕ) :
    run (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (upPolicy P fee hfee n k policy).val.rule (upSample P fee hfee n k sample) time =
      upState n k (run (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped
        (zeroAccounting _) policy.rule sample time) := by
  induction time with
  | zero => rfl
  | succ time ih =>
    let old := run (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) policy.rule sample time
    let new := run (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (upPolicy P fee hfee n k policy).val.rule (upSample P fee hfee n k sample) time
    have hv : new = upState n k old := ih
    by_cases hhalt : old.halted = true
    · have hn : new.halted = true := by rw [hv]; exact hhalt
      rw [run_succ_of_halted _ _ _ _ _ _ time hn, run_succ_of_halted _ _ _ _ _ _ time hhalt]
      exact ih
    · have ha : old.halted = false := Bool.eq_false_iff.mpr hhalt
      obtain ⟨oldTime, _, hp⟩ := run_has_prefix (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped
        (zeroAccounting _) policy.rule policy.legal sample time
      obtain ⟨next, hs⟩ := policy.legal sample.1 ((P.freshInput n k fee hfee).truthAt sample.2)
        (worldTapes (P.freshInput n k fee hfee) sample.2) oldTime old hp ha
      obtain ⟨newTime, _, hpn⟩ := run_has_prefix (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped
        (zeroAccounting _) (upPolicy P fee hfee n k policy).val.rule
        (upPolicy P fee hfee n k policy).val.legal (upSample P fee hfee n k sample) time
      have hraw : upRule n k policy.rule sample.1 new.history = upAction n k (policy.rule sample.1 old.history) := by
        rw [hv]
        exact upRule_on_history n k policy.rule sample.1 old.history
      have hsnew : Step (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
          (worldTapes (P.freshInput n (k + 1) fee hfee) (upWorld P fee hfee n k sample.2))
          new (upRule n k policy.rule sample.1 new.history) (upState n k next) := by
        rw [hraw, hv]
        exact upStep P fee hfee n k _ hs
      have hguard := PDMenu.paidGuardedRule_eq_of_step (P.freshInput n (k + 1) fee hfee)
        (paidRelaxedContract _) (paidRelaxedContract_rights _) (zeroAccounting _)
        (upPolicy P fee hfee n k policy).val.rule (upRule n k policy.rule) sample.1
        ((P.freshInput n (k + 1) fee hfee).truthAt (upWorld P fee hfee n k sample.2))
        (worldTapes (P.freshInput n (k + 1) fee hfee) (upWorld P fee hfee n k sample.2))
        hpn (upImage k) hsnew (upRule_allocate_image n k policy.rule sample.1 new.history)
      have hsactual : Step (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
          (worldTapes (P.freshInput n (k + 1) fee hfee) (upWorld P fee hfee n k sample.2))
          new ((upPolicy P fee hfee n k policy).val.rule sample.1 new.history) (upState n k next) := by
        change Step _ _ _ _ _ _ (PDMenu.paidGuardedRule (upImage k) (upRule n k policy.rule) sample.1 new.history) _
        rw [hguard]
        exact hsnew
      have han : new.halted = false := by rw [hv]; exact ha
      rw [run_succ_of_step _ _ _ _ _ _ time (upState n k next) han hsactual,
          run_succ_of_step _ _ _ _ _ _ time next ha hs]

theorem runActualBill_upPolicy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) Seed)
    (sample : Seed × (P.freshInput n k fee hfee).World) :
    runActualBill (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (upPolicy P fee hfee n k policy).val.rule (upSample P fee hfee n k sample) =
      runActualBill (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) policy.rule sample := by
  unfold runActualBill
  apply iSup_congr
  intro time
  rw [run_upPolicy]
  exact upLedger_actualBill P fee hfee n k _

theorem runSuccess_upPolicy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (policy : Policy (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) Seed)
    (sample : Seed × (P.freshInput n k fee hfee).World)
    (h : runSuccess (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) policy.rule sample) :
    runSuccess (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (upPolicy P fee hfee n k policy).val.rule (upSample P fee hfee n k sample) := by
  obtain ⟨time, hh, hs⟩ := h
  refine ⟨time, ?_, ?_⟩
  · rw [run_upPolicy]
    exact hh
  · rw [run_upPolicy]
    exact upLedger_success n k _ hs

end RootPaidToolTransport
