module

public import PaperProofs.Paid.RootPaidToolTransport006

@[expose] public section

namespace RootPaidToolTransport

open MeasureTheory PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

def downRawRule {Seed : Type*} (n k : ℕ) (rule : PolicyRule (freshInstance n (k + 1)) Seed) :
    PolicyRule (freshInstance n k) Seed :=
  fun seed history => downAction n k (rule seed (upHistory n k history))

theorem measurable_downRawRule {Seed : Type*} [MeasurableSpace Seed] (n k : ℕ)
    (rule : PolicyRule (freshInstance n (k + 1)) Seed) (hm : MeasurableRule rule) :
    MeasurableRule (downRawRule n k rule) := by
  apply measurable_from_prod_countable_left
  intro history
  have h : Measurable (fun seed : Seed => rule seed (upHistory n k history)) :=
    hm.comp (measurable_id.prodMk measurable_const)
  change Measurable (fun seed : Seed => downAction n k (rule seed (upHistory n k history)))
  exact (measurable_of_countable (downAction n k)).comp h

def downPolicy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (policy : AvailablePolicy (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _)
      (zeroAccounting _) (upImage k) Seed) :
    Policy (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _) Seed where
  rule := PDMenu.paidGuardedRule Finset.univ (downRawRule n k policy.val.rule)
  measurable_rule := PDMenu.measurable_paidGuardedRule _ _ (measurable_downRawRule n k _ policy.val.measurable_rule)
  legal := PDMenu.paidGuardedRule_legal _ _ rfl _ _ _

def downWorld (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    (world : (P.freshInput n (k + 1) fee hfee).World) : (P.freshInput n k fee hfee).World :=
  fun stage => world (upStage n k stage)

theorem measurePreserving_downWorld (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) :
    MeasurePreserving (downWorld P fee hfee n k)
      (P.freshInput n (k + 1) fee hfee).worldLaw (P.freshInput n k fee hfee).worldLaw :=
  measurePreserving_piCongrLeft (fun stage => (P.freshInput n k fee hfee).stageLaw stage) (stages n k).symm

def downSample (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) {Seed : Type*}
    (sample : Seed × (P.freshInput n (k + 1) fee hfee).World) : Seed × (P.freshInput n k fee hfee).World :=
  (sample.1, downWorld P fee hfee n k sample.2)

theorem measurePreserving_downSample (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (downSample P fee hfee n k (Seed := Seed))
      ((P.freshInput n (k + 1) fee hfee).seededWorldLaw ν)
      ((P.freshInput n k fee hfee).seededWorldLaw ν) :=
  (MeasurePreserving.id ν).prod (measurePreserving_downWorld P fee hfee n k)

theorem run_downPolicy (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    {Seed : Type*} [MeasurableSpace Seed]
    (policy : AvailablePolicy (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _)
      (zeroAccounting _) (upImage k) Seed)
    (sample : Seed × (P.freshInput n (k + 1) fee hfee).World) (time : ℕ) :
    run (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      policy.val.rule sample time =
      upState n k (run (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
        (downPolicy P fee hfee n k policy).rule (downSample P fee hfee n k sample) time) := by
  induction time with
  | zero => rfl
  | succ time ih =>
    let big := run (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      policy.val.rule sample time
    let small := run (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
      (downPolicy P fee hfee n k policy).rule (downSample P fee hfee n k sample) time
    have hv : big = upState n k small := ih
    by_cases hhalt : big.halted = true
    · have hh : small.halted = true := (congrArg (fun s => s.halted) hv).symm.trans hhalt
      rw [run_succ_of_halted _ _ _ _ _ _ time hhalt, run_succ_of_halted _ _ _ _ _ _ time hh]
      exact ih
    · have ha : big.halted = false := Bool.eq_false_iff.mpr hhalt
      obtain ⟨bigTime, _, hp⟩ := run_has_prefix (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped
        (zeroAccounting _) policy.val.rule policy.val.legal sample time
      obtain ⟨next, hs⟩ := policy.val.legal sample.1 ((P.freshInput n (k + 1) fee hfee).truthAt sample.2)
        (worldTapes (P.freshInput n (k + 1) fee hfee) sample.2) bigTime big hp ha
      have halloc : ∀ handle tool, policy.val.rule sample.1 big.history = .allocate handle tool → tool ∈ upImage k :=
        policy.property sample.1 ((P.freshInput n (k + 1) fee hfee).truthAt sample.2)
          (worldTapes (P.freshInput n (k + 1) fee hfee) sample.2) bigTime big hp ha
      have hsmap : Step (P.freshInput n (k + 1) fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
          (upTapes P fee hfee n k (worldTapes (P.freshInput n k fee hfee) (downWorld P fee hfee n k sample.2)))
          (upState n k small) (policy.val.rule sample.1 big.history) next := hv ▸ hs
      obtain ⟨action, smallNext, haction, hsmall, hnext⟩ := reflectStep P fee hfee n k _ hsmap halloc
      have hraw : downRawRule n k policy.val.rule sample.1 small.history = action := by
        change downAction n k (policy.val.rule sample.1 (upHistory n k small.history)) = action
        have hh : upHistory n k small.history = big.history := (congrArg (fun s => s.history) hv).symm
        rw [hh, ← haction, down_up_action]
      obtain ⟨smallTime, _, hps⟩ := run_has_prefix (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped
        (zeroAccounting _) (downPolicy P fee hfee n k policy).rule (downPolicy P fee hfee n k policy).legal
        (downSample P fee hfee n k sample) time
      have hstepRaw : Step (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
          (worldTapes (P.freshInput n k fee hfee) (downWorld P fee hfee n k sample.2))
          small (downRawRule n k policy.val.rule sample.1 small.history) smallNext := hraw.symm ▸ hsmall
      have hguard := PDMenu.paidGuardedRule_eq_of_step (P.freshInput n k fee hfee) (paidRelaxedContract _)
        (paidRelaxedContract_rights _) (zeroAccounting _) (downPolicy P fee hfee n k policy).rule
        (downRawRule n k policy.val.rule) sample.1 ((P.freshInput n k fee hfee).truthAt (downWorld P fee hfee n k sample.2))
        (worldTapes (P.freshInput n k fee hfee) (downWorld P fee hfee n k sample.2)) hps Finset.univ hstepRaw
        (by intro _ tool _; exact Finset.mem_univ tool)
      have hactual : Step (P.freshInput n k fee hfee) (paidRelaxedContract _) .uncapped (zeroAccounting _)
          (worldTapes (P.freshInput n k fee hfee) (downWorld P fee hfee n k sample.2))
          small ((downPolicy P fee hfee n k policy).rule sample.1 small.history) smallNext := by
        change Step _ _ _ _ _ _ (PDMenu.paidGuardedRule Finset.univ (downRawRule n k policy.val.rule) sample.1 small.history) _
        rw [hguard]
        exact hstepRaw
      have hasmall : small.halted = false := (congrArg (fun s => s.halted) hv).symm.trans ha
      rw [run_succ_of_step _ _ _ _ _ _ time next ha hs,
        run_succ_of_step _ _ _ _ _ _ time smallNext hasmall hactual]
      exact hnext.symm

end RootPaidToolTransport
