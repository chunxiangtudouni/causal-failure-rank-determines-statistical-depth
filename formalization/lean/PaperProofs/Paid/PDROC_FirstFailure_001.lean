module

public import PaperProofs.Paid.RepresentationClaims

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {Seed : Type u}

/-- A visible history detector; no hidden world is supplied to the rule. -/
def detectedStopRule (detect : List (VisibleEvent I) → Bool)
    (source : PolicyRule I Seed) : PolicyRule I Seed :=
  fun seed history => if detect history then .abandon else source seed history

theorem detectedStopRule_measurable [MeasurableSpace Seed]
    (detect : List (VisibleEvent I) → Bool) (source : PolicyRule I Seed)
    (hm : MeasurableRule source) : MeasurableRule (detectedStopRule detect source) := by
  have hd : Measurable (fun p : Seed × List (VisibleEvent I) => detect p.2) :=
    (measurable_of_countable detect).comp measurable_snd
  exact Measurable.ite (hd (measurableSet_singleton true)) measurable_const hm

theorem detectedStop_prefix_active (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (detect : List (VisibleEvent I) → Bool) (source : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting (detectedStopRule detect source) seed truth tapes n s)
    (ha : s.halted = false) : Prefix input C mode accounting source seed truth tapes n s := by
  induction hp with
  | initial => exact .initial
  | @next n before after hp step ih =>
    have hb := step_source_active input C mode accounting tapes step
    have hold := ih hb
    by_cases hd : detect before.history = true
    · have hs : Step input C mode accounting tapes before .abandon after := by
        simpa only [detectedStopRule, hd, ↓reduceIte] using step
      have heq := step_deterministic input C mode accounting tapes hs (Step.abandon before hb)
      subst after
      simp only [stopState] at ha
      contradiction
    · have hstep : Step input C mode accounting tapes before (source seed before.history) after := by
        simpa only [detectedStopRule, hd, Bool.false_eq_true, ↓reduceIte] using step
      exact .next hold hstep

theorem detectedStopRule_legal (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (detect : List (VisibleEvent I) → Bool) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) :
    LegalRule input C mode accounting (detectedStopRule detect source) := by
  intro seed truth tapes n s hp ha
  by_cases hd : detect s.history = true
  · exact ⟨stopState s true, by simpa only [detectedStopRule, hd, ↓reduceIte] using Step.abandon s ha⟩
  · obtain ⟨next, hs⟩ := hlegal seed truth tapes n s
      (detectedStop_prefix_active input C mode accounting detect source seed truth tapes hp ha) ha
    exact ⟨next, by simpa only [detectedStopRule, hd, Bool.false_eq_true, ↓reduceIte] using hs⟩

def detectedStopPolicy [MeasurableSpace Seed] (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (detect : List (VisibleEvent I) → Bool) (source : Policy input C mode accounting Seed) :
    Policy input C mode accounting Seed where
  rule := detectedStopRule detect source.rule
  measurable_rule := detectedStopRule_measurable detect source.rule source.measurable_rule
  legal := detectedStopRule_legal input C mode accounting detect source.rule source.legal

theorem detectedStop_run_eq_before (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (detect : List (VisibleEvent I) → Bool) (source : PolicyRule I Seed)
    (sample : Seed × input.World) (n : ℕ)
    (hbefore : ∀ k < n, detect (run input C mode accounting source sample k).history = false) :
    run input C mode accounting (detectedStopRule detect source) sample n =
      run input C mode accounting source sample n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq := ih (fun k hk => hbefore k (Nat.lt_succ_of_lt hk))
    simp only [run, heq, detectedStopRule, hbefore n (Nat.lt_succ_self n), Bool.false_eq_true,
      ↓reduceIte]

theorem failureStop_halted (s : State I) : (failureStop s).halted = true := by
  unfold failureStop
  split_ifs with h
  · exact h
  · rfl

theorem failureStop_actualBill (s : State I) (fees : Fees I) :
    (failureStop s).ledger.actualBill fees = s.ledger.actualBill fees := by
  unfold failureStop
  split_ifs <;> rfl

theorem failureStop_observationBill (s : State I) (fees : Fees I) :
    (failureStop s).ledger.observationBill fees = s.ledger.observationBill fees := by
  unfold failureStop
  split_ifs <;> rfl

theorem detectedStop_run_after_first (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (detect : List (VisibleEvent I) → Bool) (source : PolicyRule I Seed)
    (sample : Seed × input.World) (n : ℕ)
    (hbefore : ∀ k < n, detect (run input C mode accounting source sample k).history = false)
    (hd : detect (run input C mode accounting source sample n).history = true) (extra : ℕ) :
    run input C mode accounting (detectedStopRule detect source) sample (n + 1 + extra) =
      failureStop (run input C mode accounting source sample n) := by
  have heq := detectedStop_run_eq_before input C mode accounting detect source sample n hbefore
  have hnext : run input C mode accounting (detectedStopRule detect source) sample (n + 1) =
      failureStop (run input C mode accounting source sample n) := by
    by_cases hh : (run input C mode accounting source sample n).halted = true
    · rw [run_succ_of_halted input C mode accounting (detectedStopRule detect source) sample n (heq ▸ hh),
        heq]
      simp only [failureStop, hh, ↓reduceIte]
    · have ha := Bool.eq_false_iff.mpr hh
      rw [run_succ_of_step input C mode accounting (detectedStopRule detect source) sample n
        (stopState (run input C mode accounting source sample n) true) (heq ▸ ha)]
      · simp only [failureStop, ha, Bool.false_eq_true, ↓reduceIte]
      · rw [heq]
        simpa only [detectedStopRule, hd, ↓reduceIte] using
          Step.abandon (run input C mode accounting source sample n) ha
  rw [run_after_halt input C mode accounting (detectedStopRule detect source) sample (n + 1)
      (hnext ▸ failureStop_halted _) extra, hnext]

/-- Every stopped prefix is either the unchanged old prefix or a genuine
old prefix with only its completion flags changed by abandon. -/
theorem detectedStop_run_cases (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (detect : List (VisibleEvent I) → Bool) (source : PolicyRule I Seed)
    (sample : Seed × input.World) (n : ℕ) :
    run input C mode accounting (detectedStopRule detect source) sample n =
        run input C mode accounting source sample n ∨
      ∃ k < n, run input C mode accounting (detectedStopRule detect source) sample n =
        failureStop (run input C mode accounting source sample k) := by
  classical
  by_cases he : ∃ k < n, detect (run input C mode accounting source sample k).history = true
  · right
    let k := Nat.find he
    have hk : k < n ∧ detect (run input C mode accounting source sample k).history = true := Nat.find_spec he
    have hbefore : ∀ j < k, detect (run input C mode accounting source sample j).history = false := by
      intro j hj
      apply Bool.eq_false_iff.mpr
      intro hd
      exact Nat.find_min he hj ⟨lt_trans hj hk.1, hd⟩
    refine ⟨k, hk.1, ?_⟩
    obtain ⟨extra, hx⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hk.1)
    rw [hx]
    exact detectedStop_run_after_first input C mode accounting detect source sample k hbefore hk.2 extra
  · left
    apply detectedStop_run_eq_before
    intro k hk
    exact Bool.eq_false_iff.mpr (fun hd => he ⟨k, hk, hd⟩)

theorem detectedStop_runActualBill_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (detect : List (VisibleEvent I) → Bool) (source : PolicyRule I Seed)
    (sample : Seed × input.World) :
    runActualBill input C mode accounting (detectedStopRule detect source) sample ≤
      runActualBill input C mode accounting source sample := by
  apply iSup_le
  intro n
  rcases detectedStop_run_cases input C mode accounting detect source sample n with hn | ⟨k, _, hk⟩
  · rw [hn]
    exact prefixBill_le_runActualBill input C mode accounting source sample n
  · rw [hk, failureStop_actualBill]
    exact prefixBill_le_runActualBill input C mode accounting source sample k

theorem detectedStop_runObservationBill_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (detect : List (VisibleEvent I) → Bool) (source : PolicyRule I Seed)
    (sample : Seed × input.World) :
    runObservationBill input C mode accounting (detectedStopRule detect source) sample ≤
      runObservationBill input C mode accounting source sample := by
  apply iSup_le
  intro n
  rcases detectedStop_run_cases input C mode accounting detect source sample n with hn | ⟨k, _, hk⟩
  · rw [hn]
    exact le_iSup (fun k => (run input C mode accounting source sample k).ledger.observationBill input.fees) n
  · rw [hk, failureStop_observationBill]
    exact le_iSup (fun k => (run input C mode accounting source sample k).ledger.observationBill input.fees) k




theorem run_reachable (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting source)
    (sample : Seed × input.World) (n extra : ℕ) :
    Relation.ReflTransGen (fun before after => ∃ action,
      Step input C .uncapped accounting (worldTapes input sample.2) before action after)
      (run input C .uncapped accounting source sample n)
      (run input C .uncapped accounting source sample (n + extra)) := by
  induction extra with
  | zero => exact .refl
  | succ extra ih =>
    have hx : n + (extra + 1) = (n + extra) + 1 := by omega
    rw [hx]
    by_cases hh : (run input C .uncapped accounting source sample (n + extra)).halted = true
    · rw [run_succ_of_halted input C .uncapped accounting source sample (n + extra) hh]
      exact ih
    · have ha := Bool.eq_false_iff.mpr hh
      obtain ⟨k, _, hp⟩ := run_has_prefix input C .uncapped accounting source hlegal sample (n + extra)
      obtain ⟨next, hs⟩ := hlegal sample.1 (input.truthAt sample.2) (worldTapes input sample.2) k _ hp ha
      rw [run_succ_of_step input C .uncapped accounting source sample (n + extra) next ha hs]
      exact ih.tail ⟨_, hs⟩

theorem detectedStop_runSuccess_imp (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (detect : List (VisibleEvent I) → Bool) (source : PolicyRule I Seed)
    (sample : Seed × input.World) :
    runSuccess input C mode accounting (detectedStopRule detect source) sample →
      runSuccess input C mode accounting source sample := by
  rintro ⟨n, hn, hs⟩
  rcases detectedStop_run_cases input C mode accounting detect source sample n with heq | ⟨k, _, heq⟩
  · exact ⟨n, heq ▸ hn, heq ▸ hs⟩
  · rw [heq] at hn hs
    by_cases hh : (run input C mode accounting source sample k).halted = true
    · refine ⟨k, hh, ?_⟩
      simpa only [failureStop, hh, ↓reduceIte] using hs
    · have ha := Bool.eq_false_iff.mpr hh
      simp only [failureStop, ha, Bool.false_eq_true, ↓reduceIte, stopState, Ledger.success] at hs
      exact Bool.noConfusion hs.2.1

theorem detectedStop_runSuccess_iff_of_sound (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (detect : List (VisibleEvent I) → Bool)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C .uncapped accounting source)
    (hsound : ∀ (sample : Seed × input.World) (n : ℕ),
      detect (run input C .uncapped accounting source sample n).history = true →
        PermanentlyFailed input C accounting sample.2 (run input C .uncapped accounting source sample n))
    (sample : Seed × input.World) :
    runSuccess input C .uncapped accounting (detectedStopRule detect source) sample ↔
      runSuccess input C .uncapped accounting source sample := by
  refine ⟨detectedStop_runSuccess_imp input C .uncapped accounting detect source sample, ?_⟩
  rintro ⟨n, hn, hs⟩
  have hbefore : ∀ k < n, detect (run input C .uncapped accounting source sample k).history = false := by
    intro k hk
    apply Bool.eq_false_iff.mpr
    intro hd
    have hp := hsound sample k hd
    apply hp
    refine ⟨run input C .uncapped accounting source sample n, ?_, hn, hs⟩
    obtain ⟨extra, hx⟩ := Nat.exists_eq_add_of_le hk.le
    rw [hx]
    exact run_reachable input C accounting source hlegal sample k extra
  have heq := detectedStop_run_eq_before input C .uncapped accounting detect source sample n hbefore
  exact ⟨n, heq.symm ▸ hn, heq.symm ▸ hs⟩

theorem detectedStop_expectedBill_le [MeasurableSpace Seed] (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (detect : List (VisibleEvent I) → Bool) (source : PolicyRule I Seed) (ν : Measure Seed) :
    expectedBill input C mode accounting (detectedStopRule detect source) ν ≤
      expectedBill input C mode accounting source ν :=
  lintegral_mono (detectedStop_runActualBill_le input C mode accounting detect source)

theorem detectedStop_expectedObservationBill_le [MeasurableSpace Seed] (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (detect : List (VisibleEvent I) → Bool) (source : PolicyRule I Seed) (ν : Measure Seed) :
    expectedObservationBill input C mode accounting (detectedStopRule detect source) ν ≤
      expectedObservationBill input C mode accounting source ν :=
  lintegral_mono (detectedStop_runObservationBill_le input C mode accounting detect source)

/-- Generic genuine truncation, conditional on the still separate visible
permanence detector theorem. This is not a proof of D06's detector existence. -/
theorem firstFailureDomination_of_detector [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (detect : List (VisibleEvent I) → Bool) (source : Policy input C .uncapped accounting Seed)
    (hdetect : ∀ (sample : Seed × input.World) (n : ℕ),
      detect (run input C .uncapped accounting source.rule sample n).history = true ↔
        PermanentlyFailed input C accounting sample.2 (run input C .uncapped accounting source.rule sample n)) :
    FirstFailureDomination input C .uncapped accounting source
      (detectedStopPolicy input C .uncapped accounting detect source) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact detectedStop_runSuccess_iff_of_sound input C accounting detect source.rule source.legal
      (fun sample n h => (hdetect sample n).mp h)
  · intro sample n hbefore
    apply detectedStop_run_eq_before
    intro k hk
    exact Bool.eq_false_iff.mpr (fun h => hbefore k hk ((hdetect sample k).mp h))
  · intro sample n hn hbefore extra
    apply detectedStop_run_after_first input C .uncapped accounting detect source.rule sample n
    · intro k hk
      exact Bool.eq_false_iff.mpr (fun h => hbefore k hk ((hdetect sample k).mp h))
    · exact (hdetect sample n).mpr hn
  · intro sample
    exact ⟨detectedStop_runObservationBill_le input C .uncapped accounting detect source.rule sample,
      detectedStop_runActualBill_le input C .uncapped accounting detect source.rule sample⟩



/-- Cap relaxation of the original policy, with the same rule and randomness. -/
def uncappedSourcePolicy [MeasurableSpace Seed] (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : Policy input C mode accounting Seed) : Policy input C .uncapped accounting Seed where
  rule := source.rule
  measurable_rule := source.measurable_rule
  legal := by
    cases mode with
    | native => exact legalRule_uncapped_of_native input C accounting source.rule source.legal
    | uncapped => exact source.legal

theorem uncappedSourcePolicy_run [MeasurableSpace Seed] (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : Policy input C mode accounting Seed) (sample : Seed × input.World) (n : ℕ) :
    run input C .uncapped accounting (uncappedSourcePolicy input C mode accounting source).rule sample n =
      run input C mode accounting source.rule sample n := by
  cases mode with
  | native => exact run_uncapped_eq_native input C accounting source.rule source.legal sample n
  | uncapped => rfl

/-- Full original mode/seed coverage of the generic truncation interface.
The visible detector equivalence is the exact outstanding mathematical
obligation, not an added assumption on any original source policy. -/
theorem firstFailureDomination_of_detector_any_mode [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (detect : List (VisibleEvent I) → Bool)
    (source : Policy input C mode accounting Seed)
    (hdetect : ∀ (sample : Seed × input.World) (n : ℕ),
      detect (run input C mode accounting source.rule sample n).history = true ↔
        PermanentlyFailed input C accounting sample.2 (run input C mode accounting source.rule sample n)) :
    FirstFailureDomination input C mode accounting source
      (detectedStopPolicy input C .uncapped accounting detect
        (uncappedSourcePolicy input C mode accounting source)) := by
  have hg := firstFailureDomination_of_detector input C accounting detect
    (uncappedSourcePolicy input C mode accounting source)
    (fun sample n => by simpa only [uncappedSourcePolicy_run] using hdetect sample n)
  simpa only [FirstFailureDomination, runSuccess, runObservationBill, runActualBill,
    uncappedSourcePolicy_run] using hg

end PDROC
