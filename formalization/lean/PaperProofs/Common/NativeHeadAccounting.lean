module

public import PaperProofs.Common.NativeHeadContinuation
import Lean.Elab.Tactic.Omega

/-! Exact head/continuation accounting and the genuine no-next-entry
failure branch needed to assemble the arbitrary-policy B08 lower bound. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics

variable {I : Instance} {Seed : Type*}

theorem observationBill_eq_prefix_add_increment (input : StatisticalInput I) (before after : State I)
    (hcounts : ∀ stage, before.ledger.reviews stage ≤ after.ledger.reviews stage) :
    after.ledger.observationBill input.fees = before.ledger.observationBill input.fees + observationIncrement input before after := by
  classical
  unfold Ledger.observationBill observationIncrement
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro stage _
  rw [← mul_add, ← ENat.toENNReal_add, add_tsub_cancel_of_le (hcounts stage)]

/-- Exact native observation accounting. No subtraction of infinite bills,
finite-expected-cost assumption or successful-path restriction is used. -/
theorem runObservationBill_eq_prefix_add_future (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World) (n : ℕ) :
    runObservationBill input C mode accounting rule sample =
      (run input C mode accounting rule sample n).ledger.observationBill input.fees +
        futureObservationBill input C mode accounting rule n sample := by
  have hmono : Monotone (fun k => (run input C mode accounting rule sample k).ledger.observationBill input.fees) := by
    intro a b hab
    apply Finset.sum_le_sum
    intro stage _
    exact mul_le_mul_right (ENat.toENNReal_mono (run_reviews_mono input C mode accounting rule hlegal sample stage hab)) _
  unfold runObservationBill
  rw [← hmono.iSup_nat_add n]
  unfold futureObservationBill
  rw [ENNReal.add_iSup]
  apply iSup_congr
  intro k
  rw [Nat.add_comm k n]
  exact observationBill_eq_prefix_add_increment input _ _
    (fun stage => run_reviews_mono input C mode accounting rule hlegal sample stage (Nat.le_add_right n k))

theorem run_cursor_zero_of_no_stage_one (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (hnever : ∀ n, (run input C mode accounting rule sample n).cursor ≠ 1) :
    ∀ n, (run input C mode accounting rule sample n).cursor = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    have hb := (run_cursor_step_bounds input C mode accounting rule hlegal sample n).2
    have hn := hnever (n + 1)
    omega

/-- A real second stage cannot be skipped by the native cursor. Hence a run
which never enters it fails the original complete task, even if it continues
spending or does not terminate. -/
theorem no_stage_one_entry_failure (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (second : I.Stage) (hsecond : second.val = 1)
    (hnever : ∀ n, (run input C mode accounting rule sample n).cursor ≠ 1) :
    ¬runSuccess input C mode accounting rule sample := by
  rintro ⟨n, _, hs⟩
  have hc := run_cursor_zero_of_no_stage_one input C mode accounting rule hlegal sample hnever n
  have hinv := run_cursorInvariant input C mode accounting rule hlegal sample n
  have hw : (run input C mode accounting rule sample n).ledger.written second = none :=
    hinv.future_written second (by rw [hc, hsecond]; exact Nat.zero_lt_one)
  rcases hs.2.2.2 second with hright | ⟨e, he, hes⟩
  · rw [hw] at hright
    cases hright
  · have hg := ((run_ledgerWellFormed input C mode accounting rule hlegal sample n).genuine e he).1
    rw [hes, hw] at hg
    cases hg

private theorem reportedWrite_reviews_same (C : Contract I) (s : State I) (stage : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s stage bit).reviews = s.ledger.reviews := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

/-- A real ordinary write closes its review port permanently. -/
theorem run_reviews_written_port (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (start extra : ℕ) (head : I.Stage) (bit : Bool)
    (hw : (run input C mode accounting rule sample start).ledger.written head = some bit) :
    (run input C mode accounting rule sample (start + extra)).ledger.reviews head =
      (run input C mode accounting rule sample start).ledger.reviews head := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
    by_cases hh : (run input C mode accounting rule sample (start + extra)).halted = true
    · rw [Nat.add_succ, run_succ_of_halted input C mode accounting rule sample (start + extra) hh]
      exact ih
    · have ha : (run input C mode accounting rule sample (start + extra)).halted = false := Bool.eq_false_iff.mpr hh
      obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting rule hlegal sample (start + extra)
      obtain ⟨next, hs⟩ := hlegal sample.1 _ _ m _ hp ha
      rw [Nat.add_succ, run_succ_of_step input C mode accounting rule sample (start + extra) next ha hs]
      have hstill := run_written_some_after input C mode accounting rule hlegal sample start extra head bit hw
      generalize rule sample.1 (run input C mode accounting rule sample (start + extra)).history = action at hs
      cases hs with
      | review current live port resources =>
        have hne : head ≠ current := by intro he; subst current; rw [port] at hstill; cases hstill
        simpa only [record, reviewLedger, Function.update_of_ne hne] using ih
      | write current chosen live port resources => simpa only [record, reportedWrite_reviews_same] using ih
      | allocate | execute | advance | stop | abandon => exact ih

/-- Once a head bit is written, the test's extracted stopping count is
exactly the original stage review counter. All failed-path reviews remain. -/
theorem nativeHead_count_of_written (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (head : I.Stage) (hhead : head.val = 0)
    (sample : Seed × input.World) (n : ℕ) (bit : Bool)
    (hw : (run input C .uncapped accounting rule sample n).ledger.written head = some bit) :
    headExitStop input head rule sample.1 (worldTapes input sample.2 head) =
      (run input C .uncapped accounting rule sample n).ledger.reviews head := by
  obtain ⟨prefixN, hprefixN, hp⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample n
  obtain ⟨writtenN, old, hwlt, holdPrefix, _, haction⟩ := prefix_written_has_write input C .uncapped accounting rule sample.1 _ _ hp head bit hw
  have holdRun : run input C .uncapped accounting rule sample writtenN = old :=
    prefix_eq_run input C .uncapped accounting rule sample.1 _ _ holdPrefix
  have hactualWrite : rule sample.1 (run input C .uncapped accounting rule sample writtenN).history = .write head bit := by rw [holdRun]; exact haction
  have hbound := headExitStop_le_of_actual_write input C accounting rule head hhead sample writtenN bit hactualWrite
  generalize hstop : headExitStop input head rule sample.1 (worldTapes input sample.2 head) = stop at hbound ⊢
  have hfinite : stop ≠ ⊤ := by
    intro he
    rw [he] at hbound
    exact ENat.top_ne_natCast writtenN (top_le_iff.mp hbound).symm
  lift stop to ℕ using hfinite with k
  have hkn : k < n := (ENat.natCast_le_natCast.mp hbound).trans_lt (hwlt.trans_le hprefixN)
  have hr := run_eq_headReviewState input C accounting rule head hhead sample k (by rw [hstop])
  have hhistory : (run input C .uncapped accounting rule sample k).history = headReviewHistory input head (worldTapes input sample.2 head) k := by rw [hr]; exact headReviewState_history input accounting head _ _ k
  rcases nativeHead_exit_classification input C accounting rule hlegal head hhead sample k hstop with ⟨chosen, hwrite⟩ | hterminal
  · have ha : (run input C .uncapped accounting rule sample k).halted = false := by rw [hr]; exact headReviewState_active input accounting head _ _ k
    obtain ⟨m, _, hpk⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample k
    obtain ⟨next, hs⟩ := hlegal sample.1 _ _ m _ hpk ha
    have hactual : rule sample.1 (run input C .uncapped accounting rule sample k).history = .write head chosen := by rw [hhistory]; exact hwrite
    have hnextRun := run_succ_of_step input C .uncapped accounting rule sample k next ha hs
    have hnext : (run input C .uncapped accounting rule sample (k + 1)).ledger.written head = some chosen ∧
        (run input C .uncapped accounting rule sample (k + 1)).ledger.reviews head = k := by
      rw [hnextRun]
      rw [hactual] at hs
      cases hs
      constructor
      · classical
        simp only [record, reportedWriteLedger]
        split_ifs <;> simp only [writeLedger, Function.update_self]
      · rw [show (record accounting (run input C .uncapped accounting rule sample k) (.write head chosen)
          (writeResponses C (run input C .uncapped accounting rule sample k) head chosen)
          (reportedWriteLedger C (run input C .uncapped accounting rule sample k) head chosen)
          (run input C .uncapped accounting rule sample k).cursor false).ledger.reviews head =
            (run input C .uncapped accounting rule sample k).ledger.reviews head by simp only [record, reportedWrite_reviews_same]]
        rw [hr]
        exact headReviewState_reviews input accounting head _ _ k
    obtain ⟨extra, he⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hkn)
    have hc := run_reviews_written_port input C .uncapped accounting rule hlegal sample (k + 1) extra head chosen hnext.1
    rw [← he, hnext.2] at hc
    exact hc.symm
  · obtain ⟨extra, he⟩ := Nat.exists_eq_add_of_le hkn.le
    have hno := headExit_terminal_no_future_write input C accounting rule head hhead sample k hstop hterminal extra
    rw [← he, hw] at hno
    cases hno

/-- At real next-stage entry, the prefix charge consists of exactly the
local test charge. Every other stage's review counter is still zero. -/
theorem firstEntry_one_prefix_observationBill (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (head : I.Stage) (hhead : head.val = 0)
    (sample : Seed × input.World) (n : ℕ) (hentry : FirstEntryAt input C .uncapped accounting rule 1 n sample) :
    (run input C .uncapped accounting rule sample n).ledger.observationBill input.fees =
      (input.experiment head).observationCharge (headExitStop input head rule sample.1 (worldTapes input sample.2 head)) := by
  classical
  have hport := firstEntry_one_head_written input C .uncapped accounting rule hlegal head hhead sample n hentry
  have hcount : headExitStop input head rule sample.1 (worldTapes input sample.2 head) =
      (run input C .uncapped accounting rule sample n).ledger.reviews head := by
    cases hw : (run input C .uncapped accounting rule sample n).ledger.written head with
    | none => exact (hport hw).elim
    | some bit => exact nativeHead_count_of_written input C accounting rule hlegal head hhead sample n bit hw
  have hf := firstEntryAt_unborn input C .uncapped accounting rule hlegal sample 1 n hentry
  unfold Ledger.observationBill
  rw [Finset.sum_eq_single head]
  · rw [hcount]
    have hn := (run_finiteCounters input C .uncapped accounting rule hlegal sample n).1 head
    simp only [BinaryExperiment.observationCharge, hn, ↓reduceIte]
    simp only [StatisticalInput.fees]
    rw [← ENat.natCast_toNat hn, ENat.toENNReal_coe]
    simp only [ENat.toNat_natCast]
  · intro stage _ hne
    have hstage : 1 ≤ stage.val := by
      by_contra h
      have hs : stage.val = 0 := by omega
      exact hne (Fin.ext (hs.trans hhead.symm))
    rw [(hf.2 stage hstage).2]
    simp only [ENat.toENNReal_zero, mul_zero]
  · intro hnot
    exact (hnot (Finset.mem_univ head)).elim

/-- The SAME local test and the genuine entry continuation partition the
full original observation-plus-failure charge exactly, on every entry path. -/
theorem firstEntry_one_penaltyCharge_decomposition (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (head : I.Stage) (hhead : head.val = 0)
    (sample : Seed × input.World) (n : ℕ) (hentry : FirstEntryAt input C .uncapped accounting rule 1 n sample)
    (penalty : ℝ≥0∞) :
    runPenaltyCharge input C .uncapped accounting rule penalty sample =
      (input.experiment head).observationCharge (headExitStop input head rule sample.1 (worldTapes input sample.2 head)) +
        historyComparisonCharge input C .uncapped accounting rule n penalty sample := by
  classical
  unfold runPenaltyCharge historyComparisonCharge
  rw [runObservationBill_eq_prefix_add_future input C .uncapped accounting rule hlegal sample n,
    firstEntry_one_prefix_observationBill input C accounting rule hlegal head hhead sample n hentry, add_assoc]

/-- Analysis-only correct/error weight. Its decision is the actual extracted
native local test, with no MAP replacement and no future world in its seed. -/
noncomputable def nativeHeadContinuationWeight (input : StatisticalInput I) (head : I.Stage)
    (R : Finset I.Tool) (price : ℝ) (rule : PolicyRule I Seed) (sample : Seed × input.World) : ℝ≥0∞ := by
  classical
  exact if headExitDecision input head rule sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then
    ENNReal.ofReal (input.goodPenaltyReal head R price) else ENNReal.ofReal (input.badPenaltyReal head R price)

theorem nativeHeadContinuationWeight_le_penalty (input : StatisticalInput I) (head : I.Stage)
    (R : Finset I.Tool) (price : ℝ) (hprice : 0 ≤ price) (rule : PolicyRule I Seed) (sample : Seed × input.World) :
    nativeHeadContinuationWeight input head R price rule sample ≤ ENNReal.ofReal price := by
  classical
  have hb := input.penalty_successor_order head R price hprice
  unfold nativeHeadContinuationWeight
  split
  · exact ENNReal.ofReal_le_ofReal (hb.2.1.trans hb.2.2)
  · exact ENNReal.ofReal_le_ofReal hb.2.2

theorem nativeHeadContinuationWeight_on_entry (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (head : I.Stage) (hhead : head.val = 0)
    (sample : Seed × input.World) (n : ℕ) (hentry : FirstEntryAt input C .uncapped accounting rule 1 n sample)
    (R : Finset I.Tool) (price : ℝ) :
    nativeHeadContinuationWeight input head R price rule sample =
      ENNReal.ofReal (headEntryContinuationReal input head R price (publicStartup (run input C .uncapped accounting rule sample n))) := by
  classical
  have hc := firstEntry_one_local_correct_iff input C hearly accounting rule hlegal head hhead sample n hentry
  by_cases hp : HeadCorrectStartup head (publicStartup (run input C .uncapped accounting rule sample n))
  · have hl := hc.mp hp
    simp only [nativeHeadContinuationWeight, headEntryContinuationReal, hp, hl, ↓reduceIte]
  · have hl : headExitDecision input head rule sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head := by
      intro he
      exact hp (hc.mpr he)
    simp only [nativeHeadContinuationWeight, headEntryContinuationReal, hp, hl, ↓reduceIte]

/-- On every path outside next-stage reach, the original failure penalty
already pays the same Gg/Gb local-decision weight and all bought observations.
No termination premise is used; nonreturn/abandon and infinite reviews remain. -/
theorem nativeHead_no_entry_charge_lower (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (head : I.Stage) (hhead : head.val = 0)
    (second : I.Stage) (hsecond : second.val = 1) (sample : Seed × input.World)
    (hnever : ∀ n, (run input C .uncapped accounting rule sample n).cursor ≠ 1)
    (R : Finset I.Tool) (price : ℝ) (hprice : 0 ≤ price) :
    (input.experiment head).observationCharge (headExitStop input head rule sample.1 (worldTapes input sample.2 head)) +
      nativeHeadContinuationWeight input head R price rule sample ≤
      runPenaltyCharge input C .uncapped accounting rule (ENNReal.ofReal price) sample := by
  classical
  have hfailure := no_stage_one_entry_failure input C .uncapped accounting rule hlegal sample second hsecond hnever
  unfold runPenaltyCharge
  simp only [hfailure, ↓reduceIte]
  exact add_le_add (nativeHead_observationCharge_le input C accounting rule head hhead sample)
    (nativeHeadContinuationWeight_le_penalty input head R price hprice rule sample)

end PaperProofs.Common.Native
