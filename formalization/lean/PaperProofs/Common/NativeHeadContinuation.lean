module

public import PaperProofs.Common.NativeHeadTest
public import PaperProofs.Common.NativeBellmanLower
import Lean.Elab.Tactic.Omega

/-! Genuine head write/report facts at next-stage entry. These identify
the correct/error continuation branch from the PUBLIC startup record. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*}

theorem firstEntry_one_head_written (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (head : I.Stage) (hhead : head.val = 0)
    (sample : Seed × input.World) (n : ℕ) (hentry : FirstEntryAt input C mode accounting rule 1 n sample) :
    (run input C mode accounting rule sample n).ledger.written head ≠ none := by
  cases n with
  | zero => have hh := hentry.1; cases hh
  | succ n =>
    have hne := hentry.2 n (Nat.lt_succ_self n)
    have hcursor := hentry.1
    obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting rule hlegal sample n
    by_cases hh : (run input C mode accounting rule sample n).halted = true
    · rw [run_succ_of_halted input C mode accounting rule sample n hh] at hcursor
      exact (hne hcursor).elim
    · have ha : (run input C mode accounting rule sample n).halted = false := Bool.eq_false_iff.mpr hh
      obtain ⟨next, hs⟩ := hlegal sample.1 _ _ m _ hp ha
      have hr := run_succ_of_step input C mode accounting rule sample n next ha hs
      rw [hr] at hcursor ⊢
      generalize rule sample.1 (run input C mode accounting rule sample n).history = action at hs
      cases hs <;> try exact (hne hcursor).elim
      case advance current live written resources =>
        have he : current = head := by
          apply Fin.ext
          have hc := live.2
          change (run input C mode accounting rule sample n).cursor + 1 = 1 at hcursor
          omega
        exact he ▸ written

theorem prefix_early_written_reported (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (head : I.Stage) (hw : s.ledger.written head ≠ none) : ∃ time, s.ledger.reportTime head = some time := by
  induction hp with
  | initial => exact (hw rfl).elim
  | @next n s next earlier hs ih =>
    generalize rule seed s.history = action at hs
    cases hs with
    | write current bit live port resources =>
      by_cases he : head = current
      · subst current
        refine ⟨s.clock, ?_⟩
        simp only [record, reportedWriteLedger, hearly, ↓reduceIte, writeLedger, Function.update_self]
      · have hframe : (reportedWriteLedger C s current bit).written head = s.ledger.written head := by
          classical
          simp only [reportedWriteLedger]
          split_ifs; simp only [writeLedger, Function.update_of_ne he]
        have hwold : s.ledger.written head ≠ none := by simpa only [record, hframe] using hw
        obtain ⟨time, ht⟩ := ih hwold
        refine ⟨time, ?_⟩
        simpa only [record, reportedWriteLedger, hearly, ↓reduceIte, writeLedger, Function.update_of_ne he] using ht
    | review | allocate | execute | advance | stop | abandon => exact ih hw

def HeadCorrectStartup (head : I.Stage) (startup : Startup I) : Prop :=
  ∃ truth serial, historyReport startup.history head = some (truth, serial) ∧ startup.written head = some truth

/-- On every real early prefix with a written head, correctness is encoded
by an actual public report and the actual ordinary written bit. -/
theorem headCorrectStartup_iff (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (head : I.Stage) (hw : s.ledger.written head ≠ none) :
    HeadCorrectStartup head (publicStartup s) ↔ s.ledger.written head = some (s.ledger.truth head) := by
  obtain ⟨time, ht⟩ := prefix_early_written_reported input C hearly mode accounting rule seed truth tapes hp head hw
  have hr := prefix_historyReport_early input C hearly mode accounting rule seed truth tapes hp head
  rw [ht] at hr
  simp only [Option.map_some] at hr
  constructor
  · rintro ⟨bit, serial, hreport, hwrite⟩
    change historyReport s.history head = some (bit, serial) at hreport
    rw [hr] at hreport
    have hb := congrArg Prod.fst (Option.some.inj hreport)
    exact hwrite.trans (congrArg some hb.symm)
  · intro hc
    exact ⟨s.ledger.truth head, s.ledger.writeSerial head, hr, hc⟩

theorem run_written_some_after (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (start extra : ℕ) (head : I.Stage) (bit : Bool)
    (hw : (run input C mode accounting rule sample start).ledger.written head = some bit) :
    (run input C mode accounting rule sample (start + extra)).ledger.written head = some bit := by
  induction extra with
  | zero => exact hw
  | succ extra ih =>
    by_cases hh : (run input C mode accounting rule sample (start + extra)).halted = true
    · rw [Nat.add_succ, run_succ_of_halted input C mode accounting rule sample (start + extra) hh]
      exact ih
    · have ha : (run input C mode accounting rule sample (start + extra)).halted = false := Bool.eq_false_iff.mpr hh
      obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting rule hlegal sample (start + extra)
      obtain ⟨next, hs⟩ := hlegal sample.1 _ _ m _ hp ha
      rw [Nat.add_succ, run_succ_of_step input C mode accounting rule sample (start + extra) next ha hs]
      exact step_written_some input C mode accounting _ hs head bit ih

theorem headExitStop_le_of_actual_write (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (head : I.Stage) (hhead : head.val = 0) (sample : Seed × input.World) (n : ℕ) (bit : Bool)
    (hwrite : rule sample.1 (run input C .uncapped accounting rule sample n).history = .write head bit) :
    headExitStop input head rule sample.1 (worldTapes input sample.2 head) ≤ n := by
  by_contra hnot
  have hbound : (n : ℕ∞) ≤ headExitStop input head rule sample.1 (worldTapes input sample.2 head) :=
    le_of_lt (lt_of_not_ge hnot)
  have hr := run_eq_headReviewState input C accounting rule head hhead sample n hbound
  rw [hr, headReviewState_history] at hwrite
  apply hnot
  apply (headExitStop_le_iff input head rule sample.1 (worldTapes input sample.2 head) n).mpr
  refine ⟨n, le_rfl, ?_⟩
  rw [hwrite]
  intro he
  cases he

theorem headExit_terminal_no_future_write (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (head : I.Stage) (hhead : head.val = 0) (sample : Seed × input.World) (n : ℕ)
    (hstop : headExitStop input head rule sample.1 (worldTapes input sample.2 head) = n)
    (hterminal : rule sample.1 (headReviewHistory input head (worldTapes input sample.2 head) n) = .stop ∨
      rule sample.1 (headReviewHistory input head (worldTapes input sample.2 head) n) = .abandon) :
    ∀ extra, (run input C .uncapped accounting rule sample (n + extra)).ledger.written head = none := by
  have hr := run_eq_headReviewState input C accounting rule head hhead sample n (by rw [hstop])
  have ha : (run input C .uncapped accounting rule sample n).halted = false := by rw [hr]; exact headReviewState_active input accounting head _ _ n
  have hw : (run input C .uncapped accounting rule sample n).ledger.written head = none := by rw [hr]; exact congrFun (headReviewState_written input accounting head _ _ n) head
  have hhistory : (run input C .uncapped accounting rule sample n).history = headReviewHistory input head (worldTapes input sample.2 head) n := by rw [hr]; exact headReviewState_history input accounting head _ _ n
  have hnext : (run input C .uncapped accounting rule sample (n + 1)).halted = true ∧
      (run input C .uncapped accounting rule sample (n + 1)).ledger.written head = none := by
    rcases hterminal with hs | hs
    · have hstep : Step input C .uncapped accounting (worldTapes input sample.2)
          (run input C .uncapped accounting rule sample n)
          (rule sample.1 (run input C .uncapped accounting rule sample n).history)
          (stopState (run input C .uncapped accounting rule sample n) false) := by rw [hhistory, hs]; exact .stop _ ha
      rw [run_succ_of_step input C .uncapped accounting rule sample n _ ha hstep]
      exact ⟨rfl, hw⟩
    · have hstep : Step input C .uncapped accounting (worldTapes input sample.2)
          (run input C .uncapped accounting rule sample n)
          (rule sample.1 (run input C .uncapped accounting rule sample n).history)
          (stopState (run input C .uncapped accounting rule sample n) true) := by rw [hhistory, hs]; exact .abandon _ ha
      rw [run_succ_of_step input C .uncapped accounting rule sample n _ ha hstep]
      exact ⟨rfl, hw⟩
  intro extra
  cases extra with
  | zero => exact hw
  | succ extra =>
    rw [show n + (extra + 1) = (n + 1) + extra by omega,
      run_after_halt input C .uncapped accounting rule sample (n + 1) hnext.1 extra]
    exact hnext.2

/-- An actual later head write is precisely the extracted local decision.
This includes arbitrary non-MAP policies and does not assume source success. -/
theorem nativeHead_decision_of_written (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (head : I.Stage) (hhead : head.val = 0)
    (sample : Seed × input.World) (n : ℕ) (bit : Bool)
    (hw : (run input C .uncapped accounting rule sample n).ledger.written head = some bit) :
    headExitDecision input head rule sample.1 (worldTapes input sample.2 head) = bit := by
  obtain ⟨prefixN, hprefixN, hp⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample n
  obtain ⟨writtenN, old, hwlt, holdPrefix, hactive, haction⟩ := prefix_written_has_write input C .uncapped accounting rule sample.1 _ _ hp head bit hw
  have holdRun : run input C .uncapped accounting rule sample writtenN = old :=
    prefix_eq_run input C .uncapped accounting rule sample.1 _ _ holdPrefix
  have hactualWrite : rule sample.1 (run input C .uncapped accounting rule sample writtenN).history = .write head bit := by rw [holdRun]; exact haction
  have hbound := headExitStop_le_of_actual_write input C accounting rule head hhead sample writtenN bit hactualWrite
  generalize hstop : headExitStop input head rule sample.1 (worldTapes input sample.2 head) = stop at hbound
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
    have hnewWrite : (run input C .uncapped accounting rule sample (k + 1)).ledger.written head = some chosen := by
      rw [hnextRun]
      rw [hactual] at hs
      cases hs
      classical
      simp only [record, reportedWriteLedger]
      split_ifs <;> simp only [writeLedger, Function.update_self]
    obtain ⟨extra, he⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hkn)
    have hpersist := run_written_some_after input C .uncapped accounting rule hlegal sample (k + 1) extra head chosen hnewWrite
    rw [← he, hw] at hpersist
    have hb : chosen = bit := (Option.some.inj hpersist).symm
    rw [← hb]
    exact headExitDecision_of_write input head rule sample.1 (worldTapes input sample.2 head) k chosen hstop hwrite
  · obtain ⟨extra, he⟩ := Nat.exists_eq_add_of_le hkn.le
    have hno := headExit_terminal_no_future_write input C accounting rule head hhead sample k hstop hterminal extra
    rw [← he, hw] at hno
    cases hno

/-- The public-record good/bad split is exactly the SAME extracted local
test's correct/error split on every real next-stage entry. -/
theorem firstEntry_one_local_correct_iff (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (head : I.Stage) (hhead : head.val = 0)
    (sample : Seed × input.World) (n : ℕ) (hentry : FirstEntryAt input C .uncapped accounting rule 1 n sample) :
    HeadCorrectStartup head (publicStartup (run input C .uncapped accounting rule sample n)) ↔
      headExitDecision input head rule sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head := by
  have hwn := firstEntry_one_head_written input C .uncapped accounting rule hlegal head hhead sample n hentry
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample n
  rw [headCorrectStartup_iff input C hearly .uncapped accounting rule sample.1 _ _ hp head hwn]
  cases hw : (run input C .uncapped accounting rule sample n).ledger.written head with
  | none => exact (hwn hw).elim
  | some bit =>
    have hd := nativeHead_decision_of_written input C accounting rule hlegal head hhead sample n bit hw
    rw [run_truth input C .uncapped accounting rule hlegal sample n, hd]
    simp only [Option.some.injEq]

private theorem optionBool_wrong_of_ne (value : Option Bool) (truth : Bool)
    (hnone : value ≠ none) (hcorrect : value ≠ some truth) : value = some (!truth) := by
  cases value with
  | none => exact (hnone rfl).elim
  | some bit => cases truth <;> cases bit <;> simp_all

/-- Observable branch weight for the independently defined Gg and Gb. This
is not a Bellman/value definition; it only labels real entry records. -/
noncomputable def headEntryContinuationReal (input : StatisticalInput I) (head : I.Stage)
    (R : Finset I.Tool) (price : ℝ) (startup : Startup I) : ℝ := by
  classical
  exact if HeadCorrectStartup head startup then input.goodPenaltyReal head R price else input.badPenaltyReal head R price

section BranchMass

variable [MeasurableSpace Seed]

/-- A true first-entry atom pays its correct/error Gg/Gb weight directly
from its public startup, without any presumed optimal tool selection or
continuation-performance hypothesis. -/
theorem nativeHead_entry_branch_lower (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (head : I.Stage) (hhead : head.val = 0) (n : ℕ) (startup : Startup I) (gate : Set Seed)
    (hgate : MeasurableSet gate)
    (hentry : ∀ sample ∈ historyGate input C .uncapped accounting policy.val.rule n startup gate,
      FirstEntryAt input C .uncapped accounting policy.val.rule 1 n sample)
    (price : ℝ) (hprice : 0 ≤ price) :
    ENNReal.ofReal (headEntryContinuationReal input head R price startup) *
      input.seededWorldLaw ν (historyGate input C .uncapped accounting policy.val.rule n startup gate) ≤
      ∫⁻ sample in historyGate input C .uncapped accounting policy.val.rule n startup gate,
        historyComparisonCharge input C .uncapped accounting policy.val.rule n (ENNReal.ofReal price) sample
          ∂input.seededWorldLaw ν := by
  classical
  by_cases hc : HeadCorrectStartup head startup
  · have hcorrect sample (hs : sample ∈ historyGate input C .uncapped accounting policy.val.rule n startup gate) :
        (run input C .uncapped accounting policy.val.rule sample n).ledger.written head =
          some ((run input C .uncapped accounting policy.val.rule sample n).ledger.truth head) := by
      have hw := firstEntry_one_head_written input C .uncapped accounting policy.val.rule policy.val.legal head hhead sample n (hentry sample hs)
      obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample n
      apply (headCorrectStartup_iff input C hC.1 .uncapped accounting policy.val.rule sample.1 _ _ hp head hw).mp
      rw [hs.1]
      exact hc
    simpa only [headEntryContinuationReal, hc, ↓reduceIte] using
      nativeHead_good_branch_lower input C hC accounting R policy ν head hhead n startup gate hgate hentry hcorrect price
  · by_cases hempty : startup.commitments = []
    · have hwrong sample (hs : sample ∈ historyGate input C .uncapped accounting policy.val.rule n startup gate) :
          (run input C .uncapped accounting policy.val.rule sample n).ledger.written head =
            some (!(run input C .uncapped accounting policy.val.rule sample n).ledger.truth head) := by
        have hw := firstEntry_one_head_written input C .uncapped accounting policy.val.rule policy.val.legal head hhead sample n (hentry sample hs)
        obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample n
        apply optionBool_wrong_of_ne _ _ hw
        intro hcorrect
        apply hc
        rw [← hs.1]
        exact (headCorrectStartup_iff input C hC.1 .uncapped accounting policy.val.rule sample.1 _ _ hp head hw).mpr hcorrect
      simpa only [headEntryContinuationReal, hc, ↓reduceIte] using
        nativeHead_unallocated_wrong_branch_lower input C hC accounting R policy ν head hhead n startup gate hgate hentry hwrong hempty price hprice
    · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil startup.commitments hempty
      simpa only [headEntryContinuationReal, hc, ↓reduceIte] using
        nativeHead_allocated_branch_lower input C hC accounting R policy ν head hhead n startup gate hgate hentry a ha price

end BranchMass

end PaperProofs.Common.Native
