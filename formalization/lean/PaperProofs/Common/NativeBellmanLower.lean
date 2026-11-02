module

public import PaperProofs.Common.NativeHeadTest
public import PaperProofs.Common.RestrictedHistorySuffixBridge
import Lean.Elab.Tactic.Omega

/-!
B08 lower-bound assembly from genuine arbitrary-policy head-stage branches.
The continuation values below are the existing independent healthyPenalty
infima. No Bellman equation, optimal continuation oracle or local-test
performance assertion is supplied as a premise.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*}

private theorem reportedWrite_commitments_same (C : Contract I) (s : State I) (stage : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s stage bit).commitments = s.ledger.commitments := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

/-- Actual commitments inherit both source R permission and compatibility.
These properties are proved from native allocation steps, not stored as a
continuation-value assumption. -/
theorem prefix_commitments_usable (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (R : Finset I.Tool)
    (hR : UsesOnly input C accounting rule R) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting rule seed truth tapes n s) :
    ∀ a ∈ s.ledger.commitments, a.tool ∈ R ∧ a.tool ∈ I.eligible a.handle.stage := by
  induction hp with
  | initial => intro a ha; cases ha
  | @next n s next earlier hs ih =>
    generalize haction : rule seed s.history = action at hs
    cases hs with
    | allocate handle tool active valid compatible unused unallocated window resources =>
      intro a ha
      change a ∈ s.ledger.commitments ++ [⟨handle, tool, s.clock⟩] at ha
      rcases List.mem_append.mp ha with hold | hnew
      · exact ih a hold
      · obtain rfl := List.mem_singleton.mp hnew
        exact ⟨hR seed truth tapes n s earlier active handle tool haction, compatible⟩
    | write current bit live port resources =>
      intro a ha
      exact ih a (by simpa only [record, reportedWrite_commitments_same] using ha)
    | review | execute | advance | stop | abandon => exact ih

/-- At the true entry of stage 1, every saved commitment is on head stage 0.
No future report, write or allocation is silently included in the cache. -/
theorem firstEntry_one_commitment_stage (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (head : I.Stage) (hhead : head.val = 0)
    (sample : Seed × input.World) (n : ℕ) (hentry : FirstEntryAt input C mode accounting rule 1 n sample) :
    ∀ a ∈ (run input C mode accounting rule sample n).ledger.commitments, a.handle.stage = head := by
  obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting rule hlegal sample n
  have hinv := prefix_invariant input C mode accounting rule sample.1 _ _ hp
  have hf := firstEntryAt_unborn input C mode accounting rule hlegal sample 1 n hentry
  intro a ha
  apply Fin.ext
  have hz : a.handle.stage.val = 0 := by
    by_contra hne
    have hfuture : 1 ≤ a.handle.stage.val := by omega
    have hg := (hinv.commitment_genuine a ha).1
    rw [(hf.2 a.handle.stage hfuture).1] at hg
    cases hg
  exact hz.trans hhead.symm

theorem firstEntry_one_correct_no_commitments (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (head : I.Stage) (hhead : head.val = 0)
    (sample : Seed × input.World) (n : ℕ) (hentry : FirstEntryAt input C mode accounting rule 1 n sample)
    (hcorrect : (run input C mode accounting rule sample n).ledger.written head =
      some ((run input C mode accounting rule sample n).ledger.truth head)) :
    (run input C mode accounting rule sample n).ledger.commitments = [] := by
  obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting rule hlegal sample n
  have hinv := prefix_invariant input C mode accounting rule sample.1 _ _ hp
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro a ha
  have hs := firstEntry_one_commitment_stage input C mode accounting rule hlegal head hhead sample n hentry a ha
  have hg := (hinv.commitment_genuine a ha).1
  rw [hs, hcorrect] at hg
  cases ht : (run input C mode accounting rule sample n).ledger.truth head <;> simp only [ht, Bool.not_true, Bool.not_false] at hg
  all_goals cases hg

theorem firstEntry_one_committedTools_singleton (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (head : I.Stage) (hhead : head.val = 0)
    (sample : Seed × input.World) (n : ℕ) (hentry : FirstEntryAt input C mode accounting rule 1 n sample)
    (a : Commitment I) (ha : a ∈ (run input C mode accounting rule sample n).ledger.commitments) :
    committedTools (run input C mode accounting rule sample n) = {a.tool} := by
  classical
  have hwf := run_ledgerWellFormed input C mode accounting rule hlegal sample n
  have hall := firstEntry_one_commitment_stage input C mode accounting rule hlegal head hhead sample n hentry
  have heq (b : Commitment I) (hb : b ∈ (run input C mode accounting rule sample n).ledger.commitments) : b = a :=
    List.inj_on_of_nodup_map hwf.commitment_stages hb ha ((hall b hb).trans (hall a ha).symm)
  ext tool
  simp only [committedTools, Startup.committedTools, publicStartup, List.mem_toFinset, List.mem_map, Finset.mem_singleton]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [heq b hb]
  · intro ht
    exact ⟨a, ha, ht.symm⟩

theorem badPenaltyReal_le_tool (input : StatisticalInput I) (head : I.Stage) (R : Finset I.Tool)
    (price : ℝ) (tool : I.Tool) (htool : tool ∈ I.eligible head ∩ R) :
    input.badPenaltyReal head R price ≤ input.healthyPenaltyReal (head.val + 1) (R.erase tool) price := by
  classical
  have hn : (I.eligible head ∩ R).Nonempty := ⟨tool, htool⟩
  simp only [StatisticalInput.badPenaltyReal, hn, ↓reduceDIte]
  exact Finset.inf'_le _ htool

theorem ofReal_healthyPenaltyReal (input : StatisticalInput I) (first : ℕ)
    (R : Finset I.Tool) (price : ℝ) :
    ENNReal.ofReal (input.healthyPenaltyReal first R price) = input.healthyPenalty first R (ENNReal.ofReal price) :=
  ENNReal.ofReal_toReal (input.healthyPenalty_ne_top first R ENNReal.ofReal_ne_top)

private theorem reportedWrite_written_same (C : Contract I) (s : State I) (stage : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s stage bit).written = Function.update s.ledger.written stage (some bit) := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

theorem run_written_behind_cursor (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (start extra : ℕ) (head : I.Stage)
    (hold : head.val < (run input C mode accounting rule sample start).cursor) :
    (run input C mode accounting rule sample (start + extra)).ledger.written head =
      (run input C mode accounting rule sample start).ledger.written head := by
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
      have hc := run_cursor_monotone input C mode accounting rule hlegal sample (Nat.le_add_right start extra)
      change (run input C mode accounting rule sample start).cursor ≤ (run input C mode accounting rule sample (start + extra)).cursor at hc
      generalize rule sample.1 (run input C mode accounting rule sample (start + extra)).history = action at hs
      cases hs with
      | write current bit live port resources =>
        have hne : head ≠ current := by intro he; have hl := live.2; subst current; omega
        simpa only [record, reportedWrite_written_same, Function.update_of_ne hne] using ih
      | review | allocate | execute | advance | stop | abandon => exact ih

/-- Passing an unallocated head under a current allocation contract makes
all later head allocations impossible. Pending allocated executions remain
legal under their genuine original execution deadline. -/
theorem run_unallocated_behind_cursor (input : StatisticalInput I) (C : Contract I)
    (hcurrent : C.allocation = .currentWindow) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (start extra : ℕ) (head : I.Stage)
    (hold : head.val < (run input C mode accounting rule sample start).cursor)
    (hno : ∀ a ∈ (run input C mode accounting rule sample start).ledger.commitments, a.handle.stage ≠ head) :
    ∀ a ∈ (run input C mode accounting rule sample (start + extra)).ledger.commitments, a.handle.stage ≠ head := by
  induction extra with
  | zero => exact hno
  | succ extra ih =>
    by_cases hh : (run input C mode accounting rule sample (start + extra)).halted = true
    · rw [Nat.add_succ, run_succ_of_halted input C mode accounting rule sample (start + extra) hh]
      exact ih
    · have ha : (run input C mode accounting rule sample (start + extra)).halted = false := Bool.eq_false_iff.mpr hh
      obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting rule hlegal sample (start + extra)
      obtain ⟨next, hs⟩ := hlegal sample.1 _ _ m _ hp ha
      rw [Nat.add_succ, run_succ_of_step input C mode accounting rule sample (start + extra) next ha hs]
      have hc := run_cursor_monotone input C mode accounting rule hlegal sample (Nat.le_add_right start extra)
      change (run input C mode accounting rule sample start).cursor ≤ (run input C mode accounting rule sample (start + extra)).cursor at hc
      generalize rule sample.1 (run input C mode accounting rule sample (start + extra)).history = action at hs
      cases hs with
      | allocate handle tool active valid compatible unused unallocated window resources =>
        intro a ham
        change a ∈ (run input C mode accounting rule sample (start + extra)).ledger.commitments ++ [⟨handle, tool, (run input C mode accounting rule sample (start + extra)).clock⟩] at ham
        rcases List.mem_append.mp ham with hbefore | hnew
        · exact ih a hbefore
        · obtain rfl := List.mem_singleton.mp hnew
          intro he
          have hw := window hcurrent
          rw [he] at hw
          omega
      | write current bit live port resources =>
        intro a ham
        exact ih a (by simpa only [record, reportedWrite_commitments_same] using ham)
      | review | execute | advance | stop | abandon => exact ih

/-- The wrong/unallocated branch is permanent ORIGINAL task failure. Its
eventual-failure penalty is therefore available without suppressing later
spending or pretending that the missed allocation deadline was repaired. -/
theorem wrong_unallocated_behind_cursor_failure (input : StatisticalInput I) (C : Contract I)
    (hcurrent : C.allocation = .currentWindow) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (start : ℕ) (head : I.Stage)
    (hold : head.val < (run input C mode accounting rule sample start).cursor)
    (hwrong : (run input C mode accounting rule sample start).ledger.written head =
      some (!(run input C mode accounting rule sample start).ledger.truth head))
    (hno : ∀ a ∈ (run input C mode accounting rule sample start).ledger.commitments, a.handle.stage ≠ head) :
    ¬runSuccess input C mode accounting rule sample := by
  rintro ⟨stopped, hhalt, hsuccess⟩
  let now := max start stopped
  obtain ⟨delta, hnowStop⟩ := Nat.exists_eq_add_of_le (Nat.le_max_right start stopped)
  have hstate : run input C mode accounting rule sample now = run input C mode accounting rule sample stopped := by
    change run input C mode accounting rule sample (max start stopped) = _
    rw [hnowStop, run_after_halt input C mode accounting rule sample stopped hhalt delta]
  have hsuccessNow : (run input C mode accounting rule sample now).ledger.success C := by rw [hstate]; exact hsuccess
  obtain ⟨extra, hnowStart⟩ := Nat.exists_eq_add_of_le (Nat.le_max_left start stopped)
  have hwriteNow := run_written_behind_cursor input C mode accounting rule hlegal sample start extra head hold
  have hnoNow := run_unallocated_behind_cursor input C hcurrent mode accounting rule hlegal sample start extra head hold hno
  change max start stopped = start + extra at hnowStart
  rw [← hnowStart] at hwriteNow hnoNow
  have htruth : (run input C mode accounting rule sample now).ledger.truth head =
      (run input C mode accounting rule sample start).ledger.truth head := by
    rw [run_truth input C mode accounting rule hlegal sample now, run_truth input C mode accounting rule hlegal sample start]
  rcases hsuccessNow.2.2.2 head with hright | ⟨e, he, hes⟩
  · rw [hwriteNow, hwrong, htruth] at hright
    cases ht : (run input C mode accounting rule sample start).ledger.truth head <;> simp only [ht, Bool.not_true, Bool.not_false] at hright
    all_goals cases hright
  · have hwf := run_ledgerWellFormed input C mode accounting rule hlegal sample now
    obtain ⟨a, ha, hh, _, _⟩ := hwf.backed e he
    exact hnoNow a ha ((congrArg MismatchHandle.stage hh).trans hes)

section BranchIntegrals

variable [MeasurableSpace Seed]

/-- On each REAL correct-head first-entry atom, the saved R is unchanged,
so its whole continuation charge pays the independently defined Gg. -/
theorem nativeHead_good_branch_lower (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (head : I.Stage) (hhead : head.val = 0) (n : ℕ) (startup : Startup I) (gate : Set Seed)
    (hgate : MeasurableSet gate)
    (hentry : ∀ sample ∈ historyGate input C .uncapped accounting policy.val.rule n startup gate,
      FirstEntryAt input C .uncapped accounting policy.val.rule 1 n sample)
    (hcorrect : ∀ sample ∈ historyGate input C .uncapped accounting policy.val.rule n startup gate,
      (run input C .uncapped accounting policy.val.rule sample n).ledger.written head =
        some ((run input C .uncapped accounting policy.val.rule sample n).ledger.truth head))
    (price : ℝ) :
    ENNReal.ofReal (input.goodPenaltyReal head R price) *
      input.seededWorldLaw ν (historyGate input C .uncapped accounting policy.val.rule n startup gate) ≤
      ∫⁻ sample in historyGate input C .uncapped accounting policy.val.rule n startup gate,
        historyComparisonCharge input C .uncapped accounting policy.val.rule n (ENNReal.ofReal price) sample
          ∂input.seededWorldLaw ν := by
  classical
  let E := historyGate input C .uncapped accounting policy.val.rule n startup gate
  by_cases he : E.Nonempty
  · obtain ⟨sample, hs⟩ := he
    have hempty := firstEntry_one_correct_no_commitments input C .uncapped accounting policy.val.rule policy.val.legal
      head hhead sample n (hentry sample hs) (hcorrect sample hs)
    have hcomm : startup.committedTools = ∅ := by
      rw [← hs.1]
      simp only [publicStartup, Startup.committedTools, hempty, List.map_nil, List.toFinset_nil]
    have hb := restrictedStageEntryHistoryPenaltyBridge input C hC accounting R policy ν 1 n startup gate hgate hentry (ENNReal.ofReal price)
    rw [hcomm, Finset.sdiff_empty] at hb
    simpa only [StatisticalInput.goodPenaltyReal, hhead, Nat.zero_add, ofReal_healthyPenaltyReal] using hb
  · have hzero : E = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    change ENNReal.ofReal (input.goodPenaltyReal head R price) * input.seededWorldLaw ν E ≤ _
    rw [hzero, measure_empty, mul_zero]
    exact bot_le

/-- On a REAL saved head-tool branch, the exact used tool is legal and in
R, only that tool is removed, and the unchanged independent infimum pays Gb.
No minimum tool choice or optimal continuation is assumed. -/
theorem nativeHead_allocated_branch_lower (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (head : I.Stage) (hhead : head.val = 0) (n : ℕ) (startup : Startup I) (gate : Set Seed)
    (hgate : MeasurableSet gate)
    (hentry : ∀ sample ∈ historyGate input C .uncapped accounting policy.val.rule n startup gate,
      FirstEntryAt input C .uncapped accounting policy.val.rule 1 n sample)
    (a : Commitment I) (ha : a ∈ startup.commitments) (price : ℝ) :
    ENNReal.ofReal (input.badPenaltyReal head R price) *
      input.seededWorldLaw ν (historyGate input C .uncapped accounting policy.val.rule n startup gate) ≤
      ∫⁻ sample in historyGate input C .uncapped accounting policy.val.rule n startup gate,
        historyComparisonCharge input C .uncapped accounting policy.val.rule n (ENNReal.ofReal price) sample
          ∂input.seededWorldLaw ν := by
  classical
  let E := historyGate input C .uncapped accounting policy.val.rule n startup gate
  by_cases he : E.Nonempty
  · obtain ⟨sample, hs⟩ := he
    have ham : a ∈ (run input C .uncapped accounting policy.val.rule sample n).ledger.commitments := by
      change a ∈ (publicStartup (run input C .uncapped accounting policy.val.rule sample n)).commitments
      rw [hs.1]
      exact ha
    obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample n
    have htool := prefix_commitments_usable input C accounting policy.val.rule R policy.property sample.1 _ _ hp a ham
    have hstage := firstEntry_one_commitment_stage input C .uncapped accounting policy.val.rule policy.val.legal head hhead sample n (hentry sample hs) a ham
    rw [hstage] at htool
    have hsingleton := firstEntry_one_committedTools_singleton input C .uncapped accounting policy.val.rule policy.val.legal head hhead sample n (hentry sample hs) a ham
    have hcomm : startup.committedTools = {a.tool} := by
      rw [← hs.1]
      exact hsingleton
    have hvalue : ENNReal.ofReal (input.badPenaltyReal head R price) ≤
        input.healthyPenalty 1 (R \ startup.committedTools) (ENNReal.ofReal price) := by
      rw [hcomm, Finset.sdiff_singleton_eq_erase]
      have hb := ENNReal.ofReal_le_ofReal (badPenaltyReal_le_tool input head R price a.tool (Finset.mem_inter.mpr ⟨htool.2, htool.1⟩))
      simpa only [hhead, Nat.zero_add, ofReal_healthyPenaltyReal] using hb
    exact (mul_le_mul_left hvalue _).trans
      (restrictedStageEntryHistoryPenaltyBridge input C hC accounting R policy ν 1 n startup gate hgate hentry (ENNReal.ofReal price))
  · have hzero : E = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    change ENNReal.ofReal (input.badPenaltyReal head R price) * input.seededWorldLaw ν E ≤ _
    rw [hzero, measure_empty, mul_zero]
    exact bot_le

/-- The unallocated wrong-head atom is paid by the ORIGINAL failure penalty,
even when the policy continues legally and buys later observations. -/
theorem nativeHead_unallocated_wrong_branch_lower (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (head : I.Stage) (hhead : head.val = 0) (n : ℕ) (startup : Startup I) (gate : Set Seed)
    (hgate : MeasurableSet gate)
    (hentry : ∀ sample ∈ historyGate input C .uncapped accounting policy.val.rule n startup gate,
      FirstEntryAt input C .uncapped accounting policy.val.rule 1 n sample)
    (hwrong : ∀ sample ∈ historyGate input C .uncapped accounting policy.val.rule n startup gate,
      (run input C .uncapped accounting policy.val.rule sample n).ledger.written head =
        some (!(run input C .uncapped accounting policy.val.rule sample n).ledger.truth head))
    (hempty : startup.commitments = []) (price : ℝ) (hprice : 0 ≤ price) :
    ENNReal.ofReal (input.badPenaltyReal head R price) *
      input.seededWorldLaw ν (historyGate input C .uncapped accounting policy.val.rule n startup gate) ≤
      ∫⁻ sample in historyGate input C .uncapped accounting policy.val.rule n startup gate,
        historyComparisonCharge input C .uncapped accounting policy.val.rule n (ENNReal.ofReal price) sample
          ∂input.seededWorldLaw ν := by
  rw [← setLIntegral_const]
  apply setLIntegral_mono' (measurableSet_historyGate input C .uncapped accounting policy.val.rule policy.val.measurable_rule n startup gate hgate)
  intro sample hs
  have hsourceEmpty : (run input C .uncapped accounting policy.val.rule sample n).ledger.commitments = [] := by
    change (publicStartup (run input C .uncapped accounting policy.val.rule sample n)).commitments = []
    rw [hs.1, hempty]
  have hcursor : head.val < (run input C .uncapped accounting policy.val.rule sample n).cursor := by
    rw [(hentry sample hs).1, hhead]
    exact Nat.zero_lt_one
  have hfailure := wrong_unallocated_behind_cursor_failure input C hC.2 .uncapped accounting policy.val.rule
    policy.val.legal sample n head hcursor (hwrong sample hs) (by intro a ha; rw [hsourceEmpty] at ha; cases ha)
  have hbound : ENNReal.ofReal (input.badPenaltyReal head R price) ≤ ENNReal.ofReal price :=
    ENNReal.ofReal_le_ofReal (input.penalty_successor_order head R price hprice).2.2
  exact hbound.trans (original_failure_penalty_le_comparison input C .uncapped accounting policy.val.rule sample n (ENNReal.ofReal price) hfailure)

end BranchIntegrals

end PaperProofs.Common.Native
