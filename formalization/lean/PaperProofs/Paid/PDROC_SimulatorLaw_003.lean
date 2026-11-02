module

public import PaperProofs.Paid.PDROC_Simulator_004
public import PaperProofs.Common.NativeCausality
public import PaperProofs.Common.NativeHeadContinuation

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

def stageCorrectionCount (s : State I) (stage : I.Stage) : ℕ :=
  (s.ledger.commitments.map (fun c => c.handle.stage)).count stage +
    (s.ledger.executions.map (fun e => e.handle.stage)).count stage

theorem stageCorrectionCount_le_two {s : State I} (hw : LedgerWellFormed s.ledger) (stage : I.Stage) :
    stageCorrectionCount s stage ≤ 2 := by
  have hc := List.nodup_iff_count_le_one.mp hw.commitment_stages stage
  have he := List.nodup_iff_count_le_one.mp hw.execution_stages stage
  unfold stageCorrectionCount
  omega

/-- Before stage exit, a legal written-stage action consumes one of the
stage's at most one allocation and one physical execution. -/
theorem stageCorrectionCount_step_of_noExit (input : StatisticalInput I) (C : Contract I)
    (hpay : C.IsCurrentPayment) (mode : ResourceMode) (accounting : NormalAccounting I)
    (tapes : ReviewTapes input) {s next : State I} {action : Action I} (stage : I.Stage)
    (hc : s.cursor = stage.val) (hw : s.ledger.written stage ≠ none)
    (haNext : next.halted = false) (hcNext : next.cursor = stage.val)
    (hs : Step input C mode accounting tapes s action next) :
    stageCorrectionCount next stage = stageCorrectionCount s stage + 1 := by
  cases hs with
  | review current live port resources =>
    have heq : current = stage := Fin.ext (live.2.symm.trans hc)
    subst current
    exact (hw port).elim
  | write current bit live port resources =>
    have heq : current = stage := Fin.ext (live.2.symm.trans hc)
    subst current
    exact (hw port).elim
  | allocate handle tool active valid compatible unused unallocated window resources =>
    have heq : handle.stage = stage := Fin.ext ((window hpay.1.2).symm.trans hc)
    simp [stageCorrectionCount, record, allocateLedger, List.count_append, heq]
    omega
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    have heq : handle.stage = stage := Fin.ext ((window hpay.2).symm.trans hc)
    simp [stageCorrectionCount, record, executeLedger, List.count_append, heq]
    omega
  | advance current live written resources =>
    change s.cursor + 1 = stage.val at hcNext
    omega
  | stop active => cases haNext
  | abandon active => cases haNext

theorem run_actualStep_of_active (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (source : PolicyRule I Seed) (hl : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (n : ℕ) (ha : (run input C mode accounting source sample n).halted = false) :
    Step input C mode accounting (worldTapes input sample.2) (run input C mode accounting source sample n)
      (source sample.1 (run input C mode accounting source sample n).history)
      (run input C mode accounting source sample (n + 1)) := by
  obtain ⟨k, _, hp⟩ := run_has_prefix input C mode accounting source hl sample n
  obtain ⟨next, hs⟩ := hl sample.1 (input.truthAt sample.2) (worldTapes input sample.2) k _ hp ha
  rw [run_succ_of_step input C mode accounting source sample n next ha hs]
  exact hs

theorem run_active_of_active_later (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (source : PolicyRule I Seed) (sample : Seed × input.World) (n extra : ℕ)
    (ha : (run input C mode accounting source sample (n + extra)).halted = false) :
    (run input C mode accounting source sample n).halted = false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  rw [run_after_halt input C mode accounting source sample n hh extra, hh] at ha
  contradiction

/-- Original current-payment policies leave a written stage or terminate
within three further real Native steps, including all failed paths. -/
theorem run_written_stage_exit_within_three (input : StatisticalInput I) (C : Contract I)
    (hpay : C.IsCurrentPayment) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (source : PolicyRule I Seed) (hl : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (start : ℕ) (stage : I.Stage)
    (hc : (run input C mode accounting source sample start).cursor = stage.val)
    (hw : (run input C mode accounting source sample start).ledger.written stage ≠ none) :
    (run input C mode accounting source sample (start + 3)).halted = true ∨
      stage.val < (run input C mode accounting source sample (start + 3)).cursor := by
  by_contra hn
  have ha3 : (run input C mode accounting source sample (start + 3)).halted = false :=
    Bool.eq_false_iff.mpr (fun h => hn (Or.inl h))
  have hc3 : (run input C mode accounting source sample (start + 3)).cursor = stage.val := by
    have hlo := run_cursor_monotone input C mode accounting source hl sample (Nat.le_add_right start 3)
    change (run input C mode accounting source sample start).cursor ≤
      (run input C mode accounting source sample (start + 3)).cursor at hlo
    rw [hc] at hlo
    have hhi : ¬ stage.val < (run input C mode accounting source sample (start + 3)).cursor := fun h => hn (Or.inr h)
    omega
  have ha (k : ℕ) (hk : k ≤ 3) : (run input C mode accounting source sample (start + k)).halted = false := by
    have htime : start + k + (3 - k) = start + 3 := by omega
    exact run_active_of_active_later input C mode accounting source sample (start + k) (3 - k) (htime ▸ ha3)
  have hcursor (k : ℕ) (hk : k ≤ 3) : (run input C mode accounting source sample (start + k)).cursor = stage.val := by
    have hlo := run_cursor_monotone input C mode accounting source hl sample (Nat.le_add_right start k)
    have hhi := run_cursor_monotone input C mode accounting source hl sample (by omega : start + k ≤ start + 3)
    change (run input C mode accounting source sample start).cursor ≤
      (run input C mode accounting source sample (start + k)).cursor at hlo
    change (run input C mode accounting source sample (start + k)).cursor ≤
      (run input C mode accounting source sample (start + 3)).cursor at hhi
    rw [hc] at hlo
    rw [hc3] at hhi
    omega
  obtain ⟨bit, hb⟩ : ∃ bit, (run input C mode accounting source sample start).ledger.written stage = some bit :=
    Option.ne_none_iff_exists'.mp hw
  have hwrite (k : ℕ) : (run input C mode accounting source sample (start + k)).ledger.written stage ≠ none := by
    rw [run_written_some_after input C mode accounting source hl sample start k stage bit hb]
    simp
  have hstep (k : ℕ) (hk : k < 3) :
      stageCorrectionCount (run input C mode accounting source sample (start + (k + 1))) stage =
        stageCorrectionCount (run input C mode accounting source sample (start + k)) stage + 1 := by
    have hs := run_actualStep_of_active input C mode accounting source hl sample (start + k) (ha k (by omega))
    have h := stageCorrectionCount_step_of_noExit input C hpay mode accounting (worldTapes input sample.2) stage
      (hcursor k (by omega)) (hwrite k) (by simpa only [Nat.add_assoc] using ha (k + 1) (by omega))
      (by simpa only [Nat.add_assoc] using hcursor (k + 1) (by omega)) hs
    simpa only [Nat.add_assoc] using h
  have h0 := hstep 0 (by omega)
  have h1 := hstep 1 (by omega)
  have h2 := hstep 2 (by omega)
  have hbound := stageCorrectionCount_le_two (run_ledgerWellFormed input C mode accounting source hl sample (start + 3)) stage
  norm_num only [Nat.add_zero] at h0 h1 h2
  omega






def postwriteResponse : Action I → List (VisibleEvent I)
  | .allocate handle tool => [.committed handle tool]
  | .execute handle tool => [.executed handle tool]
  | .advance stage => [.advanced stage]
  | .stop => [.stopped]
  | .abandon | .review _ | .write _ _ => [.abandoned]

def postwriteStageStep {Seed : Type*} (source : PolicyRule I Seed) (seed : Seed) (stage : I.Stage)
    (history : List (VisibleEvent I)) : List (VisibleEvent I) :=
  if historyHalted history then history else
    if historyCursor history = stage.val then history ++ postwriteResponse (source seed history) else history

def postwriteStageTrace {Seed : Type*} (source : PolicyRule I Seed) (seed : Seed) (stage : I.Stage)
    (history : List (VisibleEvent I)) : ℕ → List (VisibleEvent I)
  | 0 => history
  | k + 1 => postwriteStageStep source seed stage (postwriteStageTrace source seed stage history k)

theorem measurable_postwriteStageStep {Seed : Type*} [MeasurableSpace Seed]
    (source : PolicyRule I Seed) (hm : MeasurableRule source) (stage : I.Stage) :
    Measurable (fun pair : Seed × List (VisibleEvent I) => postwriteStageStep source pair.1 stage pair.2) := by
  exact (measurable_of_countable (fun pair : List (VisibleEvent I) × Action I =>
    if historyHalted pair.1 then pair.1 else if historyCursor pair.1 = stage.val then
      pair.1 ++ postwriteResponse pair.2 else pair.1)).comp (measurable_snd.prodMk hm)

theorem measurable_postwriteStageTrace {Seed : Type*} [MeasurableSpace Seed]
    (source : PolicyRule I Seed) (hm : MeasurableRule source) (stage : I.Stage) (k : ℕ) :
    Measurable (fun pair : Seed × List (VisibleEvent I) => postwriteStageTrace source pair.1 stage pair.2 k) := by
  induction k with
  | zero => exact measurable_snd
  | succ k ih => exact (measurable_postwriteStageStep source hm stage).comp (measurable_fst.prodMk ih)

theorem writtenStage_step_history (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (stage : I.Stage)
    (hc : s.cursor = stage.val) (hw : s.ledger.written stage ≠ none)
    (hs : Step input C mode accounting tapes s action next) :
    next.history = s.history ++ postwriteResponse action := by
  cases hs with
  | review current live port resources =>
    have heq : current = stage := Fin.ext (live.2.symm.trans hc)
    subst current
    exact (hw port).elim
  | write current bit live port resources =>
    have heq : current = stage := Fin.ext (live.2.symm.trans hc)
    subst current
    exact (hw port).elim
  | allocate | execute | advance | stop | abandon => rfl

theorem postwriteStageStep_eq_nextHistory (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (source : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s next : State I} (stage : I.Stage)
    (hp : Prefix input C mode accounting source seed truth tapes n s)
    (ha : s.halted = false) (hc : s.cursor = stage.val) (hw : s.ledger.written stage ≠ none)
    (hs : Step input C mode accounting tapes s (source seed s.history) next) :
    postwriteStageStep source seed stage s.history = next.history := by
  have h := writtenStage_step_history input C mode accounting tapes stage hc hw hs
  simpa only [postwriteStageStep, prefix_historyHalted input C mode accounting source seed truth tapes hp,
    ha, Bool.false_eq_true, ↓reduceIte, prefix_historyCursor input C mode accounting source seed truth tapes hp,
    hc, ite_eq_left rfl] using h.symm

theorem postwriteStageStep_freeze_at_exit (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (source : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (stage : I.Stage)
    (hp : Prefix input C mode accounting source seed truth tapes n s)
    (hexit : s.halted = true ∨ stage.val < s.cursor) :
    postwriteStageStep source seed stage s.history = s.history := by
  rcases hexit with hh | hc
  · simp only [postwriteStageStep, prefix_historyHalted input C mode accounting source seed truth tapes hp,
      hh, ↓reduceIte]
  · have hne : historyCursor s.history ≠ stage.val := by
      rw [prefix_historyCursor input C mode accounting source seed truth tapes hp]
      omega
    simp [postwriteStageStep, hne]

/-- The concrete three-step transducer returns exactly the original full
history at its first written-stage exit, preserving abandonment and failed
paths. It does not run the source controller into a later fresh stage. -/
theorem postwriteStageTrace_three_eq_actual_exit (input : StatisticalInput I) (C : Contract I)
    (hpay : C.IsCurrentPayment) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (source : PolicyRule I Seed) (hl : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (start : ℕ) (stage : I.Stage)
    (hc : (run input C mode accounting source sample start).cursor = stage.val)
    (hw : (run input C mode accounting source sample start).ledger.written stage ≠ none) :
    ∃ exit : ℕ, exit ≤ 3 ∧
      ((run input C mode accounting source sample (start + exit)).halted = true ∨
        stage.val < (run input C mode accounting source sample (start + exit)).cursor) ∧
      postwriteStageTrace source sample.1 stage (run input C mode accounting source sample start).history 3 =
        (run input C mode accounting source sample (start + exit)).history := by
  classical
  let E := fun k : ℕ => (run input C mode accounting source sample (start + k)).halted = true ∨
    stage.val < (run input C mode accounting source sample (start + k)).cursor
  have he : ∃ k : ℕ, E k := ⟨3, run_written_stage_exit_within_three input C hpay mode accounting source hl sample start stage hc hw⟩
  let exit := Nat.find he
  have hExit : E exit := Nat.find_spec he
  have hBound : exit ≤ 3 := Nat.find_min' he (run_written_stage_exit_within_three input C hpay mode accounting source hl sample start stage hc hw)
  have hbefore (k : ℕ) (hk : k < exit) :
      (run input C mode accounting source sample (start + k)).halted = false ∧
        (run input C mode accounting source sample (start + k)).cursor = stage.val := by
    have hnot : ¬ E k := Nat.find_min he hk
    refine ⟨Bool.eq_false_iff.mpr (fun hh => hnot (Or.inl hh)), ?_⟩
    have hlo := run_cursor_monotone input C mode accounting source hl sample (Nat.le_add_right start k)
    change (run input C mode accounting source sample start).cursor ≤
      (run input C mode accounting source sample (start + k)).cursor at hlo
    rw [hc] at hlo
    have hhi : ¬ stage.val < (run input C mode accounting source sample (start + k)).cursor := fun h => hnot (Or.inr h)
    omega
  obtain ⟨bit, hb⟩ : ∃ bit, (run input C mode accounting source sample start).ledger.written stage = some bit := Option.ne_none_iff_exists'.mp hw
  have hwritten (k : ℕ) : (run input C mode accounting source sample (start + k)).ledger.written stage ≠ none := by
    rw [run_written_some_after input C mode accounting source hl sample start k stage bit hb]
    simp
  have hTrace (k : ℕ) :
      postwriteStageTrace source sample.1 stage (run input C mode accounting source sample start).history k =
        (run input C mode accounting source sample (start + min k exit)).history := by
    induction k with
    | zero => simp only [postwriteStageTrace, Nat.zero_min, Nat.add_zero]
    | succ k ih =>
      rw [postwriteStageTrace, ih]
      by_cases hk : k < exit
      · rw [Nat.min_eq_left hk.le]
        obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting source hl sample (start + k)
        have hstep := run_actualStep_of_active input C mode accounting source hl sample (start + k) (hbefore k hk).1
        have hnext := postwriteStageStep_eq_nextHistory input C mode accounting source sample.1
          (input.truthAt sample.2) (worldTapes input sample.2) stage hp (hbefore k hk).1 (hbefore k hk).2 (hwritten k) hstep
        simpa only [Nat.min_eq_left (by omega : k + 1 ≤ exit), Nat.add_assoc] using hnext
      · have hke : exit ≤ k := by omega
        rw [Nat.min_eq_right hke, Nat.min_eq_right (by omega : exit ≤ k + 1)]
        obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting source hl sample (start + exit)
        exact postwriteStageStep_freeze_at_exit input C mode accounting source sample.1
          (input.truthAt sample.2) (worldTapes input sample.2) stage hp hExit
  refine ⟨exit, hBound, hExit, ?_⟩
  simpa only [Nat.min_eq_right hBound] using hTrace 3

end PDROC

