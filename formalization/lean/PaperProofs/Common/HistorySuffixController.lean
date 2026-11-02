module

public import PaperProofs.Common.HistoryPenaltyBridge
public import PaperProofs.Common.NativeHistoryReplay
import Lean.Elab.Tactic.Omega

/-!
B09 actual controller-extraction components. The frozen target is the genuine
first-stage-entry bridge, not an intermediate posterior-history bound.

This file implements bounded, measurable simulation of old pending executions
using public startup data and the original history rule. These executions are
real legal original steps on a reached run: no future bit/tape is read, no old
handle is invented, no commitment is released, no execution deadline is waived,
and no failed-path charge is erased from the original run. They are INTERNAL
steps of the lower comparison, so they do not consume suffix native clocks.

Consequently a fixed original/suffix clock offset is insufficient for general
policies. Future handles must be rebound to the actual suffix write serial.
The stage/action projection below performs that rebinding using only the real
suffix visible history. A complete AvailablePolicy still requires replaying
those suffix responses into the original public cache and proving the resulting
native run relation, observation-charge identity, and failure domination.
Neither of the outstanding history bridges is an input to these components.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance}

/-- The public effect of one actual execution, including the ORIGINAL action
clock and accounting response. There is no hidden truth/tape argument. -/
def Startup.executePublic (accounting : NormalAccounting I) (startup : Startup I)
    (handle : MismatchHandle I) (tool : I.Tool) : Startup I :=
  { startup with
    executions := startup.executions ++ [⟨handle, tool, startup.clock⟩]
    normalCalls := startup.normalCalls +
      accounting startup.history (.execute handle tool) [.executed handle tool]
    clock := startup.clock + 1
    history := startup.history ++ [.executed handle tool]
    halted := false }

theorem publicStartup_execute (accounting : NormalAccounting I) (s : State I)
    (handle : MismatchHandle I) (tool : I.Tool) :
    publicStartup (record accounting s (.execute handle tool) [.executed handle tool]
      (executeLedger s handle tool) s.cursor false) =
      (publicStartup s).executePublic accounting handle tool := rfl

theorem executePublic_preserves_commitments (accounting : NormalAccounting I)
    (startup : Startup I) (handle : MismatchHandle I) (tool : I.Tool) :
    (startup.executePublic accounting handle tool).commitments = startup.commitments := rfl

theorem executePublic_preserves_available (accounting : NormalAccounting I)
    (startup : Startup I) (handle : MismatchHandle I) (tool : I.Tool) :
    (startup.executePublic accounting handle tool).availableTools = startup.availableTools := rfl

theorem executePublic_preserves_reviews (accounting : NormalAccounting I)
    (startup : Startup I) (handle : MismatchHandle I) (tool : I.Tool) :
    (startup.executePublic accounting handle tool).reviews = startup.reviews := rfl

theorem executePublic_preserves_serials (accounting : NormalAccounting I)
    (startup : Startup I) (handle : MismatchHandle I) (tool : I.Tool) :
    (startup.executePublic accounting handle tool).writeSerial = startup.writeSerial := rfl

def oldExecutionRequest (first : ℕ) : Action I → Option (MismatchHandle I × I.Tool)
  | .execute handle tool => if handle.stage.val < first then some (handle, tool) else none
  | _ => none

theorem oldExecutionRequest_some_iff (first : ℕ) (action : Action I)
    (handle : MismatchHandle I) (tool : I.Tool) :
    oldExecutionRequest first action = some (handle, tool) ↔
      action = .execute handle tool ∧ handle.stage.val < first := by
  cases action <;> simp only [oldExecutionRequest, reduceCtorEq, false_and]
  rename_i h r
  split_ifs with hold
  · simp only [Option.some.injEq, Prod.mk.injEq, Action.execute.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨rfl, rfl⟩, hold⟩
    · rintro ⟨⟨rfl, rfl⟩, _⟩
      exact ⟨rfl, rfl⟩
  · simp only [false_iff, not_and]
    intro heq
    cases heq
    exact hold

/-- One policy-selected old execution, simulated on PUBLIC data. The halted
case is preserved and never queries a legal-action premise outside its domain. -/
def silentOldNext (first : ℕ) (accounting : NormalAccounting I)
    (startup : Startup I) (action : Action I) : Option (Startup I) :=
  if startup.halted then none else
    (oldExecutionRequest first action).map fun request =>
      startup.executePublic accounting request.1 request.2

theorem silentOldNext_some_iff (first : ℕ) (accounting : NormalAccounting I)
    (startup next : Startup I) (action : Action I) :
    silentOldNext first accounting startup action = some next ↔
      startup.halted = false ∧ ∃ handle tool,
        action = .execute handle tool ∧ handle.stage.val < first ∧
          next = startup.executePublic accounting handle tool := by
  cases hh : startup.halted with
  | true => simp [silentOldNext, hh]
  | false =>
    simp only [silentOldNext, hh, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff]
    constructor
    · rintro ⟨⟨handle, tool⟩, hrequest, rfl⟩
      obtain ⟨ha, hold⟩ := (oldExecutionRequest_some_iff first action handle tool).mp hrequest
      exact ⟨True.intro, handle, tool, ha, hold, rfl⟩
    · rintro ⟨_, handle, tool, ha, hold, rfl⟩
      exact ⟨(handle, tool),
        (oldExecutionRequest_some_iff first action handle tool).mpr ⟨ha, hold⟩, rfl⟩

/-- At most `fuel` internal old executions. `none` stops immediately. The
elapsed original native action count is returned with the public cache. -/
def settleOldExecutions {Seed : Type*} (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) : ℕ → Seed → Startup I → Startup I × ℕ
  | 0, _, startup => (startup, 0)
  | fuel + 1, seed, startup =>
    match silentOldNext first accounting startup (rule seed startup.history) with
    | none => (startup, 0)
    | some next =>
      let result := settleOldExecutions first accounting rule fuel seed next
      (result.1, result.2 + 1)

theorem settleOldExecutions_count_le {Seed : Type*} (first : ℕ)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (fuel : ℕ) (seed : Seed) (startup : Startup I) :
    (settleOldExecutions first accounting rule fuel seed startup).2 ≤ fuel := by
  induction fuel generalizing startup with
  | zero => exact le_rfl
  | succ fuel ih =>
    simp only [settleOldExecutions]
    split
    · exact Nat.zero_le _
    · exact Nat.succ_le_succ (ih _)

theorem settleOldExecutions_execution_count {Seed : Type*} (first : ℕ)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (fuel : ℕ) (seed : Seed) (startup : Startup I) :
    (settleOldExecutions first accounting rule fuel seed startup).1.executions.length =
      startup.executions.length + (settleOldExecutions first accounting rule fuel seed startup).2 := by
  induction fuel generalizing startup with
  | zero => simp only [settleOldExecutions, Nat.add_zero]
  | succ fuel ih =>
    generalize hn : silentOldNext first accounting startup (rule seed startup.history) = next
    cases next with
    | none => simp only [settleOldExecutions, hn, Nat.add_zero]
    | some next =>
      obtain ⟨_, handle, tool, _, _, rfl⟩ :=
        (silentOldNext_some_iff first accounting startup next _).mp hn
      simp only [settleOldExecutions, hn]
      rw [ih]
      simp only [Startup.executePublic, List.length_append, List.length_singleton]
      omega

theorem settleOldExecutions_available {Seed : Type*} (first : ℕ)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (fuel : ℕ) (seed : Seed) (startup : Startup I) :
    (settleOldExecutions first accounting rule fuel seed startup).1.availableTools =
      startup.availableTools := by
  induction fuel generalizing startup with
  | zero => rfl
  | succ fuel ih =>
    generalize hn : silentOldNext first accounting startup (rule seed startup.history) = next
    cases next with
    | none => simp only [settleOldExecutions, hn]
    | some next =>
      obtain ⟨_, handle, tool, _, _, rfl⟩ :=
        (silentOldNext_some_iff first accounting startup next _).mp hn
      simp only [settleOldExecutions, hn]
      rw [ih, executePublic_preserves_available]

section Measurable

variable {Seed : Type*} [MeasurableSpace Seed]

theorem measurable_silentOldNext (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hrule : MeasurableRule rule) :
    Measurable (fun sample : Seed × Startup I =>
      silentOldNext first accounting sample.2 (rule sample.1 sample.2.history)) := by
  have hh : Measurable (fun sample : Seed × Startup I => sample.2.history) :=
    (measurable_of_countable (fun startup : Startup I => startup.history)).comp measurable_snd
  have ha := hrule.comp (measurable_fst.prodMk hh)
  exact (measurable_of_countable (fun pair : Startup I × Action I =>
    silentOldNext first accounting pair.1 pair.2)).comp (measurable_snd.prodMk ha)

theorem measurable_settleOldExecutions (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hrule : MeasurableRule rule) (fuel : ℕ) :
    Measurable (fun sample : Seed × Startup I =>
      settleOldExecutions first accounting rule fuel sample.1 sample.2) := by
  induction fuel with
  | zero => exact measurable_snd.prodMk measurable_const
  | succ fuel ih =>
    let step : Seed × Startup I → Option (Startup I) := fun sample =>
      silentOldNext first accounting sample.2 (rule sample.1 sample.2.history)
    have hs : Measurable step := measurable_silentOldNext first accounting rule hrule
    let resumed : Seed × Startup I → Seed × Startup I := fun sample =>
      (sample.1, (step sample).getD sample.2)
    have hn : Measurable resumed := measurable_fst.prodMk
      ((measurable_of_countable (fun pair : Option (Startup I) × Startup I =>
        pair.1.getD pair.2)).comp (hs.prodMk measurable_snd))
    have htail : Measurable (fun sample =>
        ((settleOldExecutions first accounting rule fuel
          (resumed sample).1 (resumed sample).2).1,
          (settleOldExecutions first accounting rule fuel
            (resumed sample).1 (resumed sample).2).2 + 1)) :=
      (measurable_of_countable (fun result : Startup I × ℕ => (result.1, result.2 + 1))).comp
        (ih.comp hn)
    have hm : Measurable (fun sample : Seed × Startup I =>
        if step sample = none then (sample.2, 0) else
          ((settleOldExecutions first accounting rule fuel
            (resumed sample).1 (resumed sample).2).1,
            (settleOldExecutions first accounting rule fuel
              (resumed sample).1 (resumed sample).2).2 + 1)) :=
      Measurable.ite (hs (measurableSet_singleton none))
        (measurable_snd.prodMk measurable_const) htail
    convert hm using 1
    funext sample
    cases hn' : step sample <;> simp [settleOldExecutions, resumed, step] at hn' ⊢
    · rw [hn']
    · rw [hn']
      rfl

end Measurable

theorem settleOldExecutions_stops_of_count_lt {Seed : Type*} (first : ℕ)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (fuel : ℕ) (seed : Seed) (startup : Startup I)
    (hcount : (settleOldExecutions first accounting rule fuel seed startup).2 < fuel) :
    silentOldNext first accounting
      (settleOldExecutions first accounting rule fuel seed startup).1
      (rule seed (settleOldExecutions first accounting rule fuel seed startup).1.history) = none := by
  induction fuel generalizing startup with
  | zero => exact (Nat.not_lt_zero _ hcount).elim
  | succ fuel ih =>
    generalize hn : silentOldNext first accounting startup (rule seed startup.history) = next
    cases next with
    | none => simp only [settleOldExecutions, hn]
    | some next =>
      simp only [settleOldExecutions, hn] at hcount ⊢
      exact ih next (Nat.lt_of_succ_lt_succ hcount)

theorem settleOldExecutions_reviews {Seed : Type*} (first : ℕ)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (fuel : ℕ) (seed : Seed) (startup : Startup I) :
    (settleOldExecutions first accounting rule fuel seed startup).1.reviews = startup.reviews := by
  induction fuel generalizing startup with
  | zero => rfl
  | succ fuel ih =>
    generalize hn : silentOldNext first accounting startup (rule seed startup.history) = next
    cases next with
    | none => simp only [settleOldExecutions, hn]
    | some next =>
      obtain ⟨_, handle, tool, _, _, rfl⟩ :=
        (silentOldNext_some_iff first accounting startup next _).mp hn
      simp only [settleOldExecutions, hn]
      rw [ih, executePublic_preserves_reviews]

section ActualSimulation

variable {Seed : Type*}

/-- This preprocessing step is the exact public effect of the original LEGAL
native step, with all original deadline guards and failed-path ledger intact. -/
theorem silentOldNext_actual (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (first n : ℕ) (next : Startup I)
    (hn : silentOldNext first accounting (publicStartup (run input C mode accounting rule sample n))
      (rule sample.1 (run input C mode accounting rule sample n).history) = some next) :
    next = publicStartup (run input C mode accounting rule sample (n + 1)) := by
  obtain ⟨ha, handle, tool, haction, _, hnext⟩ :=
    (silentOldNext_some_iff first accounting _ next _).mp hn
  obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting rule hlegal sample n
  obtain ⟨s', hs⟩ := hlegal sample.1 _ _ m _ hp ha
  have hr := run_succ_of_step input C mode accounting rule sample n s' ha hs
  rw [haction] at hs
  cases hs
  rw [hr, publicStartup_execute]
  exact hnext

/-- Exact original-run time transport for the entire bounded public
preprocessing, not an abstract continuation oracle or assumed history transport. -/
theorem settleOldExecutions_actual (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (first fuel n : ℕ) :
    let result := settleOldExecutions first accounting rule fuel sample.1
      (publicStartup (run input C mode accounting rule sample n))
    result.1 = publicStartup (run input C mode accounting rule sample (n + result.2)) := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
    generalize hn : silentOldNext first accounting
      (publicStartup (run input C mode accounting rule sample n))
      (rule sample.1 (publicStartup (run input C mode accounting rule sample n)).history) = next
    cases next with
    | none => simp only [settleOldExecutions, hn, Nat.add_zero]
    | some next =>
      have hnext := silentOldNext_actual input C mode accounting rule hlegal sample first n next hn
      have ht := ih (n + 1)
      rw [← hnext] at ht
      simp only [settleOldExecutions, hn]
      rw [show n + ((settleOldExecutions first accounting rule fuel sample.1 next).2 + 1) =
        (n + 1) + (settleOldExecutions first accounting rule fuel sample.1 next).2 by omega]
      exact ht

/-- q+1 preprocessing fuel ALWAYS suffices on actual legal paths. Every
successful internal step consumes a distinct actual execution slot, so no
stopping-time, finite-expectation, or risk-control premise is required. -/
theorem settleOldExecutions_actual_stops (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (first n : ℕ) :
    let result := settleOldExecutions first accounting rule (I.toolCount + 1) sample.1
      (publicStartup (run input C mode accounting rule sample n))
    silentOldNext first accounting result.1 (rule sample.1 result.1.history) = none := by
  let start := publicStartup (run input C mode accounting rule sample n)
  let result := settleOldExecutions first accounting rule (I.toolCount + 1) sample.1 start
  have hr : result.1 = publicStartup (run input C mode accounting rule sample (n + result.2)) :=
    settleOldExecutions_actual input C mode accounting rule hlegal sample first (I.toolCount + 1) n
  have hlen : result.1.executions.length ≤ I.toolCount := by
    rw [hr]
    exact (run_actualCorrections_le input C mode accounting rule hlegal sample (n + result.2)).trans
      (min_le_right _ _)
  have hcount : result.1.executions.length = start.executions.length + result.2 :=
    settleOldExecutions_execution_count first accounting rule _ sample.1 start
  apply settleOldExecutions_stops_of_count_lt
  change result.2 < I.toolCount + 1
  omega

/-- A past execution is never simulated as though its actual deadline were
open: under a current-window deadline, such an original step is impossible. -/
theorem old_execution_impossible_current (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    (hC : C.execution = .currentWindow) {s s' : State I} (first : ℕ)
    (hcursor : first ≤ s.cursor) (handle : MismatchHandle I) (tool : I.Tool)
    (hold : handle.stage.val < first) :
    ¬ Step input C mode accounting tapes s (.execute handle tool) s' := by
  intro hs
  cases hs with
  | execute _ _ _ _ _ _ _ _ window _ =>
    have hw := window hC
    omega

/-- The whole internal preprocessing interval has exactly zero actual review
increment, on every original path. Earlier and later failed-path observations
remain in the original comparison charge. No finite expected bill is assumed. -/
theorem settleOldExecutions_observationIncrement_zero (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (first fuel n : ℕ) :
    let result := settleOldExecutions first accounting rule fuel sample.1
      (publicStartup (run input C mode accounting rule sample n))
    observationIncrement input (run input C mode accounting rule sample n)
      (run input C mode accounting rule sample (n + result.2)) = 0 := by
  let start := publicStartup (run input C mode accounting rule sample n)
  let result := settleOldExecutions first accounting rule fuel sample.1 start
  have hr : result.1 = publicStartup (run input C mode accounting rule sample (n + result.2)) :=
    settleOldExecutions_actual input C mode accounting rule hlegal sample first fuel n
  have hv : (run input C mode accounting rule sample (n + result.2)).ledger.reviews =
      (run input C mode accounting rule sample n).ledger.reviews := by
    have hh : result.1.reviews = start.reviews :=
      settleOldExecutions_reviews first accounting rule fuel sample.1 start
    rw [hr] at hh
    exact hh
  change observationIncrement input (run input C mode accounting rule sample n)
    (run input C mode accounting rule sample (n + result.2)) = 0
  simp only [observationIncrement, hv, tsub_self, ENat.toENNReal_zero, mul_zero, Finset.sum_const_zero]

end ActualSimulation

/-! Stage lowering and dynamic native handle rebinding. The serial is read
from the REAL suffix history, never obtained from a fixed clock offset. -/

def suffixStageOf (first : ℕ) (stage : I.Stage) (hfuture : first ≤ stage.val) :
    (I.freshSuffix first).Stage :=
  ⟨stage.val - first, by
    have hs := stage.isLt
    change stage.val - first < (I.freshSuffix first).stageCount
    rw [I.freshSuffix_stageCount]
    change stage.val < I.stageCount at hs
    omega⟩

@[simp] theorem freshStageLift_suffixStageOf (first : ℕ) (stage : I.Stage)
    (hfuture : first ≤ stage.val) :
    I.freshStageLift first (suffixStageOf first stage hfuture) = stage := by
  apply Fin.ext
  change first + (stage.val - first) = stage.val
  omega

def suffixHandleOf (first : ℕ) (history : List (VisibleEvent (I.freshSuffix first)))
    (handle : MismatchHandle I) (hfuture : first ≤ handle.stage.val) :
    MismatchHandle (I.freshSuffix first) :=
  ⟨suffixStageOf first handle.stage hfuture,
    historyWriteSerial history (suffixStageOf first handle.stage hfuture)⟩

def suffixActionOf (first : ℕ) (history : List (VisibleEvent (I.freshSuffix first))) :
    Action I → Option (Action (I.freshSuffix first))
  | .review stage => if h : first ≤ stage.val then some (.review (suffixStageOf first stage h)) else none
  | .write stage bit => if h : first ≤ stage.val then some (.write (suffixStageOf first stage h) bit) else none
  | .allocate handle tool => if h : first ≤ handle.stage.val then
      some (.allocate (suffixHandleOf first history handle h) tool) else none
  | .execute handle tool => if h : first ≤ handle.stage.val then
      some (.execute (suffixHandleOf first history handle h) tool) else none
  | .advance stage => if h : first ≤ stage.val then some (.advance (suffixStageOf first stage h)) else none
  | .stop => some .stop
  | .abandon => some .abandon

/-- Once all selected old executions have been simulated, every legal current
allocation action has a real suffix action. Old reviews/writes/advances and old
allocations are excluded by the original native guards, not by policy promises. -/
theorem suffixActionOf_exists_of_step (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    (hC : C.allocation = .currentWindow) (first : ℕ)
    (history : List (VisibleEvent (I.freshSuffix first))) {s s' : State I} {action : Action I}
    (hcursor : first ≤ s.cursor) (hs : Step input C mode accounting tapes s action s')
    (hsettled : oldExecutionRequest first action = none) :
    ∃ nextAction, suffixActionOf first history action = some nextAction := by
  cases hs with
  | review stage live _ _ =>
    have hf : first ≤ stage.val := live.2 ▸ hcursor
    exact ⟨.review (suffixStageOf first stage hf), by simp only [suffixActionOf, hf, ↓reduceDIte]⟩
  | write stage bit live _ _ =>
    have hf : first ≤ stage.val := live.2 ▸ hcursor
    exact ⟨.write (suffixStageOf first stage hf) bit, by simp only [suffixActionOf, hf, ↓reduceDIte]⟩
  | allocate handle tool _ _ _ _ _ window _ =>
    have hf : first ≤ handle.stage.val := window hC ▸ hcursor
    exact ⟨.allocate (suffixHandleOf first history handle hf) tool,
      by simp only [suffixActionOf, hf, ↓reduceDIte]⟩
  | execute handle tool _ _ _ _ _ _ _ _ =>
    have hf : first ≤ handle.stage.val := by
      by_contra h
      have hold := Nat.lt_of_not_ge h
      simp only [oldExecutionRequest, hold, ↓reduceIte] at hsettled
      cases hsettled
    exact ⟨.execute (suffixHandleOf first history handle hf) tool,
      by simp only [suffixActionOf, hf, ↓reduceDIte]⟩
  | advance stage live _ _ =>
    have hf : first ≤ stage.val := live.2 ▸ hcursor
    exact ⟨.advance (suffixStageOf first stage hf), by simp only [suffixActionOf, hf, ↓reduceDIte]⟩
  | stop | abandon => exact ⟨_, rfl⟩

/-- The serial in a rebound handle is the actual suffix native write serial.
The mismatch and report premises are the concrete public-ledger part of the
run relation still to be established by the suffix-response replay. -/
theorem suffixHandleOf_valid_of_prefix (input : StatisticalInput I) (first : ℕ)
    (C : Contract (I.freshSuffix first)) (mode : ResourceMode)
    (accounting : NormalAccounting (I.freshSuffix first)) {Seed : Type*}
    (rule : PolicyRule (I.freshSuffix first) Seed) (seed : Seed)
    (truth : (I.freshSuffix first).Stage → Bool) (tapes : ReviewTapes (input.freshSuffix first))
    {n : ℕ} {target : State (I.freshSuffix first)}
    (hp : Prefix (input.freshSuffix first) C mode accounting rule seed truth tapes n target)
    (source : State I) (handle : MismatchHandle I) (hf : first ≤ handle.stage.val)
    (hvalid : validHandle source handle)
    (hwritten : target.ledger.written (suffixStageOf first handle.stage hf) =
      source.ledger.written handle.stage)
    (htruth : target.ledger.truth (suffixStageOf first handle.stage hf) = source.ledger.truth handle.stage)
    (hreport : ∃ t, target.ledger.reportTime (suffixStageOf first handle.stage hf) = some t) :
    validHandle target (suffixHandleOf first target.history handle hf) := by
  refine ⟨?_, ?_, hreport⟩
  · change target.ledger.written (suffixStageOf first handle.stage hf) =
      some (!target.ledger.truth (suffixStageOf first handle.stage hf))
    rw [hwritten, htruth]
    exact hvalid.1
  · exact prefix_historyWriteSerial (input.freshSuffix first) C mode accounting rule seed truth tapes hp _

/-- UsesOnly inheritance against the genuine saved committed-tool set. The
original reached-allocation guard prevents reuse of EVERY old commitment,
including pending ones and paths on which the task has already failed. -/
theorem allocated_tool_available_at_saved_prefix (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting rule)
    (sample : Seed × input.World) (saved now : ℕ) (horder : saved ≤ now)
    (handle : MismatchHandle I) (tool : I.Tool) {s' : State I}
    (hs : Step input C mode accounting (worldTapes input sample.2)
      (run input C mode accounting rule sample now) (.allocate handle tool) s') :
    tool ∈ (publicStartup (run input C mode accounting rule sample saved)).availableTools := by
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ tool, ?_⟩
  intro hold
  have hused : tool ∈ committedTools (run input C mode accounting rule sample now) :=
    run_committedTools_monotone input C mode accounting rule hlegal sample horder hold
  exact step_allocate_fresh_tool input C mode accounting _ handle tool hs hused

def suffixEventOf (first : ℕ) (clock : ℕ)
    (history : List (VisibleEvent (I.freshSuffix first))) :
    VisibleEvent I → Option (VisibleEvent (I.freshSuffix first))
  | .observation stage symbol => if h : first ≤ stage.val then
      some (.observation (suffixStageOf first stage h) symbol) else none
  | .wrote stage bit _ => if h : first ≤ stage.val then
      some (.wrote (suffixStageOf first stage h) bit clock) else none
  | .report stage truth _ => if h : first ≤ stage.val then
      some (.report (suffixStageOf first stage h) truth clock) else none
  | .committed handle tool => if h : first ≤ handle.stage.val then
      some (.committed (suffixHandleOf first history handle h) tool) else none
  | .executed handle tool => if h : first ≤ handle.stage.val then
      some (.executed (suffixHandleOf first history handle h) tool) else none
  | .advanced stage => if h : first ≤ stage.val then
      some (.advanced (suffixStageOf first stage h)) else none
  | .stopped => some .stopped
  | .abandoned => some .abandoned

/-- Real early write/report responses commute with stage lowering and the
current REAL suffix clock. Only the visible report's truth is copied. -/
theorem suffixEventOf_writeResponses (C : Contract I)
    (hearly : C.reporting = .early) (first : ℕ) (source : State I)
    (target : State (I.freshSuffix first)) (stage : I.Stage) (hf : first ≤ stage.val) (bit : Bool)
    (htruth : target.ledger.truth (suffixStageOf first stage hf) = source.ledger.truth stage) :
    (writeResponses C source stage bit).filterMap (suffixEventOf first target.clock target.history) =
      writeResponses (currentRelaxedContract (I.freshSuffix first)) target (suffixStageOf first stage hf) bit := by
  simp only [writeResponses, hearly, currentRelaxedContract, ↓reduceIte,
    List.filterMap_append, List.filterMap_cons, List.filterMap_nil, suffixEventOf,
    hf, ↓reduceDIte, writeLedger, htruth]

/-- Total public next-action extraction after bounded old-execution simulation.
`startup` is the CURRENT original public cache. Reconstructing that cache from
the new suffix responses is a separate unfinished replay component: this is
not presented as a complete PolicyRule with a frozen initial cache. -/
def suffixActionAtPublicCache {Seed : Type*} (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (startup : Startup I)
    (history : List (VisibleEvent (I.freshSuffix first))) : Action (I.freshSuffix first) :=
  let cache := (settleOldExecutions first accounting rule (I.toolCount + 1) seed startup).1
  if cache.halted then .stop else
    (suffixActionOf first history (rule seed cache.history)).getD .abandon

section CacheExtraction

variable {Seed : Type*} [MeasurableSpace Seed]

theorem measurable_suffixActionAtPublicCache (first : ℕ) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hrule : MeasurableRule rule) :
    Measurable (fun sample : (Seed × Startup I) × List (VisibleEvent (I.freshSuffix first)) =>
      suffixActionAtPublicCache first accounting rule sample.1.1 sample.1.2 sample.2) := by
  let cache : (Seed × Startup I) × List (VisibleEvent (I.freshSuffix first)) → Startup I :=
    fun sample => (settleOldExecutions first accounting rule (I.toolCount + 1)
      sample.1.1 sample.1.2).1
  have hc : Measurable cache :=
    (measurable_settleOldExecutions first accounting rule hrule (I.toolCount + 1)).fst.comp measurable_fst
  have hh : Measurable (fun sample => (cache sample).history) :=
    (measurable_of_countable (fun startup : Startup I => startup.history)).comp hc
  have ha : Measurable (fun sample => rule sample.1.1 (cache sample).history) :=
    hrule.comp ((measurable_fst.comp measurable_fst).prodMk hh)
  exact (measurable_of_countable
    (fun data : Startup I × List (VisibleEvent (I.freshSuffix first)) × Action I =>
      if data.1.halted then .stop else (suffixActionOf first data.2.1 data.2.2).getD .abandon)).comp
        (hc.prodMk (measurable_snd.prodMk ha))

omit [MeasurableSpace Seed] in
/-- On every real legal active continuation the extractor's fallback abandon
is unreachable. Its returned action is the projection of an actual original
native step after q-bounded internal old executions. This is a real source
run/action theorem; it does not yet assert legality of the new target Step. -/
theorem suffixActionAtPublicCache_actual (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (hC : C.allocation = .currentWindow)
    (sample : Seed × input.World) (first n : ℕ)
    (history : List (VisibleEvent (I.freshSuffix first)))
    (hcursor : first ≤ (run input C mode accounting rule sample n).cursor)
    (hactive : (settleOldExecutions first accounting rule (I.toolCount + 1) sample.1
      (publicStartup (run input C mode accounting rule sample n))).1.halted = false) :
    let result := settleOldExecutions first accounting rule (I.toolCount + 1) sample.1
      (publicStartup (run input C mode accounting rule sample n))
    ∃ next : State I,
      Step input C mode accounting (worldTapes input sample.2)
        (run input C mode accounting rule sample (n + result.2))
        (rule sample.1 result.1.history) next ∧
      suffixActionOf first history (rule sample.1 result.1.history) =
        some (suffixActionAtPublicCache first accounting rule sample.1
          (publicStartup (run input C mode accounting rule sample n)) history) := by
  let start := publicStartup (run input C mode accounting rule sample n)
  let result := settleOldExecutions first accounting rule (I.toolCount + 1) sample.1 start
  have hr : result.1 = publicStartup (run input C mode accounting rule sample (n + result.2)) :=
    settleOldExecutions_actual input C mode accounting rule hlegal sample first _ n
  have ha : (run input C mode accounting rule sample (n + result.2)).halted = false := by
    change result.1.halted = false at hactive
    rw [hr] at hactive
    exact hactive
  obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting rule hlegal sample (n + result.2)
  obtain ⟨next, hs⟩ := hlegal sample.1 _ _ m _ hp ha
  have hnone : silentOldNext first accounting result.1 (rule sample.1 result.1.history) = none :=
    settleOldExecutions_actual_stops input C mode accounting rule hlegal sample first n
  have hreq : oldExecutionRequest first (rule sample.1 result.1.history) = none := by
    change result.1.halted = false at hactive
    simpa only [silentOldNext, hactive, Bool.false_eq_true, ↓reduceIte,
      Option.map_eq_none_iff] using hnone
  have hc : first ≤ (run input C mode accounting rule sample (n + result.2)).cursor :=
    hcursor.trans (run_cursor_monotone input C mode accounting rule hlegal sample (Nat.le_add_right n result.2))
  have hs' : Step input C mode accounting (worldTapes input sample.2)
      (run input C mode accounting rule sample (n + result.2))
      (rule sample.1 result.1.history) next := by
    rw [hr]
    exact hs
  obtain ⟨action, haction⟩ := suffixActionOf_exists_of_step input C mode accounting _ hC first history hc hs' hreq
  refine ⟨next, hs', ?_⟩
  change suffixActionOf first history (rule sample.1 result.1.history) =
    some (if result.1.halted then .stop else
      (suffixActionOf first history (rule sample.1 result.1.history)).getD .abandon)
  rw [hactive, haction]
  rfl

end CacheExtraction

end PaperProofs.Common.Native
