module

public import PaperProofs.Common.HealthyValue
public import PaperProofs.Common.NativeCausality
public import PaperProofs.Common.NativePartial
import Lean.Elab.Tactic.Omega

/-!
B09 workpad, bound to the frozen price-proofs.tex:57--114 and model.tex.

The fresh-prior comparison is stated at FIRST STAGE ENTRY. This is the
stage-entry meaning needed by the proof in price-proofs.tex:87--90. The literal
phrase "every healthy history" does not justify a fresh-prior lower bound
after reviews of the current stage have already been bought. No theorem below
identifies an intermediate posterior value with the fresh-suffix value.

`StageEntryHistoryPenaltyBridge` is the stronger ALLOCATION-ONLY analysis
comparison. If execution is current-window, an old wrong output that was
allocated but not executed before advance may already be permanent failure;
allocation alone does not certify a genuinely healthy continuation. The
comparison keeps such paths and charges their ORIGINAL eventual failure.
`DeadlineViableBefore` additionally requires actual timely old executions
when the contract requires them, and `HealthyStageEntryHistoryPenaltyBridge`
is the genuine healthy-entry statement. Only the specification projection
from the stronger bridge to the healthy one assumes the stronger bridge;
the operational, charge, and freshness helpers do not assume either bridge.

`Startup` contains public execution data only, including the original handle
serials and commitment/execution clocks. Its type has no hidden truth or tape
field. `restore` receives truth separately, and `restartRun` receives a fresh
world separately; neither is an extra policy-seed argument.

The first-entry bridge below is proved in `HistorySuffixBridge`, using the
actual suffix controller, all-path observation charges, success domination
and entry-event joint law. The helpers here do not assume it under another
name. The broader temporal reading is separately kept as the unproved
`AllHealthyHistoryPenaltyBridge` in `HealthyHistoryScope`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance}

/-- Public fields of a reached native state. In particular, there is no field
for the complete truth function or any unobserved review tape. -/
structure Startup (I : Instance) where
  written : I.Stage → Option Bool
  writeSerial : I.Stage → ℕ
  reportTime : I.Stage → Option ℕ
  advanceTime : I.Stage → Option ℕ
  reviews : I.Stage → ℕ∞
  normalCalls : ℕ∞
  commitments : List (Commitment I)
  executions : List (Execution I)
  finished : Bool
  abandoned : Bool
  cursor : ℕ
  clock : ℕ
  history : List (VisibleEvent I)
  halted : Bool
  deriving Countable

instance : MeasurableSpace (Startup I) := ⊤
instance : MeasurableSingletonClass (Startup I) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

instance : MeasurableSpace (Option (Startup I)) := ⊤
instance : MeasurableSingletonClass (Option (Startup I)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

def publicStartup (s : State I) : Startup I where
  written := s.ledger.written
  writeSerial := s.ledger.writeSerial
  reportTime := s.ledger.reportTime
  advanceTime := s.ledger.advanceTime
  reviews := s.ledger.reviews
  normalCalls := s.ledger.normalCalls
  commitments := s.ledger.commitments
  executions := s.ledger.executions
  finished := s.ledger.finished
  abandoned := s.ledger.abandoned
  cursor := s.cursor
  clock := s.clock
  history := s.history
  halted := s.halted

def Startup.restore (startup : Startup I) (truth : I.Stage → Bool) : State I where
  ledger := {
    truth := truth
    written := startup.written
    writeSerial := startup.writeSerial
    reportTime := startup.reportTime
    advanceTime := startup.advanceTime
    reviews := startup.reviews
    normalCalls := startup.normalCalls
    commitments := startup.commitments
    executions := startup.executions
    finished := startup.finished
    abandoned := startup.abandoned }
  cursor := startup.cursor
  clock := startup.clock
  history := startup.history
  halted := startup.halted

@[simp] theorem publicStartup_restore (startup : Startup I) (truth : I.Stage → Bool) :
    publicStartup (startup.restore truth) = startup := by
  cases startup
  rfl

@[simp] theorem restore_publicStartup (s : State I) :
    (publicStartup s).restore s.ledger.truth = s := rfl

@[simp] theorem publicStartup_retargetTruth (s : State I) (truth : I.Stage → Bool) :
    publicStartup (retargetTruth s truth) = publicStartup s := rfl

theorem restore_publicStartup_retarget (s : State I) (truth : I.Stage → Bool) :
    (publicStartup s).restore truth = retargetTruth s truth := rfl

/-- Allocation, rather than physical execution, determines unavailable tools. -/
def Startup.committedTools (startup : Startup I) : Finset I.Tool :=
  (startup.commitments.map (·.tool)).toFinset

def committedTools (s : State I) : Finset I.Tool := (publicStartup s).committedTools

def Startup.availableTools (startup : Startup I) : Finset I.Tool :=
  I.tools \ startup.committedTools

def pendingCommitment (s : State I) (a : Commitment I) : Prop :=
  a ∈ s.ledger.commitments ∧
    ¬ ∃ e ∈ s.ledger.executions, e.handle = a.handle ∧ e.tool = a.tool

theorem mem_committedTools (s : State I) (tool : I.Tool) :
    tool ∈ committedTools s ↔ ∃ a ∈ s.ledger.commitments, a.tool = tool := by
  simp only [committedTools, Startup.committedTools, publicStartup, List.mem_toFinset,
    List.mem_map]

theorem pending_tool_occupied {s : State I} {a : Commitment I}
    (h : pendingCommitment s a) : a.tool ∈ committedTools s :=
  (mem_committedTools s a.tool).mpr ⟨a, h.1, rfl⟩

theorem pending_tool_not_available {s : State I} {a : Commitment I}
    (h : pendingCommitment s a) : a.tool ∉ (publicStartup s).availableTools := by
  intro hm
  exact (Finset.mem_sdiff.mp hm).2 (pending_tool_occupied h)

theorem execute_preserves_committedTools (accounting : NormalAccounting I) (s : State I)
    (handle : MismatchHandle I) (tool : I.Tool) :
    committedTools (record accounting s (.execute handle tool) [.executed handle tool]
      (executeLedger s handle tool) s.cursor false) = committedTools s := rfl

theorem step_commitments_subset (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s s' : State I} {action : Action I}
    (h : Step input C mode accounting tapes s action s') :
    s.ledger.commitments ⊆ s'.ledger.commitments := by
  cases h with
  | write i bit _ _ _ =>
    simp only [record, reportedWriteLedger]
    split_ifs <;> exact List.Subset.refl _
  | allocate => exact List.subset_append_left _ _
  | review | execute | advance | stop | abandon => exact List.Subset.refl _

theorem step_committedTools_subset (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s s' : State I} {action : Action I}
    (h : Step input C mode accounting tapes s action s') :
    committedTools s ⊆ committedTools s' := by
  intro tool ht
  obtain ⟨a, ha, rfl⟩ := (mem_committedTools s tool).mp ht
  exact (mem_committedTools s' a.tool).mpr
    ⟨a, step_commitments_subset input C mode accounting tapes h ha, rfl⟩

theorem step_allocate_fresh_tool (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s s' : State I} (handle : MismatchHandle I) (tool : I.Tool)
    (h : Step input C mode accounting tapes s (.allocate handle tool) s') :
    tool ∉ committedTools s := by
  cases h with
  | allocate _ _ _ _ _ unused _ _ _ =>
    intro ht
    obtain ⟨a, ha, heq⟩ := (mem_committedTools s tool).mp ht
    exact unused a ha heq

/-- A pending old obligation cannot be reassigned, even before it executes. -/
theorem pending_tool_cannot_reallocate (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s s' : State I} {a : Commitment I} (hpending : pendingCommitment s a)
    (handle : MismatchHandle I) :
    ¬ Step input C mode accounting tapes s (.allocate handle a.tool) s' := by
  intro hs
  exact step_allocate_fresh_tool input C mode accounting tapes handle a.tool hs
    (pending_tool_occupied hpending)

/-- Commitments persist along the actual run, including after permanent
failure; the guard concerns every reached allocation, not successful paths. -/
theorem run_committedTools_monotone (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting policy)
    (sample : Seed × input.World) :
    Monotone (fun n => committedTools (run input C mode accounting policy sample n)) := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hh : (run input C mode accounting policy sample n).halted = true
  · rw [run_succ_of_halted input C mode accounting policy sample n hh]
  · have ha := Bool.eq_false_iff.mpr hh
    obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting policy hlegal sample n
    obtain ⟨s', hs⟩ := hlegal sample.1 _ _ m _ hp ha
    rw [run_succ_of_step input C mode accounting policy sample n s' ha hs]
    exact step_committedTools_subset input C mode accounting _ hs

theorem pending_tool_occupied_forever (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting policy)
    (sample : Seed × input.World) (n k : ℕ) (a : Commitment I)
    (hpending : pendingCommitment (run input C mode accounting policy sample n) a) :
    a.tool ∈ committedTools (run input C mode accounting policy sample (n + k)) :=
  run_committedTools_monotone input C mode accounting policy hlegal sample
    (Nat.le_add_right n k) (pending_tool_occupied hpending)

section Restart

variable {Seed : Type*}

/-- Same native interpreter, resumed from public startup data and a separately
supplied truth/tape world. Original clocks and history are retained. -/
noncomputable def restartRun (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (seed : Seed) (startup : Startup I) (world : input.World) : ℕ → State I
  | 0 => startup.restore (input.truthAt world)
  | k + 1 =>
    let s := restartRun input C mode accounting policy seed startup world k
    nextFromFrontier input C mode accounting s (policy seed s.history) (frontierOf input s world)

/-- Exact visible-ledger restart; this is not yet the stage/tool suffix
projection required for the healthy-value lower bound. -/
theorem restartRun_eq_actual_suffix (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (sample : Seed × input.World)
    (n k : ℕ) :
    restartRun input C mode accounting policy sample.1
      (publicStartup (run input C mode accounting policy sample n)) sample.2 k =
        run input C mode accounting policy sample (n + k) := by
  induction k with
  | zero =>
    simp only [restartRun, Nat.add_zero]
    rw [← run_truth input C mode accounting policy hlegal sample n]
    exact restore_publicStartup _
  | succ k ih =>
    simp only [restartRun, ih, run]
    rfl

end Restart

section ActualCharge

variable {Seed : Type*}

/-- All actual observation increments after a fixed interpreter clock. No
success restriction, finite-cost assumption, or subtraction of two infinite
total bills is used. Each finite-clock starting counter is native-finite. -/
noncomputable def observationIncrement (input : StatisticalInput I)
    (before after : State I) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal (input.fees.observation i : ℝ) *
    ((after.ledger.reviews i - before.ledger.reviews i : ℕ∞) : ℝ≥0∞)

noncomputable def futureObservationBill (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (n : ℕ) (sample : Seed × input.World) : ℝ≥0∞ :=
  ⨆ k, observationIncrement input (run input C mode accounting policy sample n)
    (run input C mode accounting policy sample (n + k))

/-- Exactly one penalty for the original eventual-failure event, including
nontermination, abandonment, and unexecuted old commitments. -/
noncomputable def historyComparisonCharge (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (n : ℕ) (penalty : ℝ≥0∞) (sample : Seed × input.World) : ℝ≥0∞ := by
  classical
  exact futureObservationBill input C mode accounting policy n sample +
    if runSuccess input C mode accounting policy sample then 0 else penalty

theorem futureObservationBill_zero (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (sample : Seed × input.World) :
    futureObservationBill input C mode accounting policy 0 sample =
      runObservationBill input C mode accounting policy sample := by
  simp only [futureObservationBill, observationIncrement, runObservationBill,
    Nat.zero_add, run, initial, tsub_zero, Ledger.observationBill]

/-- Halting retains the preceding ledger, while buying no further reviews. -/
theorem futureObservationBill_of_halted (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (sample : Seed × input.World) (n : ℕ)
    (hh : (run input C mode accounting policy sample n).halted = true) :
    futureObservationBill input C mode accounting policy n sample = 0 := by
  unfold futureObservationBill
  simp only [run_after_halt input C mode accounting policy sample n hh,
    observationIncrement, tsub_self, ENat.toENNReal_zero, mul_zero, Finset.sum_const_zero,
    iSup_const]

theorem original_failure_penalty_le_comparison (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (sample : Seed × input.World) (n : ℕ) (penalty : ℝ≥0∞)
    (hfailure : ¬runSuccess input C mode accounting policy sample) :
    penalty ≤ historyComparisonCharge input C mode accounting policy n penalty sample := by
  classical
  simp only [historyComparisonCharge, hfailure, ↓reduceIte]
  exact le_add_self

theorem observations_le_comparison (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (sample : Seed × input.World) (n : ℕ) (penalty : ℝ≥0∞) :
    futureObservationBill input C mode accounting policy n sample ≤
      historyComparisonCharge input C mode accounting policy n penalty sample :=
  le_self_add

variable [MeasurableSpace Seed]

private theorem measurable_observationIncrement (input : StatisticalInput I) :
    Measurable (fun pair : State I × State I =>
      observationIncrement input pair.1 pair.2) := measurable_of_countable _

attribute [local irreducible] observationIncrement

private theorem measurable_incrementSup {Ω : Type*} [MeasurableSpace Ω]
    (input : StatisticalInput I) (before : Ω → State I) (after : ℕ → Ω → State I)
    (hb : Measurable before) (ha : ∀ k, Measurable (after k)) :
    Measurable (fun sample => ⨆ k : ℕ, observationIncrement input (before sample) (after k sample)) := by
  refine Measurable.iSup fun k => ?_
  exact (measurable_observationIncrement input).comp (hb.prodMk (ha k))

theorem measurable_futureObservationBill (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hpolicy : MeasurableRule policy) (n : ℕ) :
    Measurable (futureObservationBill input C mode accounting policy n) := by
  exact measurable_incrementSup input
    (fun sample => run input C mode accounting policy sample n)
    (fun k sample => run input C mode accounting policy sample (n + k))
    (measurable_run input C mode accounting policy hpolicy n)
    (fun k => measurable_run input C mode accounting policy hpolicy (n + k))

theorem measurable_historyComparisonCharge (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hpolicy : MeasurableRule policy) (n : ℕ) (penalty : ℝ≥0∞) :
    Measurable (historyComparisonCharge input C mode accounting policy n penalty) := by
  classical
  exact (measurable_futureObservationBill input C mode accounting policy hpolicy n).add
    (Measurable.ite (measurableSet_runSuccess input C mode accounting policy hpolicy)
      measurable_const measurable_const)

end ActualCharge

section Statement

variable {Seed : Type*}

/-- The FIRST clock with this cursor. A posterior history later in the same
stage does not satisfy this predicate. -/
def FirstEntryAt (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (next n : ℕ) (sample : Seed × input.World) : Prop :=
  (run input C mode accounting policy sample n).cursor = next ∧
    ∀ k < n, (run input C mode accounting policy sample k).cursor ≠ next

/-- Allocation-only analysis condition: earlier erroneous outputs have real,
timely allocations. Execution is deliberately not required, and committed
tools remain occupied. With current-window execution this condition includes
already-failed paths that missed execution before advance; it must not be
read as full deadline viability. Their original eventual failure is retained
in `historyComparisonCharge`. -/
def AllocationHealthyBefore (s : State I) (next : ℕ) : Prop :=
  s.halted = false ∧ s.ledger.abandoned = false ∧
    ∀ i : I.Stage, i.val < next →
      s.ledger.written i = some (s.ledger.truth i) ∨
        ∃ a ∈ s.ledger.commitments, a.handle.stage = i ∧
          a.tool ∈ I.eligible i ∧
          ∃ t, s.ledger.advanceTime i = some t ∧ a.atTime < t

/-- Genuine health before a new stage: allocation obligations are resolved,
and a current-window execution contract has already received every required
actual correction before advance. Under terminal-barrier execution, pending
old commitments remain permitted and their tools remain occupied. -/
def DeadlineViableBefore (C : Contract I) (s : State I) (next : ℕ) : Prop :=
  AllocationHealthyBefore s next ∧
    (C.execution = .currentWindow → ∀ i : I.Stage, i.val < next →
      s.ledger.written i = some (s.ledger.truth i) ∨
        ∃ e ∈ s.ledger.executions, e.handle.stage = i ∧
          ∃ t, s.ledger.advanceTime i = some t ∧ e.atTime < t)

theorem DeadlineViableBefore.allocationHealthy {C : Contract I} {s : State I} {next : ℕ}
    (h : DeadlineViableBefore C s next) : AllocationHealthyBefore s next := h.1

theorem DeadlineViableBefore.current_execution {C : Contract I} {s : State I} {next : ℕ}
    (h : DeadlineViableBefore C s next) (hC : C.execution = .currentWindow)
    (i : I.Stage) (hi : i.val < next) :
    s.ledger.written i = some (s.ledger.truth i) ∨
      ∃ e ∈ s.ledger.executions, e.handle.stage = i ∧
        ∃ t, s.ledger.advanceTime i = some t ∧ e.atTime < t := h.2 hC i hi

/-- Fixed public snapshot intersected with an arbitrary measurable private
seed gate; neither the event nor Startup is a conditional-probability oracle. -/
def historyGate (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (n : ℕ) (startup : Startup I) (gate : Set Seed) : Set (Seed × input.World) :=
  {sample | publicStartup (run input C mode accounting policy sample n) = startup} ∩
    Prod.fst ⁻¹' gate

variable [MeasurableSpace Seed]

theorem measurableSet_historyGate (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hpolicy : MeasurableRule policy) (n : ℕ) (startup : Startup I)
    (gate : Set Seed) (hgate : MeasurableSet gate) :
    MeasurableSet (historyGate input C mode accounting policy n startup gate) := by
  exact ((measurable_run input C mode accounting policy hpolicy n)
    (MeasurableSpace.measurableSet_top
      (s := {s : State I | publicStartup s = startup}))).inter
        (measurable_fst hgate)

end Statement

/-- Allocation-only analysis bridge at the stage-entry
interpretation required by the frozen proof's freshness sentence. It also
covers old allocated but unexecuted wrong outputs after their current-window
execution deadline has passed. Such paths are not declared healthy or repaired:
the ORIGINAL eventual-failure term in `historyComparisonCharge` pays for them.
The genuinely healthy statement is `HealthyStageEntryHistoryPenaltyBridge`.
It quantifies over arbitrary seed universes and measurable seed gates. It is
a mass inequality, so null events and infinite bills/penalties are included
without regular conditional laws.

`HistorySuffixBridge.stageEntryHistoryPenaltyBridge` proves this statement
from actual native continuations, including old pending execution simulation,
original-failure domination, the complete charge identity and the independent
suffix world law. No operational, charge or freshness helper assumes this
proposition. The wider current-posterior scope is not inferred from it. -/
def StageEntryHistoryPenaltyBridge (input : StatisticalInput I) : Prop :=
  ∀ (C : Contract I), C.IsCurrentAllocation →
    ∀ (accounting : NormalAccounting I) (Seed : Type*) (m : MeasurableSpace Seed),
      letI : MeasurableSpace Seed := m
      ∀ (policy : Policy input C .native accounting Seed) (ν : Measure Seed),
        IsProbabilityMeasure ν →
        ∀ (next n : ℕ) (_hnext : next ≤ I.stageCount) (startup : Startup I)
          (gate : Set Seed), MeasurableSet gate →
          (∀ sample ∈ historyGate input C .native accounting policy.rule n startup gate,
            FirstEntryAt input C .native accounting policy.rule next n sample ∧
              AllocationHealthyBefore (run input C .native accounting policy.rule sample n) next) →
          ∀ penalty : ℝ≥0∞,
            input.healthyPenalty next startup.availableTools penalty *
                input.seededWorldLaw ν
                  (historyGate input C .native accounting policy.rule n startup gate) ≤
              ∫⁻ sample in historyGate input C .native accounting policy.rule n startup gate,
                historyComparisonCharge input C .native accounting policy.rule n penalty sample
                  ∂input.seededWorldLaw ν

/-- The original genuinely healthy first-entry bridge, with actual execution
obligations respected whenever execution has a current-window deadline.
Pending old executions are allowed exactly when that deadline permits them.
This follows from the proved allocation-only bridge by `healthy_projection`,
as instantiated in `HistorySuffixBridge`. -/
def HealthyStageEntryHistoryPenaltyBridge (input : StatisticalInput I) : Prop :=
  ∀ (C : Contract I), C.IsCurrentAllocation →
    ∀ (accounting : NormalAccounting I) (Seed : Type*) (m : MeasurableSpace Seed),
      letI : MeasurableSpace Seed := m
      ∀ (policy : Policy input C .native accounting Seed) (ν : Measure Seed),
        IsProbabilityMeasure ν →
        ∀ (next n : ℕ) (_hnext : next ≤ I.stageCount) (startup : Startup I)
          (gate : Set Seed), MeasurableSet gate →
          (∀ sample ∈ historyGate input C .native accounting policy.rule n startup gate,
            FirstEntryAt input C .native accounting policy.rule next n sample ∧
              DeadlineViableBefore C (run input C .native accounting policy.rule sample n) next) →
          ∀ penalty : ℝ≥0∞,
            input.healthyPenalty next startup.availableTools penalty *
                input.seededWorldLaw ν
                  (historyGate input C .native accounting policy.rule n startup gate) ≤
              ∫⁻ sample in historyGate input C .native accounting policy.rule n startup gate,
                historyComparisonCharge input C .native accounting policy.rule n penalty sample
                  ∂input.seededWorldLaw ν

universe uBridge

/-- Direct restriction of the stronger analysis statement to genuine healthy
entries. This is only a specification implication, not a proof of either
bridge or a hypothesis of the still-missing suffix-controller extraction. -/
theorem StageEntryHistoryPenaltyBridge.healthy_projection (input : StatisticalInput I)
    (hbridge : StageEntryHistoryPenaltyBridge.{uBridge} input) :
    HealthyStageEntryHistoryPenaltyBridge.{uBridge} input := by
  intro C hC accounting Seed m
  let : MeasurableSpace Seed := m
  intro policy ν hν next n hnext startup gate hgate hhealthy penalty
  apply hbridge C hC accounting Seed m policy ν hν next n hnext startup gate hgate ?_ penalty
  intro sample hsample
  obtain ⟨hentry, hviable⟩ := hhealthy sample hsample
  exact ⟨hentry, hviable.allocationHealthy⟩

section BoundaryCases

variable {Seed : Type*} [MeasurableSpace Seed]

theorem history_bridge_null_event (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed) (ν : Measure Seed)
    (next n : ℕ) (startup : Startup I) (gate : Set Seed) (penalty : ℝ≥0∞)
    (hzero : input.seededWorldLaw ν
      (historyGate input C .native accounting policy n startup gate) = 0) :
    input.healthyPenalty next startup.availableTools penalty *
        input.seededWorldLaw ν (historyGate input C .native accounting policy n startup gate) ≤
      ∫⁻ sample in historyGate input C .native accounting policy n startup gate,
        historyComparisonCharge input C .native accounting policy n penalty sample
          ∂input.seededWorldLaw ν := by
  rw [hzero, mul_zero]
  exact zero_le

theorem history_bridge_terminal (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed) (ν : Measure Seed)
    (next n : ℕ) (hterminal : I.stageCount ≤ next) (startup : Startup I)
    (gate : Set Seed) (penalty : ℝ≥0∞) :
    input.healthyPenalty next startup.availableTools penalty *
        input.seededWorldLaw ν (historyGate input C .native accounting policy n startup gate) ≤
      ∫⁻ sample in historyGate input C .native accounting policy n startup gate,
        historyComparisonCharge input C .native accounting policy n penalty sample
          ∂input.seededWorldLaw ν := by
  rw [input.healthyPenalty_terminal next hterminal, zero_mul]
  exact zero_le

end BoundaryCases

section EntryFrame

variable {Seed : Type*}

theorem firstEntryAt_strictly_before (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (sample : Seed × input.World)
    (next n : ℕ) (hentry : FirstEntryAt input C mode accounting policy next n sample) :
    ∀ k < n, (run input C mode accounting policy sample k).cursor < next := by
  intro k hk
  have hle := run_cursor_monotone input C mode accounting policy hlegal sample hk.le
  change (run input C mode accounting policy sample k).cursor ≤
    (run input C mode accounting policy sample n).cursor at hle
  rw [hentry.1] at hle
  exact lt_of_le_of_ne hle (hentry.2 k hk)

/-- The complete public startup at an entry is unchanged if all as-yet-unborn
facts and tapes are replaced. No full State.truth is packed into Startup. -/
theorem firstEntryAt_public_transport (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (seed : Seed)
    (world world' : input.World) (next : I.Stage) (n : ℕ)
    (hpast : ∀ i : I.Stage, i.val < next.val → world' i = world i)
    (hentry : FirstEntryAt input C mode accounting policy next.val n (seed, world)) :
    FirstEntryAt input C mode accounting policy next.val n (seed, world') ∧
      publicStartup (run input C mode accounting policy (seed, world') n) =
        publicStartup (run input C mode accounting policy (seed, world) n) := by
  have hbefore := firstEntryAt_strictly_before input C mode accounting policy hlegal
    (seed, world) next.val n hentry
  have heq := run_retarget_of_before input C mode accounting policy hlegal
    seed world world' next hpast n hbefore
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [heq]
    exact hentry.1
  · intro k hk
    have heqk := run_retarget_of_before input C mode accounting policy hlegal seed world world'
      next hpast k (fun j hj => hbefore j (hj.trans hk))
    rw [heqk]
    exact hentry.2 k hk
  · rw [heq, publicStartup_retargetTruth]

/-- A fixed-clock entry record. `none` retains paths with no first entry at
this clock; the record never tests eventual success. -/
noncomputable def entryStartupAt (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (next : I.Stage) (n : ℕ) (sample : Seed × input.World) : Option (Startup I) := by
  classical
  exact if FirstEntryAt input C mode accounting policy next.val n sample then
    some (publicStartup (run input C mode accounting policy sample n)) else none

theorem entryStartupAt_eq_of_past (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting policy) (seed : Seed)
    (world world' : input.World) (next : I.Stage) (n : ℕ)
    (hpast : ∀ i : I.Stage, i.val < next.val → world' i = world i) :
    entryStartupAt input C mode accounting policy next n (seed, world') =
      entryStartupAt input C mode accounting policy next n (seed, world) := by
  classical
  by_cases he : FirstEntryAt input C mode accounting policy next.val n (seed, world)
  · obtain ⟨he', hs⟩ := firstEntryAt_public_transport input C mode accounting policy hlegal
      seed world world' next n hpast he
    simp only [entryStartupAt, he, he', ↓reduceIte, hs]
  · have he' : ¬ FirstEntryAt input C mode accounting policy next.val n (seed, world') := by
      intro h
      exact he (firstEntryAt_public_transport input C mode accounting policy hlegal
        seed world' world next n (fun i hi => (hpast i hi).symm) h).1
    simp only [entryStartupAt, he, he', ↓reduceIte]

variable [MeasurableSpace Seed]

theorem measurableSet_firstEntryAt (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hpolicy : MeasurableRule policy) (next n : ℕ) :
    MeasurableSet {sample | FirstEntryAt input C mode accounting policy next n sample} := by
  have hc (k : ℕ) : MeasurableSet {sample : Seed × input.World |
      (run input C mode accounting policy sample k).cursor = next} :=
    (measurable_run input C mode accounting policy hpolicy k)
      (MeasurableSpace.measurableSet_top (s := {s : State I | s.cursor = next}))
  have heq : {sample | FirstEntryAt input C mode accounting policy next n sample} =
      {sample | (run input C mode accounting policy sample n).cursor = next} ∩
        ⋂ k : ℕ, {sample | k < n →
          (run input C mode accounting policy sample k).cursor ≠ next} := by
    ext sample
    simp only [FirstEntryAt, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [heq]
  refine (hc n).inter (MeasurableSet.iInter fun k => ?_)
  by_cases hk : k < n
  · have hs : {sample : Seed × input.World | k < n →
        (run input C mode accounting policy sample k).cursor ≠ next} =
        {sample | (run input C mode accounting policy sample k).cursor = next}ᶜ := by
      ext sample
      simp [hk]
    rw [hs]
    exact (hc k).compl
  · simp only [hk, false_implies, Set.ofPred_true]
    exact MeasurableSet.univ

theorem measurable_entryStartupAt (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hpolicy : MeasurableRule policy) (next : I.Stage) (n : ℕ) :
    Measurable (entryStartupAt input C mode accounting policy next n) := by
  classical
  exact Measurable.ite (measurableSet_firstEntryAt input C mode accounting policy hpolicy next.val n)
    ((measurable_of_countable (fun s : State I => some (publicStartup s))).comp
      (measurable_run input C mode accounting policy hpolicy n)) measurable_const

/-- The factorization is constructed using a fixed arbitrary completion,
whose future values are erased again by the actual-run transport theorem. -/
theorem entryStartupAt_factorization (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (next : I.Stage) (n : ℕ) :
    ∃ record : Seed × input.PastWorld next → Option (Startup I),
      Measurable record ∧ ∀ sample : Seed × input.World,
        entryStartupAt input C mode accounting policy.rule next n sample =
          record (input.preBirthView next sample) := by
  let complete : Seed × input.PastWorld next → Seed × input.World :=
    fun sample => (sample.1, completePastWorld input next sample.2)
  have hm : Measurable complete :=
    measurable_fst.prodMk ((measurable_completePastWorld input next).comp measurable_snd)
  refine ⟨fun sample => entryStartupAt input C mode accounting policy.rule next n (complete sample),
    (measurable_entryStartupAt input C mode accounting policy.rule policy.measurable_rule next n).comp hm, ?_⟩
  rintro ⟨seed, world⟩
  exact (entryStartupAt_eq_of_past input C mode accounting policy.rule policy.legal seed world
    (completePastWorld input next (fun i => world i.val)) next n
      (fun i hi => completePastWorld_apply_past input next (fun i => world i.val) i hi)).symm

/-- The seed stays in the joint conditioning record: arbitrary seed gates
cannot be justified by independence of the public history alone. -/
noncomputable def entrySeedStartupAt (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (next : I.Stage) (n : ℕ) (sample : Seed × input.World) : Seed × Option (Startup I) :=
  (sample.1, entryStartupAt input C mode accounting policy next n sample)

theorem measurable_entrySeedStartupAt (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (hpolicy : MeasurableRule policy) (next : I.Stage) (n : ℕ) :
    Measurable (entrySeedStartupAt input C mode accounting policy next n) :=
  measurable_fst.prodMk (measurable_entryStartupAt input C mode accounting policy hpolicy next n)

theorem entrySeedStartupAt_independent_next (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (next : I.Stage) (n : ℕ) :
    ProbabilityTheory.IndepFun (entrySeedStartupAt input C mode accounting policy.rule next n)
      (fun sample : Seed × input.World => sample.2 next) (input.seededWorldLaw ν) := by
  obtain ⟨record, hrecord, hpointwise⟩ :=
    entryStartupAt_factorization input C mode accounting policy next n
  let joint : Seed × input.PastWorld next → Seed × Option (Startup I) :=
    fun sample => (sample.1, record sample)
  have hm : Measurable joint := measurable_fst.prodMk hrecord
  have heq : entrySeedStartupAt input C mode accounting policy.rule next n =
      fun sample => joint (input.preBirthView next sample) := by
    funext sample
    simp only [entrySeedStartupAt, joint, StatisticalInput.preBirthView, hpointwise sample]
  rw [heq]
  exact input.preBirthRecord_independent_next ν next joint hm

end EntryFrame

/-! Full unborn-world freshness, without choosing or revealing a future
realization as part of Startup. This keeps the original stage indices; it is
not the reference-controller suffix renumbering. -/

abbrev UnbornWorld (input : StatisticalInput I) (next : I.Stage) :=
  ∀ i : {i : I.Stage // next.val ≤ i.val}, input.StageSample i.val

def unbornView (input : StatisticalInput I) (next : I.Stage)
    (world : input.World) : UnbornWorld input next := fun i => world i.val

theorem measurable_unbornView (input : StatisticalInput I) (next : I.Stage) :
    Measurable (unbornView input next) :=
  measurable_pi_iff.mpr fun i => measurable_pi_apply i.val

theorem pastWorld_independent_unborn (input : StatisticalInput I) (next : I.Stage) :
    ProbabilityTheory.IndepFun (fun world : input.World =>
        fun i : {i : I.Stage // i.val < next.val} => world i.val)
      (unbornView input next) input.worldLaw := by
  have hd : Disjoint {i : I.Stage | i.val < next.val} {i : I.Stage | next.val ≤ i.val} := by
    apply Set.disjoint_left.mpr
    intro i hi hj
    exact Nat.not_lt_of_ge hj hi
  exact (input.worldLaw_independent_stages).indepFun_set
    {i : I.Stage | i.val < next.val} {i : I.Stage | next.val ≤ i.val} hd
      (fun i => measurable_pi_apply i)

section UnbornFreshness

variable {Seed : Type*} [MeasurableSpace Seed]

theorem seededWorldLaw_unbornView (input : StatisticalInput I) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (next : I.Stage) :
    (input.seededWorldLaw ν).map (fun sample => unbornView input next sample.2) =
      input.worldLaw.map (unbornView input next) := by
  change (input.seededWorldLaw ν).map (unbornView input next ∘ Prod.snd) = _
  rw [← Measure.map_map (measurable_unbornView input next) measurable_snd,
    input.seededWorldLaw_world ν]

/-- The private seed and all old hidden data jointly remain independent of
the ENTIRE fresh suffix, rather than only the next current bit. -/
theorem preBirthView_independent_unborn (input : StatisticalInput I) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (next : I.Stage) :
    ProbabilityTheory.IndepFun (input.preBirthView (Seed := Seed) next)
      (fun sample : Seed × input.World => unbornView input next sample.2)
        (input.seededWorldLaw ν) := by
  let past : input.World → input.PastWorld next := fun world i => world i.val
  let future := unbornView input next
  have hp : Measurable past := measurable_pi_iff.mpr fun i => measurable_pi_apply i.val
  have hf : Measurable future := measurable_unbornView input next
  have hfuture : Measurable (fun sample : Seed × input.World => future sample.2) :=
    hf.comp measurable_snd
  have hw : input.worldLaw.map (fun world => (past world, future world)) =
      (input.worldLaw.map past).prod (input.worldLaw.map future) :=
    (pastWorld_independent_unborn input next).map_prod_eq_prod_map_map hp.aemeasurable hf.aemeasurable
  have hs : (input.seededWorldLaw ν).map
      (fun sample => (sample.1, (past sample.2, future sample.2))) =
      ν.prod ((input.worldLaw.map past).prod (input.worldLaw.map future)) := by
    calc
      _ = ν.prod (input.worldLaw.map (fun world => (past world, future world))) := by
        have hmap : Prod.map (id : Seed → Seed)
            (fun world : input.World => (past world, future world)) =
            (fun sample : Seed × input.World =>
              (sample.1, (past sample.2, future sample.2))) := by
          funext sample
          rfl
        unfold StatisticalInput.seededWorldLaw
        rw [← hmap]
        simpa only [Measure.map_id] using
          (Measure.map_prod_map ν input.worldLaw measurable_id (hp.prodMk hf)).symm
      _ = _ := by rw [hw]
  apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    (input.measurable_preBirthView next).aemeasurable hfuture.aemeasurable).mpr
  rw [input.seededWorldLaw_preBirthView, seededWorldLaw_unbornView]
  apply (MeasurableEquiv.prodAssoc :
    (Seed × input.PastWorld next) × UnbornWorld input next ≃ᵐ
      Seed × input.PastWorld next × UnbornWorld input next).map_measurableEquiv_injective
  rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable
    ((input.measurable_preBirthView next).prodMk hfuture), Measure.prodAssoc_prod]
  exact hs

/-- Includes arbitrary measurable functions of the private seed; no
regular conditional probability/disintegration is used. -/
theorem entrySeedStartupAt_independent_unborn (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (next : I.Stage) (n : ℕ) :
    ProbabilityTheory.IndepFun (entrySeedStartupAt input C mode accounting policy.rule next n)
      (fun sample : Seed × input.World => unbornView input next sample.2)
        (input.seededWorldLaw ν) := by
  obtain ⟨record, hrecord, hpointwise⟩ :=
    entryStartupAt_factorization input C mode accounting policy next n
  let joint : Seed × input.PastWorld next → Seed × Option (Startup I) :=
    fun sample => (sample.1, record sample)
  have hm : Measurable joint := measurable_fst.prodMk hrecord
  have heq : entrySeedStartupAt input C mode accounting policy.rule next n =
      fun sample => joint (input.preBirthView next sample) := by
    funext sample
    simp only [entrySeedStartupAt, joint, StatisticalInput.preBirthView, hpointwise sample]
  rw [heq]
  exact (preBirthView_independent_unborn input ν next).comp hm measurable_id

theorem entrySeedStartupAt_jointUnbornLaw (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (next : I.Stage) (n : ℕ) :
    (input.seededWorldLaw ν).map (fun sample =>
        (entrySeedStartupAt input C mode accounting policy.rule next n sample,
          unbornView input next sample.2)) =
      ((input.seededWorldLaw ν).map
        (entrySeedStartupAt input C mode accounting policy.rule next n)).prod
          (input.worldLaw.map (unbornView input next)) := by
  have hind := entrySeedStartupAt_independent_unborn input C mode accounting policy ν next n
  have hm := measurable_entrySeedStartupAt input C mode accounting policy.rule
    policy.measurable_rule next n
  have hf : Measurable (fun sample : Seed × input.World => unbornView input next sample.2) :=
    (measurable_unbornView input next).comp measurable_snd
  rw [hind.map_prod_eq_prod_map_map hm.aemeasurable hf.aemeasurable,
    seededWorldLaw_unbornView]

/-- Exact mass factorization for a public entry snapshot intersected with an
arbitrary measurable seed gate, against any event of the complete unborn
truth/tape world. This includes zero mass and uses no division by that mass. -/
theorem entry_snapshot_seedGate_unborn_mass (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (policy : Policy input C mode accounting Seed) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (next : I.Stage) (n : ℕ) (startup : Startup I)
    (gate : Set Seed) (hgate : MeasurableSet gate) (futureEvent : Set (UnbornWorld input next))
    (hfutureEvent : MeasurableSet futureEvent) :
    input.seededWorldLaw ν
        ((entrySeedStartupAt input C mode accounting policy.rule next n) ⁻¹'
          (gate ×ˢ {some startup}) ∩
          (fun sample : Seed × input.World => unbornView input next sample.2) ⁻¹' futureEvent) =
      input.seededWorldLaw ν
          ((entrySeedStartupAt input C mode accounting policy.rule next n) ⁻¹'
            (gate ×ˢ {some startup})) *
        (input.worldLaw.map (unbornView input next)) futureEvent := by
  have hind := entrySeedStartupAt_independent_unborn input C mode accounting policy ν next n
  rw [hind.measure_inter_preimage_eq_mul (gate ×ˢ {some startup}) futureEvent
    (hgate.prod (measurableSet_singleton _)) hfutureEvent]
  congr 1
  have hm : Measurable (fun sample : Seed × input.World => unbornView input next sample.2) :=
    (measurable_unbornView input next).comp measurable_snd
  rw [← Measure.map_apply hm hfutureEvent, seededWorldLaw_unbornView]

end UnbornFreshness

end PaperProofs.Common.Native
