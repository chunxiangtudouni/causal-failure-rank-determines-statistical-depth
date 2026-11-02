module

public import PaperProofs.Paid.PDROC_CalibratedSignature_002
public import PaperProofs.Common.NativeHeadContinuation
public import PaperProofs.Paid.PDLower_BlindCapacity_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC.CalibratedSignature

variable {I : Instance} {Seed : Type*}

theorem step_executions_subset (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {state next : State I} {action : Action I}
    (step : Step input C mode accounting tapes state action next) :
    ∀ execution ∈ state.ledger.executions, execution ∈ next.ledger.executions := by
  cases step with
  | write =>
      simp only [record, reportedWriteLedger]
      split_ifs <;> exact fun _ member => member
  | execute =>
      intro execution member
      exact List.mem_append.mpr (Or.inl member)
  | review | allocate | advance | stop | abandon => exact fun _ member => member

theorem run_executions_mono (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (legal : LegalRule input C mode accounting rule) (sample : Seed × input.World) :
    Monotone (fun clock => {execution : Execution I |
      execution ∈ (run input C mode accounting rule sample clock).ledger.executions}) := by
  apply monotone_nat_of_le_succ
  intro clock
  by_cases halted : (run input C mode accounting rule sample clock).halted = true
  · rw [run_succ_of_halted input C mode accounting rule sample clock halted]
  · have active : (run input C mode accounting rule sample clock).halted = false := Bool.eq_false_iff.mpr halted
    obtain ⟨n, _before, path⟩ := run_has_prefix input C mode accounting rule legal sample clock
    obtain ⟨next, step⟩ := legal sample.1 (input.truthAt sample.2) (worldTapes input sample.2)
      n _ path active
    rw [run_succ_of_step input C mode accounting rule sample clock next active step]
    exact step_executions_subset input C mode accounting _ step

theorem exists_written_iff_of_halted (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (legal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (clock : ℕ) (halted : (run input C mode accounting rule sample clock).halted = true)
    (stage : I.Stage) (bit : Bool) :
    (∃ n, (run input C mode accounting rule sample n).ledger.written stage = some bit) ↔
      (run input C mode accounting rule sample clock).ledger.written stage = some bit := by
  constructor
  · rintro ⟨n, written⟩
    have persistent := run_written_some_after input C mode accounting rule legal sample n clock stage bit written
    rw [Nat.add_comm n clock, run_after_halt input C mode accounting rule sample clock halted n] at persistent
    exact persistent
  · exact fun written => ⟨clock, written⟩

theorem exists_execution_iff_of_halted (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (legal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (clock : ℕ) (halted : (run input C mode accounting rule sample clock).halted = true)
    (predicate : Execution I → Prop) :
    (∃ n, ∃ execution ∈ (run input C mode accounting rule sample n).ledger.executions, predicate execution) ↔
      ∃ execution ∈ (run input C mode accounting rule sample clock).ledger.executions, predicate execution := by
  constructor
  · rintro ⟨n, execution, member, satisfies⟩
    have persistent := run_executions_mono input C mode accounting rule legal sample
      (Nat.le_add_right n clock) member
    change execution ∈ (run input C mode accounting rule sample (n + clock)).ledger.executions at persistent
    rw [Nat.add_comm n clock, run_after_halt input C mode accounting rule sample clock halted n] at persistent
    exact ⟨execution, persistent, satisfies⟩
  · exact fun ⟨execution, member, satisfies⟩ => ⟨clock, execution, member, satisfies⟩

section Paid

theorem eventualFlag_writtenTruth_of_halted (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (legal : LegalRule (P.input fee hfee) C.val mode accounting rule)
    (sample : Seed × (P.input fee hfee).World) (clock : ℕ)
    (halted : (run (P.input fee hfee) C.val mode accounting rule sample clock).halted = true)
    (stage : P.sharedInstance.Stage) (transform : Bool → Bool) :
    P.eventualFlag fee hfee C mode accounting rule
        (fun state => state.ledger.written stage = some (transform (state.ledger.truth stage))) sample =
      decide ((run (P.input fee hfee) C.val mode accounting rule sample clock).ledger.written stage =
        some (transform ((run (P.input fee hfee) C.val mode accounting rule sample clock).ledger.truth stage))) := by
  classical
  unfold Parameters.eventualFlag
  congr 1
  simp only [run_truth (P.input fee hfee) C.val mode accounting rule legal sample]
  exact propext (exists_written_iff_of_halted (P.input fee hfee) C.val mode accounting rule legal sample
    clock halted stage (transform ((P.input fee hfee).truthAt sample.2 stage)))

noncomputable def terminalExecutionSignature (P : Parameters) (C : P.PaymentContract)
    (ledger : Ledger P.sharedInstance) : P.ExecutionSignature := by
  classical
  exact (fun stage => decide (ledger.written stage = some (ledger.truth stage)),
    fun stage => decide (ledger.written stage = some (!ledger.truth stage)),
    (fun stage tool => decide (∃ execution ∈ ledger.executions,
      execution.handle.stage = stage ∧ execution.tool = tool)),
    decide (¬ ledger.success C.val))

/-- Eventual write flags and physical stage/tool flags are exactly the
terminal ledger flags once this actual run halts. Earlier executions and
writes are retained; unvisited stages are not assigned guessed outcomes. -/
theorem executionSignature_eq_of_halted (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (legal : LegalRule (P.input fee hfee) C.val mode accounting rule)
    (sample : Seed × (P.input fee hfee).World) (clock : ℕ)
    (halted : (run (P.input fee hfee) C.val mode accounting rule sample clock).halted = true) :
    P.executionSignature fee hfee C mode accounting rule sample =
      terminalExecutionSignature P C (run (P.input fee hfee) C.val mode accounting rule sample clock).ledger := by
  classical
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · funext stage
    exact eventualFlag_writtenTruth_of_halted P fee hfee C mode accounting rule legal sample clock halted stage id
  · funext stage
    exact eventualFlag_writtenTruth_of_halted P fee hfee C mode accounting rule legal sample clock halted stage Bool.not
  · funext stage tool
    change decide (∃ n, ∃ execution ∈ (run (P.input fee hfee) C.val mode accounting rule sample n).ledger.executions,
      execution.handle.stage = stage ∧ execution.tool = tool) =
      decide (∃ execution ∈ (run (P.input fee hfee) C.val mode accounting rule sample clock).ledger.executions,
        execution.handle.stage = stage ∧ execution.tool = tool)
    exact decide_eq_decide.mpr (exists_execution_iff_of_halted (P.input fee hfee) C.val mode accounting rule legal sample
      clock halted (fun execution => execution.handle.stage = stage ∧ execution.tool = tool))
  · change decide (¬ runSuccess (P.input fee hfee) C.val mode accounting rule sample) =
      decide (¬ (run (P.input fee hfee) C.val mode accounting rule sample clock).ledger.success C.val)
    exact decide_eq_decide.mpr (not_congr
      (PDLower.runSuccess_iff_success_of_halted (P.input fee hfee) C.val mode accounting rule sample clock halted))

end Paid

end PDROC.CalibratedSignature
