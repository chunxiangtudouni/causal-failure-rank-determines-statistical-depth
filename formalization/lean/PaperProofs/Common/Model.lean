module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Shared finite inputs and actual-execution accounting for the frozen manuscript.
Source: submission_2026-10-27/manuscript/sections/model.tex.

This module does not yet supply the stochastic operational semantics of a legal
policy. `LedgerWellFormed` records the accounting invariants only. In particular,
it is not a substitute for the freshness, filtration or nonanticipation proofs.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace PaperProofs.Common

structure Instance where
  toolCount : ℕ
  compatibility : List (Finset (Fin toolCount))

abbrev Instance.Tool (I : Instance) := Fin I.toolCount
abbrev Instance.Stage (I : Instance) := Fin I.compatibility.length

def Instance.stageCount (I : Instance) : ℕ := I.compatibility.length

def Instance.eligible (I : Instance) (i : I.Stage) : Finset I.Tool :=
  I.compatibility.get i

def Instance.tools (I : Instance) : Finset I.Tool := Finset.univ

inductive Reporting where
  | early
  | late
  deriving DecidableEq

inductive Deadline where
  | currentWindow
  | terminalBarrier
  deriving DecidableEq

/-- Allocation and physical execution deadlines are separate contractual data. -/
structure Contract (I : Instance) where
  reporting : Reporting
  allocation : Deadline
  execution : Deadline
  reviewQuota : I.Stage → ℕ
  totalCallCap : ℕ
  normalCallBound : ℕ

def Contract.IsCurrentAllocation {I : Instance} (C : Contract I) : Prop :=
  C.reporting = .early ∧ C.allocation = .currentWindow

def Contract.IsCurrentPayment {I : Instance} (C : Contract I) : Prop :=
  C.IsCurrentAllocation ∧ C.execution = .currentWindow

def Contract.IsEarlyRetained {I : Instance} (C : Contract I) : Prop :=
  C.reporting = .early ∧ C.allocation = .terminalBarrier ∧
    C.execution = .terminalBarrier

def Contract.IsLateRetained {I : Instance} (C : Contract I) : Prop :=
  C.reporting = .late ∧ C.allocation = .terminalBarrier ∧
    C.execution = .terminalBarrier

theorem Contract.currentPayment_implies_currentAllocation {I : Instance}
    {C : Contract I} (h : C.IsCurrentPayment) : C.IsCurrentAllocation := h.1

/-- The same slots and tools can have current allocation with deferred execution. -/
theorem Contract.currentAllocation_allows_deferredExecution (I : Instance)
    (quota : I.Stage → ℕ) (cap normal : ℕ) :
    let C : Contract I := ⟨.early, .currentWindow, .terminalBarrier, quota, cap, normal⟩
    C.IsCurrentAllocation ∧ ¬ C.IsCurrentPayment := by
  simp [Contract.IsCurrentAllocation, Contract.IsCurrentPayment]

structure Fees (I : Instance) where
  observation : I.Stage → ℚ
  observation_pos : ∀ i, 0 < observation i
  correction : I.Stage → I.Tool → ℚ
  correction_nonneg : ∀ i r, 0 ≤ correction i r

/-- Serial binds a mismatch handle to the actual ordinary write, not to a guess. -/
structure MismatchHandle (I : Instance) where
  stage : I.Stage
  writeSerial : ℕ
  deriving DecidableEq

structure Commitment (I : Instance) where
  handle : MismatchHandle I
  tool : I.Tool
  atTime : ℕ

structure Execution (I : Instance) where
  handle : MismatchHandle I
  tool : I.Tool
  atTime : ℕ

inductive Action (I : Instance) where
  | review (i : I.Stage)
  | write (i : I.Stage) (bit : Bool)
  | allocate (handle : MismatchHandle I) (tool : I.Tool)
  | execute (handle : MismatchHandle I) (tool : I.Tool)
  | advance (i : I.Stage)
  | stop
  | abandon

inductive VisibleEvent (I : Instance) where
  | observation (i : I.Stage) (symbol : ℕ)
  | wrote (i : I.Stage) (bit : Bool) (serial : ℕ)
  | report (i : I.Stage) (truth : Bool) (serial : ℕ)
  | committed (handle : MismatchHandle I) (tool : I.Tool)
  | executed (handle : MismatchHandle I) (tool : I.Tool)
  | advanced (i : I.Stage)
  | stopped
  | abandoned

/-- Private seed is not a visible-history field. No MAP or Markov restriction. -/
abbrev PolicyRule (I : Instance) (Seed : Type*) :=
  Seed → List (VisibleEvent I) → Action I

/-- Counts can be infinite in relaxed comparisons; completed corrections are finite. -/
structure Ledger (I : Instance) where
  truth : I.Stage → Bool
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

/-- Necessary bookkeeping invariants; full native legality is a separate obligation. -/
structure LedgerWellFormed {I : Instance} (L : Ledger I) : Prop where
  commitment_tools : (L.commitments.map (·.tool)).Nodup
  commitment_stages : (L.commitments.map (·.handle.stage)).Nodup
  execution_tools : (L.executions.map (·.tool)).Nodup
  execution_stages : (L.executions.map (·.handle.stage)).Nodup
  compatible : ∀ e ∈ L.executions, e.tool ∈ I.eligible e.handle.stage
  genuine : ∀ e ∈ L.executions,
    L.written e.handle.stage = some (!L.truth e.handle.stage) ∧
    e.handle.writeSerial = L.writeSerial e.handle.stage
  reported : ∀ a ∈ L.commitments,
    ∃ t, L.reportTime a.handle.stage = some t ∧ t ≤ a.atTime
  backed : ∀ e ∈ L.executions, ∃ a ∈ L.commitments,
    a.handle = e.handle ∧ a.tool = e.tool ∧ a.atTime ≤ e.atTime

def Ledger.windowObligations {I : Instance} (L : Ledger I) (C : Contract I) : Prop :=
  ∀ i t, L.advanceTime i = some t → L.written i = some (!L.truth i) →
    (C.allocation = .currentWindow →
      ∃ a ∈ L.commitments, a.handle.stage = i ∧ a.atTime < t) ∧
    (C.execution = .currentWindow →
      ∃ e ∈ L.executions, e.handle.stage = i ∧ e.atTime < t)

def Ledger.success {I : Instance} (L : Ledger I) (C : Contract I) : Prop :=
  L.finished = true ∧ L.abandoned = false ∧ L.windowObligations C ∧
    ∀ i, L.written i = some (L.truth i) ∨
      ∃ e ∈ L.executions, e.handle.stage = i

def Ledger.failure {I : Instance} (L : Ledger I) (C : Contract I) : Prop :=
  ¬ L.success C

noncomputable def Ledger.observationBill {I : Instance} (L : Ledger I)
    (F : Fees I) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal (F.observation i : ℝ) * (L.reviews i : ℝ≥0∞)

/-- Commitments are deliberately absent: only actual executions are billed. -/
noncomputable def Ledger.correctionBill {I : Instance} (L : Ledger I)
    (F : Fees I) : ℝ≥0∞ :=
  (L.executions.map fun e ↦ ENNReal.ofReal (F.correction e.handle.stage e.tool : ℝ)).sum

noncomputable def Ledger.actualBill {I : Instance} (L : Ledger I)
    (F : Fees I) : ℝ≥0∞ := L.observationBill F + L.correctionBill F

noncomputable def Ledger.totalCalls {I : Instance} (L : Ledger I) : ℕ∞ :=
  L.normalCalls + ∑ i, L.reviews i + L.executions.length

def Ledger.obeysCaps {I : Instance} (L : Ledger I) (C : Contract I) : Prop :=
  (∀ i, L.reviews i ≤ (C.reviewQuota i : ℕ∞)) ∧
    L.totalCalls ≤ (C.totalCallCap : ℕ∞)

theorem Ledger.execution_count_le {I : Instance} {L : Ledger I}
    (h : LedgerWellFormed L) : L.executions.length ≤ min I.stageCount I.toolCount := by
  apply le_min
  · have hc := h.execution_stages.length_le_card
    simpa [Instance.Stage, Instance.stageCount] using hc
  · have hc := h.execution_tools.length_le_card
    simpa [Instance.Tool] using hc

theorem Ledger.pending_commitment_not_billed {I : Instance} (L : Ledger I)
    (F : Fees I) (a : Commitment I) :
    ({ L with commitments := a :: L.commitments }).correctionBill F =
      L.correctionBill F := rfl

theorem Ledger.observationBill_le_actualBill {I : Instance} (L : Ledger I)
    (F : Fees I) : L.observationBill F ≤ L.actualBill F :=
  le_self_add

end PaperProofs.Common
