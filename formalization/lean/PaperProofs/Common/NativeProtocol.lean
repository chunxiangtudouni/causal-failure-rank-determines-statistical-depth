module

public import PaperProofs.Common.Input
public import Mathlib.Data.List.OfFn
public import Mathlib.Tactic.DeriveCountable

/-!
The deterministic native protocol from model.tex:4--55.

The policy receives only its private seed and the existing VisibleEvent history.
Truth and review tapes are system inputs, never extra policy arguments. Allocation
and execution have separate transitions, and failed obligations do not disable
later legal actions. In particular, decline/advance is permitted and can fail the
task; the protocol does not restrict the comparator to successful paths.

`NormalAccounting` is declared native call accounting on already-visible actions
and responses. Reviews and genuine executions each contribute their separate one
call. No resource certificate, probability guarantee, or ledger-invariant theorem
is inserted as a field or as a postcondition of a transition.
-/

@[expose] public section

namespace PaperProofs.Common.Native

open scoped ENNReal

variable {I : Instance}

deriving instance DecidableEq for Commitment, Execution, Action, VisibleEvent
deriving instance Countable for MismatchHandle, Commitment, Execution, Action, VisibleEvent, Ledger

structure State (I : Instance) where
  ledger : Ledger I
  cursor : ℕ
  clock : ℕ
  history : List (VisibleEvent I)
  halted : Bool
  deriving Countable

abbrev ReviewTapes (input : StatisticalInput I) :=
  (i : I.Stage) → (input.experiment i).Tape

/-- Native normal-call accounting cannot inspect hidden future facts or tapes. -/
abbrev NormalAccounting (I : Instance) :=
  List (VisibleEvent I) → Action I → List (VisibleEvent I) → ℕ

inductive ResourceMode where
  | native
  | uncapped
  deriving DecidableEq

def withinResources (C : Contract I) (mode : ResourceMode) (L : Ledger I) : Prop :=
  mode = .uncapped ∨ L.obeysCaps C

def allWritten (L : Ledger I) : Prop := ∀ i, L.written i ≠ none

def liveStage (s : State I) (i : I.Stage) : Prop :=
  s.halted = false ∧ s.cursor = i.val

def validHandle (s : State I) (h : MismatchHandle I) : Prop :=
  s.ledger.written h.stage = some (!s.ledger.truth h.stage) ∧
    h.writeSerial = s.ledger.writeSerial h.stage ∧
    ∃ t, s.ledger.reportTime h.stage = some t

/-- A terminal deadline permits earlier assignment; it does not prohibit it. -/
def allocationOpen (C : Contract I) (s : State I) (i : I.Stage) : Prop :=
  C.allocation = .currentWindow → s.cursor = i.val

def executionOpen (C : Contract I) (s : State I) (i : I.Stage) : Prop :=
  C.execution = .currentWindow → s.cursor = i.val

def initial (truth : I.Stage → Bool) : State I where
  ledger := {
    truth := truth
    written := fun _ ↦ none
    writeSerial := fun _ ↦ 0
    reportTime := fun _ ↦ none
    advanceTime := fun _ ↦ none
    reviews := fun _ ↦ 0
    normalCalls := 0
    commitments := []
    executions := []
    finished := false
    abandoned := false
  }
  cursor := 0
  clock := 0
  history := []
  halted := false

/-- Append actual responses and the original interface's additional normal calls. -/
def record (accounting : NormalAccounting I) (s : State I) (action : Action I)
    (responses : List (VisibleEvent I)) (L : Ledger I) (cursor : ℕ) (halted : Bool) : State I where
  ledger := { L with normalCalls := L.normalCalls + accounting s.history action responses }
  cursor := cursor
  clock := s.clock + 1
  history := s.history ++ responses
  halted := halted

def reviewLedger (s : State I) (i : I.Stage) : Ledger I :=
  { s.ledger with reviews := Function.update s.ledger.reviews i (s.ledger.reviews i + 1) }

def writeLedger (s : State I) (i : I.Stage) (bit : Bool) : Ledger I :=
  { s.ledger with
    written := Function.update s.ledger.written i (some bit)
    writeSerial := Function.update s.ledger.writeSerial i s.clock }

def reportAll (L : Ledger I) : List (VisibleEvent I) :=
  List.ofFn fun i : I.Stage ↦ .report i (L.truth i) (L.writeSerial i)

noncomputable def reportedWriteLedger (C : Contract I) (s : State I) (i : I.Stage)
    (bit : Bool) : Ledger I := by
  classical
  let L := writeLedger s i bit
  exact if C.reporting = .early then
    { L with reportTime := Function.update L.reportTime i (some s.clock) }
  else if allWritten L then { L with reportTime := fun _ ↦ some s.clock } else L

noncomputable def writeResponses (C : Contract I) (s : State I) (i : I.Stage)
    (bit : Bool) : List (VisibleEvent I) := by
  classical
  let L := writeLedger s i bit
  exact [.wrote i bit s.clock] ++
    if C.reporting = .early then [.report i (L.truth i) s.clock]
    else if allWritten L then reportAll L else []

theorem reportedWriteLedger_truth (C : Contract I) (s : State I) (i : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s i bit).truth = s.ledger.truth := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

def allocateLedger (s : State I) (h : MismatchHandle I) (r : I.Tool) : Ledger I :=
  { s.ledger with commitments := s.ledger.commitments ++ [⟨h, r, s.clock⟩] }

def executeLedger (s : State I) (h : MismatchHandle I) (r : I.Tool) : Ledger I :=
  { s.ledger with executions := s.ledger.executions ++ [⟨h, r, s.clock⟩] }

def advanceLedger (s : State I) (i : I.Stage) : Ledger I :=
  { s.ledger with advanceTime := Function.update s.ledger.advanceTime i (some s.clock) }

noncomputable def stopState (s : State I) (abandon : Bool) : State I := by
  classical
  exact {
    ledger := { s.ledger with finished := decide (allWritten s.ledger), abandoned := abandon }
    cursor := s.cursor
    clock := s.clock + 1
    history := s.history ++ [if abandon then .abandoned else .stopped]
    halted := true
  }

/-- The actual protocol, not a performance specification. There is deliberately no
guard requiring previously written outputs to be correct or all obligations to be
repairable. This permits permanent failure followed by continued legal spending. -/
inductive Step (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input) :
    State I → Action I → State I → Prop where
  | review (s : State I) (i : I.Stage)
      (live : liveStage s i) (port : s.ledger.written i = none)
      (resources : withinResources C mode (record accounting s (.review i)
        [.observation i (tapes i (s.ledger.reviews i).toNat).val]
        (reviewLedger s i) s.cursor false).ledger) :
      Step input C mode accounting tapes s (.review i)
        (record accounting s (.review i)
          [.observation i (tapes i (s.ledger.reviews i).toNat).val]
          (reviewLedger s i) s.cursor false)
  | write (s : State I) (i : I.Stage) (bit : Bool)
      (live : liveStage s i) (port : s.ledger.written i = none)
      (resources : withinResources C mode (record accounting s (.write i bit)
        (writeResponses C s i bit) (reportedWriteLedger C s i bit) s.cursor false).ledger) :
      Step input C mode accounting tapes s (.write i bit)
        (record accounting s (.write i bit) (writeResponses C s i bit)
          (reportedWriteLedger C s i bit) s.cursor false)
  | allocate (s : State I) (h : MismatchHandle I) (r : I.Tool)
      (active : s.halted = false) (handle : validHandle s h)
      (compatible : r ∈ I.eligible h.stage)
      (unused : ∀ a ∈ s.ledger.commitments, a.tool ≠ r)
      (unallocated : ∀ a ∈ s.ledger.commitments, a.handle.stage ≠ h.stage)
      (window : allocationOpen C s h.stage)
      (resources : withinResources C mode (record accounting s (.allocate h r)
        [.committed h r] (allocateLedger s h r) s.cursor false).ledger) :
      Step input C mode accounting tapes s (.allocate h r)
        (record accounting s (.allocate h r) [.committed h r]
          (allocateLedger s h r) s.cursor false)
  | execute (s : State I) (h : MismatchHandle I) (r : I.Tool)
      (active : s.halted = false) (handle : validHandle s h)
      (compatible : r ∈ I.eligible h.stage)
      (committed : ∃ a ∈ s.ledger.commitments, a.handle = h ∧ a.tool = r)
      (unused : ∀ e ∈ s.ledger.executions, e.tool ≠ r)
      (uncorrected : ∀ e ∈ s.ledger.executions, e.handle.stage ≠ h.stage)
      (window : executionOpen C s h.stage)
      (resources : withinResources C mode (record accounting s (.execute h r)
        [.executed h r] (executeLedger s h r) s.cursor false).ledger) :
      Step input C mode accounting tapes s (.execute h r)
        (record accounting s (.execute h r) [.executed h r]
          (executeLedger s h r) s.cursor false)
  | advance (s : State I) (i : I.Stage)
      (live : liveStage s i) (written : s.ledger.written i ≠ none)
      (resources : withinResources C mode (record accounting s (.advance i)
        [.advanced i] (advanceLedger s i) (s.cursor + 1) false).ledger) :
      Step input C mode accounting tapes s (.advance i)
        (record accounting s (.advance i) [.advanced i]
          (advanceLedger s i) (s.cursor + 1) false)
  | stop (s : State I) (active : s.halted = false) :
      Step input C mode accounting tapes s .stop (stopState s false)
  | abandon (s : State I) (active : s.halted = false) :
      Step input C mode accounting tapes s .abandon (stopState s true)

/-- A finite actual prefix follows the same policy rule at every reached history. -/
inductive Prefix (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) {Seed : Type*} (policy : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) :
    ℕ → State I → Prop where
  | initial : Prefix input C mode accounting policy seed truth tapes 0 (initial truth)
  | next {n : ℕ} {s s' : State I}
      (earlier : Prefix input C mode accounting policy seed truth tapes n s)
      (step : Step input C mode accounting tapes s (policy seed s.history) s') :
      Prefix input C mode accounting policy seed truth tapes (n + 1) s'

/-- Native legality requires a legal next action on every reachable nonhalted path,
not merely almost surely and not only on eventually successful histories. -/
def LegalRule (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) {Seed : Type*} (policy : PolicyRule I Seed) : Prop :=
  ∀ (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) (n : ℕ) (s : State I),
    Prefix input C mode accounting policy seed truth tapes n s → s.halted = false →
      ∃ s', Step input C mode accounting tapes s (policy seed s.history) s'

theorem step_deterministic (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s s₁ s₂ : State I} {action : Action I}
    (h₁ : Step input C mode accounting tapes s action s₁)
    (h₂ : Step input C mode accounting tapes s action s₂) : s₁ = s₂ := by
  cases h₁ <;> cases h₂ <;> rfl

theorem step_truth_unchanged (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s s' : State I} {action : Action I}
    (h : Step input C mode accounting tapes s action s') : s'.ledger.truth = s.ledger.truth := by
  cases h <;> simp [record, reviewLedger, reportedWriteLedger_truth,
    allocateLedger, executeLedger, advanceLedger, stopState]

theorem prefix_truth (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) {Seed : Type*} (policy : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I}
    (h : Prefix input C mode accounting policy seed truth tapes n s) : s.ledger.truth = truth := by
  induction h with
  | initial => rfl
  | next _ step ih => exact (step_truth_unchanged input C mode accounting tapes step).trans ih

end PaperProofs.Common.Native
