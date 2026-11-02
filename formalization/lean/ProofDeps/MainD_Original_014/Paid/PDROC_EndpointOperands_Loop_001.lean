module

public import Paid.RootD27Endpoint_CalleeSpace_036

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver
open RootD27.Endpoint
open PDLower.CalibrationCompute (linearExecute)

/- Interface draft only: no compilation or cache admission has occurred.
The frozen functional program and endpoint/cache formulas are unchanged.
Each node retains the source boundary rather than asserting that an
intermediate counter/power/header already has its next boundary value. -/

/-- Exactly the original row body before its final backwards jump. -/
def rowStraightCode : List Instruction :=
  castRowCode ++ headerCode rowCommands ++ pairStoreCode ++ advanceCode

/-- A genuine successful literal prefix, including the complete body,
or its one actual fetched control step. This is execution evidence, not
a postulated numerical guarantee for a trace. -/
def ControlledPrefix (program : Program) (input : List Cell)
    (code : List Instruction) (before : State) (target : ℕ) (state : State) : Prop :=
  (∃ count ≤ code.length,
    linearExecute input (code.take count) before = some state) ∨
  (∃ middle, linearExecute input code before = some middle ∧
    step program input middle = some state ∧ state = {middle with pc := target})

inductive Phase where
  | test | body | restore

def phaseCode : Phase → List Instruction
  | .test => rowCompareCode
  | .body => rowStraightCode
  | .restore => returnPrefixCode

def phaseEntryPC (testPC bodyPC exitPC : ℕ) : Phase → ℕ
  | .test => testPC
  | .body => bodyPC
  | .restore => exitPC

def phaseTarget (P : Parameters) (returnPC testPC bodyPC exitPC m : ℕ) : Phase → ℕ
  | .test => if m ≤ P.certificate.M then bodyPC else exitPC
  | .body => testPC
  | .restore => returnPC

/-- The REAL source of a local block. In particular m is its source
counter even while the actual prefix updates slot7 before slot8. -/
structure Boundary (P : Parameters) (base E returnPC testPC bodyPC exitPC : ℕ)
    (phase : Phase) (m : ℕ) (values : ℕ → Cell) (before : State) : Prop where
  position : before.pc = phaseEntryPC testPC bodyPC exitPC phase
  header : Header before base values
  fresh : before.register .fresh = .natural base
  invariant : EndpointValues P E returnPC m values
  stored : StoredCache P E m before
  rowBound : m ≤ P.certificate.M + 1
  eligible : match phase with
    | .test => True
    | .body => m ≤ P.certificate.M
    | .restore => m = P.certificate.M + 1

/-- Canonical loop history carries the concrete caller and the literal
source of every local prefix. It places no numerical bound on arbitrary
old scratch, unwritten suffix cells, caller output or old live memory. -/
inductive LoopProvenance (P : Parameters) (program : Program) (input : List Cell)
    (base E returnPC testPC bodyPC exitPC : ℕ) (caller : State) : State → Prop where
  | initial : LoopProvenance P program input base E returnPC testPC bodyPC exitPC caller caller
  | block {before state : State} {phase : Phase} {m : ℕ} {values : ℕ → Cell}
      (previous : LoopProvenance P program input base E returnPC testPC bodyPC exitPC caller before)
      (entry : Boundary P base E returnPC testPC bodyPC exitPC phase m values before)
      (actual : ControlledPrefix program input (phaseCode phase) before
        (phaseTarget P returnPC testPC bodyPC exitPC m phase) state) :
      LoopProvenance P program input base E returnPC testPC bodyPC exitPC caller state

/-- A local prefix closure for proof-side composition. Final numerical
instantiation will discharge this from actual block PrefixSafe lemmas;
it is not an extra premise of the original callee or final numeric API. -/
def LoopClosed (P : Parameters) (program : Program) (input : List Cell)
    (base E returnPC testPC bodyPC exitPC : ℕ) (Good : State → Prop) : Prop :=
  ∀ (phase : Phase) (m : ℕ) (values : ℕ → Cell) (before state : State),
    Boundary P base E returnPC testPC bodyPC exitPC phase m values before →
    Good before →
    ControlledPrefix program input (phaseCode phase) before
      (phaseTarget P returnPC testPC bodyPC exitPC m phase) state → Good state

theorem loopProvenance_closed (P : Parameters) (program : Program) (input : List Cell)
    (base E returnPC testPC bodyPC exitPC : ℕ) (caller : State) :
    LoopClosed P program input base E returnPC testPC bodyPC exitPC
      (LoopProvenance P program input base E returnPC testPC bodyPC exitPC caller) := by
  intro phase m values before state entry previous actual
  exact LoopProvenance.block previous entry actual

end PDROC.EndpointOperands.Loop
