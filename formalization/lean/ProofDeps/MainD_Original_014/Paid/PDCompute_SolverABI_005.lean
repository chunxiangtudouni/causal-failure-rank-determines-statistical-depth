module

public import Paid.PDMenu_ComputeFrame_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

/-- Static code-generation choice. ROM solver uses the ORIGINAL solveInput;
core uses its actually computed live endpoint cache. Neither is an oracle. -/
inductive ReaderMode where
  | inputROM
  | liveHeap
  deriving DecidableEq

def ReaderMode.read (mode : ReaderMode) (target pointer : Register) : Instruction :=
  match mode with
  | .inputROM => .loadInput target pointer
  | .liveHeap => .load target pointer

def headerWords : ℕ := 48
def entryWords : ℕ := 6
def entryCount (n k : ℕ) : ℕ := (n+1)*(k+1)
def tableBase (base : ℕ) : ℕ := base+headerWords
def cellBase (base k row column : ℕ) : ℕ := tableBase base+entryWords*(row*(k+1)+column)
def resultBase (base n k : ℕ) : ℕ := tableBase base+entryWords*entryCount n k
def resultCapacity (n k : ℕ) : ℕ := 1+(n+1)*(1+6*(k+1))
def workspaceSize (n k : ℕ) : ℕ := headerWords+entryWords*entryCount n k+resultCapacity n k
def workspace (base n k : ℕ) : Finset ℕ := (Finset.range (workspaceSize n k)).image (base+·)

theorem workspaceSize_linear (n k : ℕ) : workspaceSize n k ≤ 62*entryCount n k := by
  unfold workspaceSize headerWords entryWords resultCapacity entryCount
  nlinarith

def HeapList (state : State) (base : ℕ) (cells : List Cell) : Prop :=
  (∀ offset < cells.length, base+offset ∈ state.live) ∧ heapSegment state base cells.length=cells

def EndpointSource (mode : ReaderMode) (input : List Cell) (P : Parameters)
    (source : ℕ) (state : State) : Prop :=
  match mode with
  | .inputROM =>
      ∀ offset < (encodeList encodeEndpoint P.endpointCache.toList).length,
        input[source+offset]? = (encodeList encodeEndpoint P.endpointCache.toList)[offset]?
  | .liveHeap => HeapList state source (encodeList encodeEndpoint P.endpointCache.toList)

/-- A real callee entry specification only. It contains no existence,
running-time or returned-table assumption. All n/k and rational penalties
remain arbitrary, as in the original standalone solver target. -/
def Entry (mode : ReaderMode) (input : List Cell) (P : Parameters) (fee penalty : ℚ)
    (n k base source returnPC : ℕ) (state : State) : Prop :=
  state.register .fresh=.natural base ∧
  state.register .old=.natural returnPC ∧
  state.register .address=.natural source ∧
  state.register .total=.rational penalty ∧
  state.register .index=.natural n ∧
  state.register .value=.natural k ∧
  state.register .flag=.rational fee ∧
  EndpointSource mode input P source state ∧ Disjoint state.live (workspace base n k)

def Frame (before after : State) (base n k : ℕ) : Prop :=
  (∀ address ∉ workspace base n k, after.heap address=before.heap address) ∧
  (∀ address ∉ workspace base n k, address ∈ after.live ↔ address ∈ before.live)

/-- Exact original serialized result in actual live heap cells. Standalone
wrapper emits it; core retains it and releases obsolete tables. -/
def Return (P : Parameters) (fee penalty : ℚ) (n k base returnPC : ℕ) (before after : State) : Prop :=
  after.pc=returnPC ∧
  after.register .fresh=.natural base ∧
  after.register .old=.natural returnPC ∧
  after.register .address=.natural (resultBase base n k) ∧
  after.register .index=.natural (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n)).length ∧
  HeapList after (resultBase base n k) (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n)) ∧
  after.output=before.output ∧ Frame before after base n k

theorem heapReader_noInput (target pointer : Register) :
    PDMenu.ComputeFrame.NoInputInstruction (ReaderMode.liveHeap.read target pointer) := by trivial

end PDCompute.Solver
