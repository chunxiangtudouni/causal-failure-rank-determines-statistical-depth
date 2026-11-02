module

public import Paid.PDROC_D27Prepare_Search_002
public import Paid.PDROC_D27Prepare_Search_003
public import Paid.PDROC_D27Prepare_Program_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid
open PaperProofs.Paid.Computation

namespace PDROC.D27Prepare.Search

/-- A typed initialized cell in the actual machine heap. -/
def SlotHas (state : State) (address : ℕ) (value : Cell) : Prop :=
  address ∈ state.live ∧ state.heap address = value

/-- The raw six cells and the literal scalar constants used by all phases.
This predicate mentions the original machine state, not an auxiliary input. -/
structure RawConstants (P : Parameters) (fee : ℚ) (state : State) : Prop where
  fresh : state.register .fresh = .natural 0
  stages : SlotHas state 0 (.natural P.certificate.stages)
  tools : SlotHas state 1 (.natural P.tools)
  gamma : SlotHas state 2 (.rational P.certificate.gamma)
  risk : SlotHas state 3 (.rational P.certificate.risk)
  reviewFee : SlotHas state 4 (.rational P.reviewFee)
  feeValue : SlotHas state 5 (.rational fee)
  natZero : SlotHas state 13 (.natural 0)
  natOne : SlotHas state 14 (.natural 1)
  natTwo : SlotHas state 15 (.natural 2)
  ratZero : SlotHas state 16 (.rational 0)
  ratOne : SlotHas state 17 (.rational 1)
  ratTwo : SlotHas state 18 (.rational 2)
  ratThree : SlotHas state 19 (.rational 3)
  ratFour : SlotHas state 20 (.rational 4)
  ratHalf : SlotHas state 21 (.rational (1 / 2))

/-- The actual state reached immediately after the fixed prologue. -/
structure SearchInitial (P : Parameters) (fee : ℚ) (state : State) : Prop where
  raw : RawConstants P fee state
  location : state.pc = Program.pc 1
  t0 : SlotHas state 6 (.natural 1)
  M : SlotHas state 7 (.natural 0)
  E : SlotHas state 8 (.natural 1)
  Q : SlotHas state 9 (.natural 1)

/-- Exact state interface at page21. Scratch cells not listed here impose
no premise on the following phase. -/
structure SearchFinished (P : Parameters) (fee : ℚ) (state : State) : Prop where
  raw : RawConstants P fee state
  location : state.pc = Program.pc 21
  t0 : SlotHas state 6 (.natural P.certificate.t0)
  M : SlotHas state 7 (.natural P.certificate.M)
  E : SlotHas state 8 (.natural P.certificate.E)
  Q : SlotHas state 9 (.natural P.certificate.Q)
  ratStages : SlotHas state 22 (.rational P.certificate.stages)
  ratT0 : SlotHas state 23 (.rational P.certificate.t0)
  gammaSquared : SlotHas state 24 (.rational (P.certificate.gamma ^ 2))
  variance : SlotHas state 25 (.rational P.certificate.varianceBase)
  varianceSquared : SlotHas state 26 (.rational (P.certificate.varianceBase ^ 2))
  majorityThreshold : SlotHas state 27
    (.rational ((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) ^ 2))
  menuRatio : SlotHas state 29 (.rational P.certificate.menuRatio)
  odds : SlotHas state 30 (.rational P.certificate.odds)
  exponentThreshold : SlotHas state 31 (.rational (P.certificate.gamma * P.certificate.epsilon))

/-- The only writable addresses of pages1 through20. -/
def searchRegion : Finset ℕ := {6, 7, 8, 9, 22, 23, 24, 25, 26, 27, 28,
  29, 30, 31, 32, 33, 34, 52, 53}

theorem searchRegion_bound (address : ℕ) (member : address ∈ searchRegion) :
    address < Program.heapBound := by
  simp only [searchRegion, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

theorem SlotHas_of_heap_live (before after : State) (address : ℕ) (value : Cell)
    (old : SlotHas before address value)
    (heap : after.heap address = before.heap address)
    (live : address ∈ before.live → address ∈ after.live) : SlotHas after address value :=
  ⟨live old.1, heap.trans old.2⟩

end PDROC.D27Prepare.Search
