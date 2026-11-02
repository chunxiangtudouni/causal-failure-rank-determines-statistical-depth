module

public import Paid.PDCompute_SolverEndpointResultFacts_041

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute linearExecute_append loadSlot loadSlotResult)

def scanEndpointCode (mode : ReaderMode) : List Instruction :=
  loadSlot 39 .address++endpointHeaderCode mode

def scanEndpointValues (values : ℕ → Cell) (error charge : ℚ) : ℕ → Cell :=
  Function.update (Function.update values 26 (.rational error)) 27 (.rational charge)

theorem scanEndpointCode_length (mode : ReaderMode) : (scanEndpointCode mode).length=13 := rfl

theorem scanEndpointCode_straight (mode : ReaderMode) : PDMenu.ComputeFrame.StraightCode (scanEndpointCode mode) := by
  intro instruction member
  simp only [scanEndpointCode,List.mem_append] at member
  rcases member with member|member
  · exact loadSlot_straight 39 .address instruction member
  · exact endpointHeaderCode_straight mode instruction member

/-- The thirteen real reads/stores are composed behind an existential
state boundary. Later score code cannot expand this concrete state. -/
theorem scanEndpointCode_execute (mode : ReaderMode) (input : List Cell) (P : Parameters)
    (before : State) (base source index n k : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (hindex : index ≤ P.certificate.M)
    (hpointer : values 39=.natural (source+(1+2*index))) :
    ∃ after : State, linearExecute input (scanEndpointCode mode) before=some after ∧
      Header after base (scanEndpointValues values (P.cachedEndpoint P.endpointCache index).error
        (P.cachedEndpoint P.endpointCache index).charge) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+13 ∧
      Frame before after base n k ∧ after.output=before.output := by
  let pointer := loadSlotResult before base 39 .address
  let endpoint := P.cachedEndpoint P.endpointCache index
  let after := endpointHeaderResult pointer base (source+(1+2*index)) endpoint.error endpoint.charge
  have pointerRun := header.loadSlot_execute input 39 .address (by decide) hbase
  have pointerHeader : Header pointer base values := header
  have pointerBase : pointer.register .fresh=.natural base :=
    (loadSlotResult_fresh before base 39 .address (by decide)).trans hbase
  have pointerAddress : pointer.register .address=.natural (source+(1+2*index)) :=
    pointerRun.2.trans hpointer
  have pointerSource : EndpointSource mode input P source pointer := by
    cases mode <;> exact hsource
  have endpointRun := endpointHeaderCode_execute mode input P pointer base source index
    pointerSource hindex pointerBase pointerAddress
  refine ⟨after,?_,endpointHeaderResult_header pointer base _ _ _ values pointerHeader,
    (endpointHeaderResult_fresh pointer base _ _ _).trans pointerBase,?_,
    (loadSlotResult_frame before base 39 n k .address).trans
      (endpointHeaderResult_frame pointer base _ n k _ _),?_⟩
  · rw [scanEndpointCode,linearExecute_append,pointerRun.1,Option.bind_some]
    exact endpointRun
  · change (endpointHeaderResult pointer base _ _ _).pc=before.pc+13
    rw [endpointHeaderResult_pc,loadSlotResult_pc]
  · exact (endpointHeaderResult_output pointer base _ _ _).trans
      (loadSlotResult_output before base 39 .address)

end PDCompute.Solver
