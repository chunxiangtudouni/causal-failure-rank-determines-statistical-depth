module

public import Paid.PDCompute_SolverInitialization_058
public import Paid.PDCompute_SolverHeaderLoads_038
public import Paid.PDCompute_SolverSequenceMemory_051

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute linearExecute_append loadSlot loadSlotResult storeSlot storeSlotResult)

/-- Read ORIGINAL cache length and actually subtract one. The standalone
version reads ROM directly and never allocates an M-dependent heap copy. -/
def endpointCountHeaderCode (mode : ReaderMode) : List Instruction :=
  loadSlot 0 .address++
    [mode.read .index .address,.constant .value (.natural 1),.natOp .subtract .index .index .value]++
      storeSlot 6 .index

def endpointCountComputed (loaded : State) (last : ℕ) : State :=
  let read := ({loaded with pc:=loaded.pc+1}).set .index (.natural (last+1))
  (({read with pc:=read.pc+2}).set .value (.natural 1)).set .index (.natural last)

theorem endpointCountHeaderCode_length (mode : ReaderMode) : (endpointCountHeaderCode mode).length=9 := rfl

theorem endpointCountHeaderCode_execute (mode : ReaderMode) (input : List Cell) (P : Parameters)
    (before : State) (base source : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (sourceValue : values 0=.natural source) :
    ∃ after : State, linearExecute input (endpointCountHeaderCode mode) before=some after ∧
      Header after base (Function.update values 6 (.natural P.certificate.M)) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+9 ∧
      HeaderMemory before after base := by
  let loaded := loadSlotResult before base 0 .address
  let computed := endpointCountComputed loaded P.certificate.M
  let after := storeSlotResult computed base 6 .index
  have loadRun := header.loadSlot_execute input 0 .address (by decide) hbase
  have firstRun : linearExecute input (loadSlot 0 .address) before=some loaded := loadRun.1
  have loadedBase : loaded.register .fresh=.natural base :=
    (loadSlotResult_fresh before base 0 .address (by decide)).trans hbase
  have loadedAddress : loaded.register .address=.natural source := loadRun.2.trans sourceValue
  have loadedSource : EndpointSource mode input P source loaded := by cases mode <;> exact hsource
  have readRun := readEndpointCount_execute mode input P source loaded .index loadedSource loadedAddress
  have middleRun : linearExecute input
      [mode.read .index .address,.constant .value (.natural 1),.natOp .subtract .index .index .value]
      loaded=some computed := by
    rw [linearExecute,readRun,Option.bind_some]
    simp [linearExecute,endpointCountComputed,computed,Instruction.execute,State.set,
      NatOp.eval,Cell.nat?]
  have computedBase : computed.register .fresh=.natural base := loadedBase
  have storeRun := PDLower.CalibrationCompute.storeSlot_execute input computed base 6 .index computedBase (by decide)
  have heap : after.heap=Function.update before.heap (base+6) (.natural P.certificate.M) := by
    simp only [after,storeSlotResult,computed,endpointCountComputed,State.set,Function.update_self]
    rfl
  have live : after.live=insert (base+6) before.live := rfl
  have output : after.output=before.output := rfl
  refine ⟨after,?_,?_,?_,?_,HeaderMemory.write header 6 (by decide) (.natural P.certificate.M) heap live output⟩
  · rw [endpointCountHeaderCode,linearExecute_append,linearExecute_append,firstRun,Option.bind_some]
    rw [middleRun,Option.bind_some]
    exact storeRun
  · apply Header.update header 6 (.natural P.certificate.M) heap
    rw [live]
    exact Finset.subset_insert _ _
  · exact computedBase
  · change before.pc+3+1+2+3=before.pc+9
    omega

end PDCompute.Solver
