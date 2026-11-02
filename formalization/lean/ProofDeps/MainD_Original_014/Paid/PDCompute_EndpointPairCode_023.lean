module

public import Paid.PDCompute_EndpointCells_022

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDMenu.ComputeFrame

/-- A streaming endpoint read consists of two actual one-cell reads and
one pointer increment. ROM and heap variants differ only in the opcode. -/
def endpointPairCode (mode : ReaderMode) : List Instruction :=
  [mode.read .total .address,.constant .flag (.natural 1),
    .natOp .add .address .address .flag,mode.read .value .address]

def endpointPairResult (before : State) (address : ℕ) (error charge : ℚ) : State :=
  { before with
    register := Function.update
      (Function.update (Function.update (Function.update before.register .total (.rational error))
        .flag (.natural 1)) .address (.natural (address+1))) .value (.rational charge)
    pc := before.pc+4 }

theorem endpointPairCode_length (mode : ReaderMode) : (endpointPairCode mode).length=4 := rfl

theorem endpointPairCode_straight (mode : ReaderMode) : StraightCode (endpointPairCode mode) := by
  intro instruction member
  simp only [endpointPairCode,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h <;> subst instruction <;> cases mode <;> trivial

theorem endpointPairCode_noInput (instruction : Instruction)
    (member : instruction ∈ endpointPairCode .liveHeap) : NoInputInstruction instruction := by
  simp only [endpointPairCode,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h <;> subst instruction <;> trivial

theorem endpointPairCode_execute (mode : ReaderMode) (input : List Cell) (before : State)
    (address : ℕ) (error charge : ℚ) (haddress : before.register .address=.natural address)
    (herror : mode.HasCell input before address (.rational error))
    (hcharge : mode.HasCell input before (address+1) (.rational charge)) :
    linearExecute input (endpointPairCode mode) before=some (endpointPairResult before address error charge) := by
  cases mode with
  | inputROM =>
    change input[address]?=some (.rational error) at herror
    change input[address+1]?=some (.rational charge) at hcharge
    simp [endpointPairCode,ReaderMode.read,linearExecute,Instruction.execute,haddress,Cell.nat?,
      herror,hcharge,NatOp.eval,State.set,endpointPairResult]
  | liveHeap =>
    simp [endpointPairCode,ReaderMode.read,linearExecute,Instruction.execute,haddress,Cell.nat?,
      herror.1,herror.2,hcharge.1,hcharge.2,NatOp.eval,State.set,endpointPairResult]

theorem endpointPairCode_original (mode : ReaderMode) (input : List Cell) (P : Parameters)
    (before : State) (source index : ℕ) (hsource : EndpointSource mode input P source before)
    (hindex : index ≤ P.certificate.M) (haddress : before.register .address=.natural (source+(1+2*index))) :
    linearExecute input (endpointPairCode mode) before=
      some (endpointPairResult before (source+(1+2*index))
        (P.cachedEndpoint P.endpointCache index).error (P.cachedEndpoint P.endpointCache index).charge) := by
  apply endpointPairCode_execute mode input before _ _ _ haddress
    (EndpointSource.error mode input P source index before hsource hindex)
  simpa only [Nat.add_assoc] using EndpointSource.charge mode input P source index before hsource hindex

theorem endpointPairCode_trace (mode : ReaderMode) (program : Program) (input : List Cell) (P : Parameters)
    (before : State) (source index : ℕ) (hsource : EndpointSource mode input P source before)
    (hindex : index ≤ P.certificate.M) (haddress : before.register .address=.natural (source+(1+2*index)))
    (hfetch : FetchesCode program before.pc (endpointPairCode mode)) :
    ∃ trace : List State, trace.head?=some before ∧
      trace.getLast?=some (endpointPairResult before (source+(1+2*index))
        (P.cachedEndpoint P.endpointCache index).error (P.cachedEndpoint P.endpointCache index).charge) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 75 ∧
      ∀ state ∈ trace.dropLast, ∃ count < 4,
        linearExecute input ((endpointPairCode mode).take count) before=some state := by
  simpa only [endpointPairCode_length] using linearExecute_trace_time program input (endpointPairCode mode)
    (endpointPairCode_straight mode) before _ hfetch
    (endpointPairCode_original mode input P before source index hsource hindex haddress)

end PDCompute.Solver
