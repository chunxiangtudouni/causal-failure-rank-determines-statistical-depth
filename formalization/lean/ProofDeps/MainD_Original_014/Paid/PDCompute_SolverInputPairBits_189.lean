module

public import Paid.PDCompute_SolverCompareBits_164

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDLower.CalibrationCompute (linearExecute)
open PDROC.CalibrationRow.Operand

/-- The two literal instructions used at original solverInput positions
0,1,3,4. This definition is only a proof-side spelling of those opcodes. -/
def constantInputPair (location : ℕ) (target : Register) : List Instruction :=
  [.constant .address (.natural location),.loadInput target .address]

def constantInputPairResult (before : State) (location : ℕ) (target : Register) (value : Cell) : State :=
  let middle:=({before with pc:=before.pc+1}).set .address (.natural location)
  ({middle with pc:=middle.pc+1}).set target value

theorem constantInputPair_execute (input : List Cell) (before : State) (location : ℕ) (target : Register) (value : Cell)
    (fetched : input[location]?=some value) :
    linearExecute input (constantInputPair location target) before=some (constantInputPairResult before location target value) := by
  simp [constantInputPair,constantInputPairResult,linearExecute,Instruction.execute,State.set,Cell.nat?,fetched]

theorem constantInputPair_prefix_safe (input : List Cell) (before : State) (location budget : ℕ) (target : Register) (value : Cell)
    (safe : RootD27.Bits.SafeBits before budget) (fetched : input[location]?=some value)
    (addressBits : (.natural location : Cell).bits≤budget) (valueBits : value.bits≤budget) (pcBits : natBits (before.pc+2)≤budget) :
    PrefixSafe input (constantInputPair location target) before budget := by
  let middle:=({before with pc:=before.pc+1}).set .address (.natural location)
  let after:=({middle with pc:=middle.pc+1}).set target value
  have firstRun : linearExecute input [.constant .address (.natural location)] before=some middle := rfl
  have firstSafe:=PrefixSafe.constant input before budget .address (.natural location) safe addressBits
    ((natBits_mono (by omega : before.pc+1≤before.pc+2)).trans pcBits)
  have middleSafe:=firstSafe.final firstRun
  have actual : Instruction.execute input (.loadInput target .address) middle=some after := by
    simp [Instruction.execute,middle,after,State.set,Cell.nat?,fetched]
  have afterSafe:=PDLower.CalibrationCompute.loadInput_execute_safe input middle after target .address location budget value middleSafe
    (by simp [middle,State.set]) fetched valueBits (by simpa only [middle,State.set,Nat.add_assoc] using pcBits) actual
  have secondSafe:=PrefixSafe.singleton input (.loadInput target .address) middle after budget actual middleSafe afterSafe
  exact PrefixSafe.append input _ _ before middle budget firstRun firstSafe secondSafe

/-- Constant-only suffix on actual literal prefixes. No scratch or
whole-input bound is silently added to the standalone theorem. -/
theorem constants_prefix_safe (input : List Cell) (values : List (Register×Cell)) (before : State) (budget : ℕ)
    (safe : RootD27.Bits.SafeBits before budget) (bounded : ∀ value∈values,value.2.bits≤budget)
    (pcBits : natBits (before.pc+values.length)≤budget) :
    PrefixSafe input (values.map (fun pair=>Instruction.constant pair.1 pair.2)) before budget := by
  induction values generalizing before with
  | nil => exact PrefixSafe.nil input before budget safe
  | cons pair rest ih =>
    let middle:=({before with pc:=before.pc+1}).set pair.1 pair.2
    have actual : Instruction.execute input (.constant pair.1 pair.2) before=some middle := rfl
    have middleSafe : RootD27.Bits.SafeBits middle budget :=
      (safe.withPC _ ((natBits_mono (by simp only [List.length_cons]; omega : before.pc+1≤before.pc+(pair::rest).length)).trans pcBits)).set _ _ (bounded pair (by simp))
    have laterCounter : natBits (middle.pc+rest.length)≤budget := by
      simpa only [middle,State.set,List.length_cons,Nat.add_assoc,Nat.add_comm 1 rest.length] using pcBits
    exact PrefixSafe.cons input _ _ before middle budget actual safe
      (ih middle middleSafe (fun value member=>bounded value (List.mem_cons_of_mem pair member)) laterCounter)

end PDCompute.Solver
