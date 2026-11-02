module

public import Paid.PDCompute_SolverInputPairBits_189
public import Paid.PDCompute_SolverInputLoader_092

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
open PDROC.CalibrationRow.Operand

/-- Original11-op readonly argument loader at input0/1/3/4. The cache
remains in the actual original readonly solveInput and is not copied. -/
theorem solverInputCode_prefix_safe (P : Parameters) (fee penalty : ℚ) (n k returnPC budget : ℕ) (before : State)
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (nBits : (.natural n : Cell).bits≤budget) (kBits : (.natural k : Cell).bits≤budget)
    (feeBits : (.rational fee : Cell).bits≤budget) (penaltyBits : (.rational penalty : Cell).bits≤budget)
    (returnBits : (.natural returnPC : Cell).bits≤budget) (counter : natBits (before.pc+11)≤budget) :
    PrefixSafe (solveInput P fee penalty n k) (solverInputCode returnPC) before budget := by
  let input:=solveInput P fee penalty n k
  let a:=constantInputPairResult before 0 .index (.natural n)
  let b:=constantInputPairResult a 1 .value (.natural k)
  let c:=constantInputPairResult b 3 .flag (.rational fee)
  let d:=constantInputPairResult c 4 .total (.rational penalty)
  have literal (value : ℕ) (inside : value≤5) : (.natural value : Cell).bits≤budget := by
    have bound:=natBits_mono inside
    have five : natBits 5=3 := by norm_num [natBits]
    change 1+natBits value≤budget
    omega
  have aRun:=constantInputPair_execute input before 0 .index (.natural n) rfl
  have aSafe:=constantInputPair_prefix_safe input before 0 budget .index (.natural n) safe rfl (literal 0 (by decide)) nBits
    ((natBits_mono (by omega : before.pc+2≤before.pc+11)).trans counter)
  have bRun:=constantInputPair_execute input a 1 .value (.natural k) rfl
  have bCounter : natBits (a.pc+2)≤budget :=
    (natBits_mono (by change before.pc+1+1+2≤before.pc+11; omega)).trans counter
  have bSafe:=constantInputPair_prefix_safe input a 1 budget .value (.natural k) (aSafe.final aRun) rfl (literal 1 (by decide)) kBits bCounter
  have cRun:=constantInputPair_execute input b 3 .flag (.rational fee) rfl
  have cCounter : natBits (b.pc+2)≤budget :=
    (natBits_mono (by change before.pc+1+1+1+1+2≤before.pc+11; omega)).trans counter
  have cSafe:=constantInputPair_prefix_safe input b 3 budget .flag (.rational fee) (bSafe.final bRun) rfl (literal 3 (by decide)) feeBits cCounter
  have dRun:=constantInputPair_execute input c 4 .total (.rational penalty) rfl
  have dCounter : natBits (c.pc+2)≤budget :=
    (natBits_mono (by change before.pc+1+1+1+1+1+1+2≤before.pc+11; omega)).trans counter
  have dSafe:=constantInputPair_prefix_safe input c 4 budget .total (.rational penalty) (cSafe.final cRun) rfl (literal 4 (by decide)) penaltyBits dCounter
  let constants : List (Register×Cell):=[(.address,.natural 5),(.old,.natural returnPC),(.fresh,.natural 0)]
  have constantsBound : ∀ value∈constants,value.2.bits≤budget := by
    intro value member
    simp only [constants,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same|same <;> subst value
    · exact literal 5 (le_refl _)
    · exact returnBits
    · exact literal 0 (by decide)
  have lastCounter : natBits (d.pc+constants.length)≤budget := by
    simpa only [d,c,b,a,constantInputPairResult,State.set,constants,List.length_cons,List.length_nil,Nat.add_assoc] using counter
  have constantsSafe:=constants_prefix_safe input constants d budget (dSafe.final dRun) constantsBound lastCounter
  have lastPair:=PrefixSafe.append input (constantInputPair 4 .total) (constants.map (fun pair=>Instruction.constant pair.1 pair.2)) c d budget dRun dSafe constantsSafe
  have secondPair:=PrefixSafe.append input (constantInputPair 3 .flag) _ b c budget cRun cSafe lastPair
  have firstPair:=PrefixSafe.append input (constantInputPair 1 .value) _ a b budget bRun bSafe secondPair
  exact PrefixSafe.append input (constantInputPair 0 .index) _ before a budget aRun aSafe firstPair

theorem solverInput_trace_bits (P : Parameters) (fee penalty : ℚ) (n k returnPC budget : ℕ) (program : Program) (before : State)
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (nBits : (.natural n : Cell).bits≤budget) (kBits : (.natural k : Cell).bits≤budget)
    (feeBits : (.rational fee : Cell).bits≤budget) (penaltyBits : (.rational penalty : Cell).bits≤budget)
    (returnBits : (.natural returnPC : Cell).bits≤budget) (counter : natBits (before.pc+11)≤budget)
    (fetch : FetchesCode program before.pc (solverInputCode returnPC)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (solverInputResult before returnPC n k fee penalty) ∧
      trace.IsChain (fun first later=>step program (solveInput P fee penalty n k) first=some later) ∧ time program trace≤180 ∧
      ∀ state∈trace,state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output ∧ RootD27.Bits.SafeBits state budget := by
  have bounded:=solverInputCode_prefix_safe P fee penalty n k returnPC budget before safe small nBits kBits feeBits penaltyBits returnBits counter
  have run:=solverInputCode_execute P fee penalty n k returnPC before
  obtain ⟨trace,head,last,chain,cost,resources⟩:=PDCompute.Pack.linearExecute_trace_invariant program (solveInput P fee penalty n k)
    (solverInputCode returnPC) (solverInputCode_straight returnPC) before _ fetch run
    (fun state=>state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output ∧ RootD27.Bits.SafeBits state budget) (by
      intro count bound state executed
      have memory:=solverInputCode_prefix_storage P fee penalty n k returnPC before state count bound executed
      exact ⟨memory.1,memory.2.1,memory.2.2,bounded count state executed⟩)
  exact ⟨trace,head,last,chain,cost,resources⟩

end PDCompute.Solver
