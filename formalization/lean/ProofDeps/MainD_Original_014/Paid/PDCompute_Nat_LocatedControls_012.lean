module
public import Paid.PDCompute_Nat_ControlContext_010
public import Paid.PDCompute_Nat_NaturalBranchBits_008
public import Paid.PDCompute_Nat_CounterBackBits_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000
@[expose] public section
namespace PDCompute.NatControl
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

theorem fetchedBlock_head (program : Program) (counter : ℕ) (block : List Instruction)
    (nonempty : 0<block.length) (fetch : FetchesCode program counter block) :
    ∃ instruction : Instruction,program[counter]?=some instruction := by
  have literal : block[0]?=some block[0]:=List.getElem?_eq_some_iff.mpr ⟨nonempty,rfl⟩
  exact ⟨block[0],by simpa only [Nat.add_zero] using (fetch 0 nonempty).trans literal⟩

/-- Both absolute target bounds and the real7-op comparison counter are
DERIVED from original fetched code. Comparands may be arbitrary large
live words; only the new0/1 flag and actual addresses need new caps. -/
theorem naturalBranch_trace_context (mode : ReaderMode) (origin : ℕ) (input : List Cell) (caller before : State)
    (incoming base n k left right x y whenZero whenNonzero budget : ℕ) (comparison : Comparison) (values : ℕ → Cell)
    (context : SolverControlContext caller incoming base n k mode origin budget)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (leftInside : left<headerWords) (rightInside : right<headerWords)
    (leftValue : values left=.natural x) (rightValue : values right=.natural y) (safe : RootD27.Bits.SafeBits before budget)
    (zeroInstruction nonzeroInstruction : Instruction)
    (zeroFetch : (solverLocatedProgram mode origin)[whenZero]?=some zeroInstruction)
    (nonzeroFetch : (solverLocatedProgram mode origin)[whenNonzero]?=some nonzeroInstruction)
    (fetch : FetchesCode (solverLocatedProgram mode origin) before.pc (naturalBranchCode comparison left right whenZero whenNonzero)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun a b=>step (solverLocatedProgram mode origin) input a=some b) ∧
      time (solverLocatedProgram mode origin) trace≤135 ∧ Header after base values ∧ after.register .fresh=.natural base ∧
      after.pc=(if comparison.nat x y then whenNonzero else whenZero) ∧ Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have endBits:=SolverControlContext.block (before:=before) context _ (by change (0:ℕ)<8;decide) fetch
  have comparePC : natBits (before.pc+7)≤budget:=
    (natBits_mono (by change before.pc+7≤before.pc+8;omega)).trans endBits
  exact naturalBranch_trace_bits _ input before base n k left right x y whenZero whenNonzero budget comparison values header leftInside rightInside
    leftValue rightValue fresh safe (context.small 1 (by decide)) context.header comparePC
    (SolverControlContext.instruction context zeroInstruction zeroFetch) (SolverControlContext.instruction context nonzeroInstruction nonzeroFetch) fetch

/-- Actual amount1 increment/backedge. The concrete row/column wrappers
below discharge nextWithinCap from the true original loop indices. -/
theorem counterBack_one_trace_context (mode : ReaderMode) (origin : ℕ) (input : List Cell) (caller before : State)
    (incoming base n k slot value target budget : ℕ) (values : ℕ → Cell)
    (context : SolverControlContext caller incoming base n k mode origin budget)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (inside : slot<headerWords) (hvalue : values slot=.natural value) (safe : RootD27.Bits.SafeBits before budget)
    (nextWithinCap : value+1≤PDCompute.Pack.naturalCap base n k) (targetInstruction : Instruction)
    (targetFetch : (solverLocatedProgram mode origin)[target]?=some targetInstruction)
    (fetch : FetchesCode (solverLocatedProgram mode origin) before.pc (counterBackCode slot 1 target)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun a b=>step (solverLocatedProgram mode origin) input a=some b) ∧
      time (solverLocatedProgram mode origin) trace≤150 ∧ Header after base (Function.update values slot (.natural (value+1))) ∧
      after.register .fresh=.natural base ∧ after.pc=target ∧ Frame before after base n k ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) ∧
      ∀ state∈trace.dropLast,before.pc≤state.pc ∧ state.pc<before.pc+(counterBackCode slot 1 target).length := by
  have endBits:=SolverControlContext.block (before:=before) context _ (by change (0:ℕ)<9;decide) fetch
  have incPC : natBits (before.pc+8)≤budget:=
    (natBits_mono (by change before.pc+8≤before.pc+9;omega)).trans endBits
  exact counterBack_trace_bits_pc _ input before base n k slot value 1 target budget values header fresh inside hvalue safe
    (context.natural _ (PDCompute.Pack.naturalCap_header_address base n k slot inside)) (context.small 1 (by decide))
    (context.natural _ nextWithinCap) incPC (SolverControlContext.instruction context targetInstruction targetFetch) fetch

end PDCompute.NatControl
