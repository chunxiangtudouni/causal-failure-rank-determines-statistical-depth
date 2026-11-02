module

public import Paid.PDLower_CoreSearch_Compare_006
public import Paid.PDLower_CoreSearch_NumericSegment_018
public import Paid.PDCompute_SolverRationalBranchBits_177

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute storeSlot)
open PDROC.CalibrationRow.Operand

namespace PDLower.CoreSearch

/-- Frozen generic7-op comparison177 followed by the actual3-op store
of flag to40, with no arithmetic budget enlargement. -/
theorem comparisonStored_prefix_safe (comparison : Comparison) (left right : ℕ) (x y : ℚ)
    (input : List Cell) (before : State) (values : ℕ→Cell) (budget : ℕ)
    (header : Header before 0 values) (leftInside : left<headerWords) (rightInside : right<headerWords)
    (leftValue : values left=.rational x) (rightValue : values right=.rational y) (fresh : before.register .fresh=.natural 0)
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+10)≤budget) : PrefixSafe input (comparisonStoredCode comparison left right) before budget := by
  let compared := PDROC.D27Prepare.Program.comparisonResult before 0 left right (comparison.rat x y)
  have firstRun : linearExecute input (rationalCompareCode comparison left right) before=some compared :=
    PDROC.D27Prepare.Program.ratCompareSlots_execute input before 0 left right x y comparison fresh
      (header.live left leftInside) (header.live right rightInside)
      ((header.value left leftInside).trans leftValue) ((header.value right rightInside).trans rightValue)
  have firstSafe := rationalCompareCode_prefix_safe input before 0 left right budget values x y comparison header fresh
    leftInside rightInside leftValue rightValue safe small (by simpa only [Nat.zero_add] using addressBits)
    ((natBits_mono (by omega : before.pc+7≤before.pc+10)).trans pcBits)
  have fields := PDROC.D27Prepare.Program.comparisonResult_fields before 0 left right (comparison.rat x y)
  have middleFresh : compared.register .fresh=.natural 0 := fields.2.2.1.trans fresh
  have storePC : natBits (compared.pc+3)≤budget := by
    dsimp only [compared]
    rw [fields.2.2.2.2.1]
    exact pcBits
  have laterSafe := PrefixSafe.storeSlot input compared 0 40 budget .flag (firstSafe.final firstRun) middleFresh (by decide)
    (by
      have bounded := natBits_mono (by decide : (40:ℕ)≤headerWords)
      simpa only [Nat.zero_add] using (Nat.add_le_add_left bounded 1).trans addressBits) storePC
  exact PrefixSafe.append input _ _ before compared budget firstRun firstSafe laterSafe

theorem comparisonStored_segment_bits (comparison : Comparison) (left right : ℕ) (x y : ℚ)
    (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell) (budget : ℕ)
    (header : Header before 0 values) (leftInside : left<headerWords) (rightInside : right<headerWords)
    (leftValue : values left=.rational x) (rightValue : values right=.rational y) (fresh : before.register .fresh=.natural 0)
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+10)≤budget) (fetched : FetchesCode program before.pc (comparisonStoredCode comparison left right)) :
    NumericSegment program input before (comparisonStoredResult before left right (comparison.rat x y)) 165 budget ∧
      Header (comparisonStoredResult before left right (comparison.rat x y)) 0
        (Function.update values 40 (.natural (if comparison.rat x y then 1 else 0))) := by
  let after := comparisonStoredResult before left right (comparison.rat x y)
  have run := comparisonStored_execute comparison left right x y input before values header leftInside rightInside leftValue rightValue fresh
  have prefixSafe := comparisonStored_prefix_safe comparison left right x y input before values budget header leftInside rightInside
    leftValue rightValue fresh safe small addressBits pcBits
  obtain ⟨trace,head,last,chain,cost,properties⟩ := PDCompute.Pack.linearExecute_trace_invariant program input
    (comparisonStoredCode comparison left right) (comparisonStored_straight comparison left right) before after fetched run
    (fun state => (MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0) ∧ RootD27.Bits.SafeBits state budget) (by
      intro count bounded state executed
      exact ⟨comparisonStored_prefix_memory comparison left right x y input before state values header leftInside rightInside
        leftValue rightValue fresh count (by simpa only [comparisonStored_length] using bounded) executed,prefixSafe count state executed⟩)
  have fields := comparisonStored_fields before left right (comparison.rat x y)
  have afterHeader : Header after 0 (Function.update values 40 (.natural (if comparison.rat x y then 1 else 0))) :=
    header.update 40 _ fields.1 (by rw [fields.2.1];exact Finset.subset_insert _ _)
  exact ⟨⟨trace,head,last,chain,by simpa only [comparisonStored_length] using cost,properties⟩,afterHeader⟩

end PDLower.CoreSearch
