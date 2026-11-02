module

public import Paid.RootD27Core_InitializeSearch_064
public import Paid.PDLower_CoreSearch_Stop_016

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open PDLower.CoreSearch

/-- Recover the exact original source scalar fields from the actual
retained-buffer representation; there is no new statistic-input oracle. -/
theorem SolvedBuffer.original_values {P : Parameters} {fee : ℚ} {solution : MultiplierSolve}
    {upper : Bool} {state : State} (original : OriginalSolved P fee solution)
    (represented : SolvedBuffer P fee solution.multiplier upper state) :
    state.heap (multiplierSlot upper)=.rational solution.multiplier ∧
    state.heap (statisticsSlot upper)=.rational (P.solveRecord solution).observation ∧
    state.heap (statisticsSlot upper+1)=.rational (P.solveRecord solution).repairs ∧
    state.heap (statisticsSlot upper+2)=.rational (P.solveRecord solution).failure := by
  have price:=PDLower.CalibrationCompute.HeapList.value represented.1 0 (by change 0<1;decide)
  have observation:=PDLower.CalibrationCompute.HeapList.value represented.2.1 0 (by change 0<3;decide)
  have repairs:=PDLower.CalibrationCompute.HeapList.value represented.2.1 1 (by change 1<3;decide)
  have failure:=PDLower.CalibrationCompute.HeapList.value represented.2.1 2 (by change 2<3;decide)
  change state.heap (multiplierSlot upper)=.rational solution.multiplier at price
  change state.heap (statisticsSlot upper)=.rational (originalSolveRecord P fee solution.multiplier).observation at observation
  change state.heap (statisticsSlot upper+1)=.rational (originalSolveRecord P fee solution.multiplier).repairs at repairs
  change state.heap (statisticsSlot upper+2)=.rational (originalSolveRecord P fee solution.multiplier).failure at failure
  have records : originalSolveRecord P fee solution.multiplier=P.solveRecord solution := by
    unfold originalSolveRecord
    exact congrArg P.solveRecord original.symm
  rw [records] at observation repairs failure
  exact ⟨price,observation,repairs,failure⟩

/-- Stopping/selector scripts return all source metadata below29
unchanged. Combine that fact with their actual scalar frame, rather
than inferring unchanged fields from the much wider Header48 frame. -/
theorem scalar_final_region {before after : State}
    (memory : MemoryFrame scalarRegion before after ∧ HeaderMemory before after 0)
    (low : ∀ slot<29,after.heap slot=before.heap slot) :
    RegionMemory before after (Finset.Icc 29 42) := by
  refine ⟨?_,?_,?_,memory.2.2.2⟩
  · intro address outside
    by_cases below : address<29
    · exact low address below
    · apply memory.1.1
      intro member
      have bounds:=Finset.mem_Icc.mp member
      exact outside (Finset.mem_Icc.mpr ⟨by omega,bounds.2⟩)
  · rw [memory.2.2.1]
    exact Finset.subset_union_left
  · rw [memory.2.2.1]

theorem SolvedBuffer.preserve_low_scalars {P : Parameters} {fee penalty : ℚ} {upper : Bool}
    {before after : State} (represented : SolvedBuffer P fee penalty upper before)
    (memory : MemoryFrame scalarRegion before after ∧ HeaderMemory before after 0)
    (low : ∀ slot<29,after.heap slot=before.heap slot) :
    SolvedBuffer P fee penalty upper after := by
  have actual:=scalar_final_region memory low
  have tableLower : 48≤retainedTableBase (99+2*P.certificate.M) P.certificate.stages P.tools upper := by
    have bound:=retained_base_above_workspace (99+2*P.certificate.M) P.certificate.stages P.tools upper
    unfold workspaceSize headerWords at bound
    omega
  apply represented.preserve _ actual
  · intro offset inside
    simp only [Finset.mem_Icc]
    cases upper <;> simp only [multiplierSlot,Bool.false_eq_true,ite_false,ite_true] <;> omega
  · intro offset inside
    simp only [Finset.mem_Icc]
    cases upper <;> simp only [statisticsSlot,Bool.false_eq_true,ite_false,ite_true] <;> omega
  · intro offset inside
    simp only [Finset.mem_Icc]
    cases upper <;> simp only [tableLengthSlot,Bool.false_eq_true,ite_false,ite_true] <;> omega
  · intro offset _inside
    simp only [Finset.mem_Icc]
    omega

private theorem tag_preserve {before after : State} (value : Cell)
    (stored : HeapList before 13 [value]) (memory : RegionMemory before after (Finset.Icc 29 42)) :
    HeapList after 13 [value] := by
  apply memory.heapList stored
  intro offset inside
  change offset<1 at inside
  simp only [Finset.mem_Icc]
  omega

theorem SearchStateRep.preserve_low_scalars {P : Parameters} {fee : ℚ} {source : MultiplierState}
    {before after : State} (represented : SearchStateRep P fee before source)
    (memory : MemoryFrame scalarRegion before after ∧ HeaderMemory before after 0)
    (low : ∀ slot<29,after.heap slot=before.heap slot) :
    SearchStateRep P fee after source := by
  have actual:=scalar_final_region memory low
  cases source with
  | exact solution =>
    obtain ⟨original,tag,buffer⟩:=represented
    exact ⟨original,tag_preserve _ tag actual,buffer.preserve_low_scalars memory low⟩
  | bracket lower upper =>
    obtain ⟨lowerOriginal,upperOriginal,tag,lowerBuffer,upperBuffer⟩:=represented
    exact ⟨lowerOriginal,upperOriginal,tag_preserve _ tag actual,
      lowerBuffer.preserve_low_scalars memory low,upperBuffer.preserve_low_scalars memory low⟩

end RootD27.Core
