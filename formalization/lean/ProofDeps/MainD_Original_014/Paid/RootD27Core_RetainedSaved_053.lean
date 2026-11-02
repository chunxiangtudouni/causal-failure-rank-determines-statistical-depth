module

public import Paid.RootD27Core_RetainedCopy_037

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

/-- A genuinely computed retained lower/upper table: physically saves
the actual returned pointer/length, reads original N/K, computes the
runtime buffer base, then performs every copy load/store and true return.
No prefilled buffer or additional original-input oracle is assumed. -/
theorem retained_table_copy_saved_actual (P : Parameters) (fee penalty : ℚ)
    (program : Program) (input : List Cell) (before : State) (base returnPC : ℕ) (upper : Bool)
    (prepared : HeapList before 0 (preparedInput P fee))
    (fresh : before.register .fresh=.natural base)
    (address : before.register .address=.natural (resultBase base P.certificate.stages P.tools))
    (index : before.register .index=.natural (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)).length)
    (table : HeapList before (resultBase base P.certificate.stages P.tools)
      (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)))
    (fetched : FetchesCode program before.pc (retainedCopyCode before.pc upper returnPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤150*(encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)).length+360 ∧
      after.pc=returnPC ∧ after.register .old=.natural returnPC ∧ after.register .index=.natural 0 ∧
      HeapList after (retainedTableBase base P.certificate.stages P.tools upper)
        (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)) ∧
      HeapList after (resultBase base P.certificate.stages P.tools)
        (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)) ∧
      HeapList after 0 (preparedInput P fee) ∧ after.output=before.output ∧
      peakCells trace≤workingCells before+
        (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)).length+2 ∧
      (∀ state∈trace,RegionMemory before state (retainedCopyRegion base P.certificate.stages P.tools
        (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)).length upper)) ∧
      HeapList after 46 [.natural (resultBase base P.certificate.stages P.tools),
        .natural (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages)).length] := by
  let n:=P.certificate.stages
  let k:=P.tools
  let cells:=encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n)
  let source:=resultBase base n k
  let target:=retainedTableBase base n k upper
  let region:=retainedCopyRegion base n k cells.length upper
  let middle:=retainedArgumentsResult before base n k source cells.length returnPC upper
  have nLive : 0∈before.live:=prepared.1 0 (by change 0<13;decide)
  have kLive : 1∈before.live:=prepared.1 1 (by change 1<13;decide)
  have nValue : before.heap 0=.natural n:=PDLower.CalibrationCompute.HeapList.value prepared 0 (by change 0<13;decide)
  have kValue : before.heap 1=.natural k:=PDLower.CalibrationCompute.HeapList.value prepared 1 (by change 1<13;decide)
  obtain ⟨setup,sh,sl,sc,st,sm⟩:=retainedArguments_actual program input before base n k source cells.length returnPC upper
    fresh address index nLive kLive nValue kValue fetched.append_left
  have middleMemory : RegionMemory before middle {46,47}:=RegionMemory.trace_last sm sl
  have sourceLower : 48≤source := by unfold source resultBase tableBase headerWords;omega
  have middleTable : HeapList middle source cells := by
    apply PDLower.CalibrationCompute.HeapList.regionMemory table middleMemory
    intro offset _inside
    change source+offset∉({46,47} : Finset ℕ)
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  have copyFetch : FetchesCode program middle.pc (heapCopyCode middle.pc) := by
    have middlePC : middle.pc=before.pc+20:=rfl
    rw [middlePC]
    simpa only [retainedArguments_length] using fetched.append_right
  obtain ⟨copied,after,ch,cl,cc,ct,pc,_nextFresh,_nextAddress,nextIndex,nextOld,copiedTable,sourceRetained,_copyOutput,_copyPeak,cm⟩:=
    heapCopy_actual program input middle.pc returnPC middle source target cells rfl rfl rfl rfl rfl middleTable
      (Or.inl (original_table_before_retained P fee penalty base n k upper)) copyFetch
  have setupMemory : ∀ state∈setup,RegionMemory before state region :=
    fun state member=>(sm state member).enlarge Finset.subset_union_left
  have copyMemory : ∀ state∈copied,RegionMemory middle state region :=
    fun state member=>(cm state member).enlarge Finset.subset_union_right
  have allMemory:=RegionMemory.join_trace setup copied before middle region sl setupMemory copyMemory
  have joined:=joinTrace_spec program input setup copied before middle after 315 (150*cells.length+45)
    sh sl ch cl sc cc st ct
  have finalMemory:=RegionMemory.trace_last allMemory joined.2.1
  have targetLower : 48≤target := by
    have lower:=retained_base_above_workspace base n k upper
    unfold workspaceSize headerWords at lower
    omega
  have middleSaved : HeapList middle 46 [.natural source,.natural cells.length] := by
    apply PDLower.CalibrationCompute.HeapList.of_values
    · intro offset inside
      change offset<2 at inside
      interval_cases offset <;> simp [middle,retainedArgumentsResult]
    · intro offset inside
      change offset<2 at inside
      interval_cases offset <;> simp [middle,retainedArgumentsResult]
  have savedAfter : HeapList after 46 [.natural source,.natural cells.length] := by
    apply PDLower.CalibrationCompute.HeapList.regionMemory middleSaved (RegionMemory.trace_last cm cl)
    intro offset inside
    change offset<2 at inside
    rw [mem_cellRegion_iff]
    omega
  have preparedRetained : HeapList after 0 (preparedInput P fee) := by
    apply PDLower.CalibrationCompute.HeapList.regionMemory prepared finalMemory
    intro offset inside
    change offset<13 at inside
    change 0+offset∉({46,47}∪cellRegion target cells.length)
    intro member
    rcases Finset.mem_union.mp member with scratch|destination
    · have alternatives : 0+offset=46 ∨ 0+offset=47 := by
        simpa only [Finset.mem_insert,Finset.mem_singleton] using scratch
      omega
    · have bounds:=(mem_cellRegion_iff target cells.length (0+offset)).mp destination
      omega
  have card : region.card≤cells.length+2 := by
    have destination : (cellRegion target cells.length).card≤cells.length := by
      unfold cellRegion
      exact Finset.card_image_le.trans (by rw [Finset.card_range])
    have scratch : ({46,47} : Finset ℕ).card=2:=by decide
    have unionBound:=Finset.card_union_le ({46,47} : Finset ℕ) (cellRegion target cells.length)
    rw [scratch] at unionBound
    exact unionBound.trans (by omega)
  have allSpace : ∀ state∈joinTrace setup copied,workingCells state≤workingCells before+cells.length+2 := by
    intro state member
    have bound:=(allMemory state member).workingCells_le
    omega
  have budget : 315+(150*cells.length+45)≤150*cells.length+360:=by omega
  exact ⟨joinTrace setup copied,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2.trans budget,
    pc,nextOld,nextIndex,copiedTable,sourceRetained,preparedRetained,finalMemory.2.2.2,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allMemory,savedAfter⟩

end RootD27.Core
