module
public import Paid.PDCompute_Pack_Code_002
public import Paid.PDCompute_SolverDenseWriteBlock_077

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

theorem short_write_code : writeSlots [24,27,28,29]=denseWriteCellCode 24++denseWriteBlockCode 27 3 := rfl
theorem test_write_code : writeSlots [24,25,26,27,28,29]=denseWriteBlockCode 24 6 := rfl

/-- Actual non-test emission skips the two working action words.
The singleton and the three contiguous cost words reuse frozen075/077. -/
theorem short_write_trace (program : Program) (input : List Cell) (before : State)
    (base pointer : ℕ) (values : ℕ → Cell) (tag observation repairs failure : Cell)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hpointer : before.register .old=.natural pointer)
    (htag : values 24=tag) (ho : values 27=observation) (hr : values 28=repairs) (hf : values 29=failure)
    (outside : ∀ offset<4,pointer+offset<base ∨ base+headerWords≤pointer+offset)
    (fetched : FetchesCode program before.pc (writeSlots [24,27,28,29])) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤435 ∧
      Header after base values ∧ PDLower.CalibrationCompute.HeapList after pointer [tag,observation,repairs,failure] ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural (pointer+4) ∧
      after.pc=before.pc+24 ∧ after.output=before.output ∧
      ∀ state∈trace,RegionMemory before state (cellRegion pointer 4) := by
  rw [short_write_code] at fetched
  let first:=denseWriteCellResult before base 24 pointer
  obtain ⟨firstTrace,firstHead,firstLast,firstChain,firstTime,firstMemory⟩:=
    denseWriteCell_trace program input before base 24 pointer values header (by decide) hbase hpointer fetched.append_left
  have firstHeader : Header first base values := denseWriteCellResult_header before base 24 pointer values header
    (by simpa only [Nat.add_zero] using outside 0 (by decide))
  have firstBase : first.register .fresh=.natural base := hbase
  have firstPointer : first.register .old=.natural (pointer+1) := rfl
  have firstPC : first.pc=before.pc+6 := rfl
  have firstValue : first.heap pointer=tag := by
    change Function.update before.heap pointer (before.heap (base+24)) pointer=tag
    rw [Function.update_self,header.value 24 (by decide),htag]
  have contents : ∀ (offset : ℕ) (inside : offset<[observation,repairs,failure].length),
      values (27+offset)=[observation,repairs,failure][offset] := by
    intro offset inside
    simp only [List.length_cons,List.length_nil] at inside
    interval_cases offset <;> assumption
  have tailOutside : ∀ offset<[observation,repairs,failure].length,
      pointer+1+offset<base ∨ base+headerWords≤pointer+1+offset := by
    intro offset inside
    have h:=outside (offset+1) (by simp only [List.length_cons,List.length_nil] at inside;omega)
    simpa only [Nat.add_assoc,Nat.add_comm 1 offset] using h
  have tailFetch : FetchesCode program first.pc (denseWriteBlockCode 27 3) := fetched.append_right
  obtain ⟨tail,after,tailHead,tailLast,tailChain,tailTime,afterHeader,tailHeap,afterBase,afterPointer,afterPC,afterOutput,tailMemory⟩:=
    denseWriteBlock_trace program input [observation,repairs,failure] first base 27 (pointer+1) values firstHeader
      (by change 30≤48;decide) firstBase firstPointer contents tailOutside tailFetch
  have tailFinal:=RegionMemory.trace_last tailMemory tailLast
  have firstRegion : ∀ state∈firstTrace,RegionMemory before state (cellRegion pointer 4) := by
    intro state member
    exact (firstMemory state member).region ((mem_cellRegion_iff pointer 4 pointer).mpr (by omega))
  have tailRegion : ∀ state∈tail,RegionMemory first state (cellRegion pointer 4) := by
    intro state member
    exact (tailMemory state member).enlarge (cellRegion_tail_subset pointer 3)
  have joined:=joinTrace_spec program input firstTrace tail before first after 105 330
    firstHead firstLast tailHead tailLast firstChain tailChain firstTime tailTime
  refine ⟨joinTrace firstTrace tail,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    afterHeader,?_,afterBase,?_,?_,afterOutput,
    RegionMemory.join_trace firstTrace tail before first _ firstLast firstRegion tailRegion⟩
  · apply PDLower.CalibrationCompute.HeapList.of_values
    · intro offset inside
      cases offset with
      | zero =>
        simp only [Nat.add_zero]
        apply tailFinal.2.2.1
        exact Finset.mem_insert_self _ _
      | succ offset =>
        have bound : offset<[observation,repairs,failure].length := by
          simp only [List.length_cons,List.length_nil] at inside ⊢
          omega
        have live:=tailHeap.1 offset bound
        simpa only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm 1 offset] using live
    · intro offset inside
      cases offset with
      | zero =>
        change after.heap (pointer+0)=tag
        rw [Nat.add_zero,tailFinal.1 pointer (by rw [mem_cellRegion_iff];omega)]
        exact firstValue
      | succ offset =>
        have bound : offset<[observation,repairs,failure].length := by
          simp only [List.length_cons,List.length_nil] at inside ⊢
          omega
        have value:=PDLower.CalibrationCompute.HeapList.value tailHeap offset bound
        change after.heap (pointer+Nat.succ offset)=[observation,repairs,failure][offset]
        simpa only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm 1 offset] using value
  · rw [afterPointer]
    congr 1
  · rw [afterPC,firstPC]
    rfl

end PDCompute.Pack
