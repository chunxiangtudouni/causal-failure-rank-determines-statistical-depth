module
public import Paid.PDCompute_CoreSelector_Actual_004
public import Paid.PDCompute_CoreFinalTail_Resources_001
public import Paid.PDCompute_CoreGlobalBudget_Search_004
public import Paid.PDCompute_CoreMemory_Output_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace PDCompute.CoreFinalization
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open RootD27.Core PDLower.CoreSearch PDCompute.CoreSearchLoop

theorem code_eq (origin : ℕ) :
    finalizationCode origin=finalSelectorCode origin++PDCompute.CoreFinalTail.code (origin+180) := by
  simp only [finalizationCode,PDCompute.CoreFinalTail.code,Nat.add_assoc,List.append_assoc]

theorem fetch_parts (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (finalizationCode origin)) :
    FetchesCode program origin (finalSelectorCode origin) ∧
    FetchesCode program (origin+180) (PDCompute.CoreFinalTail.code (origin+180)) := by
  rw [code_eq] at fetched
  exact ⟨fetched.append_left,by simpa only [finalSelector_length] using fetched.append_right⟩

theorem original_solved_length (P : Parameters) (fee : ℚ) (solution : MultiplierSolve)
    (solved : OriginalSolved P fee solution) :
    (encodeTable solution.table).length≤8*PDCompute.Solver.entryCount P.certificate.stages P.tools := by
  have encoding:=original_solution_encoding P fee solution solved
  have bound:=PDCompute.CoreMemory.original_table_length_le P fee solution.multiplier P.certificate.stages P.tools
  change (originalSolveEncoding P fee solution.multiplier).length≤_ at bound
  rw [encoding] at bound
  exact bound

theorem represented_state_length (P : Parameters) (fee : ℚ) (source : MultiplierState) (state : State)
    (represented : SearchStateRep P fee state source) :
    (encodeState source).length≤16*PDCompute.Solver.entryCount P.certificate.stages P.tools+3 := by
  apply PDCompute.CoreMemory.encodeState_length_le
  cases source with
  | exact solution=>exact original_solved_length P fee solution represented.1
  | bracket lower upper=>exact ⟨original_solved_length P fee lower represented.1,
      original_solved_length P fee upper represented.2.1⟩

theorem scalar_live_eq {before after : State}
    (header : Header before 0 (fun slot=>before.heap slot)) (memory : RegionMemory before after scalarRegion) :
    after.live=before.live := by
  have existing : scalarRegion⊆before.live := by
    intro address member
    have bounds:=Finset.mem_Icc.mp member
    simpa only [Nat.zero_add] using header.live address (by change address<48;omega)
  apply Finset.Subset.antisymm
  · intro address live
    rcases Finset.mem_union.mp (memory.2.1 live) with old|written
    · exact old
    · exact existing written
  · exact memory.2.2.1

/-- One fixed heap-write region with a separate actual output prefix.
RegionMemory's output-unchanged field is deliberately NOT asserted for
the emitting phase. Selector heap changes remain visible and allowed. -/
structure OutputRegion (before : State) (cells : List Cell) (current : State) : Prop where
  heapOutside : ∀ address,address∉scalarRegion→current.heap address=before.heap address
  live : current.live=before.live
  emitted : ∃ written pending : List Cell,cells=written++pending ∧ current.output=before.output++written

theorem OutputRegion.of_scalar {before current : State} (cells : List Cell)
    (header : Header before 0 (fun slot=>before.heap slot)) (memory : RegionMemory before current scalarRegion) :
    OutputRegion before cells current :=
  ⟨memory.1,scalar_live_eq header memory,[],cells,by simp,by simpa using memory.2.2.2⟩

theorem OutputRegion.of_emitted {before selected current : State} {cells : List Cell}
    (header : Header before 0 (fun slot=>before.heap slot)) (memory : RegionMemory before selected scalarRegion)
    (output : selected.output=before.output) (emitted : EmittedPrefix selected cells current) :
    OutputRegion before cells current := by
  obtain ⟨heap,live,written,pending,decomposition,writtenOutput⟩:=emitted
  exact ⟨fun address outside=>by rw [heap];exact memory.1 address outside,
    live.trans (scalar_live_eq header memory),written,pending,decomposition,by simpa only [output] using writtenOutput⟩

theorem OutputRegion.space {before current : State} {cells : List Cell}
    (actual : OutputRegion before cells current) : workingCells current≤workingCells before+cells.length := by
  obtain ⟨written,pending,decomposition,output⟩:=actual.emitted
  have length:=congrArg List.length decomposition
  simp only [List.length_append] at length
  unfold workingCells
  rw [actual.live,output,List.length_append]
  omega

theorem OutputRegion.output_length {before current : State} {cells : List Cell}
    (actual : OutputRegion before cells current) : current.output.length≤before.output.length+cells.length := by
  obtain ⟨written,pending,decomposition,output⟩:=actual.emitted
  have length:=congrArg List.length decomposition
  simp only [List.length_append] at length
  rw [output,List.length_append]
  omega

theorem live_selector (state : State) (weight : ℚ) (header : Header state 0 (fun slot=>state.heap slot))
    (value : state.heap 29=.rational weight) : HeapList state 29 [.rational weight] := by
  apply PDLower.CalibrationCompute.HeapList.of_values
  · intro offset inside
    have zero : offset=0:=by change offset<1 at inside;omega
    subst offset
    simpa only [Nat.add_zero,Nat.zero_add] using header.live 29 (by decide)
  · intro offset inside
    have zero : offset=0:=by change offset<1 at inside;omega
    subst offset
    simpa only [Nat.add_zero,List.getElem_cons_zero] using value

end PDCompute.CoreFinalization
