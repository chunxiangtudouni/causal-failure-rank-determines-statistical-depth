module

public import Paid.PDCompute_SolverPackBridge_141
public import Paid.PDCompute_Pack_Resources_095

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

/-- Actual serializer writes only Header+result, preserving the REAL
original dense table on the SAME trace, including its final root cell. -/
theorem DenseOriginalTable.after_serializer {before after : State} {P : Parameters} {fee penalty : ℚ} {base n k : ℕ}
    (dense : DenseOriginalTable before P fee penalty base n k)
    (memory : RegionMemory before after (PDCompute.Pack.writeRegion base n k)) :
    DenseOriginalTable after P fee penalty base n k := by
  intro row rowBound column columnBound
  apply memory.heapList (dense row rowBound column columnBound)
  intro offset inside
  have bound : offset<entryWords := by simpa only [denseEncodeEntry_length] using inside
  exact PDCompute.Pack.dense_outside_writeRegion base n k row column offset rowBound columnBound bound

/-- Consumer from an ACTUAL original matrix's independently produced
dense cells. Select095's resource witness ONCE; final dense root and ALL
serializer bits belong to this SAME real functional/time/space trace. -/
theorem serializer_original_table_resources (program : Program) (input : List Cell) (origin : ℕ)
    (P : Parameters) (fee penalty : ℚ) (before : State) (base n k returnPC : ℕ) (values : ℕ → Cell)
    (code : FetchesCode program origin (PDCompute.Pack.serializerCode origin)) (pc : before.pc=origin)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hn : values 3=.natural n) (hk : values 4=.natural k) (savedReturn : values 1=.natural returnPC)
    (dense : DenseOriginalTable before P fee penalty base n k) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤4096*(n+1)*(k+1) ∧
      PDLower.CalibrationCompute.HeapList after (resultBase base n k) (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n)) ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural returnPC ∧
      after.register .address=.natural (resultBase base n k) ∧ after.register .index=.natural (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n)).length ∧
      after.pc=returnPC ∧ after.output=before.output ∧ peakCells trace≤workingCells before+62*entryCount n k ∧
      peakOperandBits trace≤PDCompute.Pack.serializerBudget before n k origin ∧
      (∀ state∈trace,RegionMemory before state (PDCompute.Pack.writeRegion base n k)) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state (PDCompute.Pack.serializerBudget before n k origin)) ∧
      (∀ state∈trace,DenseOriginalTable state P fee penalty base n k) ∧
      PDLower.CalibrationCompute.HeapList after (cellBase base k n k)
        (denseEncodeEntry (menuEntryAt (P.cachedSolveMenuTable P.endpointCache fee penalty k n) n k)) := by
  obtain ⟨trace,after,head,last,chain,timeBound,heap,afterBase,afterOld,afterAddress,afterIndex,afterPC,afterOutput,space,bits,memory,safe⟩:=
    PDCompute.Pack.serializer_cells_resources program input origin (P.cachedSolveMenuTable P.endpointCache fee penalty k n)
      before base n k returnPC values code pc header fresh hn hk savedReturn (originalTable_rows P fee penalty n k)
      (originalTable_columns P fee penalty n k) dense.pack_cells
  have allDense : ∀ state∈trace,DenseOriginalTable state P fee penalty base n k :=
    fun state member=>dense.after_serializer (memory state member)
  have root:=(allDense after (List.mem_of_getLast? last)) n (le_refl _) k (le_refl _)
  exact ⟨trace,after,head,last,chain,timeBound,heap,afterBase,afterOld,afterAddress,afterIndex,afterPC,afterOutput,space,bits,memory,safe,allDense,root⟩

end PDCompute.Solver
