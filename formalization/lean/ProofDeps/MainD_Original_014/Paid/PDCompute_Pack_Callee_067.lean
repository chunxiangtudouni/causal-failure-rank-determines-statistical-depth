module
public import Paid.PDCompute_Pack_Run_052
public import Paid.PDCompute_Pack_PeakCells_053
public import Paid.PDCompute_Pack_DenseInput_056

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

/-- Complete actual serializer functional/time/physical-space callee.
Operand bits are a separate unfinished component, not a new premise. -/
theorem serializer_trace_space (program : Program) (input : List Cell) (origin : ℕ) (table : MenuTable)
    (before : State) (base n k returnPC : ℕ) (values : ℕ → Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hn : values 3=.natural n) (hk : values 4=.natural k) (savedReturn : values 1=.natural returnPC)
    (rows : table.size=n+1) (columns : ∀ row∈table,row.size=k+1)
    (dense : HeapList before (tableBase base) (denseRows table.toList)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 4096*(n+1)*(k+1) ∧
      HeapList after (resultBase base n k) (encodeTable table) ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural returnPC ∧
      after.register .address=.natural (resultBase base n k) ∧ after.register .index=.natural (encodeTable table).length ∧
      after.pc=returnPC ∧ after.output=before.output ∧
      peakCells trace ≤ workingCells before+62*PDCompute.Solver.entryCount n k ∧
      ∀ state∈trace,RegionMemory before state (writeRegion base n k) := by
  obtain ⟨trace,after,hh,hl,hchain,ht,heap,afterFresh,afterOld,afterAddress,afterIndex,afterPC,afterOutput,memory⟩:=
    serializer_trace program input origin table before base n k returnPC values code pc header fresh hn hk savedReturn rows columns dense
  exact ⟨trace,after,hh,hl,hchain,ht,heap,afterFresh,afterOld,afterAddress,afterIndex,afterPC,afterOutput,
    prefix_region_peakCells trace before base n k memory,memory⟩

/-- Consumer ABI from genuine per-entry input cells. The fixed literal
program derives the ORIGINAL4/6 encoding and returns by real old-PC. -/
theorem serializer_cells_trace (program : Program) (input : List Cell) (origin : ℕ) (table : MenuTable)
    (before : State) (base n k returnPC : ℕ) (values : ℕ → Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hn : values 3=.natural n) (hk : values 4=.natural k) (savedReturn : values 1=.natural returnPC)
    (rows : table.size=n+1) (columns : ∀ row∈table,row.size=k+1)
    (dense : ∀ (row : ℕ) (rowBound : row<table.size) (column : ℕ) (columnBound : column<table[row].size),
      HeapList before (cellBase base k row column) (denseEncodeEntry table[row][column])) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 4096*(n+1)*(k+1) ∧
      HeapList after (resultBase base n k) (encodeTable table) ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural returnPC ∧
      after.register .address=.natural (resultBase base n k) ∧ after.register .index=.natural (encodeTable table).length ∧
      after.pc=returnPC ∧ after.output=before.output ∧
      peakCells trace ≤ workingCells before+62*PDCompute.Solver.entryCount n k ∧
      ∀ state∈trace,RegionMemory before state (writeRegion base n k) :=
  serializer_trace_space program input origin table before base n k returnPC values code pc header fresh hn hk savedReturn rows columns
    (denseTable_heap before table base k columns dense)

end PDCompute.Pack
