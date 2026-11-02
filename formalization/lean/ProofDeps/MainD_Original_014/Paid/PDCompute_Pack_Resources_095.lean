module
public import Paid.PDCompute_Pack_RunBits_094
public import Paid.PDCompute_Pack_Callee_067

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

/-- The original233-op serializer with original4/6 output, actual saved
return, linear time, all-prefix physical frame/peak and SAME trace bits.
All numeric bounds are derived from the actual entry and original table
shape. Arbitrary initial registers, live heap and output are paid by
initialBits; no P-only bound on prior caller scratch is assumed. -/
theorem serializer_trace_resources (program : Program) (input : List Cell) (origin : ℕ) (table : MenuTable)
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
      peakOperandBits trace ≤ serializerBudget before n k origin ∧
      (∀ state∈trace,RegionMemory before state (writeRegion base n k)) ∧
      (∀ state∈trace,SafeBits state (serializerBudget before n k origin)) := by
  obtain ⟨trace,after,hh,hl,hchain,ht,heap,afterFresh,afterOld,afterAddress,afterIndex,afterPC,afterOutput,memory,bits⟩:=
    serializer_trace_budget program input origin table before base n k returnPC values code pc header fresh hn hk savedReturn rows columns dense
  exact ⟨trace,after,hh,hl,hchain,ht,heap,afterFresh,afterOld,afterAddress,afterIndex,afterPC,afterOutput,
    prefix_region_peakCells trace before base n k memory,safeBits_peak trace _ bits,memory,bits⟩

/-- Consumer ABI from genuine per-entry input cells. The fixed literal
program derives the ORIGINAL4/6 encoding and returns by real old-PC. -/
theorem serializer_cells_resources (program : Program) (input : List Cell) (origin : ℕ) (table : MenuTable)
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
      peakOperandBits trace ≤ serializerBudget before n k origin ∧
      (∀ state∈trace,RegionMemory before state (writeRegion base n k)) ∧
      (∀ state∈trace,SafeBits state (serializerBudget before n k origin)) :=
  serializer_trace_resources program input origin table before base n k returnPC values code pc header fresh hn hk savedReturn rows columns
    (denseTable_heap before table base k columns dense)


end PDCompute.Pack
