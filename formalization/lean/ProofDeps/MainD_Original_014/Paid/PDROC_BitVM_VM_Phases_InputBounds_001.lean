module

public import Paid.PDROC_BitVM_VM_BoundaryBudget_Output_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.VM.Phases.InputBounds

open PaperProofs.Paid.Computation

/-! Pure size bridges for the ACTUAL thirteen-cell prepare output.
No source run/output is manufactured, no physical bank is overridden,
and no relation to the raw6 input length is assumed or proved here. -/

theorem header_thirteen : (encodeNatBits 13).length = 9 := by decide

theorem encoded_thirteen (cells : List Cell) (budget : ℕ)
    (count : cells.length = 13) (bounded : ∀ cell ∈ cells, cell.bits ≤ budget) :
    (encodeBits cells).length ≤ 26 * budget + 10 := by
  have payload := BoundaryBudget.encoded_cells_length cells budget bounded
  have header : (encodeNatBits cells.length).length = 9 := by rw [count]; exact header_thirteen
  rw [count] at payload
  simp only [encodeBits, List.length_append, List.length_singleton]
  rw [header]
  omega

/-- The final state's cell-width witness is derived from the peak of
this SAME actual Runs, not from an unrelated desired thirteen-vector. -/
theorem runs_thirteen (code : Program) (input : List Cell) (states : List State) (final : State)
    (actual : Runs code input states final) (cells : List Cell) (output : final.output = cells)
    (count : cells.length = 13) (budget : ℕ) (peak : peakOperandBits states ≤ budget) :
    (encodeBits cells).length ≤ 26 * budget + 10 := by
  have member : final ∈ states := List.mem_of_mem_getLast? (by rw [actual.2.2.1]; rfl)
  have allBits := BoundaryBudget.state_bits_of_peak states budget peak final member
  apply encoded_thirteen cells budget count
  intro cell inCells
  apply BoundaryBudget.output_cell_bits final budget allBits cell
  simpa only [output] using inCells

/-- Checked against the original definition: rawInput has six original
fields and preparedInput appends exactly seven actually computed fields. -/
theorem prepared_count (P : PaperProofs.Paid.Parameters) (fee : ℚ) : (preparedInput P fee).length = 13 := rfl

theorem prepared_from_runs (code : Program) (P : PaperProofs.Paid.Parameters) (fee : ℚ)
    (states : List State) (final : State) (actual : Runs code (rawInput P fee) states final)
    (output : final.output = preparedInput P fee) (budget : ℕ) (peak : peakOperandBits states ≤ budget) :
    (encodeBits (preparedInput P fee)).length ≤ 26 * budget + 10 :=
  runs_thirteen code (rawInput P fee) states final actual (preparedInput P fee) output (prepared_count P fee) budget peak

end PDROC.BitVM.VM.Phases.InputBounds
