module

public import Paid.PDROC_CalibrationRow_ScatterOperands_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.CalibrationRow.ScatterOperands

open PaperProofs.Paid.Computation PDLower.CalibrationCompute

/-- SSA composition carries the first macro's new sources into the
second macro. Bit-budget composition remains the parent's PrefixSafe;
this lemma records the additional caller-relative equality information. -/
theorem append_prefix_sources (input : List Cell) (first later : List Instruction)
    (before middle after : State) (New : Cell → Prop) (count : ℕ)
    (run : linearExecute input first before = some middle)
    (firstSources : ∀ n ≤ first.length, ∀ state,
      linearExecute input (first.take n) before = some state → Sources before state New)
    (laterSources : ∀ n ≤ later.length, ∀ state,
      linearExecute input (later.take n) middle = some state → Sources middle state New)
    (bound : count ≤ (first ++ later).length)
    (executed : linearExecute input ((first ++ later).take count) before = some after) :
    Sources before after New := by
  by_cases short : count ≤ first.length
  · rw [List.take_append_of_le_length short] at executed
    exact firstSources count short after executed
  · rw [List.take_append, List.take_of_length_le (by omega : first.length ≤ count),
      linearExecute_append, run, Option.bind_some] at executed
    have remaining : count - first.length ≤ later.length := by
      rw [List.length_append] at bound
      omega
    have earlier := firstSources first.length (Nat.le_refl _) middle
      (by simpa only [List.take_length] using run)
    exact earlier.trans (laterSources (count - first.length) remaining after executed)

end PDROC.CalibrationRow.ScatterOperands
