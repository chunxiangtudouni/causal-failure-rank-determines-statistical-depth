module

public import Paid.PDROC_CalibrationRow_002
public import Paid.PDROC_CalibrationRow_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Nine real non-storing instructions followed by the one header8 store. -/
def widthPrefixCode : List Instruction :=
  loadSlot 5 .index ++
    [.constant .flag (.natural 2),.natOp .multiply .index .index .flag,
      .constant .flag (.natural 1),.natOp .add .index .index .flag,
      .constant .address (.natural 8),.natOp .add .address .fresh .address]

theorem widthCode_decompose : widthCode=widthPrefixCode++[.store .address .index] := rfl

theorem widthPrefixCode_length : widthPrefixCode.length=9 := rfl

theorem widthCode_length : widthCode.length=10 := rfl

theorem widthPrefix_static (region : Finset ℕ) :
    ∀ instruction ∈ widthPrefixCode,∀ state,WritesWithin region instruction state := by
  intro instruction member state
  simp only [widthPrefixCode,loadSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (h|h|h)|(h|h|h|h|h|h) <;> subst instruction <;> trivial

/-- Every actual prefix preserves the same precise row-subroutine region;
no final-frame assumption replaces the intermediate physical stores. -/
theorem width_prefix_frames (input : List Cell) (before : State) (base level M : ℕ)
    (fresh : before.register .fresh=.natural base)
    (live : base+5 ∈ before.live) (value : before.heap (base+5)=.natural level) :
    LinearFrames (region base M) input widthCode before := by
  intro count after executed
  by_cases short : count ≤ widthPrefixCode.length
  · rw [widthCode_decompose,List.take_append_of_le_length short] at executed
    exact LinearFrames.of_static (region base M) input widthPrefixCode (widthPrefix_static _) before count after executed
  · have all : widthCode.length ≤ count := by rw [widthCode_length]; rw [widthPrefixCode_length] at short; omega
    rw [List.take_of_length_le all,width_execute input before base level fresh live value] at executed
    have same : widthResult before base level=after := Option.some.inj executed
    subst after
    exact widthResult_frame before base level M

end PDROC.CalibrationRow
