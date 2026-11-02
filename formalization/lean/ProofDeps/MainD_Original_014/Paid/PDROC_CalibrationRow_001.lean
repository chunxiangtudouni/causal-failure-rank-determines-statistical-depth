module

public import Paid.PDLower_CalibrationCompute_Trace_012
public import Paid.PDLower_CalibrationCompute_Fresh_013
public import Paid.PDLower_CalibrationCompute_Rows_007
public import Paid.PDLower_CalibrationCompute_Header_006
public import Paid.PDMenu_ComputeFrame_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Only these five header words and the two row buffers may change.
The result cache starts immediately after this region. -/
def region (base M : ℕ) : Finset ℕ :=
  Finset.Icc (base+6) (base+10) ∪
    (Finset.range (2*rowWidth M)).image (fun i => base+16+i)

theorem mem_region (base M address : ℕ) : address ∈ region base M ↔
    (base+6 ≤ address ∧ address ≤ base+10) ∨
    (base+16 ≤ address ∧ address < resultBase base M) := by
  simp only [region,Finset.mem_union,Finset.mem_Icc,Finset.mem_image,Finset.mem_range]
  constructor
  · rintro (header|⟨i,inside,equal⟩)
    · exact Or.inl header
    · right
      unfold resultBase
      omega
  · rintro (header|⟨lower,upper⟩)
    · exact Or.inl header
    · right
      refine ⟨address-(base+16),?_,?_⟩
      · unfold resultBase at upper
        omega
      · omega

theorem header_mem_region (base M offset : ℕ) (low : 6 ≤ offset) (high : offset ≤ 10) :
    base+offset ∈ region base M :=
  (mem_region base M _).mpr (Or.inl (by omega))

theorem first_mem_region (base M index : ℕ) (inside : index < rowWidth M) :
    firstRow base+index ∈ region base M := by
  apply (mem_region base M _).mpr
  right
  unfold firstRow resultBase
  omega

theorem second_mem_region (base M index : ℕ) (inside : index < rowWidth M) :
    secondRow base M+index ∈ region base M := by
  apply (mem_region base M _).mpr
  right
  unfold secondRow resultBase
  omega

theorem result_outside (base M address : ℕ) (afterRows : resultBase base M ≤ address) :
    address ∉ region base M := by
  rw [mem_region]
  unfold resultBase at *
  omega

theorem header_outside (base M offset : ℕ) (bound : offset < 16)
    (preservedOffset : offset < 6 ∨ 10 < offset) : base+offset ∉ region base M := by
  rw [mem_region]
  omega

/-- Physical premises supplied by the original caller. No row contents,
clock, cursor, read/write pointers or successful execution are assumed. -/
structure Header (P : Parameters) (base level : ℕ) (state : State) : Prop where
  fresh : state.register .fresh=.natural base
  live : ∀ offset < 16, base+offset ∈ state.live
  M : state.heap (base+2)=.natural P.certificate.M
  Q : state.heap (base+3)=.natural P.certificate.Q
  gamma : state.heap (base+4)=.rational P.certificate.gamma
  level : state.heap (base+5)=.natural level
  leftBias : state.heap (base+12)=.rational (1/2-P.certificate.gamma)
  rightBias : state.heap (base+13)=.rational (1/2+P.certificate.gamma)

theorem Header.transport (P : Parameters) (base level : ℕ) (before after : State)
    (header : Header P base level before)
    (frame : MemoryFrame (region base P.certificate.M) before after)
    (live : before.live ⊆ after.live)
    (fresh : after.register .fresh=before.register .fresh) : Header P base level after := by
  refine ⟨fresh.trans header.fresh,fun offset inside => live (header.live offset inside),?_,?_,?_,?_,?_,?_⟩
  · exact (frame.1 _ (header_outside base _ 2 (by decide) (by decide))).trans header.M
  · exact (frame.1 _ (header_outside base _ 3 (by decide) (by decide))).trans header.Q
  · exact (frame.1 _ (header_outside base _ 4 (by decide) (by decide))).trans header.gamma
  · exact (frame.1 _ (header_outside base _ 5 (by decide) (by decide))).trans header.level
  · exact (frame.1 _ (header_outside base _ 12 (by decide) (by decide))).trans header.leftBias
  · exact (frame.1 _ (header_outside base _ 13 (by decide) (by decide))).trans header.rightBias

/-- The true physical orientation is allowed to swap after each update. -/
def Buffers (base M read write : ℕ) : Prop :=
  (read=firstRow base ∧ write=secondRow base M) ∨
    (read=secondRow base M ∧ write=firstRow base)

theorem Buffers.separate (base M read write : ℕ) (buffers : Buffers base M read write)
    (i j : ℕ) (hi : i < rowWidth M) (hj : j < rowWidth M) : read+i ≠ write+j := by
  rcases buffers with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> unfold firstRow secondRow <;> omega

theorem activeWidth_le (M level : ℕ) (levelBound : level ≤ M+1) : 2*level+1 ≤ rowWidth M := by
  unfold rowWidth
  omega

/-- Strong frames preserve every previously emitted result cell, not
only memory outside the larger whole-calibration workspace. -/
theorem results_preserved (base M : ℕ) (before after : State)
    (frame : MemoryFrame (region base M) before after) (index : ℕ) :
    after.heap (resultBase base M+index)=before.heap (resultBase base M+index) ∧
    (resultBase base M+index ∈ after.live ↔ resultBase base M+index ∈ before.live) := by
  have outside := result_outside base M (resultBase base M+index) (Nat.le_add_right _ _)
  exact ⟨frame.1 _ outside,frame.2 _ outside⟩

end PDROC.CalibrationRow
