module

public import Paid.PDROC_CalibrationRow_009
public import Paid.PDROC_CalibrationRow_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

theorem levelInit_live (before : State) (base level M : ℕ) :
    before.live ⊆ (levelInitResult before base level M).live := by
  rw [(levelInit_fields before base level M).2.1]
  exact (Finset.subset_insert _ _).trans ((Finset.subset_insert _ _).trans
    ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _)))

theorem levelInit_slots (before : State) (base level M : ℕ) :
    (levelInitResult before base level M).heap (base+7)=.natural 0 ∧
    (levelInitResult before base level M).heap (base+8)=.natural (2*level+1) ∧
    (levelInitResult before base level M).heap (base+9)=.natural (firstRow base) ∧
    (levelInitResult before base level M).heap (base+10)=.natural (secondRow base M) := by
  simp [(levelInit_fields before base level M).1]

theorem levelInit_header (P : Parameters) (before : State) (base level : ℕ)
    (header : Header P base level before) :
    Header P base level (levelInitResult before base level P.certificate.M) :=
  Header.transport P base level before _ header (levelInit_frame before base level _)
    (levelInit_live before base level _) (levelInit_fields before base level _).2.2.1

theorem levelInit_prefix_frames (input : List Cell) (P : Parameters) (before : State) (base level : ℕ)
    (header : Header P base level before) :
    LinearFrames (region base P.certificate.M) input (basicBlock .levelInit).body before := by
  let width := widthResult before base level
  have widthFields := widthResult_fields before base level
  have widthHeader := Header.transport P base level before width header
    (widthResult_frame before base level _) (by rw [widthFields.2.1]; exact Finset.subset_insert _ _)
    widthFields.2.2.1
  let first := firstPointerResult width base
  have firstFields := firstPointer_fields width base
  have firstHeader := Header.transport P base level width first widthHeader
    (firstPointer_frame width base _) (by rw [firstFields.2.1]; exact Finset.subset_insert _ _)
    firstFields.2.2.1
  let second := secondPointerResult first base P.certificate.M
  have secondFresh := (secondPointer_fields first base P.certificate.M).2.2.1.trans firstHeader.fresh
  have widthRun := width_execute input before base level header.fresh (header.live 5 (by decide)) header.level
  have firstRun := firstPointer_execute input width base widthHeader.fresh
  have secondRun := secondPointer_execute input first base P.certificate.M firstHeader.fresh
    firstFields.2.2.2.1 (firstHeader.live 2 (by decide)) firstHeader.M
  have pairRun : linearExecute input (firstPointerCode++secondPointerCode) width=some second := by
    rw [linearExecute_append,firstRun,Option.bind_some,secondRun]
  have pairFrames := LinearFrames.append (region base P.certificate.M) input firstPointerCode secondPointerCode
    width first firstRun (firstPointer_prefix_frames input width base _ widthHeader.fresh)
    (secondPointer_prefix_frames input first base _ firstHeader.fresh firstFields.2.2.2.1
      (firstHeader.live 2 (by decide)) firstHeader.M)
  have restFrames := LinearFrames.append (region base P.certificate.M) input
    (firstPointerCode++secondPointerCode) (constantSlot 7 (.natural 0)) width second pairRun pairFrames
    (constant_prefix_frames _ input second base 7 (.natural 0) secondFresh
      (header_mem_region base _ 7 (by decide) (by decide)))
  have whole := LinearFrames.append (region base P.certificate.M) input widthCode
    ((firstPointerCode++secondPointerCode)++constantSlot 7 (.natural 0)) before width widthRun
    (width_prefix_frames input before base level _ header.fresh (header.live 5 (by decide)) header.level) restFrames
  simpa only [←buffersCode_decompose,←levelInit_decompose] using whole

/-- Actual original levelInit control edge. Its entry assumes no row,
clock, cursor or pointer contents, only the original caller header. -/
theorem levelInit_trace (origin : ℕ) (input : List Cell) (P : Parameters)
    (before : State) (base level : ℕ) (header : Header P base level before)
    (position : before.pc=labelAddress origin .levelInit) :
    ∃ trace : List State,
      trace.head?=some before ∧
      trace.getLast?=some {levelInitResult before base level P.certificate.M with
        pc:=labelAddress origin .initGate} ∧
      trace.IsChain (fun a b => step (locatedBlock origin (kernel origin)) input a=some b) ∧
      time (locatedBlock origin (kernel origin)) trace ≤ 480 ∧
      ∀ state ∈ trace,MemoryFrame (region base P.certificate.M) before state ∧
        state.output=before.output ∧ state.register .fresh=before.register .fresh ∧
        (∀ offset < 16,base+offset ∈ state.live) := by
  let middle := levelInitResult before base level P.certificate.M
  let after : State := {middle with pc:=labelAddress origin .initGate}
  have body := levelInit_execute input P before base level header
  have control : (controlInstruction origin (basicBlock .levelInit).control).execute input middle=some after := rfl
  obtain ⟨trace,head,last,length,chain,cost,prefixes⟩ :=
    row_block_prefix_trace origin input .levelInit before middle after position body control
  refine ⟨trace,head,last,chain,?_,?_⟩
  · change time (locatedBlock origin (kernel origin)) trace ≤ 15*(30+2) at cost
    exact cost
  · intro state member
    rcases prefixes state member with ⟨count,_,run⟩|equal
    · exact ⟨levelInit_prefix_frames input P before base level header count state run,
        rowBody_prefix_output input .levelInit rfl before state count run,
        rowBody_prefix_fresh input .levelInit before state count run,
        fun offset bound => rowBody_prefix_live input .levelInit rfl before state count run (header.live offset bound)⟩
    · subst state
      exact ⟨levelInit_frame before base level P.certificate.M,
        (levelInit_fields before base level P.certificate.M).2.2.2.2,
        (levelInit_fields before base level P.certificate.M).2.2.1,
        fun offset bound => levelInit_live before base level P.certificate.M (header.live offset bound)⟩

end PDROC.CalibrationRow
