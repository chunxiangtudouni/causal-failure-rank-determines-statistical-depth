module

public import Paid.PDROC_CalibrationRow_Scatter_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- The real control instruction adds no memory/output/fresh mutation.
Derive the terminal preservation facts from the actual body/control pair,
so every phase can reuse its proved literal-prefix frame. -/
theorem scatterBlock_safe_of_frames (P : Parameters) (origin base level clock cursor read write : ℕ)
    (input : List Cell) (Good : State→Prop)
    (closed : ScatterClosed P origin base level clock read write input Good)
    (label : Label) (row : rowLabel label=true) (before middle after : State)
    (entry : ScatterEntry P base level clock cursor read write before label) (good : Good before)
    (position : before.pc=labelAddress origin label)
    (body : linearExecute input (basicBlock label).body before=some middle)
    (control : (controlInstruction origin (basicBlock label).control).execute input middle=some after)
    (frames : LinearFrames (region base P.certificate.M) input (basicBlock label).body before) :
    SafeSegment origin base (region base P.certificate.M) input Good before after
      (15*((basicBlock label).body.length+2)) := by
  have controlFrame := execute_memoryFrame (region base P.certificate.M)
    (controlInstruction origin (basicBlock label).control) input middle after
    (by cases (basicBlock label).control <;> trivial) control
  have bodyOutput := linearExecute_noOutput input _ (rowBody_noOutput label row) before middle body
  have controlOutput := execute_output_eq_of_noOutput _ input middle after
    (control_noOutput origin (basicBlock label).control) control
  have bodyFresh := rowBody_prefix_fresh input label before middle (basicBlock label).body.length
    (by simpa only [List.take_length] using body)
  have controlFresh := execute_preserves_fresh _ (control_noFresh origin (basicBlock label).control)
    input middle after control
  have bodyLive := linearExecute_live_mono input _ (rowBody_noRelease label row) before middle body
  have controlLive := execute_live_mono _ input middle after
    (by cases (basicBlock label).control <;> rfl) control
  exact scatterBlock_safe P origin base level clock cursor read write input Good closed label row
    before middle after entry good position body control frames ((frames.final body).trans controlFrame)
    (controlOutput.trans bodyOutput) (controlFresh.trans bodyFresh) (bodyLive.trans controlLive)

theorem leftStore_phase_frames (input : List Cell) (P : Parameters)
    (base level clock cursor read write : ℕ) (before : State)
    (data : ScatterData P base level clock cursor read write before)
    (inside : cursor<2*level+1) (levelBound : level≤P.certificate.M+1)
    (index : before.register .index=.natural (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).val)
    (value : before.register .value=.rational ((P.walkRow level true clock).getD cursor 0*(1/2-P.certificate.gamma))) :
    LinearFrames (region base P.certificate.M) input (basicBlock .leftStore).body before := by
  let target := (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).val
  let previous := rowScatterPrefix P level (P.walkRow level true clock) cursor
  let amount := (P.walkRow level true clock).getD cursor 0*(1/2-P.certificate.gamma)
  have targetInRow : target<previous.size := by
    simpa only [previous,rowScatterPrefix_size] using (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).isLt
  have targetBound : target<rowWidth P.certificate.M :=
    (walkMove level ⟨cursor,inside⟩ (0 : Fin 2)).isLt.trans_le (activeWidth_le _ _ levelBound)
  rw [leftStore_body]
  exact scatterStore_prefix_frames _ input before base write target (previous.getD target 0) amount
    data.control.header.fresh (data.control.header.live 10 (by decide)) data.control.write index value
    (data.writeRow.live target targetInRow) (data.writeRow.value target targetInRow)
    (Buffers.write_mem base P.certificate.M read write target data.control.buffers targetBound)

theorem rightStore_phase_frames (input : List Cell) (P : Parameters)
    (base level clock cursor read write : ℕ) (inside : cursor<2*level+1) (before : State)
    (data : ScatterLeftData P base level clock cursor read write inside before)
    (levelBound : level≤P.certificate.M+1)
    (index : before.register .index=.natural (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).val)
    (value : before.register .value=.rational ((P.walkRow level true clock).getD cursor 0*(1/2+P.certificate.gamma))) :
    LinearFrames (region base P.certificate.M) input (basicBlock .rightStore).body before := by
  let target := (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).val
  let previous := rowLeftPrefix P level clock cursor inside
  let amount := (P.walkRow level true clock).getD cursor 0*(1/2+P.certificate.gamma)
  have targetInRow : target<previous.size := by
    simpa only [previous,rowLeftPrefix,PDROC.endpointArrayBump_size,rowScatterPrefix_size] using
      (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).isLt
  have targetBound : target<rowWidth P.certificate.M :=
    (walkMove level ⟨cursor,inside⟩ (1 : Fin 2)).isLt.trans_le (activeWidth_le _ _ levelBound)
  rw [rightStore_body]
  exact scatterStore_prefix_frames _ input before base write target (previous.getD target 0) amount
    data.control.header.fresh (data.control.header.live 10 (by decide)) data.control.write index value
    (data.writeRow.live target targetInRow) (data.writeRow.value target targetInRow)
    (Buffers.write_mem base P.certificate.M read write target data.control.buffers targetBound)

end PDROC.CalibrationRow
