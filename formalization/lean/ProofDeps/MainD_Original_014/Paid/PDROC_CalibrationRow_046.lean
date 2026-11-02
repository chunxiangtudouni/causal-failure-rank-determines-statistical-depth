module

public import Paid.PDROC_CalibrationRow_041
public import Paid.PDROC_CalibrationRow_014
public import Paid.PDROC_CalibrationRow_010
public import Paid.PDROC_CalibrationRow_Init_SafeSegment_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- An actual instruction prefix, or the state after the actual control
instruction. The concrete entry state carries all unmodified operands. -/
def BlockPrefix (input : List Cell) (label : Label) (before after state : State) : Prop :=
  (∃ count≤(basicBlock label).body.length,
    linearExecute input ((basicBlock label).body.take count) before=some state) ∨ state=after

theorem levelInit_safe (input : List Cell) (P : Parameters) (origin base level : ℕ)
    (before : State) (header : Header P base level before)
    (position : before.pc=labelAddress origin .levelInit) (Good : State→Prop)
    (provenance : ∀ state,BlockPrefix input .levelInit before
      {levelInitResult before base level P.certificate.M with pc:=labelAddress origin .initGate} state→Good state) :
    SafeSegment origin base (region base P.certificate.M) input Good before
      {levelInitResult before base level P.certificate.M with pc:=labelAddress origin .initGate} 480 := by
  let middle := levelInitResult before base level P.certificate.M
  let after : State := {middle with pc:=labelAddress origin .initGate}
  exact SafeSegment.ofBlock origin base _ input Good .levelInit rfl before middle after position
    (levelInit_execute input P before base level header) rfl
    (levelInit_prefix_frames input P before base level header) header.live
    (levelInit_frame before base level P.certificate.M)
    (levelInit_fields before base level P.certificate.M).2.2.2.2
    (levelInit_fields before base level P.certificate.M).2.2.1
    (levelInit_live before base level P.certificate.M) provenance

/-- Real reset6/reset7 blocks. In particular reset6 accepts an arbitrary
incoming heap6 Cell; its type is established by the actual final store. -/
theorem constantRow_safe (input : List Cell) (P : Parameters) (origin base level offset : ℕ)
    (label target : Label) (before : State) (header : Header P base level before)
    (row : rowLabel label=true) (position : before.pc=labelAddress origin label)
    (code : (basicBlock label).body=constantSlot offset (.natural 0))
    (jump : (basicBlock label).control=.go target) (offsetLow : 6≤offset) (offsetHigh : offset≤10)
    (Good : State→Prop)
    (provenance : ∀ state,BlockPrefix input label before
      {constantSlotResult before base offset (.natural 0) with pc:=labelAddress origin target} state→Good state) :
    SafeSegment origin base (region base P.certificate.M) input Good before
      {constantSlotResult before base offset (.natural 0) with pc:=labelAddress origin target} 90 := by
  let middle := constantSlotResult before base offset (.natural 0)
  let after : State := {middle with pc:=labelAddress origin target}
  have body : linearExecute input (basicBlock label).body before=some middle := by
    rw [code]
    exact constantSlot_execute input before base offset (.natural 0) header.fresh
  have control : (controlInstruction origin (basicBlock label).control).execute input middle=some after := by
    rw [jump]
    rfl
  have frames : LinearFrames (region base P.certificate.M) input (basicBlock label).body before := by
    rw [code]
    exact constant_prefix_frames _ input before base offset (.natural 0) header.fresh
      (header_mem_region base _ offset offsetLow offsetHigh)
  have lastFrame : MemoryFrame (region base P.certificate.M) before after := by
    change MemoryFrame _ before middle
    exact frames.final body
  have lastLive : before.live ⊆ after.live := by
    change before.live ⊆ middle.live
    rw [constantSlot_live]
    exact Finset.subset_insert _ _
  have run := SafeSegment.ofBlock origin base _ input Good label row before middle after position body control
    frames header.live lastFrame (constantSlot_output before base offset (.natural 0))
    (constantSlot_fresh before base offset (.natural 0)) lastLive provenance
  have length : (basicBlock label).body.length=4 := by rw [code]; rfl
  simpa only [length] using run

theorem stepGate_safe (input : List Cell) (P : Parameters) (origin base level clock : ℕ)
    (before : State) (data : StepData P base level clock before)
    (position : before.pc=labelAddress origin .stepGate) (Good : State→Prop)
    (provenance : ∀ state,BlockPrefix input .stepGate before
      {gateResult before base 6 3 clock P.certificate.Q with
        pc:=labelAddress origin (if clock<P.certificate.Q then .zeroStart else .sumStart)} state→Good state) :
    SafeSegment origin base (region base P.certificate.M) input Good before
      {gateResult before base 6 3 clock P.certificate.Q with
        pc:=labelAddress origin (if clock<P.certificate.Q then .zeroStart else .sumStart)} 135 := by
  let middle := gateResult before base 6 3 clock P.certificate.Q
  let after : State := {middle with pc:=labelAddress origin (if clock<P.certificate.Q then .zeroStart else .sumStart)}
  have body : linearExecute input (basicBlock .stepGate).body before=some middle := by
    rw [stepGate_body]
    exact gate_execute input before base 6 3 clock P.certificate.Q data.control.header.fresh
      (data.control.header.live 6 (by decide)) (data.control.header.live 3 (by decide))
      data.control.clockValue data.control.header.Q
  have control : (controlInstruction origin (basicBlock .stepGate).control).execute input middle=some after :=
    gate_control_execute input before base 6 3 clock P.certificate.Q origin .sumStart .zeroStart
  have fields := gate_fields before base 6 3 clock P.certificate.Q data.control.clockValue data.control.header.Q
  exact SafeSegment.ofBlock origin base _ input Good .stepGate rfl before middle after position body control
    (by simpa only [stepGate_body] using gate_prefix_frames (region base P.certificate.M) input before 6 3)
    data.control.header.live ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩ fields.2.2.2.2.2.2.2 fields.2.2.1
    (fun _ member => member) provenance

theorem stepNext_safe (input : List Cell) (P : Parameters) (origin base level clock read write : ℕ)
    (before : State) (data : RowControl P base level clock (2*level+1) read write before)
    (position : before.pc=labelAddress origin .stepNext) (Good : State→Prop)
    (provenance : ∀ state,BlockPrefix input .stepNext before
      {stepNextResult before base clock with pc:=labelAddress origin .stepGate} state→Good state) :
    SafeSegment origin base (region base P.certificate.M) input Good before
      {stepNextResult before base clock with pc:=labelAddress origin .stepGate} 330 := by
  let middle := stepNextResult before base clock
  let after : State := {middle with pc:=labelAddress origin .stepGate}
  have body := stepNext_execute input before base clock data.header.fresh
    (data.header.live 6 (by decide)) data.clockValue (data.header.live 9 (by decide)) (data.header.live 10 (by decide))
  have frames := stepNext_prefix_frames (region base P.certificate.M) input before base clock data.header.fresh
    (data.header.live 6 (by decide)) data.clockValue (data.header.live 9 (by decide)) (data.header.live 10 (by decide))
    (header_mem_region base _ 6 (by decide) (by decide)) (header_mem_region base _ 9 (by decide) (by decide))
    (header_mem_region base _ 10 (by decide) (by decide))
  have lastFrame : MemoryFrame (region base P.certificate.M) before after := by
    change MemoryFrame _ before middle
    exact frames.final body
  have fields := stepNext_fields before base clock read write data.read data.write
  have lastLive : before.live ⊆ after.live := by
    change before.live ⊆ middle.live
    rw [fields.2.1]
    exact fun _ member => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem member))
  exact SafeSegment.ofBlock origin base _ input Good .stepNext rfl before middle after position body rfl
    frames data.header.live lastFrame fields.2.2.2.2 fields.2.2.1 lastLive provenance

end PDROC.CalibrationRow
