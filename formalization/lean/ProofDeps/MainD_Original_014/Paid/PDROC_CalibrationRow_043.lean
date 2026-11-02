module

public import Paid.PDROC_CalibrationRow_042
public import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Actual Q-counter induction. The terminal stepGate really reads Q
and branches to sumStart; Q0 takes this base case after the real reset6.
Each successor invokes the proved zero/scatter/swap machine fragments. -/
theorem qLoop (input : List Cell) (P : Parameters) (origin base level clock : ℕ) (before : State)
    (data : StepData P base level clock before) (position : before.pc=labelAddress origin .stepGate)
    (clockBound : clock≤P.certificate.Q) (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,Segment origin input before after (5000*(P.certificate.Q-clock)*(level+1)+135) ∧
      StepData P base level P.certificate.Q after ∧ after.pc=labelAddress origin .sumStart ∧
      MemoryFrame (region base P.certificate.M) before after ∧ after.output=before.output ∧
      after.register .fresh=before.register .fresh := by
  have go (remaining : ℕ) : ∀ clock before,P.certificate.Q-clock=remaining →
      clock≤P.certificate.Q → StepData P base level clock before →
      before.pc=labelAddress origin .stepGate →
      ∃ after : State,Segment origin input before after (5000*(P.certificate.Q-clock)*(level+1)+135) ∧
        StepData P base level P.certificate.Q after ∧ after.pc=labelAddress origin .sumStart ∧
        MemoryFrame (region base P.certificate.M) before after ∧ after.output=before.output ∧
        after.register .fresh=before.register .fresh := by
    induction remaining with
    | zero =>
      intro clock before remainingEq clockBound data position
      have equal : clock=P.certificate.Q := by omega
      subst clock
      let middle := gateResult before base 6 3 P.certificate.Q P.certificate.Q
      let after : State := {middle with pc:=labelAddress origin .sumStart}
      have body : linearExecute input (basicBlock .stepGate).body before=some middle := by
        rw [stepGate_body]
        exact gate_execute input before base 6 3 P.certificate.Q P.certificate.Q data.control.header.fresh
          (data.control.header.live 6 (by decide)) (data.control.header.live 3 (by decide))
          data.control.clockValue data.control.header.Q
      have control : (controlInstruction origin (basicBlock .stepGate).control).execute input middle=some after := by
        simpa only [basicBlock,lt_self_iff_false,ite_false,middle,after] using
          gate_control_execute input before base 6 3 P.certificate.Q P.certificate.Q origin .sumStart .zeroStart
      have run : Segment origin input before after 135 :=
        kernel_block_trace origin .stepGate input before middle after position body control
      have fields := gate_fields before base 6 3 P.certificate.Q P.certificate.Q data.control.clockValue data.control.header.Q
      refine ⟨after,?_,StepData.sameMemory P base level P.certificate.Q before after data rfl rfl fields.2.2.1,
        rfl,⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩,rfl,fields.2.2.1⟩
      simpa only [Nat.sub_self,Nat.mul_zero,Nat.zero_mul,Nat.zero_add] using run
    | succ remaining ih =>
      intro clock before remainingEq clockBound data position
      have inside : clock<P.certificate.Q := by omega
      obtain ⟨next,firstRun,nextData,nextPosition,firstFrame,firstOutput,firstFresh⟩ :=
        qIteration input P origin base level clock before data position inside levelBound
      obtain ⟨after,run,done,last,frame,output,fresh⟩ :=
        ih (clock+1) next (by omega) (by omega) nextData nextPosition
      have distance : P.certificate.Q-clock=(P.certificate.Q-(clock+1))+1 := by omega
      have cost : 5000*(level+1)+(5000*(P.certificate.Q-(clock+1))*(level+1)+135)=
          5000*(P.certificate.Q-clock)*(level+1)+135 := by
        rw [distance]
        ring
      exact ⟨after,cost ▸ firstRun.trans run,done,last,firstFrame.trans frame,
        output.trans firstOutput,fresh.trans firstFresh⟩
  exact go (P.certificate.Q-clock) clock before rfl clockBound data position

end PDROC.CalibrationRow
