module

public import Paid.PDROC_CalibrationRow_050
public import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Remaining-Q induction composes the SAME actual safe trace through
every iteration and the real terminal gate, retaining all prefix facts. -/
theorem qLoop_provenance_from (input : List Cell) (P : Parameters) (origin base level clock : ℕ)
    (caller before : State) (previousProof : QProvenance P origin base level input caller before)
    (data : StepData P base level clock before) (position : before.pc=labelAddress origin .stepGate)
    (clockBound : clock≤P.certificate.Q) (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,SafeSegment origin base (region base P.certificate.M) input
      (QProvenance P origin base level input caller) before after (5000*(P.certificate.Q-clock)*(level+1)+135) ∧
      StepData P base level P.certificate.Q after ∧ after.pc=labelAddress origin .sumStart := by
  let Good := QProvenance P origin base level input caller
  have go (remaining : ℕ) : ∀ clock before,P.certificate.Q-clock=remaining → clock≤P.certificate.Q →
      QProvenance P origin base level input caller before → StepData P base level clock before →
      before.pc=labelAddress origin .stepGate →
      ∃ after : State,SafeSegment origin base (region base P.certificate.M) input Good before after
          (5000*(P.certificate.Q-clock)*(level+1)+135) ∧
        StepData P base level P.certificate.Q after ∧ after.pc=labelAddress origin .sumStart := by
    induction remaining with
    | zero =>
      intro clock before remainingEq clockBound previousProof data position
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
      have fields := gate_fields before base 6 3 P.certificate.Q P.certificate.Q data.control.clockValue data.control.header.Q
      have run : SafeSegment origin base (region base P.certificate.M) input Good before after 135 :=
        SafeSegment.ofBlock origin base _ input Good .stepGate rfl before middle after position body control
          (by simpa only [stepGate_body] using gate_prefix_frames (region base P.certificate.M) input before 6 3)
          data.control.header.live ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩ fields.2.2.2.2.2.2.2 fields.2.2.1
          (fun _ member => member)
          (qProvenance_closed P origin base level input caller .stepGate before middle after
            (.gate P.certificate.Q before (Nat.le_refl _) data) previousProof position body control)
      refine ⟨after,?_,StepData.sameMemory P base level P.certificate.Q before after data rfl rfl fields.2.2.1,rfl⟩
      simpa only [Nat.sub_self,Nat.mul_zero,Nat.zero_mul,Nat.zero_add] using run
    | succ remaining ih =>
      intro clock before remainingEq clockBound previousProof data position
      have inside : clock<P.certificate.Q := by omega
      obtain ⟨next,firstRun,nextData,nextPosition⟩ :=
        qIteration_provenance input P origin base level clock caller before previousProof data position inside levelBound
      obtain ⟨after,run,done,last⟩ :=
        ih (clock+1) next (by omega) (by omega) firstRun.final.2.2.2.2 nextData nextPosition
      have distance : P.certificate.Q-clock=(P.certificate.Q-(clock+1))+1 := by omega
      have cost : 5000*(level+1)+(5000*(P.certificate.Q-(clock+1))*(level+1)+135)=
          5000*(P.certificate.Q-clock)*(level+1)+135 := by rw [distance]; ring
      exact ⟨after,cost ▸ firstRun.trans run,done,last⟩
  exact go (P.certificate.Q-clock) clock before rfl clockBound previousProof data position

theorem qLoop_provenance (input : List Cell) (P : Parameters) (origin base level clock : ℕ)
    (before : State) (data : StepData P base level clock before)
    (position : before.pc=labelAddress origin .stepGate)
    (clockBound : clock≤P.certificate.Q) (levelBound : level≤P.certificate.M+1) :
    ∃ after : State,SafeSegment origin base (region base P.certificate.M) input
      (QProvenance P origin base level input before) before after (5000*(P.certificate.Q-clock)*(level+1)+135) ∧
      StepData P base level P.certificate.Q after ∧ after.pc=labelAddress origin .sumStart :=
  qLoop_provenance_from input P origin base level clock before before .initial data position clockBound levelBound

end PDROC.CalibrationRow
