module

public import Paid.PDLower_CalibrationCompute_LevelGate_037
public import Paid.PDLower_CalibrationCompute_Finish_036

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

theorem levelGate_continue (origin : ℕ) (input : List Cell) (base : ℕ)
    (before : State) (header : Header)
    (position : before.pc=labelAddress origin .levelGate)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base)
    (bounded : header.level≤header.M+1) :
    ∃ after : State,Segment origin input before after 165 ∧
      after.pc=labelAddress origin .levelInit ∧ header.At after base ∧
      after.register .fresh=.natural base ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  let middle := levelGateResult before base header.level header.M
  let after : State := {middle with pc:=labelAddress origin .levelInit}
  have gate := segment_branch origin .levelGate .finish .levelInit input before middle
    (header.level≤header.M+1) position (levelGate_execute input before base header represented fresh)
      rfl (by simp [middle,levelGateResult])
  have budget : 15*((basicBlock .levelGate).body.length+1)+15=165 := by decide
  refine ⟨after,?_,rfl,represented,?_,rfl,rfl,rfl⟩
  · simpa only [ite_eq_left bounded,budget] using gate
  · exact (levelGate_fresh before base header.level header.M).trans fresh

/-- The real final outer test falls through to the original indirect
return. All seven registers' required ABI fields are obtained by loads;
the heap, live set and existing output remain physically identical. -/
theorem levelGate_finish (origin : ℕ) (input : List Cell) (base : ℕ)
    (before : State) (header : Header)
    (position : before.pc=labelAddress origin .levelGate)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base)
    (finished : header.M+1<header.level) :
    ∃ after : State,Segment origin input before after 420 ∧
      after.pc=header.returnPC ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural header.returnPC ∧
      after.register .address=.natural (resultBase base header.M) ∧
      after.register .index=.natural (rowWidth header.M) ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  let middle := levelGateResult before base header.level header.M
  let branch : State := {middle with pc:=labelAddress origin .finish}
  have gate := segment_branch origin .levelGate .finish .levelInit input before middle
    (header.level≤header.M+1) position (levelGate_execute input before base header represented fresh)
      rfl (by simp [middle,levelGateResult])
  have budget : 15*((basicBlock .levelGate).body.length+1)+15=165 := by decide
  have branchRun : Segment origin input before branch 165 := by
    simpa only [ite_eq_right (by omega : ¬header.level≤header.M+1),budget] using gate
  have branchHeader : header.At branch base := represented
  have branchFresh : branch.register .fresh=.natural base :=
    (levelGate_fresh before base header.level header.M).trans fresh
  let after : State := {finishResult branch base header.M with pc:=header.returnPC}
  have finishRun : Segment origin input branch after 255 :=
    finish_return origin input branch base header rfl branchHeader branchFresh
  have registers := finish_registers branch base header branchHeader branchFresh
  exact ⟨after,branchRun.trans finishRun,rfl,registers.2.1,registers.1,registers.2.2.1,
    registers.2.2.2,rfl,rfl,rfl⟩

end PDLower.CalibrationCompute
