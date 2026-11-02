module
public import RootB236_Controller_DFSDriver_Certified021

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver.Machine
open Turing RootB23.GenericRank PaperProofs.Structure
open PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*}
attribute [local irreducible] pushProfile actionProfile nodeProfile

/-- Exact depth/spool accounting for one actual push/recursive-child/pop segment. -/
theorem bounded_child (finish : Statement C) (limit q bound cap : Nat) (stages : List (Finset (Fin q)))
    (remaining : Finset (Fin q)) (child : BoundedSpec finish limit q bound cap stages remaining)
    (memory : Store C) (parent : Stack → List Bool) (kind flag : Bool) (tail : List Bool)
    (r0 : parent 0=rows q stages) (r2 : parent 2=unary limit) (r4 : parent 4=EraseSem.mask remaining)
    (r11 : parent 11=unary q) (r13 : parent 13=flag::tail) (fields : FieldsBound parent bound)
    (limitBound : limit≤bound) (widthBound : q≤bound) (rowsBound : (rows q stages).length≤bound)
    (room : tail.length+(stages.length+1)*(28*bound+30)≤cap) :
    ∃ steps order,BoundedRun finish (peak C bound cap) (state (.inr (.pushBoot kind)) memory parent)
      (state (.inl (if kind then returnedGood else returnedBad)) (memory.1,false,false,order)
        (B23_6.DFSFrame.restoreBank parent (unary (evaluateCode q limit stages remaining).rank))) steps ∧
      steps+2*localTime bound cap≤nodeTime bound cap*(evaluate q stages remaining).nodes := by
  obtain ⟨pushed,pushRun,pushTime⟩:=push finish memory parent kind
  have parentBound:=complete_bank_bound parent bound cap flag tail fields r13 (by omega)
  have pushSmall : pushed≤localTime bound cap := pushTime.trans (frame_time_bound parent bound cap parentBound)
  have pushBounded:=atom pushRun bound cap parentBound pushSmall
  let bank:=B23_6.DFSFrame.pushBank kind parent
  let frame:=B23_6.DFSFrame.framePrefix parent kind 14
  have childRoom : frame.length+stages.length*(28*bound+30)≤cap := depth_room parent bound cap stages.length kind flag tail fields r13 room
  obtain ⟨evaluated,final,childRun,reply,childTime⟩:=child (memory.1,false,false,memory.2.2.2) bank false frame
    r0 r2 r4 r11 rfl (push_fields_bound parent bound kind fields) limitBound widthBound rowsBound childRoom
  have nested : returnPort frame=.inr .popBoot := by
    have nonempty:=frame_nonempty parent kind
    have notEmpty : frame.isEmpty=false := by
      cases same : frame with
      | nil => exact False.elim (nonempty same)
      | cons head rest => rfl
    simp only [returnPort,notEmpty,Bool.false_eq_true,ite_false]
  have finalState:=active_state final (.inr .popBoot) (by rw [reply.active,nested])
  rw [finalState] at childRun
  obtain ⟨popped,popRun,popTime⟩:=pop finish final.var parent final.stk kind (evaluateCode q limit stages remaining).pick.isSome reply.spool
  have returnedBound:=complete_bank_bound final.stk bound cap (evaluateCode q limit stages remaining).pick.isSome frame reply.fields reply.spool (by omega)
  have popSmall : popped≤localTime bound cap := popTime.trans (frame_time_bound final.stk bound cap returnedBound)
  have popBounded:=atom popRun bound cap returnedBound popSmall
  rw [reply.rank,reply.context] at popBounded
  refine ⟨_,final.var.2.2.2,pushBounded.trans (childRun.trans popBounded),?_⟩
  omega
end RootB236.Controller.DFSDriver.Machine
