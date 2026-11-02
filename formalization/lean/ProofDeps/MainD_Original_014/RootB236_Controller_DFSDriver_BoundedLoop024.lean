module
public import RootB236_Controller_DFSDriver_BoundedOps023

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

/-- Bounded scan composition charges each real child edge once and composes workspace by its fixed peak. -/
theorem bounded_scan_loop (finish : Statement C) (limit q bound cap : Nat) (later : List (Finset (Fin q)))
    (children : ∀ remaining,BoundedSpec finish limit q bound cap later remaining)
    (bg : Stack → List Bool) (r0 : bg 0=rows q later) (fields : FieldsBound bg bound)
    (limitBound : limit≤bound) (widthBound : q≤bound) (rowsBound : (rows q later).length≤bound)
    (skip : Nat) (skipBound : skip≤limit) (frame : List Bool)
    (room : frame.length+(later.length+1)*(28*bound+30)≤cap) (remaining : Finset (Fin q)) (tools : List (Fin q)) :
    ∀ (best : CodeBest q),bestCode best≤limit → ∀ (context : C) (order : Ordering) (before : State C),
      ScanResult bg context order limit skip best frame remaining tools before →
      ∃ steps final,BoundedRun finish (peak C bound cap) before final steps ∧
        BoundedComplete limit skip (scanCode (fun tool => (evaluateCode q limit later (remaining.erase tool)).rank) tools best)
          frame (bg 1) remaining context bound final ∧
        steps≤localTime bound cap+nodeTime bound cap*(tools.map (fun tool => (evaluate q later (remaining.erase tool)).nodes)).sum := by
  induction tools with
  | nil =>
    intro best bestBound context order before result
    rcases result with ⟨tool,rest,bits,impossible,_pending,_width,_ended⟩ | ⟨_empty,rfl⟩
    · cases impossible
    · obtain ⟨steps,final,run,complete,time⟩:=bounded_merge finish bg (context,true,true,order)
        limit skip bound cap best frame remaining fields limitBound widthBound skipBound bestBound (by omega)
      exact ⟨steps,final,run,complete,by simpa only [List.map_nil,List.sum_nil,Nat.mul_zero,Nat.add_zero] using time⟩
  | cons tool tools ih =>
    intro best bestBound context order before result
    rcases result with ⟨chosen,rest,bits,shape,pending,width,ended⟩ | ⟨impossible,_ended⟩
    · obtain ⟨rfl,rfl⟩:=List.cons.inj shape
      subst before
      let parent:=scanBank bg limit skip best frame bits (EraseSem.mask (remaining.erase tool))
        (EraseSem.mask remaining) tool.val (tool.val+1)
      have parentFields : FieldsBound parent bound := scan_fields_bound bg bound limit skip best frame bits
        (EraseSem.mask (remaining.erase tool)) (EraseSem.mask remaining) tool.val (tool.val+1) fields limitBound
        (skipBound.trans limitBound) (bestBound.trans limitBound) widthBound (by omega) (mask_length_le _ widthBound)
        (mask_length_le _ widthBound) (Nat.le_of_lt tool.isLt |>.trans widthBound) (by omega)
      have parentWidth : parent 11=unary q := by change unary (EraseSem.mask remaining).length=unary q;rw [EraseSem.mask_length]
      obtain ⟨called,returnedOrder,callRun,callTime⟩:=bounded_child finish limit q bound cap later (remaining.erase tool)
        (children (remaining.erase tool)) (context,false,false,order) parent false (hasCode best) frame r0 rfl rfl parentWidth rfl
        parentFields limitBound widthBound rowsBound room
      have returnedBank : B23_6.DFSFrame.restoreBank parent
          (unary (evaluateCode q limit later (remaining.erase tool)).rank)=
          bestInput bg limit skip best frame bits (EraseSem.mask (remaining.erase tool))
            (EraseSem.mask remaining) tool.val (tool.val+1) (evaluateCode q limit later (remaining.erase tool)).rank := rfl
      rw [returnedBank] at callRun
      have childRank:=code_rank_bound limit q later (remaining.erase tool)
      obtain ⟨updated,updatedMemory,updateRun,updatedContext,updateTime⟩:=bounded_update finish bg
        (context,false,false,returnedOrder) limit skip bound cap best frame remaining bits tool
        (evaluateCode q limit later (remaining.erase tool)).rank width fields limitBound widthBound skipBound bestBound childRank (by omega)
      have newBestBound:=update_code_bound limit best tool (evaluateCode q limit later (remaining.erase tool)).rank bestBound childRank
      obtain ⟨scanned,next,scanRun,outcome,scanTime⟩:=bounded_resume finish bg updatedMemory limit skip bound cap
        (updateCode best tool (evaluateCode q limit later (remaining.erase tool)).rank) frame remaining bits
        (EraseSem.mask (remaining.erase tool)) tool.val (tool.val+1) tools width pending fields limitBound widthBound skipBound newBestBound
        (by omega) (mask_length_le _ (Nat.le_refl q)) (Nat.le_of_lt tool.isLt)
      rw [updatedContext] at outcome
      obtain ⟨completed,final,completeRun,complete,completeTime⟩:=ih
        (updateCode best tool (evaluateCode q limit later (remaining.erase tool)).rank) newBestBound context updatedMemory.2.2.2 next outcome
      refine ⟨_,final,callRun.trans (updateRun.trans (scanRun.trans completeRun)),complete,?_⟩
      simp only [List.map_cons,List.sum_cons,Nat.mul_add]
      omega
    · cases impossible
end RootB236.Controller.DFSDriver.Machine
