module
public import RootB236_Controller_DFSDriver_Recursive014

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver.Machine
open Turing RootB23.GenericRank PaperProofs.Structure
open PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*} {q : Nat}

structure Completed (limit skip : Nat) (best : CodeBest q) (tail : List Bool) (context : C) (final : State C) : Prop where
  active : final.l=some (returnPort tail)
  context : final.var.1=context
  spool : final.stk 13=hasCode best::tail
  rank : final.stk 15=unary (RankMerge.merged limit (bestCode best) skip)
  tool : final.stk 14=toolCode best

theorem core_return (tail : List Bool) : coreMap (if tail.isEmpty then rootDone else popFrame)=returnPort tail := by
  unfold returnPort
  by_cases empty : tail.isEmpty=true
  · simp only [empty,ite_true];rfl
  · simp only [empty];rfl

theorem merge_current (finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (limit skip : Nat) (best : CodeBest q) (tail : List Bool) (remaining : Finset (Fin q)) :
    ∃ steps final,Run finish
      (state (.inl (.merge RankMerge.entry)) memory
        (scanBank bg limit skip best tail [] (EraseSem.mask remaining) (EraseSem.mask remaining) 0 q)) final steps ∧
      Completed limit skip best tail memory.1 final := by
  let slots:=scanBank bg limit skip best tail [] (EraseSem.mask remaining) (EraseSem.mask remaining) 0 q
  obtain ⟨steps,finalMemory,path,context,_time⟩:=scan_nil_path .halt .halt .halt .halt slots memory
    limit (bestCode best) skip (hasCode best) tail rfl rfl rfl rfl rfl rfl rfl
  have run:=core_path finish path
  rw [core_state,core_state,core_return] at run
  change Run finish (state (.inl (.merge RankMerge.entry)) memory slots) _ _ at run
  exact ⟨steps,_,run,rfl,context,rfl,rfl,rfl⟩

/-- Actual finite-source scan loop. Every found edge enters a real recursive child and returns through the saved kind. -/
theorem scan_loop (finish : Statement C) (limit q : Nat) (later : List (Finset (Fin q)))
    (children : ∀ remaining,NodeSpec finish limit q later remaining)
    (bg : Stack → List Bool) (r0 : bg 0=rows q later) (skip : Nat) (frame : List Bool)
    (remaining : Finset (Fin q)) (tools : List (Fin q)) :
    ∀ (best : CodeBest q) (context : C) (order : Ordering) (before : State C),
      ScanResult bg context order limit skip best frame remaining tools before →
      ∃ steps final,Run finish before final steps ∧
        Completed limit skip (scanCode (fun tool => (evaluateCode q limit later (remaining.erase tool)).rank) tools best) frame context final := by
  induction tools with
  | nil =>
    intro best context order before result
    rcases result with ⟨tool,rest,bits,impossible,_pending,_width,_ended⟩ | ⟨_empty,rfl⟩
    · cases impossible
    · exact merge_current finish bg (context,true,true,order) limit skip best frame remaining
  | cons tool tools ih =>
    intro best context order before result
    rcases result with ⟨chosen,rest,bits,shape,pending,width,ended⟩ | ⟨impossible,_ended⟩
    · obtain ⟨rfl,rfl⟩:=List.cons.inj shape
      subst before
      let parent:=scanBank bg limit skip best frame bits (EraseSem.mask (remaining.erase tool))
        (EraseSem.mask remaining) tool.val (tool.val+1)
      have parentWidth : parent 11=unary q := by
        change unary (EraseSem.mask remaining).length=unary q
        rw [EraseSem.mask_length]
      obtain ⟨called,returnedOrder,callRun⟩:=child_call finish limit q later (remaining.erase tool)
        (children (remaining.erase tool)) (context,false,false,order) parent false r0 rfl rfl parentWidth
      have returnedBank : B23_6.DFSFrame.restoreBank parent
          (unary (evaluateCode q limit later (remaining.erase tool)).rank)=
          bestInput bg limit skip best frame bits (EraseSem.mask (remaining.erase tool))
            (EraseSem.mask remaining) tool.val (tool.val+1) (evaluateCode q limit later (remaining.erase tool)).rank := rfl
      rw [returnedBank] at callRun
      obtain ⟨updated,updatedMemory,updatePath,updatedContext,_time⟩:=update_path .halt .halt .halt .halt bg
        (context,false,false,returnedOrder) limit skip best frame bits (EraseSem.mask (remaining.erase tool))
        (EraseSem.mask remaining) tool (tool.val+1) (evaluateCode q limit later (remaining.erase tool)).rank
      have updateRun:=core_path finish updatePath
      rw [core_state,core_state] at updateRun
      change Run finish (state (.inl returnedBad) _ _) (state (.inl (.resume .clear)) _ _) _ at updateRun
      obtain ⟨scanned,next,scanRun,outcome,_scanTime⟩:=resume_current finish bg updatedMemory limit skip
        (updateCode best tool (evaluateCode q limit later (remaining.erase tool)).rank) frame remaining bits
        (EraseSem.mask (remaining.erase tool)) tool.val (tool.val+1) tools width pending
      rw [updatedContext] at outcome
      obtain ⟨completed,final,completeRun,complete⟩:=ih
        (updateCode best tool (evaluateCode q limit later (remaining.erase tool)).rank) context updatedMemory.2.2.2 next outcome
      exact ⟨_,final,callRun.trans (updateRun.trans (scanRun.trans completeRun)),complete⟩
    · cases impossible
end RootB236.Controller.DFSDriver.Machine
