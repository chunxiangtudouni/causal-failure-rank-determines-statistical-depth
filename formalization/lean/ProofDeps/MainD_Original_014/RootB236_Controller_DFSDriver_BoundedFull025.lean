module
public import RootB236_Controller_DFSDriver_BoundedLoop024

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

theorem bounded_cons (finish : Statement C) (limit q bound cap : Nat) (eligible : Finset (Fin q))
    (later : List (Finset (Fin q))) (remaining : Finset (Fin q))
    (children : ∀ remaining,BoundedSpec finish limit q bound cap later remaining) :
    BoundedSpec finish limit q bound cap (eligible::later) remaining := by
  intro memory before flag tail r0 r2 r4 r11 r13 fields limitBound widthBound rowBound room
  have suffixBound : (rows q later).length≤bound := by
    rw [rows_cons,List.length_cons,List.length_append,EraseSem.mask_length] at rowBound
    omega
  have depthRoom : tail.length+(later.length+1)*(28*bound+30)≤cap := by simpa only [List.length_cons] using room
  have input : before 0=true::(EraseSem.mask eligible++rows q later) := by rw [r0,rows_cons]
  have normal:=node_bank_eq before _ limit (EraseSem.mask remaining) q (flag::tail) input r2 r4 r11 r13
  have entered:=call_cons_path .halt .halt .halt .halt before memory (EraseSem.mask eligible) (rows q later)
    limit (EraseSem.mask remaining) q (flag::tail) (EraseSem.mask_length eligible)
  rw [normal] at entered
  have entryRun:=core_path finish entered
  rw [core_state,core_state] at entryRun
  change Run finish (state start memory before) (state (.inr (.pushBoot true)) _ _) _ at entryRun
  have entryBound:=complete_bank_bound before bound cap flag tail fields r13 (by omega)
  have cleanCost:=clear_cost_bound before bound fields
  have entryTime : clearCost before+4*q+7≤localTime bound cap := by dsimp only [localTime,entryCap];omega
  have entryBounded:=atom entryRun bound cap entryBound entryTime
  let parent:=readyBank before (rows q later) (EraseSem.mask eligible) limit (EraseSem.mask remaining) q (false::tail)
  have parentFields : FieldsBound parent bound := ready_fields_bound before bound (rows q later) (EraseSem.mask eligible) limit
    (EraseSem.mask remaining) q (false::tail) fields suffixBound (mask_length_le eligible widthBound) limitBound
    (mask_length_le remaining widthBound) widthBound
  obtain ⟨called,returnedOrder,callRun,callTime⟩:=bounded_child finish limit q bound cap later remaining (children remaining)
    (memory.1,false,false,memory.2.2.2) parent true false tail rfl rfl rfl rfl rfl parentFields limitBound widthBound suffixBound depthRoom
  let returned:=B23_6.DFSFrame.restoreBank parent (unary (evaluateCode q limit later remaining).rank)
  have rankBound:=code_rank_bound limit q later remaining
  have kept:=good_to_select .halt .halt .halt .halt returned (memory.1,false,false,returnedOrder)
    (evaluateCode q limit later remaining).rank rfl rfl rfl
  have skipBank : Function.update (Function.update returned 10 (unary (evaluateCode q limit later remaining).rank)) 15 []=
      firstBank parent limit (evaluateCode q limit later remaining).rank (none : CodeBest q) tail eligible remaining := by
    funext slot;fin_cases slot <;> rfl
  rw [skipBank] at kept
  have goodRun:=core_path finish kept
  rw [core_state,core_state] at goodRun
  change Run finish (state (.inl returnedGood) _ _) (state (.inl (.select SelectErase.entry)) _ _) _ at goodRun
  have returnedFields : FieldsBound returned bound := restore_fields_bound parent bound _ parentFields (unary_length_le (rankBound.trans limitBound))
  have returnedBound:=complete_bank_bound returned bound cap false tail returnedFields rfl (by omega)
  have keepTime : 3*(evaluateCode q limit later remaining).rank+4≤localTime bound cap := by dsimp only [localTime,entryCap];omega
  have goodBounded:=atom goodRun bound cap returnedBound keepTime
  obtain ⟨selected,selectedFinal,selectRun,outcome,selectTime⟩:=bounded_select finish parent
    (memory.1,false,true,returnedOrder) limit (evaluateCode q limit later remaining).rank bound cap (none : CodeBest q) tail eligible remaining
    parentFields limitBound widthBound rankBound (Nat.zero_le _) (by omega)
  obtain ⟨completed,final,completeRun,complete,completeTime⟩:=bounded_scan_loop finish limit q bound cap later children parent rfl
    parentFields limitBound widthBound suffixBound (evaluateCode q limit later remaining).rank rankBound tail depthRoom remaining
    (genericRankCandidates q eligible remaining) none (Nat.zero_le _) memory.1 returnedOrder selectedFinal outcome
  have whole:=entryBounded.trans (callRun.trans (goodBounded.trans (selectRun.trans completeRun)))
  refine ⟨_,final,whole,⟨⟨complete.active,complete.context,?_,complete.rank,?_⟩,complete.fields,
    complete.archive,complete.limit_saved,complete.remaining_saved,complete.width_saved⟩,?_⟩
  · change final.stk 13=((scanCode _ _ (none : CodeBest q)).map Prod.fst).isSome::tail
    rw [pick_presence]
    exact complete.spool
  · change final.stk 14=pickBits ((scanCode _ _ (none : CodeBest q)).map Prod.fst)
    rw [pick_code]
    exact complete.tool
  · rw [evaluate_nodes_cons,Nat.mul_add,Nat.mul_add,Nat.mul_one]
    have overhead : 6*localTime bound cap≤nodeTime bound cap := by dsimp only [nodeTime];omega
    omega

/-- Complete original DFS source and uniform peak, using exact frame depth and no retained run history. -/
theorem bounded_staged (finish : Statement C) (limit q bound cap : Nat) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q)) :
    BoundedSpec finish limit q bound cap stages remaining := by
  induction stages generalizing remaining with
  | nil => exact bounded_terminal finish limit q bound cap remaining
  | cons eligible later ih => exact bounded_cons finish limit q bound cap eligible later remaining ih
end RootB236.Controller.DFSDriver.Machine
