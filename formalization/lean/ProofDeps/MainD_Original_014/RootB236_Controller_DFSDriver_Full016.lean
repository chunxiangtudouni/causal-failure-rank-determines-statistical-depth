module
public import RootB236_Controller_DFSDriver_Loop015

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver.Machine
open Turing RootB23.GenericRank PaperProofs.Structure
open PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*} {q : Nat}

theorem pick_code (best : CodeBest q) : pickBits (best.map Prod.fst)=toolCode best := by cases best <;> rfl
theorem pick_presence (best : CodeBest q) : (best.map Prod.fst).isSome=hasCode best := by cases best <;> rfl

/-- A whole nonterminal node: good first, then original finRange suffix, then rank merge and physical return. -/
theorem cons_spec (finish : Statement C) (limit q : Nat) (eligible : Finset (Fin q))
    (later : List (Finset (Fin q))) (remaining : Finset (Fin q))
    (children : ∀ remaining,NodeSpec finish limit q later remaining) :
    NodeSpec finish limit q (eligible::later) remaining := by
  intro memory before flag tail r0 r2 r4 r11 r13
  have input : before 0=true::(EraseSem.mask eligible++rows q later) := by
    rw [r0,rows_cons]
  have normal:=node_bank_eq before _ limit (EraseSem.mask remaining) q (flag::tail) input r2 r4 r11 r13
  have entered:=call_cons_path .halt .halt .halt .halt before memory (EraseSem.mask eligible) (rows q later)
    limit (EraseSem.mask remaining) q (flag::tail) (EraseSem.mask_length eligible)
  rw [normal] at entered
  have entryRun:=core_path finish entered
  rw [core_state,core_state] at entryRun
  change Run finish (state start memory before) (state (.inr (.pushBoot true)) _ _) _ at entryRun
  let parent:=readyBank before (rows q later) (EraseSem.mask eligible) limit (EraseSem.mask remaining) q (false::tail)
  obtain ⟨called,returnedOrder,callRun⟩:=child_call finish limit q later remaining (children remaining)
    (memory.1,false,false,memory.2.2.2) parent true rfl rfl rfl rfl
  let returned:=B23_6.DFSFrame.restoreBank parent (unary (evaluateCode q limit later remaining).rank)
  have kept:=good_to_select .halt .halt .halt .halt returned (memory.1,false,false,returnedOrder)
    (evaluateCode q limit later remaining).rank rfl rfl rfl
  have skipBank : Function.update (Function.update returned 10 (unary (evaluateCode q limit later remaining).rank)) 15 []=
      firstBank parent limit (evaluateCode q limit later remaining).rank (none : CodeBest q) tail eligible remaining := by
    funext slot;fin_cases slot <;> rfl
  rw [skipBank] at kept
  have goodRun:=core_path finish kept
  rw [core_state,core_state] at goodRun
  change Run finish (state (.inl returnedGood) _ _) (state (.inl (.select SelectErase.entry)) _ _) _ at goodRun
  obtain ⟨selected,selectedFinal,selectRun,outcome,_selectTime⟩:=select_current finish parent
    (memory.1,false,true,returnedOrder) limit (evaluateCode q limit later remaining).rank (none : CodeBest q) tail eligible remaining
  obtain ⟨completed,final,completeRun,complete⟩:=scan_loop finish limit q later children parent rfl
    (evaluateCode q limit later remaining).rank tail remaining (genericRankCandidates q eligible remaining)
    none memory.1 returnedOrder selectedFinal outcome
  have whole:=entryRun.trans (callRun.trans (goodRun.trans (selectRun.trans completeRun)))
  refine ⟨_,final,whole,complete.active,complete.context,?_,complete.rank,?_⟩
  · change final.stk 13=((scanCode _ _ (none : CodeBest q)).map Prod.fst).isSome::tail
    rw [pick_presence]
    exact complete.spool
  · change final.stk 14=pickBits ((scanCode _ _ (none : CodeBest q)).map Prod.fst)
    rw [pick_code]
    exact complete.tool

/-- Fully instantiated finite-source staged DFS. No logical next/evaluate result is loaded into the machine. -/
theorem staged_spec (finish : Statement C) (limit q : Nat) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q)) :
    NodeSpec finish limit q stages remaining := by
  induction stages generalizing remaining with
  | nil => exact terminal_spec finish limit q remaining
  | cons eligible later ih => exact cons_spec finish limit q eligible later remaining ih

/-- Original rank and FIRST maximizer are decoded from the very same concrete global-source run. -/
theorem original_actual (finish : Statement C) (limit q : Nat) (stages : List (Finset (Fin q)))
    (remaining : Finset (Fin q)) (depth : stages.length≤limit) (memory : Store C) (before : Stack → List Bool)
    (flag : Bool) (tail : List Bool) (r0 : before 0=rows q stages) (r2 : before 2=unary (limit+1))
    (r4 : before 4=EraseSem.mask remaining) (r11 : before 11=unary q) (r13 : before 13=flag::tail) :
    ∃ steps final,Run finish (state start memory before) final steps ∧ final.l=some (returnPort tail) ∧
      final.var.1=memory.1 ∧ final.stk 15=unary (rankCode limit (genericRank stages remaining)) ∧
      final.stk 13=(match stages with | [] => none | eligible::later => pickGenericMaxRankTool q eligible later remaining).isSome::tail ∧
      final.stk 14=pickBits (match stages with | [] => none | eligible::later => pickGenericMaxRankTool q eligible later remaining) := by
  obtain ⟨steps,final,run,reply⟩:=staged_spec finish (limit+1) q stages remaining memory before flag tail r0 r2 r4 r11 r13
  have exactValue:=evaluate_code_original limit q stages remaining depth
  refine ⟨steps,final,run,reply.active,reply.context,?_,?_,?_⟩
  · rw [reply.rank,exactValue.1]
  · rw [reply.spool,exactValue.2]
    cases stages <;> rfl
  · rw [reply.tool,exactValue.2]
    cases stages <;> rfl
end RootB236.Controller.DFSDriver.Machine
