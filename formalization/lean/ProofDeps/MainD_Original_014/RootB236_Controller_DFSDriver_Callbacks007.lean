module
public import RootB236_Controller_DFSDriver_NodeEntry006

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver
open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*}
def clearChildPoint (isBad : Bool) : Label := if isBad then .control 19 else .control 18
def clearChildReturn (isBad : Bool) : Label := if isBad then .resume .clear else .select SelectErase.entry

theorem clear_child_code (good bad pop finish : Statement C) (isBad : Bool) :
    program good bad pop finish (clearChildPoint isBad)=
      .pop 15 BestUpdate.capturePresent (.branch (fun memory => memory.2.1)
        (.goto (fun _ => clearChildPoint isBad)) (.goto (fun _ => clearChildReturn isBad))) := by
  cases isBad <;> rfl

theorem clear_child_bit (good bad pop finish : Statement C) (isBad : Bool) (slots : Stack → List Bool)
    (memory : Store C) (value : Bool) (tail : List Bool) (present : slots 15=value::tail) :
    TM2.step (program good bad pop finish) (state (clearChildPoint isBad) memory slots)=
      some (state (clearChildPoint isBad) (memory.1,true,memory.2.2.1,memory.2.2.2) (Function.update slots 15 tail)) := by
  change some (TM2.stepAux (program good bad pop finish (clearChildPoint isBad)) memory slots)=_
  rw [clear_child_code]
  simp only [TM2.stepAux,BestUpdate.capturePresent,present,List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,state]
theorem clear_child_empty (good bad pop finish : Statement C) (isBad : Bool) (slots : Stack → List Bool)
    (memory : Store C) (empty : slots 15=[]) :
    TM2.step (program good bad pop finish) (state (clearChildPoint isBad) memory slots)=
      some (state (clearChildReturn isBad) (memory.1,false,memory.2.2.1,memory.2.2.2) (Function.update slots 15 [])) := by
  change some (TM2.stepAux (program good bad pop finish (clearChildPoint isBad)) memory slots)=_
  rw [clear_child_code]
  simp only [TM2.stepAux,BestUpdate.capturePresent,empty,List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false,state]
theorem clear_child_inside (isBad : Bool) (memory : Store C) (slots : Stack → List Bool) :
    Inside (state (clearChildPoint isBad) memory slots) := by
  cases isBad <;> exact inside_control _ memory slots (Or.inr (by decide))

theorem clear_child_path (good bad pop finish : Statement C) (isBad : Bool) (slots : Stack → List Bool)
    (memory : Store C) (data : List Bool) (represented : slots 15=data) :
    Path good bad pop finish (state (clearChildPoint isBad) memory slots)
      (state (clearChildReturn isBad) (memory.1,false,memory.2.2.1,memory.2.2.2) (Function.update slots 15 [])) (data.length+1) := by
  induction data generalizing slots memory with
  | nil =>
    exact Path.step (clear_child_inside isBad memory slots)
      (clear_child_empty good bad pop finish isBad slots memory represented) .refl
  | cons value tail ih =>
    have later:=ih (Function.update slots 15 tail) (memory.1,true,memory.2.2.1,memory.2.2.2)
      (by simp only [Function.update_self])
    rw [update_twice] at later
    exact Path.step (clear_child_inside isBad memory slots)
      (clear_child_bit good bad pop finish isBad slots memory value tail represented) later

theorem good_copy_path (good bad pop finish : Statement C) (slots : Stack → List Bool) (memory : Store C) (rank : Nat)
    (child : slots 15=unary rank) (empty10 : slots 10=[]) (empty12 : slots 12=[]) :
    Path good bad pop finish (state returnedGood memory slots)
      (state (.control 18) (memory.1,true,true,memory.2.2.2) (Function.update slots 10 (unary rank))) (2*rank+3) := by
  have copied:=copy_current good bad pop finish 1 slots memory (unary rank) [] []
  rw [show (unary rank).reverse++[]=unary rank from BestUpdate.unary_reverse rank] at copied
  have inputBank : copyBank 1 slots (unary rank) [] []=slots := by
    funext slot;fin_cases slot
    all_goals first | rfl | exact child.symm | exact empty10.symm | exact empty12.symm
  have outputBank : copyBank 1 slots (unary rank) (unary rank) []=Function.update slots 10 (unary rank) := by
    funext slot;fin_cases slot
    all_goals first | rfl | exact child.symm | exact empty12.symm
  change Path good bad pop finish (state _ _ _) (state _ _ _) _ at copied
  rw [inputBank,outputBank] at copied
  simpa only [returnedGood,copyMap,copyReturn,show (1:CopyPhase)≠0 by decide,ite_false,ite_true,unary,RankCompare.unary,List.length_replicate] using copied

/-- Real good-child return: preserve skip in10, then physically empty15 before the initial AND. -/
theorem good_to_select (good bad pop finish : Statement C) (slots : Stack → List Bool) (memory : Store C) (rank : Nat)
    (child : slots 15=unary rank) (empty10 : slots 10=[]) (empty12 : slots 12=[]) :
    Path good bad pop finish (state returnedGood memory slots)
      (state (.select SelectErase.entry) (memory.1,false,true,memory.2.2.2)
        (Function.update (Function.update slots 10 (unary rank)) 15 [])) (3*rank+4) := by
  have first:=good_copy_path good bad pop finish slots memory rank child empty10 empty12
  have cleared:=clear_child_path good bad pop finish false (Function.update slots 10 (unary rank))
    (memory.1,true,true,memory.2.2.2) (unary rank) (by simpa only [Function.update_of_ne (by decide : (15:Stack)≠10)] using child)
  have whole:=first.trans cleared
  simpa only [clearChildPoint,clearChildReturn,Bool.false_eq_true,ite_false,unary,RankCompare.unary,List.length_replicate,
    show 2*rank+3+(rank+1)=3*rank+4 by omega] using whole

private theorem identity_store {Λ : Type*} (body : TM2.Stmt Alphabet Λ (Store C)) :
    StoreIso.statement (Equiv.refl (Store C)) body=body := by induction body <;> simp_all [StoreIso.statement]
private theorem identity_role {Λ σ : Type*} (body : TM2.Stmt Alphabet Λ σ) :
    StackIso.statement (Equiv.refl Stack) body=body := by induction body <;> simp_all [StackIso.statement]

/-- Complete scan-nil continuation on physical counters; then real rank9→15 and tail probe. -/
theorem scan_nil_path (good bad pop finish : Statement C) (slots : Stack → List Bool) (memory : Store C)
    (limit a b : Nat) (flag : Bool) (tail : List Bool)
    (r2 : slots 2=unary limit) (r9 : slots 9=unary a) (r10 : slots 10=unary b)
    (empty7 : slots 7=[]) (empty12 : slots 12=[]) (empty15 : slots 15=[]) (frame : slots 13=flag::tail) :
    ∃ steps finalMemory,Path good bad pop finish (state (.merge RankMerge.entry) memory slots)
      (state (if tail.isEmpty then rootDone else popFrame) finalMemory
        (Function.update (Function.update (RankMerge.bank slots limit (RankMerge.merged limit a b) b) 9 [])
          15 (unary (RankMerge.merged limit a b)))) steps ∧ finalMemory.1=memory.1 ∧
      steps≤6*a+2*limit+4*b+17 := by
  obtain ⟨early,mergedMemory,actual,context,time⟩:=RankMerge.operational .halt slots memory.1 memory.2.1 memory.2.2.1 memory.2.2.2 limit a b
  obtain ⟨trace,first,chain,last,count,proper⟩:=actual.actual
  have mapped:=mapped_path good bad pop finish (Equiv.refl Stack) (Equiv.refl (Store C)) mergeMap
    (RankMerge.program .halt) trace _ _ first chain last
    (by intro current member point active
        rw [identity_store,identity_role]
        exact merge_code good bad pop finish point (by intro same;subst point;exact proper current member active))
    (by intro current member point active
        have interior : point≠RankMerge.done := by intro same;subst point;exact proper current member active
        simp only [mergeMap,interior,ite_false]
        simp [Boundary,pushGood,pushBad,popFrame,rootDone])
  have inputBank : RankMerge.bank slots limit a b=slots := by
    funext slot;fin_cases slot
    all_goals first | rfl | exact r2.symm | exact r9.symm | exact r10.symm | exact empty7.symm | exact empty12.symm
  change Path good bad pop finish (state (.merge RankMerge.entry) memory _) (state (.control 20) mergedMemory _) _ at mapped
  rw [inputBank,count] at mapped
  have countEarly : early+1-1=early := by omega
  rw [countEarly] at mapped
  let base:=RankMerge.bank slots limit (RankMerge.merged limit a b) b
  have parked:=park_path good bad pop finish base mergedMemory (RankMerge.merged limit a b) 0
  simp only [Nat.add_zero] at parked
  have initialPark : Function.update (Function.update base 9 (unary (RankMerge.merged limit a b))) 15 (unary 0)=base := by
    funext slot;fin_cases slot
    all_goals first | rfl | (change unary 0=slots 15;simpa only [unary,RankCompare.unary,List.replicate_zero] using empty15.symm)
  rw [initialPark] at parked
  let finalBank:=Function.update (Function.update base 9 []) 15 (unary (RankMerge.merged limit a b))
  have hasFrame : finalBank 13=flag::tail := by exact frame
  have probed:=return_probe good bad pop finish finalBank (mergedMemory.1,false,false,mergedMemory.2.2.2) flag tail hasFrame
  have finalRun : Path good bad pop finish
      (state (.control 21) (mergedMemory.1,false,false,mergedMemory.2.2.2) finalBank)
      (state (if tail.isEmpty then rootDone else popFrame) (mergedMemory.1,!tail.isEmpty,flag,mergedMemory.2.2.2) finalBank) 1 :=
    Path.step (inside_control _ _ _ (Or.inr (by decide))) probed .refl
  have whole:=mapped.trans (parked.trans finalRun)
  have small : RankMerge.merged limit a b≤a+1 := (Nat.min_le_left _ _).trans (RankMerge.capped_succ_le limit a)
  refine ⟨early+(RankMerge.merged limit a b+1+1),_,whole,context,?_⟩
  omega
end RootB236.Controller.DFSDriver
