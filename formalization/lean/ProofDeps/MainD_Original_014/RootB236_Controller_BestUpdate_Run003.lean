module
public import RootB236_Controller_BestUpdate_Copy002

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.BestUpdate
open Turing PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*}
theorem unary_reverse (n : Nat) : (unary n).reverse++[]=unary n := by
  simp [unary,RankCompare.unary]
theorem boot_step (caller : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb flag : Bool) (ord : Ordering) (a b tool : Nat) (oldBest tail : List Bool) :
    TM2.step (program caller) (state boot (context,ha,hb,ord) (bank bg a b tool oldBest flag tail))=
      some (state (if flag then compareMap 0 else clearRank) (context,flag,hb,ord)
        (bank bg a b tool oldBest true tail)) := by
  cases flag <;> change some (⟨_,_,_⟩ : State C)=_
  all_goals congr 1;congr 1;funext slot;fin_cases slot <;> rfl

theorem clear_rank_step (caller : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (a b tool : Nat) (oldBest tail : List Bool) :
    TM2.step (program caller) (state clearRank (context,ha,hb,ord) (bank bg (a+1) b tool oldBest true tail))=
      some (state clearRank (context,true,hb,ord) (bank bg a b tool oldBest true tail)) := by
  change some (⟨_,_,_⟩ : State C)=_
  congr 1;congr 1;funext slot;fin_cases slot <;> rfl
theorem clear_rank_end (caller : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (b tool : Nat) (oldBest tail : List Bool) :
    TM2.step (program caller) (state clearRank (context,ha,hb,ord) (bank bg 0 b tool oldBest true tail))=
      some (state clearTool (context,false,hb,ord) (bank bg 0 b tool oldBest true tail)) := by
  change some (⟨_,_,_⟩ : State C)=_
  congr 1;congr 1;funext slot;fin_cases slot <;> rfl
theorem clear_tool_step (caller : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb value : Bool) (ord : Ordering) (b tool : Nat) (oldBest tail : List Bool) :
    TM2.step (program caller) (state clearTool (context,ha,hb,ord) (bank bg 0 b tool (value::oldBest) true tail))=
      some (state clearTool (context,true,hb,ord) (bank bg 0 b tool oldBest true tail)) := by
  change some (⟨_,_,_⟩ : State C)=_
  congr 1;congr 1;funext slot;fin_cases slot <;> rfl
theorem clear_tool_end (caller : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (b tool : Nat) (tail : List Bool) :
    TM2.step (program caller) (state clearTool (context,ha,hb,ord) (bank bg 0 b tool [] true tail))=
      some (state (copyMap false .boot) (context,false,hb,ord) (bank bg 0 b tool [] true tail)) := by
  change some (⟨_,_,_⟩ : State C)=_
  congr 1;congr 1;funext slot;fin_cases slot <;> rfl

theorem clear_rank_path (caller : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (a b tool : Nat) (oldBest tail : List Bool) :
    Path caller (state clearRank (context,ha,hb,ord) (bank bg a b tool oldBest true tail))
      (state clearTool (context,false,hb,ord) (bank bg 0 b tool oldBest true tail)) (a+1) := by
  induction a generalizing ha with
  | zero => exact Path.step (by change some (1:Label)≠some (3:Label);decide) (clear_rank_end caller bg context ha hb ord b tool oldBest tail) .refl
  | succ a ih => exact Path.step (by change some (1:Label)≠some (3:Label);decide) (clear_rank_step caller bg context ha hb ord a b tool oldBest tail) (ih true)
theorem clear_tool_path (caller : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (b tool : Nat) (oldBest tail : List Bool) :
    Path caller (state clearTool (context,ha,hb,ord) (bank bg 0 b tool oldBest true tail))
      (state (copyMap false .boot) (context,false,hb,ord) (bank bg 0 b tool [] true tail)) (oldBest.length+1) := by
  induction oldBest generalizing ha with
  | nil => exact Path.step (by change some (2:Label)≠some (3:Label);decide) (clear_tool_end caller bg context ha hb ord b tool tail) .refl
  | cons value rest ih => exact Path.step (by change some (2:Label)≠some (3:Label);decide) (clear_tool_step caller bg context ha hb value ord b tool rest tail) (ih true)

theorem copy_rank_bank (bg : Stack → List Bool) (old source dest tool : Nat) (best tail : List Bool) :
    copyBank false (bank bg old source tool best true tail) (unary source) (unary dest) []=
      bank bg dest source tool best true tail := by
  funext slot;fin_cases slot <;> rfl
theorem copy_tool_bank (bg : Stack → List Bool) (old source tool dest : Nat) (best tail : List Bool) :
    copyBank true (bank bg old source tool best true tail) (unary tool) (unary dest) []=
      bank bg old source tool (unary dest) true tail := by
  funext slot;fin_cases slot <;> rfl

theorem update_path (caller : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (a b tool : Nat) (oldBest tail : List Bool) :
    Path caller (state clearRank (context,ha,hb,ord) (bank bg a b tool oldBest true tail))
      (state done (context,true,true,ord) (bank bg b b tool (unary tool) true tail))
      (a+oldBest.length+2*b+2*tool+8) := by
  have rankCopy:=actual_copy caller false (bank bg 0 b tool [] true tail) (context,false,hb,ord) (unary b) [] []
  rw [unary_reverse] at rankCopy
  change Path caller (state _ _ _) (state _ _ _) _ at rankCopy
  have rankEntry : copyBank false (bank bg 0 b tool [] true tail) (unary b) [] []=bank bg 0 b tool [] true tail := by
    funext slot;fin_cases slot <;> rfl
  rw [rankEntry,copy_rank_bank bg 0 b b tool [] tail] at rankCopy
  have toolCopy:=actual_copy caller true (bank bg b b tool [] true tail) (context,true,true,ord) (unary tool) [] []
  rw [unary_reverse] at toolCopy
  change Path caller (state _ _ _) (state _ _ _) _ at toolCopy
  have toolEntry : copyBank true (bank bg b b tool [] true tail) (unary tool) [] []=bank bg b b tool [] true tail := by
    funext slot;fin_cases slot <;> rfl
  rw [toolEntry,copy_tool_bank bg b b tool tool [] tail] at toolCopy
  have whole:=(clear_rank_path caller bg context ha hb ord a b tool oldBest tail).trans
    ((clear_tool_path caller bg context false hb ord b tool oldBest tail).trans (rankCopy.trans toolCopy))
  simpa only [unary,RankCompare.unary,List.length_replicate,copyMap,Bool.false_eq_true,ite_false,ite_true,
    show a+1+(oldBest.length+1+(2*b+3+(2*tool+3)))=a+oldBest.length+2*b+2*tool+8 by omega] using whole

theorem compare_state (bg : Stack → List Bool) (context : C) (ha hb : Bool) (ord : Ordering)
    (a b tool : Nat) (oldBest tail : List Bool) (point : RankCompare.Label) :
    LabelMap.configuration compareMap
      (RankCompare.state (bank bg a b tool oldBest true tail) point context ha hb ord a b 0 0)=
        state (compareMap point) (context,ha,hb,ord) (bank bg a b tool oldBest true tail) := by
  change (⟨some (compareMap point),(context,ha,hb,ord),_⟩ : State C)=⟨_,_,_⟩
  congr 1;funext slot;fin_cases slot <;> rfl

theorem compare_path (caller : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb : Bool) (ord : Ordering) (a b tool : Nat) (oldBest tail : List Bool) :
    ∃ steps result,RankCompare.Correct a b result ∧ steps≤2*(a+b)+3 ∧
      Path caller (state (compareMap 0) (context,ha,hb,ord) (bank bg a b tool oldBest true tail))
        (state (compareMap (RankCompare.returnLabel result)) (context,false,false,result)
          (bank bg a b tool oldBest true tail)) steps := by
  obtain ⟨trace,final,facts⟩:=RankCompare.actual_facts (C:=C) .halt .halt .halt
    (bank bg a b tool oldBest true tail) context ha hb ord a b
  obtain ⟨result,correct,rfl⟩:=facts.contents
  have path:=Path.of_mapped caller (LabelMap.configuration compareMap)
    (fun x y => TM2.step (RankCompare.program .halt .halt .halt) x=some y)
    trace _ _ facts.first facts.chain facts.last
    (by intro current member next edge
        obtain ⟨point,active,proper⟩:=facts.interior current member
        have code : ∀ other,current.l=some other → program caller (compareMap other)=
            LabelMap.statement compareMap (RankCompare.program .halt .halt .halt other) := by
          intro other activeOther
          have same : other=point := Option.some.inj (activeOther.symm.trans active)
          subst other;exact compare_code caller point proper
        rw [LabelMap.step_configuration_on compareMap (RankCompare.program .halt .halt .halt)
          (program caller) current code,edge]
        rfl)
    (by intro current member
        obtain ⟨point,active,proper⟩:=facts.interior current member
        change current.l.map compareMap≠some done
        rw [active,Option.map_some]
        fin_cases point <;> simp_all [RankCompare.Interior,compareMap,done])
  rw [compare_state,compare_state] at path
  exact ⟨_,result,correct,by have time:=facts.time;omega,path⟩

theorem resultBank_update (bg : Stack → List Bool) (a b tool : Nat) (best tail : List Bool) (flag : Bool)
    (choice : selected flag a b) : resultBank bg a b tool best flag tail=bank bg b b tool (unary tool) true tail := by
  simp only [resultBank,ite_eq_left choice]
theorem resultBank_keep (bg : Stack → List Bool) (a b tool : Nat) (best tail : List Bool) (flag : Bool)
    (choice : ¬selected flag a b) : resultBank bg a b tool best flag tail=bank bg a b tool best true tail := by
  simp only [resultBank,ite_eq_right choice]
/-- Source reads presence physically; missing best selects even a zero candidate. -/
theorem operational (caller : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb flag : Bool) (ord : Ordering) (a b tool : Nat) (oldBest tail : List Bool) :
    ∃ steps memory,Path caller (state boot (context,ha,hb,ord) (bank bg a b tool oldBest flag tail))
      (state done memory (resultBank bg a b tool oldBest flag tail)) steps ∧
      memory.1=context ∧ steps≤3*a+4*b+2*tool+oldBest.length+12 := by
  cases flag with
  | false =>
    have run:=Path.step (by change some (0:Label)≠some (3:Label);decide)
      (boot_step caller bg context ha hb false ord a b tool oldBest tail)
      (update_path caller bg context false hb ord a b tool oldBest tail)
    refine ⟨a+oldBest.length+2*b+2*tool+8+1,(context,true,true,ord),?_,rfl,by omega⟩
    rw [resultBank_update bg a b tool oldBest tail false (Or.inl rfl)]
    exact run
  | true =>
    obtain ⟨steps,result,correct,time,run⟩:=compare_path caller bg context true hb ord a b tool oldBest tail
    cases result with
    | lt =>
      have strict : a<b := correct
      have whole:=Path.step (by change some (0:Label)≠some (3:Label);decide)
        (boot_step caller bg context ha hb true ord a b tool oldBest tail)
        (run.trans (update_path caller bg context false false .lt a b tool oldBest tail))
      refine ⟨steps+(a+oldBest.length+2*b+2*tool+8)+1,(context,true,true,Ordering.lt),?_,rfl,by omega⟩
      rw [resultBank_update bg a b tool oldBest tail true (Or.inr strict)]
      exact whole
    | eq =>
      have same : a=b := correct
      have keep : ¬selected true a b := by
        intro choice;rcases choice with impossible | strict
        · cases impossible
        · omega
      have whole:=Path.step (by change some (0:Label)≠some (3:Label);decide)
        (boot_step caller bg context ha hb true ord a b tool oldBest tail) run
      refine ⟨steps+1,(context,false,false,Ordering.eq),?_,rfl,by omega⟩
      rw [resultBank_keep bg a b tool oldBest tail true keep]
      exact whole
    | gt =>
      have strict : b<a := correct
      have keep : ¬selected true a b := by
        intro choice;rcases choice with impossible | smaller
        · cases impossible
        · omega
      have whole:=Path.step (by change some (0:Label)≠some (3:Label);decide)
        (boot_step caller bg context ha hb true ord a b tool oldBest tail) run
      refine ⟨steps+1,(context,false,false,Ordering.gt),?_,rfl,by omega⟩
      rw [resultBank_keep bg a b tool oldBest tail true keep]
      exact whole
end RootB236.Controller.BestUpdate
