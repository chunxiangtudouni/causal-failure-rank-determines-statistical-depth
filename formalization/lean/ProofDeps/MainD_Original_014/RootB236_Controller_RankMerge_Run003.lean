module
public import RootB236_Controller_RankMerge_Callees002

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.RankMerge
open Turing
variable {C : Type*}
theorem increment_step (caller : Statement C) (bg : Stack → List Bool) (memory : Store C) (limit a b : Nat) :
    TM2.step (program caller) (state increment memory (bank bg limit a b))=
      some (state second memory (bank bg limit (a+1) b)) := by
  change some (⟨_,_,_⟩ : State C)=_
  congr 1;congr 1;funext slot;fin_cases slot <;> rfl

theorem clear_step (caller : Statement C) (bg : Stack → List Bool) (context : C) (ha hb : Bool)
    (ord : Ordering) (limit a b : Nat) :
    TM2.step (program caller) (state clearRank (context,ha,hb,ord) (bank bg limit (a+1) b))=
      some (state clearRank (context,true,hb,ord) (bank bg limit a b)) := by
  change some (⟨_,_,_⟩ : State C)=_
  congr 1;congr 1;funext slot;fin_cases slot <;> rfl
theorem clear_end (caller : Statement C) (bg : Stack → List Bool) (context : C) (ha hb : Bool)
    (ord : Ordering) (limit b : Nat) :
    TM2.step (program caller) (state clearRank (context,ha,hb,ord) (bank bg limit 0 b))=
      some (state (copyMap .boot) (context,false,hb,ord) (bank bg limit 0 b)) := by
  change some (⟨_,_,_⟩ : State C)=_
  congr 1;congr 1;funext slot;fin_cases slot <;> rfl
theorem clear_path (caller : Statement C) (bg : Stack → List Bool) (context : C) (ha hb : Bool)
    (ord : Ordering) (limit a b : Nat) :
    Path caller (state clearRank (context,ha,hb,ord) (bank bg limit a b))
      (state (copyMap .boot) (context,false,hb,ord) (bank bg limit 0 b)) (a+1) := by
  induction a generalizing ha with
  | zero =>
    exact Path.step (by change some (7:Label)≠some (11:Label);decide)
      (clear_end caller bg context ha hb ord limit b) .refl
  | succ a ih =>
    exact Path.step (by change some (7:Label)≠some (11:Label);decide)
      (clear_step caller bg context ha hb ord limit a b) (ih true)

theorem copy_bank (bg : Stack → List Bool) (limit old source dest : Nat) :
    BestUpdate.copyBank false (bank bg limit old source) (unary source) (unary dest) []=
      bank bg limit dest source := by
  funext slot;fin_cases slot <;> rfl

theorem replace_path (caller : Statement C) (bg : Stack → List Bool) (context : C) (ha hb : Bool)
    (ord : Ordering) (limit a b : Nat) :
    Path caller (state clearRank (context,ha,hb,ord) (bank bg limit a b))
      (state done (context,true,true,ord) (bank bg limit b b)) (a+2*b+4) := by
  have copied:=actual_copy caller (bank bg limit 0 b) (context,false,hb,ord) (unary b) [] []
  rw [show (unary b).reverse++[]=unary b from BestUpdate.unary_reverse b] at copied
  change Path caller (state _ _ _) (state _ _ _) _ at copied
  have entryBank : BestUpdate.copyBank false (bank bg limit 0 b) (unary b) [] []=bank bg limit 0 b := by
    funext slot;fin_cases slot <;> rfl
  rw [entryBank,copy_bank bg limit 0 b b] at copied
  have whole:=(clear_path caller bg context ha hb ord limit a b).trans copied
  simpa only [unary,RankCompare.unary,List.length_replicate,copyMap,
    show a+1+(2*b+3)=a+2*b+4 by omega] using whole

theorem min_path (caller : Statement C) (bg : Stack → List Bool) (context : C) (ha hb : Bool)
    (ord : Ordering) (limit a b : Nat) :
    ∃ steps memory,Path caller (state second (context,ha,hb,ord) (bank bg limit a b))
      (state done memory (bank bg limit (min a b) b)) steps ∧ memory.1=context ∧ steps≤3*a+4*b+7 := by
  obtain ⟨steps,result,correct,time,path⟩:=second_path caller bg context ha hb ord limit a b
  cases result with
  | lt =>
    have strict : a<b := correct
    refine ⟨steps,(context,false,false,Ordering.lt),?_,rfl,by omega⟩
    rw [min_eq_left (Nat.le_of_lt strict)]
    exact path
  | eq =>
    have same : a=b := correct
    refine ⟨steps,(context,false,false,Ordering.eq),?_,rfl,by omega⟩
    rw [min_eq_left (Nat.le_of_eq same)]
    exact path
  | gt =>
    have strict : b<a := correct
    have whole:=path.trans (replace_path caller bg context false false .gt limit a b)
    refine ⟨steps+(a+2*b+4),(context,true,true,Ordering.gt),?_,rfl,by omega⟩
    rw [min_eq_right (Nat.le_of_lt strict)]
    exact whole

theorem capped_succ_le (limit a : Nat) : cappedSucc limit a≤a+1 := by
  unfold cappedSucc;split_ifs <;> omega

theorem succ_path (caller : Statement C) (bg : Stack → List Bool) (context : C) (ha hb : Bool)
    (ord : Ordering) (limit a b : Nat) :
    ∃ steps result,Path caller (state entry (context,ha,hb,ord) (bank bg limit a b))
      (state second (context,false,false,result) (bank bg limit (cappedSucc limit a) b)) steps ∧
      steps≤2*(a+limit)+4 := by
  obtain ⟨steps,result,correct,time,path⟩:=first_path caller bg context ha hb ord limit a b
  cases result with
  | lt =>
    have strict : a<limit := correct
    have tail : Path caller (state increment (context,false,false,Ordering.lt) (bank bg limit a b))
        (state second (context,false,false,Ordering.lt) (bank bg limit (a+1) b)) 1 :=
      Path.step (by change some (3:Label)≠some (11:Label);decide)
        (increment_step caller bg (context,false,false,Ordering.lt) limit a b) .refl
    refine ⟨steps+1,Ordering.lt,?_,by omega⟩
    rw [cappedSucc,ite_eq_left strict]
    exact path.trans tail
  | eq =>
    have same : a=limit := correct
    have keep : ¬a<limit := by omega
    refine ⟨steps,Ordering.eq,?_,by omega⟩
    rw [cappedSucc,ite_eq_right keep]
    exact path
  | gt =>
    have strict : limit<a := correct
    have keep : ¬a<limit := by omega
    refine ⟨steps,Ordering.gt,?_,by omega⟩
    rw [cappedSucc,ite_eq_right keep]
    exact path

/-- Complete actual fixed-source operator; all values remain physical unary data. -/
theorem operational (caller : Statement C) (bg : Stack → List Bool) (context : C) (ha hb : Bool)
    (ord : Ordering) (limit a b : Nat) :
    ∃ steps memory,Path caller (state entry (context,ha,hb,ord) (bank bg limit a b))
      (state done memory (bank bg limit (merged limit a b) b)) steps ∧ memory.1=context ∧
      steps≤5*a+2*limit+4*b+14 := by
  obtain ⟨early,result,first,timeFirst⟩:=succ_path caller bg context ha hb ord limit a b
  obtain ⟨later,memory,last,preserved,timeLast⟩:=min_path caller bg context false false result limit (cappedSucc limit a) b
  have capped:=capped_succ_le limit a
  exact ⟨early+later,memory,first.trans last,preserved,by omega⟩
end RootB236.Controller.RankMerge
