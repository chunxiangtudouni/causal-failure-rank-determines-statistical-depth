module
public import RootB236_Controller_DFSDriver_Callbacks007

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver
open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*}

theorem active_state (before : State C) (point : Label) (active : before.l=some point) :
    before=state point before.var before.stk := by
  cases before with
  | mk position memory slots =>
    change position=some point at active
    subst position;rfl

/-- The bad-return prefix really updates from physical15, preserves physical10, and empties15 before Resume. -/
theorem bad_to_resume (good bad pop finish : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb flag : Bool) (ord : Ordering) (a b tool : Nat) (best tail : List Bool) :
    ∃ trace final,BestUpdate.Facts .halt bg context ha hb flag ord a b tool best tail trace final ∧
      Path good bad pop finish
        (transported badRoles (Equiv.refl (Store C)) bestMap
          (BestUpdate.state BestUpdate.boot (context,ha,hb,ord) (BestUpdate.bank bg a b tool best flag tail)))
        (state (.resume .clear) (final.var.1,false,final.var.2.2.1,final.var.2.2.2)
          (Function.update (StackIso.slots badRoles final.stk) 15 [])) (trace.length-1+(b+1)) := by
  obtain ⟨trace,final,facts,updated⟩:=best_path good bad pop finish bg context ha hb flag ord a b tool best tail
  have active : (transported badRoles (Equiv.refl (Store C)) bestMap final).l=some (.control 19) := by
    change final.l.map bestMap=some (.control 19)
    rw [facts.contents.1]
    rfl
  have asState:=active_state (transported badRoles (Equiv.refl (Store C)) bestMap final) (.control 19) active
  rw [asState] at updated
  have child : StackIso.slots badRoles final.stk 15=unary b := by
    change final.stk 10=unary b
    exact facts.outputs.2.2.1
  have cleared:=clear_child_path good bad pop finish true (StackIso.slots badRoles final.stk) final.var (unary b) child
  have whole:=updated.trans cleared
  refine ⟨trace,final,facts,?_⟩
  simpa only [clearChildPoint,clearChildReturn,ite_true,unary,RankCompare.unary,List.length_replicate] using whole

/-- Sup/current-tool/new-rank are physical fields; skip10 is untouched by the static10/15 renaming. -/
theorem best_counter_shape (bg : Stack → List Bool) (a b tool : Nat) (best tail : List Bool) (flag : Bool) :
    StackIso.slots badRoles (BestUpdate.bank bg a b tool best flag tail) 9=unary a ∧
    StackIso.slots badRoles (BestUpdate.bank bg a b tool best flag tail) 15=unary b ∧
    StackIso.slots badRoles (BestUpdate.bank bg a b tool best flag tail) 10=bg 15 ∧
    StackIso.slots badRoles (BestUpdate.bank bg a b tool best flag tail) 13=flag::tail := ⟨rfl,rfl,rfl,rfl⟩

def scanState (bg : Stack → List Bool) (point : Label) (memory : Store C)
    (bits remaining tool cursor archive room : List Bool) : State C :=
  state point memory (SelectErase.bank bg bits remaining tool cursor [] archive room [])

theorem select_initial (bg : Stack → List Bool) (memory : Store C) (eligible remaining old5 : List Bool) :
    transported (Equiv.refl Stack) BestUpdate.storeIso selectMap
      (SelectErase.initial bg (BestUpdate.storeIso.symm memory) eligible remaining old5)=
        scanState bg (.select SelectErase.entry) memory eligible remaining old5 [] [] (unary eligible.length) := by
  rfl

theorem resume_initial (bg : Stack → List Bool) (memory : Store C) (bits parent old4 old5 : List Bool) (k : Nat) :
    transported (Equiv.refl Stack) BestUpdate.storeIso resumeMap
      (ResumeErase.initial bg (BestUpdate.storeIso.symm memory) bits parent old4 old5 k)=
        scanState bg (.resume .clear) memory bits old4 old5 (unary k) parent.reverse (unary parent.length) := by
  rfl

/-- The mapped first result is selected by the actual found/empty label, with the exact same banks. -/
theorem mapped_select_outcome (bg : Stack → List Bool) (context : C) (order : Ordering)
    (eligible remaining : List Bool) (final : SelectErase.State (C×Ordering))
    (outcome : SelectErase.Outcome bg (context,order) eligible remaining final) :
    (∃ tool tail,tool<eligible.length ∧ tool+1+tail.length=eligible.length ∧
      transported (Equiv.refl Stack) BestUpdate.storeIso selectMap final=
        scanState bg pushBad (context,false,false,order) tail (SelectErase.eraseMask remaining tool)
          (unary tool) (unary (tool+1)) remaining.reverse (unary eligible.length)) ∨
    (transported (Equiv.refl Stack) BestUpdate.storeIso selectMap final=
      scanState bg (.merge RankMerge.entry) (context,true,true,order) [] remaining [] (unary eligible.length)
        remaining.reverse (unary eligible.length)) := by
  rcases outcome with ⟨tool,tail,range,width,_pending,rfl⟩ | ⟨_pending,rfl⟩
  · exact Or.inl ⟨tool,tail,range,width,rfl⟩
  · exact Or.inr rfl

/-- Resume returns to the same bad-call/merge control and never executes a second initial AND. -/
theorem mapped_resume_outcome (bg : Stack → List Bool) (context : C) (order : Ordering)
    (bits parent : List Bool) (k : Nat) (final : ResumeErase.State (C×Ordering))
    (outcome : ResumeErase.Outcome bg (context,order) bits parent k final) :
    (∃ tool tail,tool<parent.length ∧ tool+1+tail.length=parent.length ∧
      transported (Equiv.refl Stack) BestUpdate.storeIso resumeMap final=
        scanState bg pushBad (context,false,false,order) tail (SelectErase.eraseMask parent tool)
          (unary tool) (unary (tool+1)) parent.reverse (unary parent.length)) ∨
    (transported (Equiv.refl Stack) BestUpdate.storeIso resumeMap final=
      scanState bg (.merge RankMerge.entry) (context,true,true,order) [] parent [] (unary parent.length)
        parent.reverse (unary parent.length)) := by
  rcases outcome with ⟨tool,tail,range,width,_pending,rfl⟩ | ⟨_pending,rfl⟩
  · exact Or.inl ⟨tool,tail,range,width,rfl⟩
  · exact Or.inr rfl
end RootB236.Controller.DFSDriver
