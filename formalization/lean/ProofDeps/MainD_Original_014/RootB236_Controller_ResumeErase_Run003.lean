module
public import RootB236_Controller_ResumeErase_Paths002

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.ResumeErase
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM
variable {C : Type*}

def Outcome (bg : Stack → List Bool) (context : C) (bits parent : List Bool) (k : Nat) (final : State C) : Prop :=
  (∃ tool tail,tool<parent.length ∧ tool+1+tail.length=parent.length ∧
    ControllerCandidate.pending k bits=tool::ControllerCandidate.pending (tool+1) tail ∧
    final=state bg foundPort (context,false,false) tail (SelectErase.eraseMask parent tool)
      (ControllerCandidate.unary tool) (ControllerCandidate.unary (tool+1)) [] parent.reverse
      (ControllerCandidate.unary parent.length) []) ∨
  (ControllerCandidate.pending k bits=[] ∧ final=state bg emptyPort (context,true,true)
    [] parent [] (ControllerCandidate.unary parent.length) [] parent.reverse (ControllerCandidate.unary parent.length) [])

theorem outcome_map {bg : Stack → List Bool} {context : C} {bits parent : List Bool} {k : Nat}
    {final : SelectErase.State C} (outcome : OldOutcome bg context bits parent k final) :
    Outcome bg context bits parent k (LabelMap.configuration Label.body final) := by
  rcases outcome with ⟨tool,tail,range,width,pending,rfl⟩ | ⟨pending,rfl⟩
  · exact Or.inl ⟨tool,tail,range,width,pending,rfl⟩
  · exact Or.inr ⟨pending,rfl⟩

theorem actual_path (bg : Stack → List Bool) (memory : Store C) (bits parent old4 old5 : List Bool) (k : Nat)
    (extent : k+bits.length=parent.length) :
    ∃ final,Outcome bg memory.1 bits parent k final ∧
      Nonempty (Path (initial bg memory bits parent old4 old5 k) final
        (32*(old4.length+old5.length+parent.length+1))) := by
  let clear : Path (initial bg memory bits parent old4 old5 k)
      (state bg (.body (.candidate (.inr .clear))) (memory.1,false,false) bits [] old5 (ControllerCandidate.unary k)
        [] parent.reverse (ControllerCandidate.unary parent.length) []) (old4.length+2) :=
    ⟨_,clear_head _ _ _ _ _ _ _,clear_chain _ _ _ _ _ _ _,clear_last _ _ _ _ _ _ _,by rw [clear_length]⟩
  obtain ⟨oldFinal,outcome,⟨oldPath⟩⟩:=old_path bg (memory.1,false,false) bits parent old5 k extent
  let mapped:=liftPath oldPath
  have next : Path
      (state bg (.body (.candidate (.inr .clear))) (memory.1,false,false) bits [] old5 (ControllerCandidate.unary k)
        [] parent.reverse (ControllerCandidate.unary parent.length) [])
      (LabelMap.configuration Label.body oldFinal) (16*(old5.length+parent.length+1)) := mapped
  let whole:=clear.trans next
  refine ⟨_,outcome_map outcome,⟨whole.weaken ?_⟩⟩
  omega

theorem actual (bg : Stack → List Bool) (memory : Store C) (bits parent old4 old5 : List Bool) (k : Nat)
    (extent : k+bits.length=parent.length) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (initial bg memory bits parent old4 old5 k) ∧
      trace.IsChain (fun a b => TM2.step source a=some b) ∧ trace.getLast?=some final ∧
      trace.length≤32*(old4.length+old5.length+parent.length+1) ∧ Outcome bg memory.1 bits parent k final := by
  obtain ⟨final,outcome,⟨path⟩⟩:=actual_path bg memory bits parent old4 old5 k extent
  exact ⟨path.trace,final,path.head,path.chain,path.tail,path.time,outcome⟩

theorem Outcome.active {bg : Stack → List Bool} {context : C} {bits parent : List Bool} {k : Nat} {final : State C}
    (outcome : Outcome bg context bits parent k final) : final.l=some foundPort ∨ final.l=some emptyPort := by
  rcases outcome with ⟨tool,tail,_range,_width,_pending,rfl⟩ | ⟨_pending,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
end RootB236.Controller.ResumeErase
