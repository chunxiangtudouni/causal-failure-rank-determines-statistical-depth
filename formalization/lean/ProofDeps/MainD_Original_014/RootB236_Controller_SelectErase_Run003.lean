module
public import RootB236_Controller_SelectErase_Paths002

/-! The complete first select/erase path of the ONE fixed global graph.
All branch decisions were already made by actual candidate label returns. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB236.Controller.SelectErase
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM
variable {C : Type*}

def Outcome (bg : Stack → List Bool) (context : C) (eligible remaining : List Bool) (final : State C) : Prop :=
  (∃ tool tail,tool<eligible.length ∧ tool+1+tail.length=eligible.length ∧
    ControllerCandidate.pending 0 (andBits eligible remaining)=tool::ControllerCandidate.pending (tool+1) tail ∧
    final=state bg .found (context,false,false) tail (eraseMask remaining tool) (ControllerCandidate.unary tool)
      (ControllerCandidate.unary (tool+1)) [] remaining.reverse (ControllerCandidate.unary eligible.length) []) ∨
  (ControllerCandidate.pending 0 (andBits eligible remaining)=[] ∧
    final=state bg .empty (context,true,true) [] remaining [] (ControllerCandidate.unary eligible.length) []
      remaining.reverse (ControllerCandidate.unary eligible.length) [])

theorem actual_path (bg : Stack → List Bool) (memory : Store C) (eligible remaining old5 : List Bool)
    (same : eligible.length=remaining.length) :
    ∃ final,Outcome bg memory.1 eligible remaining final ∧
      Nonempty (Path (initial bg memory eligible remaining old5) final (32*(old5.length+eligible.length+1))) := by
  obtain ⟨first⟩:=archive_path bg memory eligible remaining old5
  let mem : Store C := (memory.1,true,true)
  obtain ⟨scanFinal,afterCandidate,outcome,returned,⟨candidate⟩⟩:=candidate_path bg mem eligible remaining old5 same
  have extent : 0+(andBits eligible remaining).length=eligible.length := by
    simp only [andBits,Bitwise.outputs,List.length_map,List.length_zip,same,Nat.min_self,Nat.zero_add]
  rcases ControllerCandidate.outcome_extent _ (andBits eligible remaining) 0 eligible.length extent scanFinal outcome with
    ⟨tool,tail,range,width,pending,scanEq⟩ | ⟨pending,scanEq⟩
  · have candidateEnd : afterCandidate=state bg (.restoreFound .boot) (memory.1,false,false)
        tail [] (ControllerCandidate.unary tool) (ControllerCandidate.unary (tool+1)) [] remaining.reverse
          (ControllerCandidate.unary eligible.length) [] := by
      rw [returned,scanEq]
      exact candidate_final bg eligible remaining old5 tail (ControllerCandidate.unary tool)
        (ControllerCandidate.unary (tool+1)) .found (memory.1,false,false)
    have candidate' : Path
        (state bg (.candidate (.inl 0)) (memory.1,true,true) eligible remaining old5 [] [] remaining.reverse
          (ControllerCandidate.unary eligible.length) [])
        (state bg (.restoreFound .boot) (memory.1,false,false) tail [] (ControllerCandidate.unary tool)
          (ControllerCandidate.unary (tool+1)) [] remaining.reverse (ControllerCandidate.unary eligible.length) [])
        (12*(old5.length+eligible.length+1)) := candidateEnd ▸ candidate
    obtain ⟨restored⟩:=restore_found_path bg (memory.1,false,false) tail remaining (ControllerCandidate.unary tool)
      (ControllerCandidate.unary (tool+1)) (ControllerCandidate.unary eligible.length)
    obtain ⟨erased⟩:=erase_path bg (memory.1,true,true) tail remaining (ControllerCandidate.unary (tool+1))
      (ControllerCandidate.unary eligible.length) tool (by omega)
    let whole:=((first.trans candidate').trans restored).trans erased
    refine ⟨_,Or.inl ⟨tool,tail,range,width,pending,rfl⟩,⟨whole.weaken ?_⟩⟩
    omega
  · have candidateEnd : afterCandidate=state bg (.restoreEmpty .boot) (memory.1,false,false)
        [] [] [] (ControllerCandidate.unary eligible.length) [] remaining.reverse
          (ControllerCandidate.unary eligible.length) [] := by
      rw [returned,scanEq]
      exact candidate_final bg eligible remaining old5 [] [] (ControllerCandidate.unary eligible.length)
        .empty (memory.1,false,false)
    have candidate' : Path
        (state bg (.candidate (.inl 0)) (memory.1,true,true) eligible remaining old5 [] [] remaining.reverse
          (ControllerCandidate.unary eligible.length) [])
        (state bg (.restoreEmpty .boot) (memory.1,false,false) [] [] [] (ControllerCandidate.unary eligible.length)
          [] remaining.reverse (ControllerCandidate.unary eligible.length) []) (12*(old5.length+eligible.length+1)) :=
      candidateEnd ▸ candidate
    obtain ⟨restored⟩:=restore_empty_path bg (memory.1,false,false) remaining (ControllerCandidate.unary eligible.length)
      (ControllerCandidate.unary eligible.length)
    let whole:=(first.trans candidate').trans restored
    refine ⟨_,Or.inr ⟨pending,rfl⟩,⟨whole.weaken ?_⟩⟩
    omega

theorem actual (bg : Stack → List Bool) (memory : Store C) (eligible remaining old5 : List Bool)
    (same : eligible.length=remaining.length) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (initial bg memory eligible remaining old5) ∧
      trace.IsChain (fun a b => TM2.step source a=some b) ∧ trace.getLast?=some final ∧
      trace.length≤32*(old5.length+eligible.length+1) ∧ Outcome bg memory.1 eligible remaining final := by
  obtain ⟨final,outcome,⟨path⟩⟩:=actual_path bg memory eligible remaining old5 same
  exact ⟨path.trace,final,path.head,path.chain,path.tail,path.time,outcome⟩

theorem Outcome.active {bg : Stack → List Bool} {context : C} {eligible remaining : List Bool} {final : State C}
    (outcome : Outcome bg context eligible remaining final) : final.l=some .found ∨ final.l=some .empty := by
  rcases outcome with ⟨tool,tail,_range,_width,_pending,rfl⟩ | ⟨_pending,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

end RootB236.Controller.SelectErase
