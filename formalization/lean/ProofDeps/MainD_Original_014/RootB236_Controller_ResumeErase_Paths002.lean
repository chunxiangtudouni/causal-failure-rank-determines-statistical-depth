module
public import RootB236_Controller_ResumeErase_Code001

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

structure Path (first last : State C) (budget : Nat) where
  trace : List (State C)
  head : trace.head?=some first
  chain : trace.IsChain (fun a b => TM2.step source a=some b)
  tail : trace.getLast?=some last
  time : trace.length≤budget
namespace Path
variable {a b c : State C} {s t : Nat}
def trans (front : Path a b s) (back : Path b c t) : Path a c (s+t) := by
  have shape : b::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp back.head
    rw [same];rfl
  refine ⟨front.trace++back.trace.tail,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.head];rfl
  · exact NativeTrace.join_chain _ _ _ front.tail front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.tail).trans (shape.symm ▸ back.tail)
  · have sizes:=congrArg List.length shape
    have h1:=front.time;have h2:=back.time
    simp only [List.length_cons] at sizes
    simp only [List.length_append]
    omega
def weaken (path : Path a b s) (bound : s≤t) : Path a b t :=
  ⟨path.trace,path.head,path.chain,path.tail,path.time.trans bound⟩
end Path

def liftPath {a b : SelectErase.State C} {budget : Nat} (path : SelectErase.Path a b budget) :
    Path (LabelMap.configuration Label.body a) (LabelMap.configuration Label.body b) budget :=
  ⟨path.trace.map (LabelMap.configuration Label.body),by rw [List.head?_map,path.head,Option.map_some],
    LabelMap.chain_configuration_on Label.body SelectErase.source source path.trace path.chain (by intros;exact body_closed _),
    by rw [List.getLast?_map,path.tail,Option.map_some],by simpa only [List.length_map] using path.time⟩

def clearTrace (bg : Stack → List Bool) (memory : Store C) (bits parent old5 : List Bool) (k : Nat) :
    List Bool → List (State C)
  | [] => [state bg .clear memory bits [] old5 (ControllerCandidate.unary k) [] parent.reverse
      (ControllerCandidate.unary parent.length) [],
    state bg (.body (.candidate (.inr .clear))) (memory.1,false,false) bits [] old5 (ControllerCandidate.unary k)
      [] parent.reverse (ControllerCandidate.unary parent.length) []]
  | bit::later => state bg .clear memory bits (bit::later) old5 (ControllerCandidate.unary k) [] parent.reverse
      (ControllerCandidate.unary parent.length) []::clearTrace bg (memory.1,true,bit) bits parent old5 k later
theorem clear_head (bg : Stack → List Bool) (memory : Store C) (bits parent old5 old4 : List Bool) (k : Nat) :
    (clearTrace bg memory bits parent old5 k old4).head?=some (initial bg memory bits parent old4 old5 k) := by
  cases old4 <;> rfl
theorem clear_nonempty (bg : Stack → List Bool) (memory : Store C) (bits parent old5 old4 : List Bool) (k : Nat) :
    clearTrace bg memory bits parent old5 k old4≠[] := by cases old4 <;> simp [clearTrace]
theorem clear_last (bg : Stack → List Bool) (memory : Store C) (bits parent old5 old4 : List Bool) (k : Nat) :
    (clearTrace bg memory bits parent old5 k old4).getLast?=some
      (state bg (.body (.candidate (.inr .clear))) (memory.1,false,false) bits [] old5 (ControllerCandidate.unary k)
        [] parent.reverse (ControllerCandidate.unary parent.length) []) := by
  induction old4 generalizing memory with
  | nil => rfl
  | cons bit later ih => rw [clearTrace,List.getLast?_cons_of_ne_nil (clear_nonempty _ _ _ _ _ _ _),ih]
theorem clear_length (bg : Stack → List Bool) (memory : Store C) (bits parent old5 old4 : List Bool) (k : Nat) :
    (clearTrace bg memory bits parent old5 k old4).length=old4.length+2 := by
  induction old4 generalizing memory with
  | nil => rfl
  | cons bit later ih => simp only [clearTrace,List.length_cons,ih]
theorem clear_chain (bg : Stack → List Bool) (memory : Store C) (bits parent old5 old4 : List Bool) (k : Nat) :
    (clearTrace bg memory bits parent old5 k old4).IsChain (fun a b => TM2.step source a=some b) := by
  induction old4 generalizing memory with
  | nil => exact List.isChain_cons_cons.mpr ⟨clear_end _ _ _ _ _ _ _ _ _,.singleton _⟩
  | cons bit later ih =>
    apply List.IsChain.cons (ih (memory.1,true,bit))
    intro next selected
    rw [clear_head] at selected
    have same : next=_ := (Option.mem_some_iff.mp selected).symm
    subst next
    exact clear_bit _ _ _ _ _ _ _ _ _ _ _

theorem candidate_state (bg : Stack → List Bool) (bits parent old5 output tool cursor : List Bool) (k : Nat)
    (point : ControllerCandidate.ScanLabel) (memory : Store C) :
    LabelMap.configuration SelectErase.candidateLabels (ControllerCandidate.inContext memory.1
      (ControllerCandidate.scanEmbed (ControllerCandidate.state
        (bank bg bits [] old5 (ControllerCandidate.unary k) [] parent.reverse
          (ControllerCandidate.unary parent.length) []) point memory.2 output tool cursor [])))=
    SelectErase.state bg (SelectErase.candidateLabels (.inr point)) memory output [] tool cursor [] parent.reverse
      (ControllerCandidate.unary parent.length) [] := by
  unfold LabelMap.configuration ControllerCandidate.inContext ContextLift.configuration ControllerCandidate.scanEmbed
    ControllerCandidate.state ControllerCandidate.cells SelectErase.state bank SelectErase.bank
  congr 1
  funext stack;fin_cases stack <;> rfl

theorem candidate_path (bg : Stack → List Bool) (memory : Store C) (bits parent old5 : List Bool) (k : Nat) :
    ∃ scanFinal final,
      ControllerCandidate.Outcome (bank bg bits [] old5 (ControllerCandidate.unary k) [] parent.reverse
        (ControllerCandidate.unary parent.length) []) bits k scanFinal ∧
      final=LabelMap.configuration SelectErase.candidateLabels
        (ControllerCandidate.inContext memory.1 (ControllerCandidate.scanEmbed scanFinal)) ∧
      Nonempty (SelectErase.Path
        (SelectErase.state bg (.candidate (.inr .clear)) memory bits [] old5 (ControllerCandidate.unary k) [] parent.reverse
          (ControllerCandidate.unary parent.length) []) final (6*(old5.length+k+bits.length+1))) := by
  let oldBg:=bank bg bits [] old5 (ControllerCandidate.unary k) [] parent.reverse (ControllerCandidate.unary parent.length) []
  obtain ⟨run,oldFinal,first,chain,last,time,⟨scanFinal,outcome,returned⟩,_bounds,_internal,_charge⟩:=
    ControllerCandidate.actual_resume_context memory.1 oldBg memory.2 bits old5 k
  have active : oldFinal.l≠none := by
    rw [returned]
    rcases outcome with ⟨skip,tail,shape,ended⟩ | ⟨shape,ended⟩ <;> rw [ended] <;>
      simp [ControllerCandidate.inContext,ContextLift.configuration,ControllerCandidate.scanEmbed,
        LabelMap.configuration,ControllerCandidate.state]
  have nf:=ControllerCandidate.no_early_halt_port (ControllerCandidate.withContext C) (.inr .found) rfl run oldFinal chain last active
  have ne:=ControllerCandidate.no_early_halt_port (ControllerCandidate.withContext C) (.inr .empty) rfl run oldFinal chain last active
  refine ⟨scanFinal,_,outcome,congrArg (LabelMap.configuration SelectErase.candidateLabels) returned,⟨?_,?_,?_,?_,?_⟩⟩
  · exact run.map (LabelMap.configuration SelectErase.candidateLabels)
  · rw [List.head?_map,first,Option.map_some,candidate_state];rfl
  · apply LabelMap.chain_configuration_on SelectErase.candidateLabels (ControllerCandidate.withContext C) SelectErase.source run chain
    intro current member point selected
    exact SelectErase.candidate_agrees .halt .halt point (fun same => nf current member (same ▸ selected))
      (fun same => ne current member (same ▸ selected))
  · rw [List.getLast?_map,last,Option.map_some]
  · simpa only [List.length_map] using time

def OldOutcome (bg : Stack → List Bool) (context : C) (bits parent : List Bool) (k : Nat)
    (final : SelectErase.State C) : Prop :=
  (∃ tool tail,tool<parent.length ∧ tool+1+tail.length=parent.length ∧
    ControllerCandidate.pending k bits=tool::ControllerCandidate.pending (tool+1) tail ∧
    final=SelectErase.state bg .found (context,false,false) tail (SelectErase.eraseMask parent tool)
      (ControllerCandidate.unary tool) (ControllerCandidate.unary (tool+1)) [] parent.reverse
      (ControllerCandidate.unary parent.length) []) ∨
  (ControllerCandidate.pending k bits=[] ∧ final=SelectErase.state bg .empty (context,true,true)
    [] parent [] (ControllerCandidate.unary parent.length) [] parent.reverse (ControllerCandidate.unary parent.length) [])

theorem old_path (bg : Stack → List Bool) (memory : Store C) (bits parent old5 : List Bool) (k : Nat)
    (extent : k+bits.length=parent.length) :
    ∃ final,OldOutcome bg memory.1 bits parent k final ∧
      Nonempty (SelectErase.Path (SelectErase.state bg (.candidate (.inr .clear)) memory bits [] old5
        (ControllerCandidate.unary k) [] parent.reverse (ControllerCandidate.unary parent.length) []) final
        (16*(old5.length+parent.length+1))) := by
  obtain ⟨scanFinal,afterCandidate,outcome,returned,⟨candidate⟩⟩:=candidate_path bg memory bits parent old5 k
  rcases ControllerCandidate.outcome_extent _ bits k parent.length extent scanFinal outcome with
    ⟨tool,tail,range,width,pending,scanEq⟩ | ⟨pending,scanEq⟩
  · have ended : afterCandidate=SelectErase.state bg (.restoreFound .boot) (memory.1,false,false) tail []
        (ControllerCandidate.unary tool) (ControllerCandidate.unary (tool+1)) [] parent.reverse
        (ControllerCandidate.unary parent.length) [] := by
      rw [returned,scanEq]
      exact candidate_state bg bits parent old5 tail (ControllerCandidate.unary tool) (ControllerCandidate.unary (tool+1))
        k .found (memory.1,false,false)
    have cand:=ended ▸ candidate
    obtain ⟨restored⟩:=SelectErase.restore_found_path bg (memory.1,false,false) tail parent
      (ControllerCandidate.unary tool) (ControllerCandidate.unary (tool+1)) (ControllerCandidate.unary parent.length)
    obtain ⟨erased⟩:=SelectErase.erase_path bg (memory.1,true,true) tail parent (ControllerCandidate.unary (tool+1))
      (ControllerCandidate.unary parent.length) tool range
    let whole:=(cand.trans restored).trans erased
    refine ⟨_,Or.inl ⟨tool,tail,range,width,pending,rfl⟩,⟨whole.weaken ?_⟩⟩
    omega
  · have ended : afterCandidate=SelectErase.state bg (.restoreEmpty .boot) (memory.1,false,false)
        [] [] [] (ControllerCandidate.unary parent.length) [] parent.reverse (ControllerCandidate.unary parent.length) [] := by
      rw [returned,scanEq]
      exact candidate_state bg bits parent old5 [] [] (ControllerCandidate.unary parent.length) k .empty (memory.1,false,false)
    have cand:=ended ▸ candidate
    obtain ⟨restored⟩:=SelectErase.restore_empty_path bg (memory.1,false,false) parent
      (ControllerCandidate.unary parent.length) (ControllerCandidate.unary parent.length)
    let whole:=cand.trans restored
    refine ⟨_,Or.inr ⟨pending,rfl⟩,⟨whole.weaken ?_⟩⟩
    omega

end RootB236.Controller.ResumeErase
