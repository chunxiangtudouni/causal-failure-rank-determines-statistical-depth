module
public import Structure.RootB236_Controller_Candidate_Caller_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
@[expose] public section
namespace RootB236.ControllerCandidate
open Turing PaperProofs.Common.Native PSTRWordBool PSTRWordVM

theorem actual_first_masks {C : Type*} (context : C) (bg : Stack → List Bool)
    (mem : Store) (left right : List Bool) (same : left.length=right.length) (cursor : bg 6=[]) :
    ∃ (trace : List (TM2.Cfg Alphabet Label (C×Store))) (final : TM2.Cfg Alphabet Label (C×Store)),
      trace.head?=some (inContext context (andEmbed (Bitwise.state bg 0 mem
        left right [] (unary left.length) []))) ∧
      trace.IsChain (fun a b => TM2.step (withContext C) a=some b) ∧ trace.getLast?=some final ∧
      trace.length≤12*((bg 5).length+left.length+1) ∧
      (∃ scanFinal, Outcome (scanBackground bg left.length) (Bitwise.outputs false (left.zip right)) 0 scanFinal ∧
        final=inContext context (scanEmbed scanFinal)) ∧
      (∀ current∈trace, current.var.1=context ∧
        (∀ point, (current.stk point).length≤2*mass bg+3*left.length+2) ∧
        ∀ point, ¬Owned point → current.stk point=bg point) ∧
      (∀ current∈trace, ∀ label, current.l=some label →
        ScannerClock.actions (withContext C label)≤5 ∧ AuxWorkspace.pushes (withContext C label)≤2) ∧
      (∀ current∈trace, ∀ label, current.l=some label →
        ∀ snapshot∈AuxWorkspace.nodes (withContext C label) current.var current.stk,
          snapshot.1.1=context ∧
          (∀ point, (snapshot.2 point).length≤2*mass bg+3*left.length+4) ∧
          ∀ point, ¬Owned point → snapshot.2 point=bg point) ∧
      charge (withContext C) trace≤
        (10*(2*mass bg+3*left.length+5)+1)*(12*((bg 5).length+left.length+1)) := by
  have result:=actual_first_context context bg mem (left.zip right) cursor
  have first : (left.zip right).map Prod.fst=left := List.map_fst_zip (by omega)
  have second : (left.zip right).map Prod.snd=right := List.map_snd_zip (by omega)
  have length : (left.zip right).length=left.length := by simp [List.length_zip,same]
  simpa only [first,second,length] using result

example {C : Type*} (context : C) (bg : Stack → List Bool)
    (mem : Store) (bits old : List Bool) (k : Nat) :
    ∃ (trace : List (TM2.Cfg Alphabet Label (C×Store))) (final : TM2.Cfg Alphabet Label (C×Store)),
      trace.head?=some (inContext context (scanEmbed (state bg .clear mem bits old (unary k) []))) ∧
      trace.IsChain (fun a b => TM2.step (withContext C) a=some b) ∧ trace.getLast?=some final ∧
      trace.length≤6*(old.length+k+bits.length+1) ∧
      (∃ scanFinal, Outcome bg bits k scanFinal ∧ final=inContext context (scanEmbed scanFinal)) ∧
      (∀ current∈trace, current.var.1=context ∧
        (∀ point, (current.stk point).length≤mass bg+(old.length+k+bits.length+1)) ∧
        ∀ point, ¬Allowed point → current.stk point=bg point) ∧
      (∀ current∈trace, ∀ label, current.l=some label →
        ∀ snapshot∈AuxWorkspace.nodes (withContext C label) current.var current.stk,
          snapshot.1.1=context ∧
          ∀ point, (snapshot.2 point).length≤mass bg+(old.length+k+bits.length+1)+2) ∧
      charge (withContext C) trace≤
        (10*(mass bg+(old.length+k+bits.length+1)+3)+1)*(6*(old.length+k+bits.length+1)) := by
  exact actual_resume_context context bg mem bits old k

example (bg : Stack → List Bool) (mem : Store)
    (bits old : List Bool) (k q : Nat) (extent : k+bits.length=q) (oldBound : old.length≤q) :
    ∃ (trace : List ScanState) (final : ScanState),
      trace.head?=some (state bg .clear mem bits old (unary k) []) ∧
      trace.IsChain (fun a b => TM2.step scanner a=some b) ∧ trace.getLast?=some final ∧
      trace.length≤12*(q+1) ∧ Outcome bg bits k final ∧
      ∀ current∈trace, ∀ point, (current.stk point).length≤(bg point).length+(2*q+1) := by
  exact actual_resume_extent bg mem bits old k q extent oldBound

example {q : Nat} (eligible remaining : Finset (Fin q)) :
    pending 0 (Bitwise.outputs false (incidencePairs eligible remaining))=
      (PaperProofs.Structure.genericRankCandidates q eligible remaining).map Fin.val := by
  exact original_candidates eligible remaining

example (bg : Stack → List Bool) (bits : List Bool) (k q : Nat)
    (extent : k+bits.length=q) (final : ScanState) (outcome : Outcome bg bits k final) :
    (∃ tool tail, tool<q ∧ tool+1+tail.length=q ∧
      pending k bits=tool::pending (tool+1) tail ∧
      final=state bg .found (false,false) tail (unary tool) (unary (tool+1)) []) ∨
    (pending k bits=[] ∧ final=state bg .empty (false,false) [] [] (unary q) []) := by
  exact outcome_extent bg bits k q extent final outcome

example (found empty : Statement) (trace : List State) (final : State)
    (chain : trace.IsChain (fun a b => TM2.step source a=some b))
    (last : trace.getLast?=some final) (active : final.l≠none) :
    trace.IsChain (fun a b => TM2.step (program found empty) a=some b) := by
  exact actual_caller_splice found empty trace final chain last active

example : TM2.Supports source (Finset.univ : Finset Label) := supports .halt .halt

end RootB236.ControllerCandidate
