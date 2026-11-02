module
public import Structure.RootB236_Controller_Candidate_Join_004
public import PaperProofs.Structure.RankEvaluator

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
@[expose] public section
namespace RootB236.ControllerCandidate
open Turing
open PaperProofs.Common.Native
open PSTRWordBool PSTRWordVM

/-- A specification decoder only; neither source nor store calls pending. -/
def pending : Nat → List Bool → List Nat
  | _,[] => []
  | k,false::bits => pending (k+1) bits
  | k,true::bits => k::pending (k+1) bits

theorem pending_false (count k : Nat) : pending k (List.replicate count false)=[] := by
  induction count generalizing k with
  | zero => rfl
  | succ count ih => simpa only [List.replicate_succ,pending] using ih (k+1)
theorem pending_first (skipped k : Nat) (tail : List Bool) :
    pending k (List.replicate skipped false++true::tail)=
      (k+skipped)::pending (k+skipped+1) tail := by
  induction skipped generalizing k with
  | zero => simp [pending]
  | succ skipped ih =>
    simp only [List.replicate_succ,List.cons_append,pending,ih]
    have equal : k+1+skipped=k+(skipped+1) := by omega
    rw [equal]

theorem sequential_finRange (q : Nat) :
    (List.finRange q).map Fin.val=List.range' 0 q := by
  apply List.ext_getElem
  · simp
  · intro index first second
    simp [List.finRange]

theorem pending_filter {q : Nat} (values : List (Fin q)) (test : Fin q → Bool) (k : Nat)
    (sequential : values.map Fin.val=List.range' k values.length) :
    pending k (values.map test)=(values.filter test).map Fin.val := by
  induction values generalizing k with
  | nil => rfl
  | cons tool values ih =>
    simp only [List.map_cons,List.length_cons,List.range'_succ] at sequential
    obtain ⟨head,tail⟩:=List.cons.inj sequential
    have next:=ih (k+1) tail
    cases hit : test tool <;> simp [pending,hit,next,head]

def incidencePairs {q : Nat} (eligible remaining : Finset (Fin q)) : List (Bool×Bool) :=
  (List.finRange q).map (fun tool => (decide (tool∈eligible),decide (tool∈remaining)))
theorem incidence_length {q : Nat} (eligible remaining : Finset (Fin q)) :
    (incidencePairs eligible remaining).length=q := by simp [incidencePairs]
theorem actual_and_mask {q : Nat} (eligible remaining : Finset (Fin q)) :
    Bitwise.outputs false (incidencePairs eligible remaining)=
      (List.finRange q).map (fun tool => decide (tool∈eligible∩remaining)) := by
  simp [incidencePairs,Bitwise.outputs,Bitwise.combine,Finset.mem_inter,Bool.decide_and]
theorem original_candidates {q : Nat} (eligible remaining : Finset (Fin q)) :
    pending 0 (Bitwise.outputs false (incidencePairs eligible remaining))=
      (PaperProofs.Structure.genericRankCandidates q eligible remaining).map Fin.val := by
  rw [actual_and_mask]
  exact pending_filter (List.finRange q) _ 0 (by simpa using sequential_finRange q)

/-- Exact first candidate and suffix; no tie-reordering or rank answer input. -/
theorem outcome_pending (bg : Stack → List Bool) (bits : List Bool) (k : Nat)
    (final : ScanState) (outcome : Outcome bg bits k final) :
    (∃ skipped tail, bits=List.replicate skipped false++true::tail ∧
      pending k bits=(k+skipped)::pending (k+skipped+1) tail ∧
      k+skipped<k+bits.length ∧ (k+skipped+1)+tail.length=k+bits.length ∧
      final=state bg .found (false,false) tail (unary (k+skipped)) (unary (k+skipped+1)) []) ∨
    (pending k bits=[] ∧ final=state bg .empty (false,false) [] [] (unary (k+bits.length)) []) := by
  rcases outcome with ⟨skipped,tail,same,returned⟩ | ⟨all,returned⟩
  · have length : bits.length=skipped+1+tail.length := by
      simp only [same,List.length_append,List.length_replicate,List.length_cons];omega
    exact Or.inl ⟨skipped,tail,same,by rw [same,pending_first],by omega,by omega,returned⟩
  · exact Or.inr ⟨by rw [all];exact pending_false _ _,returned⟩

/-- This is the caller's actual extent invariant, not an extra original-input premise. -/
theorem outcome_extent (bg : Stack → List Bool) (bits : List Bool) (k q : Nat)
    (extent : k+bits.length=q) (final : ScanState) (outcome : Outcome bg bits k final) :
    (∃ tool tail, tool<q ∧ tool+1+tail.length=q ∧
      pending k bits=tool::pending (tool+1) tail ∧
      final=state bg .found (false,false) tail (unary tool) (unary (tool+1)) []) ∨
    (pending k bits=[] ∧ final=state bg .empty (false,false) [] [] (unary q) []) := by
  rcases outcome_pending bg bits k final outcome with ⟨skipped,tail,_same,tools,lt,next,returned⟩ | ⟨tools,returned⟩
  · exact Or.inl ⟨k+skipped,tail,by omega,by omega,tools,returned⟩
  · exact Or.inr ⟨tools,by simpa only [extent] using returned⟩

theorem source_writes (label : Label) : StackIso.WritesOnly Owned (source label) := by
  cases label with
  | inl label =>
    fin_cases label <;> simp [source,program,Bitwise.program,LabelMap.statement,StackIso.WritesOnly,Owned]
  | inr label =>
    cases label <;> simp [source,program,scanner,LabelMap.statement,StackIso.WritesOnly,Owned]

theorem frame_step (before after : State) (edge : TM2.step source before=some after)
    (point : Stack) (outside : ¬Owned point) : after.stk point=before.stk point := by
  cases before with
  | mk active memory slots =>
    cases active with
    | none => cases edge
    | some label =>
      have endpoint : TM2.stepAux (source label) memory slots=after := Option.some.inj edge
      rw [←endpoint]
      exact StackIso.nodes_frame Owned (source label) (source_writes label) memory slots point outside _
        (AuxWorkspace.endpoint_mem (source label) memory slots)

theorem actual_frame (start : State) (rest : List State)
    (chain : (start::rest).IsChain (fun a b => TM2.step source a=some b))
    (point : Stack) (outside : ¬Owned point) :
    ∀ current∈start::rest, current.stk point=start.stk point := by
  induction rest generalizing start with
  | nil => simp
  | cons next rest ih =>
    obtain ⟨edge,tail⟩:=List.isChain_cons_cons.mp chain
    have one:=frame_step start next edge point outside
    intro current member
    rcases List.mem_cons.mp member with same | later
    · subst current; rfl
    · exact (ih next tail current later).trans one

def withContext (C : Type*) : Label → TM2.Stmt Alphabet Label (C×Store) := ContextLift.machine source
def inContext {C : Type*} (context : C) : State → TM2.Cfg Alphabet Label (C×Store) :=
  ContextLift.configuration context

theorem context_support (C : Type*) :
    TM2.Supports (withContext C) (Finset.univ : Finset Label) :=
  ContextLift.machine_supports source _ (supports .halt .halt)

theorem initial_frame (bg : Stack → List Bool) (mem : Store) (pairs : List (Bool×Bool))
    (point : Stack) (outside : ¬Owned point) :
    (andEmbed (Bitwise.state bg 0 mem (pairs.map Prod.fst) (pairs.map Prod.snd) []
      (unary pairs.length) [])).stk point=bg point := by
  simp only [Owned,not_or] at outside
  obtain ⟨h3,h4,_h5,_h6,h7,h11,h12⟩:=outside
  exact Bitwise.cells_frame bg _ _ _ _ _ point h3 h4 h7 h11 h12

theorem context_clock {C : Type*} (context : C) (current : State) (bound : Nat)
    (bounded : ∀ point, (current.stk point).length≤bound) (label : Label) :
    ScannerStatement.clock (withContext C label) (context,current.var) current.stk≤10*(bound+3) := by
  have actions : ScannerClock.actions (withContext C label)≤5 := by
    simpa only [withContext,ContextLift.machine,ContextLift.statement_actions] using (source_counts label).1
  have pushes : AuxWorkspace.pushes (withContext C label)≤2 := by
    simpa only [withContext,ContextLift.machine,ContextLift.statement_pushes] using (source_counts label).2
  have clock:=ScannerClock.clock_bound (withContext C label) (context,current.var) current.stk bound bounded
  calc
    ScannerStatement.clock (withContext C label) (context,current.var) current.stk ≤
        2*ScannerClock.actions (withContext C label)*(bound+AuxWorkspace.pushes (withContext C label)+1) := clock
    _ ≤ 2*5*(bound+2+1) := Nat.mul_le_mul (Nat.mul_le_mul_left 2 actions) (by omega)
    _ = 10*(bound+3) := by ring

/-- Same actual first-call trace and finite C context, ready for a future actual caller. -/
theorem actual_first_context {C : Type*} (context : C) (bg : Stack → List Bool)
    (mem : Store) (pairs : List (Bool×Bool)) (cursor : bg 6=[]) :
    ∃ (trace : List (TM2.Cfg Alphabet Label (C×Store))) (final : TM2.Cfg Alphabet Label (C×Store)),
      trace.head?=some (inContext context (andEmbed (Bitwise.state bg 0 mem
        (pairs.map Prod.fst) (pairs.map Prod.snd) [] (unary pairs.length) []))) ∧
      trace.IsChain (fun a b => TM2.step (withContext C) a=some b) ∧ trace.getLast?=some final ∧
      trace.length≤12*((bg 5).length+pairs.length+1) ∧
      (∃ scanFinal, Outcome (scanBackground bg pairs.length) (Bitwise.outputs false pairs) 0 scanFinal ∧
        final=inContext context (scanEmbed scanFinal)) ∧
      (∀ current∈trace, current.var.1=context ∧
        (∀ point, (current.stk point).length≤2*mass bg+3*pairs.length+2) ∧
        ∀ point, ¬Owned point → current.stk point=bg point) ∧
      (∀ current∈trace, ∀ label, current.l=some label →
        ScannerClock.actions (withContext C label)≤5 ∧ AuxWorkspace.pushes (withContext C label)≤2) ∧
      (∀ current∈trace, ∀ label, current.l=some label →
        ∀ snapshot∈AuxWorkspace.nodes (withContext C label) current.var current.stk,
          snapshot.1.1=context ∧
          (∀ point, (snapshot.2 point).length≤2*mass bg+3*pairs.length+4) ∧
          ∀ point, ¬Owned point → snapshot.2 point=bg point) ∧
      charge (withContext C) trace≤
        (10*(2*mass bg+3*pairs.length+5)+1)*(12*((bg 5).length+pairs.length+1)) := by
  obtain ⟨base,baseFinal,head,chain,last,time,outcome,bounds⟩:=actual_first bg mem pairs cursor
  have frames : ∀ current∈base, ∀ point, ¬Owned point → current.stk point=bg point := by
    obtain ⟨rest,equal⟩:=List.head?_eq_some_iff.mp head
    rw [equal] at chain
    intro current member point outside
    rw [equal] at member
    exact (actual_frame _ rest chain point outside current member).trans
      (initial_frame bg mem pairs point outside)
  have lifted:=ContextLift.actual_path source context base _ _ head chain last
  refine ⟨base.map (inContext context),inContext context baseFinal,lifted.1,lifted.2.1,lifted.2.2.1,?_,?_,?_,?_,?_,?_⟩
  · simpa only [List.length_map] using time
  · obtain ⟨scanFinal,valid,returned⟩:=outcome
    exact ⟨scanFinal,valid,congrArg (inContext context) returned⟩
  · intro current member
    obtain ⟨old,inBase,same⟩:=List.mem_map.mp member
    subst current
    exact ⟨rfl,bounds old inBase,frames old inBase⟩
  · intro current _ label _
    simpa only [withContext,ContextLift.machine,ContextLift.statement_actions,ContextLift.statement_pushes]
      using source_counts label
  · intro current member label active snapshot node
    obtain ⟨old,inBase,same⟩:=List.mem_map.mp member
    subst current
    change snapshot∈AuxWorkspace.nodes (ContextLift.statement (source label)) (context,old.var) old.stk at node
    rw [ContextLift.nodes_configuration] at node
    obtain ⟨oldNode,inNodes,same⟩:=List.mem_map.mp node
    subst snapshot
    refine ⟨rfl,?_,?_⟩
    · intro point
      exact (AuxWorkspace.node_bound (source label) old.var old.stk (2*mass bg+3*pairs.length+2)
        (bounds old inBase) oldNode inNodes point).trans
          (by have pushes:=(source_counts label).2;omega)
    · intro point outside
      exact (StackIso.nodes_frame Owned (source label) (source_writes label)
        old.var old.stk point outside oldNode inNodes).trans (frames old inBase point outside)
  · apply (charge_le (withContext C) _ _ ?_).trans
    · exact Nat.mul_le_mul_left _ (by simpa only [List.length_map] using time)
    · intro current member label _active
      obtain ⟨old,inBase,same⟩:=List.mem_map.mp member
      subst current
      exact Nat.add_le_add_right (context_clock context old _ (bounds old inBase) label) 1
end RootB236.ControllerCandidate
