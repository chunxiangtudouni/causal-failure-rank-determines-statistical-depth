module

public import RootB234_RuntimeCounter_Round_Run_005

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootB234.RuntimeCounter.Round

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PSTRWordVM RationalControllerComputation PSTRTMIncrement009
open scoped BigOperators

variable {C : Type*}

instance (slot : Stack) : Decidable (Work slot) := by unfold Work; infer_instance

def writesDecidable {σ Λ : Type*} : (body : TM2.Stmt Alphabet Λ σ) → Decidable (StackIso.WritesOnly Work body)
  | .push slot _ tail | .pop slot _ tail => by
      change Decidable (Work slot ∧ StackIso.WritesOnly Work tail)
      letI := writesDecidable tail
      infer_instance
  | .peek _ _ tail | .load _ tail => writesDecidable tail
  | .branch _ yes no => by
      change Decidable (StackIso.WritesOnly Work yes ∧ StackIso.WritesOnly Work no)
      letI := writesDecidable yes
      letI := writesDecidable no
      infer_instance
  | .goto _ | .halt => isTrue trivial

local instance (body : Statement C) : Decidable (StackIso.WritesOnly Work body) := writesDecidable body

theorem program_writes (point : Label) : StackIso.WritesOnly Work (program (C := C) point) := by
  fin_cases point <;> exact of_decide_eq_true rfl

theorem program_actions_context (point : Label) : ScannerClock.actions (program (C := C) point)≤4 := by
  simpa only [program,ContextLift.machine,ContextLift.statement_actions] using base_actions point

theorem program_pushes_context (point : Label) : AuxWorkspace.pushes (program (C := C) point)≤2 := by
  simpa only [program,ContextLift.machine,ContextLift.statement_pushes] using base_pushes point

private theorem supports_statement (body : Statement C) : TM2.SupportsStmt support body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto _ => intro _; exact Finset.mem_univ _
  | halt => trivial

theorem supports : TM2.Supports (program (C := C)) support :=
  ⟨Finset.mem_univ _,fun _ _ => supports_statement _⟩

theorem nodes_context (point : Label) (memory : Store C) (slots : Stack → List Bool)
    (node : AuxWorkspace.Snapshot (Γ := Alphabet) (σ := Store C))
    (member : node∈AuxWorkspace.nodes (program point) memory slots) : node.1.1=memory.1 := by
  rcases memory with ⟨context,registers⟩
  change node∈AuxWorkspace.nodes (ContextLift.statement (baseProgram point)) (context,registers) slots at member
  rw [ContextLift.nodes_configuration] at member
  obtain ⟨old,_present,same⟩ := List.mem_map.mp member
  subst node
  rfl

theorem step_preserves (before after : State C) (edge : TM2.step program before=some after) :
    after.var.1=before.var.1 ∧ ∀ slot,¬Work slot→after.stk slot=before.stk slot := by
  cases before with
  | mk position memory slots =>
    cases position with
    | none => cases edge
    | some point =>
      have equal : after=TM2.stepAux (program point) memory slots := (Option.some.inj edge).symm
      subst after
      refine ⟨nodes_context point memory slots _ (AuxWorkspace.endpoint_mem _ _ _),?_⟩
      intro slot untouched
      exact StackIso.nodes_frame Work _ (program_writes point) memory slots slot untouched
        _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_preserves (trace : List (State C)) (before : State C) (frame : Stack → List Bool)
    (first : trace.head?=some before) (chain : trace.IsChain (fun a b => TM2.step program a=some b))
    (framed : ∀ slot,¬Work slot→before.stk slot=frame slot) :
    ∀ current∈trace,current.var.1=before.var.1 ∧ ∀ slot,¬Work slot→current.stk slot=frame slot := by
  apply chain.induction (fun current => current.var.1=before.var.1 ∧
    ∀ slot,¬Work slot→current.stk slot=frame slot) trace
  · intro previous next edge valid
    have step := step_preserves previous next edge
    exact ⟨step.1.trans valid.1,fun slot untouched => (step.2 slot untouched).trans (valid.2 slot untouched)⟩
  · intro nonempty
    have head : trace.head nonempty=before := by simpa [List.head?_eq_some_head nonempty] using first
    rw [head]
    exact ⟨rfl,framed⟩

theorem occupied_bound (slots : Stack → List Bool) (bound : Nat)
    (bounded : ∀ slot,(slots slot).length≤bound) : occupied slots≤16*bound := by
  calc
    occupied slots≤∑ _slot : Stack,bound := Finset.sum_le_sum (fun slot _ => bounded slot)
    _=16*bound := by simp

private theorem no_early_halt (point : Label) (atPort : program (C := C) point=.halt)
    (trace : List (State C)) (final : State C)
    (chain : trace.IsChain (fun a b => TM2.step program a=some b))
    (last : trace.getLast?=some final) (active : final.l≠none) :
    ∀ current∈trace.dropLast,current.l≠some point := by
  induction trace with
  | nil => simp
  | cons before rest ih =>
    cases rest with
    | nil => simp
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      intro current present
      rw [List.dropLast_cons_cons] at present
      rcases List.mem_cons.mp present with same | later
      · subst current
        intro selected
        have stopped : TM2.step program before=some (⟨none,before.var,before.stk⟩ : State C) := by
          cases before with
          | mk label memory slots =>
            change label=some point at selected
            subst label
            change some (TM2.stepAux (program point) memory slots)=_
            rw [atPort]; rfl
        rw [stopped] at edge
        have nextStopped := (Option.some.inj edge).symm
        cases rest with
        | nil =>
          have nextFinal : next=final := Option.some.inj last
          exact active (by rw [←nextFinal,nextStopped])
        | cons after rest =>
          have impossible := (List.isChain_cons_cons.mp tailChain).1
          rw [nextStopped] at impossible
          cases impossible
      · exact ih tailChain last current later

structure Facts (source : Label → Statement C) (frame : Stack → List Bool) (memory : Store C)
    (digits : List Bool) (trace : List (State C)) (final : State C) : Prop where
  first : trace.head?=some (entry frame memory digits)
  chain : trace.IsChain (fun a b => TM2.step source a=some b)
  last : trace.getLast?=some final
  port : final.l=some (if valueDigits digits=0 then 7 else 8)
  context : final.var.1=memory.1
  contents : final.stk=cells frame (Raw.packet (Raw.outputDigits digits)) [false] []
  decoded : decoded final.var.2=(Raw.final digits).q
  time : trace.length≤256*scale frame digits
  proper : ∀ current∈trace.dropLast,current.l≠some 7 ∧ current.l≠some 8
  boundary : ∀ current∈trace,
    current.var.1=memory.1 ∧ (∀ slot,(current.stk slot).length≤513*scale frame digits) ∧
    occupied current.stk≤8208*scale frame digits ∧ ∀ slot,¬Work slot→current.stk slot=frame slot
  internal : ∀ current∈trace.dropLast,∀ point,current.l=some point→
    (∀ node∈AuxWorkspace.nodes (source point) current.var current.stk,
      node.1.1=memory.1 ∧ (∀ slot,(node.2 slot).length≤515*scale frame digits) ∧
      occupied node.2≤8240*scale frame digits ∧ ∀ slot,¬Work slot→node.2 slot=frame slot) ∧
    ScannerStatement.clock (source point) current.var current.stk≤4128*scale frame digits

theorem actual_polynomial (frame : Stack → List Bool) (memory : Store C) (digits : List Bool) :
    ∃ trace final,Facts program frame memory digits trace final := by
  obtain ⟨trace,final,first,chain,last,port,context,contents,decodedFinal,time⟩ := actual_run frame memory digits
  have positive := scale_pos frame digits
  have resources := trace_preserves trace (entry frame memory digits) frame first chain
    (fun slot untouched => cells_frame frame _ _ _ slot untouched)
  have initialBound : ∀ slot,((entry frame memory digits).stk slot).length≤scale frame digits := by
    intro slot
    exact (point_mass _ slot).trans (Nat.le_succ _)
  have slots := trace_slot_bound program program_pushes_context trace (entry frame memory digits) _ first chain initialBound
  have bounded : ∀ current∈trace,∀ slot,(current.stk slot).length≤513*scale frame digits := by
    intro current member slot
    have bound := slots current member slot
    omega
  have active : final.l≠none := by rw [port]; simp
  have proper7 := no_early_halt 7 rfl trace final chain last active
  have proper8 := no_early_halt 8 rfl trace final chain last active
  refine ⟨trace,final,⟨first,chain,last,port,context,contents,decodedFinal,time,
    fun current member => ⟨proper7 current member,proper8 current member⟩,?_,?_⟩⟩
  · intro current member
    refine ⟨(resources current member).1,bounded current member,?_,(resources current member).2⟩
    have bound := occupied_bound current.stk _ (bounded current member)
    omega
  · intro current member point _selected
    have present := List.mem_of_mem_dropLast member
    have currentBound := bounded current present
    refine ⟨?_,?_⟩
    · intro node internal
      have nodeBound : ∀ slot,(node.2 slot).length≤515*scale frame digits := by
        intro slot
        have bound := (AuxWorkspace.node_bound (program point) current.var current.stk _
          currentBound node internal slot).trans
            (Nat.add_le_add_left (program_pushes_context point) (513*scale frame digits))
        omega
      refine ⟨(nodes_context point current.var current.stk node internal).trans (resources current present).1,
        nodeBound,?_,?_⟩
      · have bound := occupied_bound node.2 _ nodeBound
        omega
      · intro slot untouched
        exact (StackIso.nodes_frame Work _ (program_writes point) current.var current.stk slot untouched
          node internal).trans ((resources current present).2 slot untouched)
    · have clock := ScannerClock.clock_bound (program point) current.var current.stk _ currentBound
      have cap := clock.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions_context point))
        (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes_context point) (513*scale frame digits)) 1))
      omega

end RootB234.RuntimeCounter.Round
