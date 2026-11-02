module

public import RootB234_PrepExponent_NatToRatRun006

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.NatToRat
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
variable {C : Type*}

def Work (slot : Stack) : Prop := slot=3 ∨ slot=4 ∨ slot=8 ∨ slot=15
instance (slot : Stack) : Decidable (Work slot) := by unfold Work;infer_instance

def writesDecidable : (body : Statement C) → Decidable (StackIso.WritesOnly Work body)
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

theorem program_writes (point : Label) : StackIso.WritesOnly Work (program (C:=C) .halt point) := by
  fin_cases point <;> exact of_decide_eq_true rfl

theorem program_actions (point : Label) : ScannerClock.actions (program (C:=C) .halt point) ≤ 4 := by
  fin_cases point <;> exact of_decide_eq_true rfl

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C:=C) .halt point) ≤ 4 := by
  fin_cases point <;> exact of_decide_eq_true rfl

theorem program_readonly (point : Label) :
    B23_4_RatWordPrep.RawGetter.Readonly (fun memory : Store C => memory.1) (program .halt point) := by
  fin_cases point
  all_goals
    dsimp [program,copyLabel,reverseLabel,LabelMap.statement,StackIso.statement,
      B23_4_RatWordPrep.WholeCopy.program,B23_4_RatWordPrep.WholeCopy.capture,
      Cells.Public.reverse3To2,Cells.program,Cells.body,Cells.entry,Cells.moving,Cells.roles,Cells.rawProgram,
      RatPacketTransport.program,RatPacketTransport.keepSource,
      B23_4_RatWordPrep.RawGetter.Readonly,RatDrop.capture]
    repeat' constructor
    all_goals (intros;rfl)

theorem step_context (before after : State C) (edge : TM2.step (program .halt) before=some after) :
    after.var.1=before.var.1 := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact B23_4_RatWordPrep.RawGetter.nodes_readonly (fun v : Store C => v.1) _ (program_readonly point) memory contents
        _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_context (trace : List (State C)) (before : State C) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program .halt) a=some b)) :
    ∀ current∈trace,current.var.1=before.var.1 := by
  induction trace generalizing before with
  | nil => simp
  | cons start rest ih =>
    have same : start=before := Option.some.inj first
    subst start
    cases rest with
    | nil =>
      intro current member
      have same := List.mem_singleton.mp member
      subst current
      rfl
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      intro current member
      rcases List.mem_cons.mp member with rfl | later
      · rfl
      · exact (ih next rfl tailChain current later).trans (step_context before next edge)


theorem step_resources (before after : State C) (bound : Nat)
    (edge : TM2.step (program .halt) before=some after)
    (bounded : ∀ slot,(before.stk slot).length ≤ bound) :
    (∀ slot,(after.stk slot).length ≤ bound+4) ∧
      ∀ slot,¬Work slot→after.stk slot=before.stk slot := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact ⟨fun slot => (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
        (Nat.add_le_add_left (program_pushes point) bound),
        fun slot untouched => StackIso.nodes_frame _ _ (program_writes point) memory contents slot untouched
          _ (AuxWorkspace.endpoint_mem _ _ _)⟩

theorem trace_resources (trace : List (State C)) (before : State C) (background : RatInput.Stack → List Bool)
    (bound : Nat) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program .halt) a=some b))
    (bounded : ∀ slot,(before.stk slot).length ≤ bound)
    (frame : ∀ slot,¬Work slot→before.stk slot=background slot) :
    ∀ current∈trace,(∀ slot,(current.stk slot).length ≤ bound+4*trace.length) ∧
      ∀ slot,¬Work slot→current.stk slot=background slot := by
  induction trace generalizing before bound with
  | nil => simp
  | cons firstState rest ih =>
    have same : firstState=before := Option.some.inj first
    subst firstState
    cases rest with
    | nil =>
      intro current member
      have same := List.mem_singleton.mp member
      subst current
      exact ⟨fun slot => (bounded slot).trans (by simp),frame⟩
    | cons next rest =>
      obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
      have step := step_resources before next bound edge bounded
      intro current member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨fun slot => (bounded slot).trans (Nat.le_add_right _ _),frame⟩
      · have tail := ih next (bound+4) rfl tailChain step.1
          (fun slot untouched => (step.2 slot untouched).trans (frame slot untouched)) current later
        refine ⟨?_,tail.2⟩
        intro slot
        have h := tail.1 slot
        simp only [List.length_cons] at h ⊢
        omega

theorem internal_resources (current : State C) (point : Label) (bound : Nat)
    (bounded : ∀ slot,(current.stk slot).length ≤ bound) :
    (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
      node.1.1=current.var.1 ∧ (∀ slot,(node.2 slot).length ≤ bound+4) ∧
        ∀ slot,¬Work slot→node.2 slot=current.stk slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk ≤ 8*(bound+5) := by
  refine ⟨?_,?_⟩
  · intro node member
    exact ⟨B23_4_RatWordPrep.RawGetter.nodes_readonly (fun v : Store C => v.1) _ (program_readonly point) current.var current.stk node member,
      fun slot => (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
        (Nat.add_le_add_left (program_pushes point) bound),
      fun slot untouched => StackIso.nodes_frame _ _ (program_writes point) current.var current.stk slot untouched node member⟩
  · exact (ScannerClock.clock_bound (program .halt point) current.var current.stk bound bounded).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions point))
        (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes point) bound) 1))



def initialMass (background : Stack → List Bool) (number : Nat) (tail : List Bool) : Nat :=
  RatInput.occupied (bank background (B23_4_RatWordPrep.NatField.packet number []) [] [] tail)

def scale (background : Stack → List Bool) (number : Nat) (tail : List Bool) : Nat :=
  initialMass background number tail+1

def statementClock (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (program .halt point) current.var current.stk

def traceClockSum (run : List (State C)) : Nat := (run.dropLast.map statementClock).sum

structure Facts (background : Stack → List Bool) (memory : Store C) (number : Nat)
    (tail : List Bool) (run : List (State C)) : Prop where
  first : run.head?=some (state background .prepare memory (B23_4_RatWordPrep.NatField.packet number []) [] [] tail)
  chain : run.IsChain (fun a b => TM2.step (program .halt) a=some b)
  last : run.getLast?=some (state background .done (memory.1,false,false)
    (B23_4_RatWordPrep.NatField.packet number []) [] [] (RatInput.Encoder.packet (number : Rat) tail))
  time : run.length ≤ 13*scale background number tail
  boundaries : ∀ current∈run,current.var.1=memory.1 ∧
    (∀ slot,(current.stk slot).length ≤ 53*scale background number tail) ∧
    ∀ slot,¬Work slot→current.stk slot=background slot
  proper : ∀ current∈run.dropLast,current.l≠some .done ∧
    ∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
        node.1.1=memory.1 ∧ (∀ slot,(node.2 slot).length ≤ 57*scale background number tail) ∧
        ∀ slot,¬Work slot→node.2 slot=background slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk ≤ 464*scale background number tail

theorem actual_bounded (background : Stack → List Bool) (memory : Store C) (number : Nat) (tail : List Bool) :
    ∃ run,Facts background memory number tail run := by
  obtain ⟨run,first,chain,last,count⟩ := actual .halt background memory number tail
  let before := state background .prepare memory (B23_4_RatWordPrep.NatField.packet number []) [] [] tail
  let M := initialMass background number tail
  let S := scale background number tail
  have packetBound := RatInput.Encoder.point_mass before.stk 8
  change (B23_4_RatWordPrep.NatField.packet number []).length ≤ M at packetBound
  have time : run.length ≤ 13*S := by dsimp only [S,scale,M] at *;omega
  have positive : 1 ≤ S := by dsimp only [S,scale];omega
  have frames : ∀ slot,¬Work slot→before.stk slot=background slot := by
    intro slot untouched
    simp only [Work,not_or] at untouched
    simp only [before,state,bank,untouched.1,untouched.2.1,untouched.2.2.1,untouched.2.2.2,ite_false]
  have rawBounds := trace_resources run before background M first chain
    (RatInput.Encoder.point_mass before.stk) frames
  have ctx := trace_context run before first chain
  have bounds : ∀ current∈run,∀ slot,(current.stk slot).length ≤ 53*S := by
    intro current member slot
    have bound := (rawBounds current member).1 slot
    have mass : M ≤ S := by dsimp only [M,S,scale];omega
    omega
  have proper := NativeMulLink.no_early_halt_port (program (C:=C) .halt) .done rfl run
    (state background .done (memory.1,false,false) (B23_4_RatWordPrep.NatField.packet number []) [] []
      (RatInput.Encoder.packet (number : Rat) tail)) chain last rfl
  refine ⟨run,⟨first,chain,last,time,?_,?_⟩⟩
  · intro current member
    exact ⟨ctx current member,bounds current member,(rawBounds current member).2⟩
  · intro current member
    refine ⟨proper current member,?_⟩
    intro point selected
    have boundaryMember := List.mem_of_mem_dropLast member
    have internal := internal_resources current point (53*S) (bounds current boundaryMember)
    refine ⟨?_,internal.2.trans (by omega)⟩
    intro node inside
    refine ⟨((internal.1 node inside).1).trans (ctx current boundaryMember),?_,?_⟩
    · intro slot
      exact ((internal.1 node inside).2.1 slot).trans (by omega)
    · intro slot untouched
      exact ((internal.1 node inside).2.2 slot untouched).trans ((rawBounds current boundaryMember).2 slot untouched)

theorem traceClockSum_le {background : Stack → List Bool} {memory : Store C} {number : Nat}
    {tail : List Bool} {run : List (State C)} (facts : Facts background memory number tail run) :
    traceClockSum run ≤ 6032*(scale background number tail)^2 := by
  let S := scale background number tail
  have terms : ∀ n∈run.dropLast.map statementClock,n ≤ 464*S := by
    intro n member
    obtain ⟨current,present,rfl⟩ := List.mem_map.mp member
    cases selected : current.l with
    | none => simp only [statementClock,selected,Nat.zero_le]
    | some point =>
      simp only [statementClock,selected]
      exact ((facts.proper current present).2 point selected).2
  have total : traceClockSum run ≤ run.dropLast.length*(464*S) := by
    simpa only [traceClockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (run.dropLast.map statementClock) (464*S) terms
  have count : run.dropLast.length ≤ 13*S := by
    rw [List.length_dropLast]
    exact (Nat.sub_le run.length 1).trans facts.time
  exact total.trans ((Nat.mul_le_mul_right _ count).trans_eq (by ring))

theorem chargedCost_le {background : Stack → List Bool} {memory : Store C} {number : Nat}
    {tail : List Bool} {run : List (State C)} (facts : Facts background memory number tail run) :
    run.length+traceClockSum run ≤ 6045*(scale background number tail)^2 := by
  have time := facts.time
  have clocks := traceClockSum_le facts
  have positive : 1 ≤ scale background number tail := by simp [scale]
  have square : scale background number tail ≤ (scale background number tail)^2 := by
    simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left (scale background number tail) positive
  omega

end RootB234.PrepExponent.NatToRat
