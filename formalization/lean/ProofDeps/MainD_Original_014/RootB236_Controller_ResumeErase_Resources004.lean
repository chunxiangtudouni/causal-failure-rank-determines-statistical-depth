module
public import RootB236_Controller_ResumeErase_Run003
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

theorem program_readonly (point : Label) :
    B23_4_RatWordPrep.RawGetter.Readonly (fun v : Store C => v.1) (source point) := by
  cases point with
  | clear => exact ⟨fun _ _ => rfl,trivial,trivial⟩
  | body point =>
    rw [body_closed,SelectErase.readonly_labelMap]
    exact SelectErase.program_readonly point

def writesDecidable : (body : Statement C) → Decidable (StackIso.WritesOnly Work body)
  | .push slot _ tail | .pop slot _ tail => by
      change Decidable (Work slot ∧ StackIso.WritesOnly Work tail)
      letI:=writesDecidable tail
      infer_instance
  | .peek _ _ tail | .load _ tail => writesDecidable tail
  | .branch _ yes no => by
      change Decidable (StackIso.WritesOnly Work yes ∧ StackIso.WritesOnly Work no)
      letI:=writesDecidable yes
      letI:=writesDecidable no
      infer_instance
  | .goto _ | .halt => isTrue trivial
local instance (body : Statement C) : Decidable (StackIso.WritesOnly Work body) := writesDecidable body

theorem program_writes (point : Label) : StackIso.WritesOnly Work (source (C:=C) point) := by
  cases point with
  | clear => exact of_decide_eq_true rfl
  | body point =>
    rw [body_closed,StackIso.writes_labelMap]
    exact SelectErase.program_writes point

theorem program_actions (point : Label) : ScannerClock.actions (source (C:=C) point)≤16 := by
  cases point with
  | clear => exact of_decide_eq_true rfl
  | body point => rw [body_closed,LabelMap.statement_actions];exact SelectErase.program_actions point

theorem program_pushes (point : Label) : AuxWorkspace.pushes (source (C:=C) point)≤16 := by
  cases point with
  | clear => exact of_decide_eq_true rfl
  | body point => rw [body_closed,LabelMap.statement_pushes];exact SelectErase.program_pushes point

theorem step_context (before after : State C)
    (edge : TM2.step source before=some after) : after.var.1=before.var.1 := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (source point) memory contents := (Option.some.inj edge).symm
      subst after
      exact B23_4_RatWordPrep.RawGetter.nodes_readonly (fun v : Store C => v.1) _
        (program_readonly point) memory contents _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_context (trace : List (State C)) (before : State C)
    (first : trace.head?=some before) (chain : trace.IsChain (fun a b => TM2.step source a=some b)) :
    ∀ current∈trace,current.var.1=before.var.1 := by
  induction trace generalizing before with
  | nil => simp
  | cons start rest ih =>
    have same : start=before := Option.some.inj first
    subst start
    cases rest with
    | nil =>
      intro current member
      have same:=List.mem_singleton.mp member
      subst current;rfl
    | cons next rest =>
      obtain ⟨edge,later⟩:=List.isChain_cons_cons.mp chain
      intro current member
      rcases List.mem_cons.mp member with rfl | laterMember
      · rfl
      · exact (ih next rfl later current laterMember).trans (step_context before next edge)

theorem step_resources (before after : State C) (bound : Nat)
    (edge : TM2.step source before=some after)
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    (∀ slot,(after.stk slot).length≤bound+16) ∧ ∀ slot,¬Work slot→after.stk slot=before.stk slot := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (source point) memory contents := (Option.some.inj edge).symm
      subst after
      exact ⟨fun slot => (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
          (Nat.add_le_add_left (program_pushes point) bound),
        fun slot untouched => StackIso.nodes_frame _ _ (program_writes point) memory contents slot untouched
          _ (AuxWorkspace.endpoint_mem _ _ _)⟩

theorem trace_resources (trace : List (State C)) (before : State C)
    (background : Stack → List Bool) (bound : Nat) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step source a=some b))
    (bounded : ∀ slot,(before.stk slot).length≤bound)
    (frame : ∀ slot,¬Work slot→before.stk slot=background slot) :
    ∀ current∈trace,(∀ slot,(current.stk slot).length≤bound+16*trace.length) ∧
      ∀ slot,¬Work slot→current.stk slot=background slot := by
  induction trace generalizing before bound with
  | nil => simp
  | cons start rest ih =>
    have same : start=before := Option.some.inj first
    subst start
    cases rest with
    | nil =>
      intro current member
      have same:=List.mem_singleton.mp member
      subst current
      exact ⟨fun slot => (bounded slot).trans (by simp),frame⟩
    | cons next rest =>
      obtain ⟨edge,later⟩:=List.isChain_cons_cons.mp chain
      have step:=step_resources before next bound edge bounded
      intro current member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨fun slot => (bounded slot).trans (Nat.le_add_right _ _),frame⟩
      · have tail:=ih next (bound+16) rfl later step.1
          (fun slot untouched => (step.2 slot untouched).trans (frame slot untouched)) current member
        refine ⟨?_,tail.2⟩
        intro slot
        have h:=tail.1 slot
        simp only [List.length_cons] at h ⊢
        omega

theorem internal_resources (current : State C) (point : Label) (bound : Nat)
    (bounded : ∀ slot,(current.stk slot).length≤bound) :
    (∀ node∈AuxWorkspace.nodes (source point) current.var current.stk,
      node.1.1=current.var.1 ∧ (∀ slot,(node.2 slot).length≤bound+16) ∧
        ∀ slot,¬Work slot→node.2 slot=current.stk slot) ∧
      ScannerStatement.clock (source point) current.var current.stk≤32*(bound+17) := by
  refine ⟨?_,?_⟩
  · intro node member
    exact ⟨B23_4_RatWordPrep.RawGetter.nodes_readonly (fun v : Store C => v.1) _
        (program_readonly point) current.var current.stk node member,
      fun slot => (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
        (Nat.add_le_add_left (program_pushes point) bound),
      fun slot untouched => StackIso.nodes_frame _ _ (program_writes point) current.var current.stk slot untouched node member⟩
  · exact (ScannerClock.clock_bound (source point) current.var current.stk bound bounded).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions point))
        (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes point) bound) 1))



def inputMass (bg : Stack → List Bool) (bits parent old4 old5 : List Bool) (k : Nat) : Nat :=
  RatInput.occupied (bank bg bits old4 old5 (ControllerCandidate.unary k) [] parent.reverse
    (ControllerCandidate.unary parent.length) [])
def inputScale (bg : Stack → List Bool) (bits parent old4 old5 : List Bool) (k : Nat) : Nat :=
  inputMass bg bits parent old4 old5 k+parent.length+1
def workspace (bg : Stack → List Bool) (bits parent old4 old5 : List Bool) (k : Nat) : Nat :=
  inputMass bg bits parent old4 old5 k+1024*inputScale bg bits parent old4 old5 k
def coefficient : Nat := 65536
theorem workspace_original (bg : Stack → List Bool) (bits parent old4 old5 : List Bool) (k : Nat) :
    workspace bg bits parent old4 old5 k=1025*inputMass bg bits parent old4 old5 k+1024*parent.length+1024 := by
  unfold workspace inputScale;ring
def statementClock (current : State C) : Nat := match current.l with
  | none => 0
  | some point => ScannerStatement.clock (source point) current.var current.stk
def traceClockSum (trace : List (State C)) : Nat := (trace.dropLast.map statementClock).sum
def chargedCost (trace : List (State C)) : Nat := trace.length+traceClockSum trace

structure Facts (bg : Stack → List Bool) (memory : Store C) (bits parent old4 old5 : List Bool) (k : Nat)
    (trace : List (State C)) (final : State C) : Prop where
  first : trace.head?=some (initial bg memory bits parent old4 old5 k)
  chain : trace.IsChain (fun a b => TM2.step source a=some b)
  last : trace.getLast?=some final
  outcome : Outcome bg memory.1 bits parent k final
  count : trace.length≤32*(old4.length+old5.length+parent.length+1)
  time : trace.length≤64*inputScale bg bits parent old4 old5 k
  boundaries : ∀ current∈trace,current.var.1=memory.1 ∧
    (∀ slot,(current.stk slot).length≤workspace bg bits parent old4 old5 k) ∧
    RatInput.occupied current.stk≤16*workspace bg bits parent old4 old5 k ∧
    ∀ slot,¬Work slot→current.stk slot=bg slot
  proper : ∀ current∈trace.dropLast,(current.l≠some foundPort ∧ current.l≠some emptyPort) ∧
    ∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (source point) current.var current.stk,
        node.1.1=memory.1 ∧
        (∀ slot,(node.2 slot).length≤workspace bg bits parent old4 old5 k+16) ∧
        RatInput.occupied node.2≤16*(workspace bg bits parent old4 old5 k+16) ∧
        ∀ slot,¬Work slot→node.2 slot=bg slot) ∧
      ScannerStatement.clock (source point) current.var current.stk≤32*(workspace bg bits parent old4 old5 k+17)

theorem actual_bounded (bg : Stack → List Bool) (memory : Store C) (bits parent old4 old5 : List Bool) (k : Nat)
    (extent : k+bits.length=parent.length) :
    ∃ trace final,Facts bg memory bits parent old4 old5 k trace final := by
  obtain ⟨trace,final,first,chain,last,count,outcome⟩:=actual bg memory bits parent old4 old5 k extent
  let before:=initial bg memory bits parent old4 old5 k
  let M:=inputMass bg bits parent old4 old5 k
  let K:=inputScale bg bits parent old4 old5 k
  let W:=workspace bg bits parent old4 old5 k
  have room4 : old4.length≤M := RatInput.Encoder.point_mass before.stk 4
  have room5 : old5.length≤M := RatInput.Encoder.point_mass before.stk 5
  have short : trace.length≤64*K := by dsimp only [K,inputScale];omega
  have frames : ∀ slot,¬Work slot→before.stk slot=bg slot := by
    intro slot untouched
    have a : slot≠3 := by intro same;subst slot;exact untouched (by decide)
    have b : slot≠4 := by intro same;subst slot;exact untouched (by decide)
    have c : slot≠5 := by intro same;subst slot;exact untouched (by decide)
    have d : slot≠6 := by intro same;subst slot;exact untouched (by decide)
    have e : slot≠7 := by intro same;subst slot;exact untouched (by decide)
    have f : slot≠8 := by intro same;subst slot;exact untouched (by decide)
    have g : slot≠11 := by intro same;subst slot;exact untouched (by decide)
    have h : slot≠12 := by intro same;subst slot;exact untouched (by decide)
    simp only [before,initial,state,bank,SelectErase.bank,a,b,c,d,e,f,g,h,ite_false]
  have bounds:=trace_resources trace before bg M first chain (RatInput.Encoder.point_mass before.stk) frames
  have contexts:=trace_context trace before first chain
  have room : M+16*trace.length≤W := by dsimp only [W,workspace];omega
  have bounded : ∀ current∈trace,∀ slot,(current.stk slot).length≤W := by
    intro current member slot
    exact ((bounds current member).1 slot).trans room
  have active : final.l≠none := by
    rcases outcome.active with h | h <;> rw [h] <;> simp
  have nf:=ControllerCandidate.no_early_halt_port source foundPort rfl trace final chain last active
  have ne:=ControllerCandidate.no_early_halt_port source emptyPort rfl trace final chain last active
  refine ⟨trace,final,⟨first,chain,last,outcome,count,short,?_,?_⟩⟩
  · intro current member
    exact ⟨contexts current member,bounded current member,
      RatInput.Encoder.occupied_bound current.stk W (bounded current member),(bounds current member).2⟩
  · intro current member
    refine ⟨⟨nf current member,ne current member⟩,?_⟩
    intro point selected
    have inside:=internal_resources current point W (bounded current (List.mem_of_mem_dropLast member))
    refine ⟨?_,inside.2⟩
    intro node present
    exact ⟨((inside.1 node present).1).trans (contexts current (List.mem_of_mem_dropLast member)),
      (inside.1 node present).2.1,
      RatInput.Encoder.occupied_bound node.2 (W+16) (inside.1 node present).2.1,
      fun slot untouched => ((inside.1 node present).2.2 slot untouched).trans
        ((bounds current (List.mem_of_mem_dropLast member)).2 slot untouched)⟩

theorem envelope (bg : Stack → List Bool) (bits parent old4 old5 : List Bool) (k : Nat) :
    let K:=inputScale bg bits parent old4 old5 k
    64*K≤coefficient*K ∧ 16*workspace bg bits parent old4 old5 k≤coefficient*K ∧
      16*(workspace bg bits parent old4 old5 k+16)≤coefficient*K ∧
      32*(workspace bg bits parent old4 old5 k+17)≤coefficient*K := by
  dsimp only [inputScale,workspace,coefficient]
  omega

theorem Facts.clock_sum {bg : Stack → List Bool} {memory : Store C} {bits parent old4 old5 : List Bool} {k : Nat}
    {trace : List (State C)} {final : State C} (facts : Facts bg memory bits parent old4 old5 k trace final) :
    traceClockSum trace≤coefficient^2*(inputScale bg bits parent old4 old5 k)^2 := by
  let cap:=coefficient*inputScale bg bits parent old4 old5 k
  have term : ∀ value∈trace.dropLast.map statementClock,value≤cap := by
    intro value member
    obtain ⟨current,present,rfl⟩:=List.mem_map.mp member
    cases selected : current.l with
    | none => simp only [statementClock,selected,Nat.zero_le]
    | some point =>
      simp only [statementClock,selected]
      exact (((facts.proper current present).2 point selected).2).trans (envelope bg bits parent old4 old5 k).2.2.2
  have sum : traceClockSum trace≤trace.dropLast.length*cap := by
    simpa only [traceClockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (trace.dropLast.map statementClock) cap term
  have count : trace.dropLast.length≤cap := by
    rw [List.length_dropLast]
    exact (Nat.sub_le trace.length 1).trans (facts.time.trans (envelope bg bits parent old4 old5 k).1)
  exact (sum.trans (Nat.mul_le_mul_right cap count)).trans_eq (by dsimp only [cap];ring)

theorem Facts.charged {bg : Stack → List Bool} {memory : Store C} {bits parent old4 old5 : List Bool} {k : Nat}
    {trace : List (State C)} {final : State C} (facts : Facts bg memory bits parent old4 old5 k trace final) :
    chargedCost trace≤(coefficient^2+coefficient)*(inputScale bg bits parent old4 old5 k)^2 := by
  have positive : 1 ≤ inputScale bg bits parent old4 old5 k := by unfold inputScale;omega
  have square : inputScale bg bits parent old4 old5 k≤(inputScale bg bits parent old4 old5 k)^2 := by nlinarith
  have time:=facts.time.trans (envelope bg bits parent old4 old5 k).1
  have sum:=facts.clock_sum
  unfold chargedCost
  nlinarith [Nat.mul_le_mul_left coefficient square]
end RootB236.Controller.ResumeErase
