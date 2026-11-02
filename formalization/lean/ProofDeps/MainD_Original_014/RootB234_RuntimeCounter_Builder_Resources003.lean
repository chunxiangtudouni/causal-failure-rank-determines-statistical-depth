module
public import RootB234_RuntimeCounter_Builder_Run002

/-! Same-trace boundary, internal-node, physical scanner and aggregate
charge bounds. Input scale is the actual occupied initial stack bank. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.RuntimeCounter.Builder
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM
variable {C : Type*}

def Work (slot : Stack) : Prop := slot=4 ∨ slot=8 ∨ slot=10 ∨ slot=11
instance (slot : Stack) : Decidable (Work slot) := by unfold Work;infer_instance

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

theorem program_writes (doubled : Bool) (point : Label) :
    StackIso.WritesOnly Work (program (C:=C) doubled .halt point) := by
  fin_cases point <;> cases doubled <;> exact of_decide_eq_true rfl

theorem program_actions (doubled : Bool) (point : Label) :
    ScannerClock.actions (program (C:=C) doubled .halt point)≤16 := by
  fin_cases point <;> cases doubled <;> exact of_decide_eq_true rfl

theorem program_pushes (doubled : Bool) (point : Label) :
    AuxWorkspace.pushes (program (C:=C) doubled .halt point)≤16 := by
  fin_cases point <;> cases doubled <;> exact of_decide_eq_true rfl

theorem program_readonly (doubled : Bool) (point : Label) :
    B23_4_RatWordPrep.RawGetter.Readonly (fun memory : Store C => memory.1) (program doubled .halt point) := by
  fin_cases point <;> cases doubled
  all_goals
    dsimp [program,StackIso.statement,RatDrop.headerBody,RatDrop.fieldBody,RatDrop.put,eraseBody,padBody,
      B23_4_RatWordPrep.RawGetter.Readonly,RatDrop.capture,RatDrop.bit]
    repeat' constructor
    all_goals (intros;rfl)

theorem step_context (doubled : Bool) (before after : State C)
    (edge : TM2.step (program doubled .halt) before=some after) : after.var.1=before.var.1 := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program doubled .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact B23_4_RatWordPrep.RawGetter.nodes_readonly (fun v : Store C => v.1) _
        (program_readonly doubled point) memory contents _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_context (doubled : Bool) (trace : List (State C)) (before : State C)
    (first : trace.head?=some before) (chain : trace.IsChain (fun a b => TM2.step (program doubled .halt) a=some b)) :
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
      · exact (ih next rfl later current laterMember).trans (step_context doubled before next edge)

theorem step_resources (doubled : Bool) (before after : State C) (bound : Nat)
    (edge : TM2.step (program doubled .halt) before=some after)
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    (∀ slot,(after.stk slot).length≤bound+16) ∧ ∀ slot,¬Work slot→after.stk slot=before.stk slot := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program doubled .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact ⟨fun slot => (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
          (Nat.add_le_add_left (program_pushes doubled point) bound),
        fun slot untouched => StackIso.nodes_frame _ _ (program_writes doubled point) memory contents slot untouched
          _ (AuxWorkspace.endpoint_mem _ _ _)⟩

theorem trace_resources (doubled : Bool) (trace : List (State C)) (before : State C)
    (background : Stack → List Bool) (bound : Nat) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program doubled .halt) a=some b))
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
      have step:=step_resources doubled before next bound edge bounded
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

theorem internal_resources (doubled : Bool) (current : State C) (point : Label) (bound : Nat)
    (bounded : ∀ slot,(current.stk slot).length≤bound) :
    (∀ node∈AuxWorkspace.nodes (program doubled .halt point) current.var current.stk,
      node.1.1=current.var.1 ∧ (∀ slot,(node.2 slot).length≤bound+16) ∧
        ∀ slot,¬Work slot→node.2 slot=current.stk slot) ∧
      ScannerStatement.clock (program doubled .halt point) current.var current.stk≤32*(bound+17) := by
  refine ⟨?_,?_⟩
  · intro node member
    exact ⟨B23_4_RatWordPrep.RawGetter.nodes_readonly (fun v : Store C => v.1) _
        (program_readonly doubled point) current.var current.stk node member,
      fun slot => (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
        (Nat.add_le_add_left (program_pushes doubled point) bound),
      fun slot untouched => StackIso.nodes_frame _ _ (program_writes doubled point) current.var current.stk slot untouched node member⟩
  · exact (ScannerClock.clock_bound (program doubled .halt point) current.var current.stk bound bounded).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions doubled point))
        (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes doubled point) bound) 1))

def coefficient : Nat := 65536

def inputScale (background : Stack → List Bool) (number : Nat) (source old10 old11 : List Bool) : Nat :=
  RatInput.occupied (bank background (B23_4_RatWordPrep.NatField.packet number source) [] old10 old11)+1

theorem packet_length (number : Nat) (tail : List Bool) :
    (B23_4_RatWordPrep.NatField.packet number tail).length=2*(PSTRTMNatValue017.rawPayload number).length+2+tail.length := by
  simp only [B23_4_RatWordPrep.NatField.packet,List.length_append,RatOutput.flagged_length,List.length_cons]
  omega

structure Facts (doubled : Bool) (background : Stack → List Bool) (context : C) (memory : RatOutput.Store)
    (number : Nat) (source old10 old11 : List Bool) (trace : List (State C)) : Prop where
  first : trace.head?=some (state background 0 context memory (B23_4_RatWordPrep.NatField.packet number source) [] old10 old11)
  chain : trace.IsChain (fun a b => TM2.step (program doubled .halt) a=some b)
  last : trace.getLast?=some (state background 5 context (false,false) (B23_4_RatWordPrep.NatField.packet number source) []
    (PSTRTMIncrement009.blocks (selectDigits doubled (PSTRTMNatValue017.rawPayload number))++[false,false,true]) [false])
  count : trace.length≤old10.length+old11.length+2*(PSTRTMNatValue017.rawPayload number).length+14
  time : trace.length≤coefficient*inputScale background number source old10 old11
  boundaries : ∀ current∈trace,current.var.1=context ∧
    (∀ slot,(current.stk slot).length≤coefficient*inputScale background number source old10 old11) ∧
    RatInput.occupied current.stk≤coefficient*inputScale background number source old10 old11 ∧
    ∀ slot,¬Work slot→current.stk slot=background slot
  proper : ∀ current∈trace.dropLast,current.l≠some 5 ∧
    ∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (program doubled .halt point) current.var current.stk,
        node.1.1=context ∧
        (∀ slot,(node.2 slot).length≤coefficient*inputScale background number source old10 old11) ∧
        RatInput.occupied node.2≤coefficient*inputScale background number source old10 old11 ∧
        ∀ slot,¬Work slot→node.2 slot=background slot) ∧
      ScannerStatement.clock (program doubled .halt point) current.var current.stk≤coefficient*inputScale background number source old10 old11

theorem actual_bounded (doubled : Bool) (background : Stack → List Bool) (context : C)
    (memory : RatOutput.Store) (number : Nat) (source old10 old11 : List Bool) :
    ∃ trace,Facts doubled background context memory number source old10 old11 trace := by
  obtain ⟨trace,first,chain,last,count⟩:=actual doubled .halt background context memory number source old10 old11
  let before:=state background 0 context memory (B23_4_RatWordPrep.NatField.packet number source) [] old10 old11
  let M:=RatInput.occupied before.stk
  let K:=inputScale background number source old10 old11
  have mscale : K=M+1 := rfl
  have packetRoom : (B23_4_RatWordPrep.NatField.packet number source).length≤M := RatInput.Encoder.point_mass before.stk 8
  have old10Room : old10.length≤M := RatInput.Encoder.point_mass before.stk 10
  have old11Room : old11.length≤M := RatInput.Encoder.point_mass before.stk 11
  rw [packet_length] at packetRoom
  have short : trace.length≤16*K := by omega
  let S:=M+16*trace.length
  have frames : ∀ slot,¬Work slot→before.stk slot=background slot := by
    intro slot untouched
    have a : slot≠4 := by intro same;subst slot;exact untouched (by decide)
    have b : slot≠8 := by intro same;subst slot;exact untouched (by decide)
    have c : slot≠10 := by intro same;subst slot;exact untouched (by decide)
    have d : slot≠11 := by intro same;subst slot;exact untouched (by decide)
    simp only [before,state,bank,a,b,c,d,ite_false]
  have bounds:=trace_resources doubled trace before background M first chain (RatInput.Encoder.point_mass before.stk) frames
  have contexts:=trace_context doubled trace before first chain
  have bounded : ∀ current∈trace,∀ slot,(current.stk slot).length≤S := by
    intro current member slot
    exact (bounds current member).1 slot
  have caps : trace.length≤coefficient*K ∧ 16*S≤coefficient*K ∧ S+16≤coefficient*K ∧
      16*(S+16)≤coefficient*K ∧ 32*(S+17)≤coefficient*K := by
    dsimp only [S,coefficient]
    omega
  have proper:=NativeMulLink.no_early_halt_port (program doubled .halt) 5 rfl trace
    (state background 5 context (false,false) (B23_4_RatWordPrep.NatField.packet number source) []
      (PSTRTMIncrement009.blocks (selectDigits doubled (PSTRTMNatValue017.rawPayload number))++[false,false,true]) [false]) chain last rfl
  refine ⟨trace,⟨first,chain,last,count,caps.1,?_,?_⟩⟩
  · intro current member
    refine ⟨contexts current member,?_,?_,(bounds current member).2⟩
    · intro slot
      exact (bounded current member slot).trans ((Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans caps.2.1)
    · exact (RatInput.Encoder.occupied_bound current.stk S (bounded current member)).trans caps.2.1
  · intro current member
    refine ⟨proper current member,?_⟩
    intro point selected
    have internal:=internal_resources doubled current point S (bounded current (List.mem_of_mem_dropLast member))
    refine ⟨?_,internal.2.trans caps.2.2.2.2⟩
    intro node inside
    refine ⟨((internal.1 node inside).1).trans (contexts current (List.mem_of_mem_dropLast member)),
      fun slot => ((internal.1 node inside).2.1 slot).trans caps.2.2.1,?_,
      fun slot untouched => ((internal.1 node inside).2.2 slot untouched).trans
        ((bounds current (List.mem_of_mem_dropLast member)).2 slot untouched)⟩
    exact (RatInput.Encoder.occupied_bound node.2 (S+16) ((internal.1 node inside).2.1)).trans caps.2.2.2.1

def statementClock (doubled : Bool) (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (program doubled .halt point) current.var current.stk

def traceClockSum (doubled : Bool) (trace : List (State C)) : Nat :=
  (trace.dropLast.map (statementClock doubled)).sum

def chargedCost (doubled : Bool) (trace : List (State C)) : Nat := trace.length+traceClockSum doubled trace

theorem traceClockSum_le {doubled : Bool} {background : Stack → List Bool} {context : C} {memory : RatOutput.Store}
    {number : Nat} {source old10 old11 : List Bool} {trace : List (State C)}
    (facts : Facts doubled background context memory number source old10 old11 trace) :
    traceClockSum doubled trace≤coefficient^2*(inputScale background number source old10 old11)^2 := by
  let cap:=coefficient*inputScale background number source old10 old11
  have term : ∀ value∈trace.dropLast.map (statementClock doubled),value≤cap := by
    intro value member
    obtain ⟨current,present,rfl⟩:=List.mem_map.mp member
    cases selected : current.l with
    | none => simp only [statementClock,selected,Nat.zero_le]
    | some point =>
      simp only [statementClock,selected]
      exact ((facts.proper current present).2 point selected).2
  have sum : traceClockSum doubled trace≤trace.dropLast.length*cap := by
    simpa only [traceClockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (trace.dropLast.map (statementClock doubled)) cap term
  have count : trace.dropLast.length≤cap := by
    rw [List.length_dropLast]
    exact (Nat.sub_le trace.length 1).trans facts.time
  exact (sum.trans (Nat.mul_le_mul_right cap count)).trans_eq (by dsimp only [cap];ring)

theorem chargedCost_le {doubled : Bool} {background : Stack → List Bool} {context : C} {memory : RatOutput.Store}
    {number : Nat} {source old10 old11 : List Bool} {trace : List (State C)}
    (facts : Facts doubled background context memory number source old10 old11 trace) :
    chargedCost doubled trace≤(coefficient^2+coefficient)*(inputScale background number source old10 old11)^2 := by
  have positive : 1 ≤ inputScale background number source old10 old11 := by unfold inputScale;omega
  have square : inputScale background number source old10 old11≤(inputScale background number source old10 old11)^2 := by nlinarith
  have time:=facts.time
  have sum:=traceClockSum_le facts
  unfold chargedCost
  nlinarith [Nat.mul_le_mul_left coefficient square]

def support : Finset Label := Finset.univ

private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt support body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro _;exact Finset.mem_univ _
  | halt => trivial

theorem supports (doubled : Bool) : TM2.Supports (program (C:=C) doubled .halt) support :=
  ⟨Finset.mem_univ _,fun _ _ => supports_stmt _⟩

end RootB234.RuntimeCounter.Builder
