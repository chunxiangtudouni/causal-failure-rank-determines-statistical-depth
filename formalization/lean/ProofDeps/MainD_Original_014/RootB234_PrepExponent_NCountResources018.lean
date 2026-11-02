module

public import RootB234_PrepExponent_NCountRun017

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.NCount
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource
variable {C : Type*}

def Work (slot : Stack) : Prop := slot=3 ∨ slot=4 ∨ slot=5 ∨ slot=6 ∨ slot=7 ∨ slot=8 ∨ slot=11 ∨ slot=15
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

theorem program_writes (point : Label) : StackIso.WritesOnly Work (program (C:=C) .halt point) := by
  fin_cases point <;> exact of_decide_eq_true rfl

theorem program_actions (point : Label) : ScannerClock.actions (program (C:=C) .halt point) ≤ 9 := by
  fin_cases point <;> exact of_decide_eq_true rfl

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C:=C) .halt point) ≤ 7 := by
  fin_cases point <;> exact of_decide_eq_true rfl

theorem program_readonly (point : Label) :
    B23_4_RatWordPrep.RawGetter.Readonly (fun memory : Store C => memory.1.1.1) (program .halt point) := by
  fin_cases point
  all_goals
    dsimp [program,copyLabel,reverseLabel,unaryLabel,moveLabel,clearLabel,LabelMap.statement,StackIso.statement,
      StoreIso.statement,unaryIso,B23_4_RatWordPrep.WholeCopy.program,B23_4_RatWordPrep.WholeCopy.capture,
      Cells.Public.reverse3To2,Cells.Public.clear0,Cells.program,Cells.body,Cells.entry,Cells.moving,Cells.roles,Cells.rawProgram,
      RuntimeCounter.Builder.program,RuntimeCounter.Builder.eraseBody,RatPacketTransport.program,RatPacketTransport.keepSource,
      PacketUnary.program,PacketUnary.convertIso,PacketUnary.collectLabel,PacketUnary.convertLabel,
      L01_3_5_TABLE_NatSerializer019.collectProgram,RatInput.program,RatInput.fieldBody,RatInput.restoreBody,
      PSTRSymbolicNaturalExport.program,PSTRSymbolicRatExport.restoreLabel,Unary.program,Unary.baseProgram,
      ContextLift.statement,Unary.captureBit,Unary.capturePresent,B23_4_RatWordPrep.RawGetter.Readonly,RatDrop.capture]
    repeat' constructor
    all_goals (intros;rfl)

theorem step_context (before after : State C) (edge : TM2.step (program .halt) before=some after) :
    after.var.1.1.1=before.var.1.1.1 := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      exact B23_4_RatWordPrep.RawGetter.nodes_readonly (fun v : Store C => v.1.1.1) _ (program_readonly point) memory contents
        _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_context (trace : List (State C)) (before : State C) (first : trace.head?=some before)
    (chain : trace.IsChain (fun a b => TM2.step (program .halt) a=some b)) :
    ∀ current∈trace,current.var.1.1.1=before.var.1.1.1 := by
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
    (∀ slot,(after.stk slot).length ≤ bound+7) ∧
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
    ∀ current∈trace,(∀ slot,(current.stk slot).length ≤ bound+7*trace.length) ∧
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
      · have tail := ih next (bound+7) rfl tailChain step.1
          (fun slot untouched => (step.2 slot untouched).trans (frame slot untouched)) current later
        refine ⟨?_,tail.2⟩
        intro slot
        have h := tail.1 slot
        simp only [List.length_cons] at h ⊢
        omega

theorem internal_resources (current : State C) (point : Label) (bound : Nat)
    (bounded : ∀ slot,(current.stk slot).length ≤ bound) :
    (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
      node.1.1.1.1=current.var.1.1.1 ∧ (∀ slot,(node.2 slot).length ≤ bound+7) ∧
        ∀ slot,¬Work slot→node.2 slot=current.stk slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk ≤ 18*(bound+8) := by
  refine ⟨?_,?_⟩
  · intro node member
    exact ⟨B23_4_RatWordPrep.RawGetter.nodes_readonly (fun v : Store C => v.1.1.1) _ (program_readonly point) current.var current.stk node member,
      fun slot => (AuxWorkspace.node_bound _ _ _ bound bounded node member slot).trans
        (Nat.add_le_add_left (program_pushes point) bound),
      fun slot untouched => StackIso.nodes_frame _ _ (program_writes point) current.var current.stk slot untouched node member⟩
  · exact (ScannerClock.clock_bound (program .halt point) current.var current.stk bound bounded).trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions point))
        (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes point) bound) 1))




def initialMass (background : Stack → List Bool) (number : Nat) : Nat :=
  RatInput.occupied (bank background (B23_4_RatWordPrep.NatField.packet number []) [] [] [] [])

def scale (background : Stack → List Bool) (number : Nat) : Nat := initialMass background number+number+1

theorem packet_bound (background : Stack → List Bool) (number : Nat) :
    (B23_4_RatWordPrep.NatField.packet number []).length ≤ initialMass background number :=
  RatInput.Encoder.point_mass (bank background (B23_4_RatWordPrep.NatField.packet number []) [] [] [] []) 8

theorem unary_mass (background : Stack → List Bool) (number : Nat) :
    PacketUnary.mass (bank background (B23_4_RatWordPrep.NatField.packet number []) [] [] []
      (B23_4_RatWordPrep.NatField.packet number [])) number [] ≤ 16*initialMass background number := by
  let input := B23_4_RatWordPrep.NatField.packet number []
  let before := bank background input [] [] [] []
  let frame := bank background input [] [] [] input
  have equality : PacketUnary.entryBank frame number []=Function.update before 15 input := by
    funext slot
    fin_cases slot <;> simp [PacketUnary.entryBank,frame,before,bank,input,packet_equal]
  have each : ∀ slot,(PacketUnary.entryBank frame number [] slot).length ≤ initialMass background number := by
    rw [equality]
    intro slot
    by_cases same : slot=15
    · subst slot
      simpa only [Function.update_self] using packet_bound background number
    · have bound : (before slot).length ≤ initialMass background number := by
        change (before slot).length ≤ RatInput.occupied before
        exact RatInput.Encoder.point_mass before slot
      simpa only [Function.update_of_ne same] using bound
  exact RatInput.Encoder.occupied_bound _ _ each

theorem uniform_time (background : Stack → List Bool) (number : Nat) :
    4*(B23_4_RatWordPrep.NatField.packet number []).length+number+PacketUnary.time number+10 ≤
      16384*(scale background number)^2 := by
  let K := scale background number
  let frame := bank background (B23_4_RatWordPrep.NatField.packet number []) [] [] []
    (B23_4_RatWordPrep.NatField.packet number [])
  have mass := unary_mass background number
  have localBound : PacketUnary.localScale frame number [] ≤ 16*K := by
    dsimp only [PacketUnary.localScale,frame,K,scale]
    omega
  have t := (PacketUnary.resource_poly frame number []).1
  have kernel : PacketUnary.time number ≤ 8192*K^2 := by
    calc
      PacketUnary.time number ≤ 32*(PacketUnary.localScale frame number [])^2 := t
      _ ≤ 32*(16*K)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left localBound 2)
      _ = _ := by ring
  have packet := packet_bound background number
  have positive : 1 ≤ K := by dsimp [K,scale];omega
  have square : K ≤ K^2 := by nlinarith
  have squarePos : 1 ≤ K^2 := one_le_pow₀ positive
  have numberBound : number ≤ K := by dsimp [K,scale];omega
  have massBound : initialMass background number ≤ K := by dsimp [K,scale];omega
  change _ ≤ 16384*K^2
  omega

def statementClock (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (program .halt point) current.var current.stk

def traceClockSum (run : List (State C)) : Nat := (run.dropLast.map statementClock).sum

structure Facts (background : Stack → List Bool) (context : C) (registers : Unary.Registers)
    (rat : RatInput.Store) (flags : RatOutput.Store) (number : Nat)
    (memory : PacketUnary.Store C) (run : List (State C)) : Prop where
  context_eq : memory.1.1=context
  first : run.head?=some (state background (.copy .boot) (((context,registers),rat),flags)
    (B23_4_RatWordPrep.NatField.packet number []) [] [] [] [])
  chain : run.IsChain (fun a b => TM2.step (program .halt) a=some b)
  last : run.getLast?=some (state background .done (memory,false,false)
    (B23_4_RatWordPrep.NatField.packet number []) [] [] (Unary.unary number) [])
  time : run.length ≤ 16384*(scale background number)^2
  boundaries : ∀ current∈run,current.var.1.1.1=context ∧
    (∀ slot,(current.stk slot).length ≤ 131072*(scale background number)^2) ∧
    ∀ slot,¬Work slot→current.stk slot=background slot
  proper : ∀ current∈run.dropLast,current.l≠some .done ∧
    ∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
        node.1.1.1.1=context ∧ (∀ slot,(node.2 slot).length ≤ 262144*(scale background number)^2) ∧
        ∀ slot,¬Work slot→node.2 slot=background slot) ∧
      ScannerStatement.clock (program .halt point) current.var current.stk ≤ 4194304*(scale background number)^2

theorem actual_bounded (background : Stack → List Bool) (context : C) (registers : Unary.Registers)
    (rat : RatInput.Store) (flags : RatOutput.Store) (number : Nat) :
    ∃ memory run,Facts background context registers rat flags number memory run := by
  obtain ⟨memory,run,contextEq,first,chain,last,count⟩ := actual .halt background context registers rat flags number
  let before := state background (.copy .boot) (((context,registers),rat),flags)
    (B23_4_RatWordPrep.NatField.packet number []) [] [] [] []
  let M := initialMass background number
  let K := scale background number
  have positive : 1 ≤ K := by dsimp [K,scale];omega
  have square : K ≤ K^2 := by nlinarith
  have squarePos : 1 ≤ K^2 := one_le_pow₀ positive
  have time : run.length ≤ 16384*K^2 := count.trans (uniform_time background number)
  have frames : ∀ slot,¬Work slot→before.stk slot=background slot := by
    intro slot untouched
    fin_cases slot <;> simp_all [Work,before,state,bank]
  have bounds := trace_resources run before background M first chain (RatInput.Encoder.point_mass before.stk) frames
  have contexts := trace_context run before first chain
  have massBound : M ≤ K^2 := by dsimp only [M,K,scale] at *;omega
  have bounded : ∀ current∈run,∀ slot,(current.stk slot).length ≤ 131072*K^2 := by
    intro current member slot
    have bound := (bounds current member).1 slot
    omega
  have proper := NativeMulLink.no_early_halt_port (program (C:=C) .halt) .done rfl run
    (state background .done (memory,false,false) (B23_4_RatWordPrep.NatField.packet number []) [] [] (Unary.unary number) [])
    chain last rfl
  refine ⟨memory,run,⟨contextEq,first,chain,last,time,?_,?_⟩⟩
  · intro current member
    exact ⟨contexts current member,bounded current member,(bounds current member).2⟩
  · intro current member
    refine ⟨proper current member,?_⟩
    intro point selected
    have boundaryMember := List.mem_of_mem_dropLast member
    have internal := internal_resources current point (131072*K^2) (bounded current boundaryMember)
    refine ⟨?_,?_⟩
    · intro node inside
      refine ⟨((internal.1 node inside).1).trans (contexts current boundaryMember),?_,?_⟩
      · intro slot
        change (node.2 slot).length ≤ 262144*K^2
        exact ((internal.1 node inside).2.1 slot).trans (by omega)
      · intro slot untouched
        exact ((internal.1 node inside).2.2 slot untouched).trans ((bounds current boundaryMember).2 slot untouched)
    · change ScannerStatement.clock (program .halt point) current.var current.stk ≤ 4194304*K^2
      exact internal.2.trans (by omega)

theorem traceClockSum_le {background : Stack → List Bool} {context : C} {registers : Unary.Registers}
    {rat : RatInput.Store} {flags : RatOutput.Store} {number : Nat} {memory : PacketUnary.Store C}
    {run : List (State C)} (facts : Facts background context registers rat flags number memory run) :
    traceClockSum run ≤ 68719476736*(scale background number)^4 := by
  let K := scale background number
  have terms : ∀ n∈run.dropLast.map statementClock,n ≤ 4194304*K^2 := by
    intro n member
    obtain ⟨current,present,rfl⟩ := List.mem_map.mp member
    cases selected : current.l with
    | none => simp only [statementClock,selected,Nat.zero_le]
    | some point =>
      simp only [statementClock,selected]
      exact ((facts.proper current present).2 point selected).2
  have total : traceClockSum run ≤ run.dropLast.length*(4194304*K^2) := by
    simpa only [traceClockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (run.dropLast.map statementClock) (4194304*K^2) terms
  have count : run.dropLast.length ≤ 16384*K^2 := by
    rw [List.length_dropLast]
    exact (Nat.sub_le run.length 1).trans facts.time
  exact total.trans ((Nat.mul_le_mul_right _ count).trans_eq (by ring))

theorem chargedCost_le {background : Stack → List Bool} {context : C} {registers : Unary.Registers}
    {rat : RatInput.Store} {flags : RatOutput.Store} {number : Nat} {memory : PacketUnary.Store C}
    {run : List (State C)} (facts : Facts background context registers rat flags number memory run) :
    run.length+traceClockSum run ≤ 68719493120*(scale background number)^4 := by
  have time := facts.time
  have clocks := traceClockSum_le facts
  have positive : 1 ≤ scale background number := by dsimp [scale];omega
  have powers : (scale background number)^2 ≤ (scale background number)^4 := Nat.pow_le_pow_right positive (by decide)
  have count := time.trans (Nat.mul_le_mul_left 16384 powers)
  omega

end RootB234.PrepExponent.NCount
