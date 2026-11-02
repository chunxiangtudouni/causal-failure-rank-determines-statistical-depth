module
public import RootB236_Controller_BestUpdate_Run003
public import Mathlib.Algebra.Order.BigOperators.Group.List

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.BestUpdate
open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.PSTRWordVM
open scoped BigOperators
variable {C : Type*}

def nodeCount : Statement C → Nat
  | .push _ _ tail | .pop _ _ tail | .peek _ _ tail | .load _ tail => nodeCount tail+1
  | .branch _ yes no => max (nodeCount yes) (nodeCount no)+1
  | .goto _ | .halt => 1
theorem nodes_count (body : Statement C) (memory : Store C) (slots : Stack → List Bool) :
    (AuxWorkspace.nodes body memory slots).length≤nodeCount body := by
  induction body generalizing memory slots with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih =>
    simp only [AuxWorkspace.nodes,List.length_cons,nodeCount];exact Nat.add_le_add_right (ih _ _) 1
  | branch test yes no yesIH noIH =>
    simp only [AuxWorkspace.nodes,nodeCount]
    cases choice : test memory
    · simp only [Bool.false_eq_true,ite_false,List.length_cons]
      exact Nat.add_le_add_right ((noIH _ _).trans (Nat.le_max_right _ _)) 1
    · simp only [ite_true,List.length_cons]
      exact Nat.add_le_add_right ((yesIH _ _).trans (Nat.le_max_left _ _)) 1
  | goto _ | halt => exact Nat.le_refl _

theorem program_actions (caller : Statement C) (point : Label) (proper : point≠done) :
    ScannerClock.actions (program caller point)≤16 := by
  fin_cases point <;> norm_num [program,boot,clearRank,clearTool,done,compareBody,copyBody,
    LabelMap.statement_actions,StackIso.statement_actions,StoreIso.statement_actions,
    RankCompare.program,RankCompare.core,ContextLift.statement_actions,ScannerClock.actions,
    B23_4_RatWordPrep.WholeCopy.program] at *
theorem program_pushes (caller : Statement C) (point : Label) (proper : point≠done) :
    AuxWorkspace.pushes (program caller point)≤16 := by
  fin_cases point <;> norm_num [program,boot,clearRank,clearTool,done,compareBody,copyBody,
    LabelMap.statement_pushes,StackIso.statement_pushes,StoreIso.statement_pushes,
    RankCompare.program,RankCompare.core,ContextLift.statement_pushes,AuxWorkspace.pushes,
    B23_4_RatWordPrep.WholeCopy.program] at *
theorem program_nodes (caller : Statement C) (point : Label) (proper : point≠done) :
    nodeCount (program caller point)≤16 := by
  fin_cases point <;> norm_num [program,boot,clearRank,clearTool,done,compareBody,copyBody,
    LabelMap.statement,StackIso.statement,StoreIso.statement,RankCompare.program,RankCompare.core,
    ContextLift.statement,B23_4_RatWordPrep.WholeCopy.program,nodeCount] at *
theorem program_writes (caller : Statement C) (point : Label) (proper : point≠done) :
    StackIso.WritesOnly Work (program caller point) := by
  fin_cases point <;> simp_all [program,boot,clearRank,clearTool,done,compareBody,copyBody,
    LabelMap.statement,StackIso.statement,StoreIso.statement,RankCompare.program,RankCompare.core,
    ContextLift.statement,B23_4_RatWordPrep.WholeCopy.program,copyRoles,Equiv.trans_apply,
    StackIso.WritesOnly,Work]
  all_goals decide
theorem program_readonly (caller : Statement C) (point : Label) (proper : point≠done) :
    B23_4_RatWordPrep.RawGetter.Readonly (fun memory : Store C => memory.1) (program caller point) := by
  fin_cases point
  all_goals try exact False.elim (proper rfl)
  all_goals dsimp [program,boot,clearRank,clearTool,done,compareBody,copyBody,LabelMap.statement,
    StackIso.statement,StoreIso.statement,RankCompare.program,RankCompare.core,ContextLift.statement,
    B23_4_RatWordPrep.WholeCopy.program,B23_4_RatWordPrep.RawGetter.Readonly,captureFlag,capturePresent,
    RankCompare.captureLeft,RankCompare.captureRight,RankCompare.select,
    B23_4_RatWordPrep.WholeCopy.capture,storeIso]
  all_goals repeat' constructor
  all_goals intros;rfl

theorem step_resources (caller : Statement C) (before after : State C) (bound : Nat)
    (proper : before.l≠some done) (edge : TM2.step (program caller) before=some after)
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    after.var.1=before.var.1 ∧ (∀ slot,(after.stk slot).length≤bound+16) ∧
      ∀ slot,¬Work slot → after.stk slot=before.stk slot := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have interior : point≠done := by intro same;subst point;exact proper rfl
      have same : after=TM2.stepAux (program caller point) memory contents := (Option.some.inj edge).symm
      subst after
      exact ⟨B23_4_RatWordPrep.RawGetter.nodes_readonly _ _ (program_readonly caller point interior)
        memory contents _ (AuxWorkspace.endpoint_mem _ _ _),
        fun slot => (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
          (Nat.add_le_add_left (program_pushes caller point interior) bound),
        fun slot outside => StackIso.nodes_frame _ _ (program_writes caller point interior)
          memory contents slot outside _ (AuxWorkspace.endpoint_mem _ _ _)⟩
theorem trace_resources (caller : Statement C) (trace : List (State C)) (before : State C) (bound : Nat)
    (first : trace.head?=some before)
    (chain : trace.IsChain (fun x y => TM2.step (program caller) x=some y))
    (proper : ∀ current∈trace.dropLast,current.l≠some done)
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    ∀ current∈trace,current.var.1=before.var.1 ∧
      (∀ slot,(current.stk slot).length≤bound+16*trace.length) ∧
      ∀ slot,¬Work slot → current.stk slot=before.stk slot := by
  induction trace generalizing before bound with
  | nil => simp
  | cons firstState rest ih =>
    have same : firstState=before := Option.some.inj first
    subst firstState
    cases rest with
    | nil =>
      intro current member
      have same:=List.mem_singleton.mp member
      subst current
      exact ⟨rfl,fun slot => (bounded slot).trans (Nat.le_add_right _ _),fun _ _ => rfl⟩
    | cons next rest =>
      obtain ⟨edge,tailChain⟩:=List.isChain_cons_cons.mp chain
      have step:=step_resources caller before next bound
        (proper before (by rw [List.dropLast_cons_cons];exact List.mem_cons_self)) edge bounded
      intro current member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨rfl,fun slot => (bounded slot).trans (Nat.le_add_right _ _),fun _ _ => rfl⟩
      · have tail:=ih next (bound+16) rfl tailChain
          (by intro other inside;exact proper other (by rw [List.dropLast_cons_cons];exact List.mem_cons_of_mem _ inside))
          step.2.1 current later
        refine ⟨tail.1.trans step.1,?_,fun slot outside => (tail.2.2 slot outside).trans (step.2.2 slot outside)⟩
        intro slot
        have small:=tail.2.1 slot
        simp only [List.length_cons] at small ⊢
        omega

def initialMass (bg : Stack → List Bool) (a b tool : Nat) (best : List Bool) (flag : Bool) (tail : List Bool) : Nat :=
  ∑ slot : Stack,(bank bg a b tool best flag tail slot).length
def scale (bg : Stack → List Bool) (a b tool : Nat) (best : List Bool) (flag : Bool) (tail : List Bool) : Nat :=
  initialMass bg a b tool best flag tail+1
theorem mass_point (bg : Stack → List Bool) (a b tool : Nat) (best : List Bool) (flag : Bool) (tail : List Bool) (slot : Stack) :
    (bank bg a b tool best flag tail slot).length≤ initialMass bg a b tool best flag tail :=
  Finset.single_le_sum (f:=fun other : Stack => (bank bg a b tool best flag tail other).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ slot)
theorem mass_inputs (bg : Stack → List Bool) (a b tool : Nat) (best : List Bool) (flag : Bool) (tail : List Bool) :
    a+b+tool+best.length≤ initialMass bg a b tool best flag tail := by
  let f:=fun slot : Stack => (bank bg a b tool best flag tail slot).length
  have small : (∑ slot∈({9,10,5,14}:Finset Stack),f slot)≤ initialMass bg a b tool best flag tail :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  simp [f,bank,unary,RankCompare.unary] at small
  omega

def statementClock (caller : Statement C) (current : State C) : Nat :=
  match current.l with | none => 0 | some point => ScannerStatement.clock (program caller point) current.var current.stk
def traceClockSum (caller : Statement C) (trace : List (State C)) : Nat :=
  (trace.dropLast.map (statementClock caller)).sum
structure Facts (caller : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb flag : Bool) (ord : Ordering) (a b tool : Nat) (best tail : List Bool)
    (trace : List (State C)) (final : State C) : Prop where
  first : trace.head?=some (state boot (context,ha,hb,ord) (bank bg a b tool best flag tail))
  chain : trace.IsChain (fun x y => TM2.step (program caller) x=some y)
  last : trace.getLast?=some final
  contents : final.l=some done ∧ final.stk=resultBank bg a b tool best flag tail
  time : trace.length≤16*scale bg a b tool best flag tail
  proper : ∀ current∈trace.dropLast,current.l≠some done

theorem actual_facts (caller : Statement C) (bg : Stack → List Bool) (context : C)
    (ha hb flag : Bool) (ord : Ordering) (a b tool : Nat) (best tail : List Bool) :
    ∃ trace final,Facts caller bg context ha hb flag ord a b tool best tail trace final := by
  obtain ⟨steps,memory,path,_preserved,time⟩:=operational caller bg context ha hb flag ord a b tool best tail
  obtain ⟨trace,first,chain,last,count,proper⟩:=path.actual
  refine ⟨trace,_,first,chain,last,⟨rfl,rfl⟩,?_,proper⟩
  have mass:=mass_inputs bg a b tool best flag tail
  change trace.length≤16*(initialMass bg a b tool best flag tail+1)
  omega

theorem bank_frame (bg : Stack → List Bool) (a b tool : Nat) (best : List Bool) (flag : Bool) (tail : List Bool)
    (slot : Stack) (outside : ¬Work slot) : bank bg a b tool best flag tail slot=bg slot := by
  fin_cases slot <;> simp_all [bank,Work]
theorem Facts.boundaries {caller : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb flag : Bool} {ord : Ordering} {a b tool : Nat} {best tail : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts caller bg context ha hb flag ord a b tool best tail trace final)
    (current : State C) (member : current∈trace) :
    current.var.1=context ∧ (∀ slot,(current.stk slot).length≤257*scale bg a b tool best flag tail) ∧
      ∀ slot,¬Work slot → current.stk slot=bg slot := by
  have raw:=trace_resources caller trace _ (initialMass bg a b tool best flag tail) facts.first facts.chain facts.proper
    (mass_point bg a b tool best flag tail) current member
  refine ⟨raw.1,?_,fun slot outside => (raw.2.2 slot outside).trans (bank_frame bg a b tool best flag tail slot outside)⟩
  intro slot
  have small:=raw.2.1 slot
  have time:=facts.time
  unfold scale at *
  omega

theorem Facts.internal {caller : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb flag : Bool} {ord : Ordering} {a b tool : Nat} {best tail : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts caller bg context ha hb flag ord a b tool best tail trace final)
    (current : State C) (member : current∈trace.dropLast) (point : Label) (active : current.l=some point) :
    (∀ node∈AuxWorkspace.nodes (program caller point) current.var current.stk,node.1.1=context ∧
      (∀ slot,(node.2 slot).length≤273*scale bg a b tool best flag tail) ∧
      ∀ slot,¬Work slot → node.2 slot=bg slot) ∧
    (AuxWorkspace.nodes (program caller point) current.var current.stk).length≤16 ∧
    ScannerClock.actions (program caller point)≤16 ∧ AuxWorkspace.pushes (program caller point)≤16 ∧
    ScannerStatement.clock (program caller point) current.var current.stk≤9000*scale bg a b tool best flag tail := by
  have proper : point≠done := by intro same;subst point;exact facts.proper current member active
  have boundary:=facts.boundaries current (List.dropLast_subset trace member)
  have positive : 0<scale bg a b tool best flag tail := by unfold scale;omega
  have actions:=program_actions caller point proper
  have pushes:=program_pushes caller point proper
  refine ⟨?_,(nodes_count _ _ _).trans (program_nodes caller point proper),actions,pushes,?_⟩
  · intro node inside
    have readonly:=B23_4_RatWordPrep.RawGetter.nodes_readonly _ _ (program_readonly caller point proper)
      current.var current.stk node inside
    refine ⟨readonly.trans boundary.1,?_,fun slot outside =>
      (StackIso.nodes_frame _ _ (program_writes caller point proper) current.var current.stk slot outside node inside).trans
        (boundary.2.2 slot outside)⟩
    intro slot
    have small:=AuxWorkspace.node_bound (program caller point) current.var current.stk
      (257*scale bg a b tool best flag tail) boundary.2.1 node inside slot
    omega
  · have clock:=ScannerClock.clock_bound (program caller point) current.var current.stk
      (257*scale bg a b tool best flag tail) boundary.2.1
    calc
      ScannerStatement.clock (program caller point) current.var current.stk≤
          (2*16)*(257*scale bg a b tool best flag tail+16+1) :=
        clock.trans (Nat.mul_le_mul (by omega) (by omega))
      _≤9000*scale bg a b tool best flag tail := by omega

theorem Facts.clock_sum {caller : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb flag : Bool} {ord : Ordering} {a b tool : Nat} {best tail : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts caller bg context ha hb flag ord a b tool best tail trace final) :
    traceClockSum caller trace≤144000*(scale bg a b tool best flag tail)^2 := by
  have terms : ∀ clock∈trace.dropLast.map (statementClock caller),clock≤9000*scale bg a b tool best flag tail := by
    intro clock member
    obtain ⟨current,inTrace,rfl⟩:=List.mem_map.mp member
    cases active : current.l with
    | none => simp [statementClock,active]
    | some point =>
      simpa only [statementClock,active] using (facts.internal current inTrace point active).2.2.2.2
  have sumBound : traceClockSum caller trace≤trace.dropLast.length*(9000*scale bg a b tool best flag tail) := by
    simpa only [traceClockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (trace.dropLast.map (statementClock caller)) (9000*scale bg a b tool best flag tail) terms
  have count : trace.dropLast.length≤16*scale bg a b tool best flag tail := by
    rw [List.length_dropLast];exact (Nat.sub_le trace.length 1).trans facts.time
  calc
    traceClockSum caller trace≤trace.dropLast.length*(9000*scale bg a b tool best flag tail) := sumBound
    _≤(16*scale bg a b tool best flag tail)*(9000*scale bg a b tool best flag tail) := Nat.mul_le_mul_right _ count
    _=144000*(scale bg a b tool best flag tail)^2 := by ring

theorem Facts.charged {caller : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb flag : Bool} {ord : Ordering} {a b tool : Nat} {best tail : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts caller bg context ha hb flag ord a b tool best tail trace final) :
    trace.length+traceClockSum caller trace≤144016*(scale bg a b tool best flag tail)^2 := by
  have positive : 0<scale bg a b tool best flag tail := by unfold scale;omega
  have power : scale bg a b tool best flag tail≤(scale bg a b tool best flag tail)^2 := by
    simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left (scale bg a b tool best flag tail) (Nat.succ_le_of_lt positive)
  exact (Nat.add_le_add (facts.time.trans (Nat.mul_le_mul_left 16 power)) facts.clock_sum).trans (by omega)

theorem Facts.caller_path {Ω : Type*} {caller : Statement C} {bg : Stack → List Bool} {context : C}
    {ha hb flag : Bool} {ord : Ordering} {a b tool : Nat} {best tail : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts caller bg context ha hb flag ord a b tool best tail trace final)
    (embed : Label → Ω) (target : Ω → TM2.Stmt Alphabet Ω (Store C))
    (code : ∀ point,point≠done → target (embed point)=LabelMap.statement embed (program caller point)) :
    (trace.map (LabelMap.configuration embed)).head?=some (LabelMap.configuration embed
      (state boot (context,ha,hb,ord) (bank bg a b tool best flag tail))) ∧
    (trace.map (LabelMap.configuration embed)).IsChain (fun x y => TM2.step target x=some y) ∧
    (trace.map (LabelMap.configuration embed)).getLast?=some (LabelMap.configuration embed final) ∧
    (trace.map (LabelMap.configuration embed)).length=trace.length ∧
    ∀ current∈trace.map (LabelMap.configuration embed),∃ old∈trace,
      current=LabelMap.configuration embed old ∧ current.var=old.var ∧ current.stk=old.stk := by
  exact LabelMap.actual_path_on embed (program caller) target trace _ _ facts.first facts.chain facts.last
    (by intro current member point active
        exact code point (by intro same;subst point;exact facts.proper current member active))
end RootB236.Controller.BestUpdate
