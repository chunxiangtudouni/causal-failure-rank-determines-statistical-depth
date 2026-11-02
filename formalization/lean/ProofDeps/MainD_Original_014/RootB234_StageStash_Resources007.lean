module
public import RootB234_StageStash_Restore006
public import Mathlib.Algebra.Order.BigOperators.Group.List

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB234.StageStash
open Turing PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
open scoped BigOperators
variable {C : Type*}

theorem work_field (i : Field) : Work (field i) := Or.inr (by rw [field_index];exact i.isLt)
theorem work_zero : Work 0 := Or.inl rfl

def nodeCount : Statement C → Nat
  | .push _ _ tail | .pop _ _ tail | .peek _ _ tail | .load _ tail => nodeCount tail+1
  | .branch _ yes no => max (nodeCount yes) (nodeCount no)+1
  | .goto _ | .halt => 1

theorem nodes_count (body : Statement C) (memory : Store C) (before : Bank) :
    (AuxWorkspace.nodes body memory before).length≤nodeCount body := by
  induction body generalizing memory before with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih =>
    simp only [AuxWorkspace.nodes,List.length_cons,nodeCount];exact Nat.add_le_add_right (ih _ _) 1
  | branch test yes no hy hn =>
    simp only [AuxWorkspace.nodes,nodeCount]
    cases choice : test memory
    · simp only [Bool.false_eq_true,ite_false,List.length_cons];exact Nat.add_le_add_right ((hn _ _).trans (Nat.le_max_right _ _)) 1
    · simp only [ite_true,List.length_cons];exact Nat.add_le_add_right ((hy _ _).trans (Nat.le_max_left _ _)) 1
  | goto _ | halt => exact Nat.le_refl _

theorem source_actions (point : Label) : ScannerClock.actions (source (C:=C) point)≤4 := by
  cases point
  all_goals simp only [source,program]
  all_goals (try split_ifs) <;> exact of_decide_eq_true rfl

theorem source_pushes (point : Label) : AuxWorkspace.pushes (source (C:=C) point)≤4 := by
  cases point
  all_goals simp only [source,program]
  all_goals (try split_ifs) <;> exact of_decide_eq_true rfl

theorem source_nodes (point : Label) : nodeCount (source (C:=C) point)≤8 := by
  cases point
  all_goals simp only [source,program]
  all_goals (try split_ifs) <;> exact of_decide_eq_true rfl

theorem source_readonly (point : Label) :
    B23_4_RatWordPrep.RawGetter.Readonly (fun memory : Store C => memory.1) (source point) := by
  cases point
  all_goals simp only [source,program]
  all_goals try split_ifs
  all_goals dsimp [B23_4_RatWordPrep.RawGetter.Readonly,capture,clean]
  all_goals repeat' constructor
  all_goals intros;rfl

theorem source_writes (point : Label) : StackIso.WritesOnly Work (source (C:=C) point) := by
  cases point
  all_goals simp only [source,program]
  all_goals try split_ifs
  all_goals simp only [StackIso.WritesOnly,work_field,work_zero,true_and]

def mass (before : Bank) : Nat := ∑ slot : Stack,(before slot).length
def scale (before : Bank) : Nat := mass before+1

theorem point_mass (before : Bank) (slot : Stack) : (before slot).length≤mass before :=
  Finset.single_le_sum (fun other _ => Nat.zero_le ((before other).length)) (Finset.mem_univ slot)

theorem fieldMass_bound (before : Bank) (n : Nat) : fieldMass before n≤n*mass before := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have one:=point_mass before (field (rom n))
    simp only [fieldMass,Nat.succ_mul]
    omega

theorem occupied_bound (before : Bank) (bound : Nat) (bounded : ∀ slot,(before slot).length≤bound) : mass before≤16*bound := by
  calc
    mass before≤∑ _slot : Stack,bound := Finset.sum_le_sum (fun slot _ => bounded slot)
    _=16*bound := by simp

theorem step_resources (before after : State C) (bound : Nat) (edge : TM2.step source before=some after)
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    after.var.1=before.var.1 ∧ (∀ slot,(after.stk slot).length≤bound+4) ∧
      ∀ slot,¬Work slot → after.stk slot=before.stk slot := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (source point) memory contents := (Option.some.inj edge).symm
      subst after
      exact ⟨B23_4_RatWordPrep.RawGetter.nodes_readonly _ _ (source_readonly point) memory contents _ (AuxWorkspace.endpoint_mem _ _ _),
        fun slot => (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans (Nat.add_le_add_left (source_pushes point) bound),
        fun slot outside => StackIso.nodes_frame _ _ (source_writes point) memory contents slot outside _ (AuxWorkspace.endpoint_mem _ _ _)⟩

theorem trace_resources (path : List (State C)) (before : State C) (bound : Nat)
    (first : path.head?=some before) (chain : path.IsChain (fun a b => TM2.step source a=some b))
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    ∀ current∈path,current.var.1=before.var.1 ∧
      (∀ slot,(current.stk slot).length≤bound+4*path.length) ∧ ∀ slot,¬Work slot→current.stk slot=before.stk slot := by
  induction path generalizing before bound with
  | nil => simp
  | cons head tail ih =>
    have same : head=before := Option.some.inj first
    subst head
    cases tail with
    | nil =>
      intro current member
      have same:=List.mem_singleton.mp member
      subst current
      exact ⟨rfl,fun slot => (bounded slot).trans (by simp),fun _ _ => rfl⟩
    | cons next rest =>
      obtain ⟨edge,laterChain⟩:=List.isChain_cons_cons.mp chain
      have step:=step_resources before next bound edge bounded
      have later:=ih next (bound+4) rfl laterChain step.2.1
      intro current member
      rcases List.mem_cons.mp member with rfl | laterMember
      · exact ⟨rfl,fun slot => (bounded slot).trans (Nat.le_add_right _ _),fun _ _ => rfl⟩
      · have facts:=later current laterMember
        refine ⟨facts.1.trans step.1,?_,fun slot outside => (facts.2.2 slot outside).trans (step.2.2 slot outside)⟩
        intro slot
        have small:=facts.2.1 slot
        simp only [List.length_cons] at small ⊢
        omega

def statementClock (current : State C) : Nat := match current.l with
  | none => 0 | some point => ScannerStatement.clock (source point) current.var current.stk
def clockSum (path : List (State C)) : Nat := (path.dropLast.map statementClock).sum

structure Facts (entry exit : Label) (memory : Store C) (before output : Bank) (path : List (State C)) (final : State C) : Prop where
  first : path.head?=some (state entry memory before)
  chain : path.IsChain (fun a b => TM2.step source a=some b)
  last : path.getLast?=some final
  active : final.l=some exit
  contents : final.stk=output
  time : path.length≤32*scale before
  boundaries : ∀ current∈path,current.var.1=memory.1 ∧
    (∀ slot,(current.stk slot).length≤129*scale before) ∧ ∀ slot,¬Work slot→current.stk slot=before slot
  proper : ∀ current∈path.dropLast,Active current

theorem bounded_run (entry exit : Label) (memory finalMemory : Store C) (before output : Bank) (n : Nat)
    (run : Run (state entry memory before) (state exit finalMemory output) n)
    (time : n+1≤32*scale before) :
    ∃ path,Facts entry exit memory before output path (state exit finalMemory output) := by
  obtain ⟨path,first,last,chain,count,proper⟩:=run.witness
  have uniform:=trace_resources path _ (mass before) first chain (point_mass before)
  refine ⟨path,⟨first,chain,last,rfl,rfl,by omega,?_,proper⟩⟩
  intro current member
  have raw:=uniform current member
  refine ⟨raw.1,?_,raw.2.2⟩
  intro slot
  have small:=raw.2.1 slot
  dsimp only [scale] at time ⊢
  omega

theorem Facts.internal {entry exit : Label} {memory : Store C} {before output : Bank} {path : List (State C)} {final : State C}
    (facts : Facts entry exit memory before output path final) (current : State C) (member : current∈path.dropLast)
    (point : Label) (_active : current.l=some point) :
    (∀ node∈AuxWorkspace.nodes (source point) current.var current.stk,node.1.1=memory.1 ∧
      (∀ slot,(node.2 slot).length≤133*scale before) ∧ ∀ slot,¬Work slot→node.2 slot=before slot) ∧
    (AuxWorkspace.nodes (source point) current.var current.stk).length≤8 ∧
    ScannerClock.actions (source (C:=C) point)≤4 ∧ AuxWorkspace.pushes (source (C:=C) point)≤4 ∧
    ScannerStatement.clock (source point) current.var current.stk≤2048*scale before := by
  have boundary:=facts.boundaries current (List.dropLast_subset path member)
  have positive : 0<scale before := by dsimp only [scale];omega
  refine ⟨?_,(nodes_count _ _ _).trans (source_nodes point),source_actions point,source_pushes point,?_⟩
  · intro node inside
    have readonly:=B23_4_RatWordPrep.RawGetter.nodes_readonly _ _ (source_readonly point) current.var current.stk node inside
    refine ⟨readonly.trans boundary.1,?_,fun slot outside =>
      (StackIso.nodes_frame _ _ (source_writes point) current.var current.stk slot outside node inside).trans (boundary.2.2 slot outside)⟩
    intro slot
    have bound:=AuxWorkspace.node_bound (source point) current.var current.stk (129*scale before) boundary.2.1 node inside slot
    have pushes:=source_pushes (C:=C) point
    omega
  · have clock:=ScannerClock.clock_bound (source point) current.var current.stk (129*scale before) boundary.2.1
    have actions:=source_actions (C:=C) point
    have pushes:=source_pushes (C:=C) point
    calc
      ScannerStatement.clock (source point) current.var current.stk≤(2*4)*(129*scale before+4+1) :=
        clock.trans (Nat.mul_le_mul (by omega) (by omega))
      _≤2048*scale before := by omega

theorem Facts.clock_sum {entry exit : Label} {memory : Store C} {before output : Bank} {path : List (State C)} {final : State C}
    (facts : Facts entry exit memory before output path final) : clockSum path≤65536*(scale before)^2 := by
  have terms : ∀ clock∈path.dropLast.map statementClock,clock≤2048*scale before := by
    intro clock member
    obtain ⟨current,inTrace,rfl⟩:=List.mem_map.mp member
    cases active : current.l with
    | none => simp [statementClock,active]
    | some point => simpa only [statementClock,active] using (facts.internal current inTrace point active).2.2.2.2
  have sumBound : clockSum path≤path.dropLast.length*(2048*scale before) := by
    simpa only [clockSum,List.length_map,Nat.nsmul_eq_mul] using List.sum_le_length_nsmul (path.dropLast.map statementClock) (2048*scale before) terms
  have count : path.dropLast.length≤32*scale before := by
    rw [List.length_dropLast]
    exact (Nat.sub_le path.length 1).trans facts.time
  calc
    clockSum path≤(32*scale before)*(2048*scale before) := sumBound.trans (Nat.mul_le_mul_right _ count)
    _=65536*(scale before)^2 := by ring

theorem Facts.charged {entry exit : Label} {memory : Store C} {before output : Bank} {path : List (State C)} {final : State C}
    (facts : Facts entry exit memory before output path final) : path.length+clockSum path≤65568*(scale before)^2 := by
  have positive : 1≤scale before := by dsimp only [scale];omega
  have power : scale before≤(scale before)^2 := by nlinarith
  exact (Nat.add_le_add (facts.time.trans (Nat.mul_le_mul_left 32 power)) facts.clock_sum).trans (by omega)
end RootB234.StageStash
