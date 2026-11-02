module
public import RootB234_Cells_Code_001

/-! Resources of the very same physical cell trace. Time counts the real
empty pop and is independent of the old destination/background mass. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.Cells
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM
variable {C : Type*}

def Work (op : Operation) (slot : Stack) : Prop :=
  slot=source op ∨ moving op=true ∧ slot=destination op
instance (op : Operation) (slot : Stack) : Decidable (Work op slot) := by unfold Work;infer_instance
def writesDecidable (op : Operation) : (statement : Statement C) → Decidable (StackIso.WritesOnly (Work op) statement)
  | .push slot _ tail | .pop slot _ tail => by
      change Decidable (Work op slot ∧ StackIso.WritesOnly (Work op) tail)
      letI:=writesDecidable op tail
      infer_instance
  | .peek _ _ tail | .load _ tail => writesDecidable op tail
  | .branch _ yes no => by
      change Decidable (StackIso.WritesOnly (Work op) yes ∧ StackIso.WritesOnly (Work op) no)
      letI:=writesDecidable op yes
      letI:=writesDecidable op no
      infer_instance
  | .goto _ | .halt => isTrue trivial
local instance (op : Operation) (statement : Statement C) : Decidable (StackIso.WritesOnly (Work op) statement) :=
  writesDecidable op statement

theorem program_writes (op : Operation) (point : Label) :
    StackIso.WritesOnly (Work op) (program (C:=C) op .halt point) := by
  cases op <;> fin_cases point <;> exact of_decide_eq_true rfl
theorem program_actions (op : Operation) (point : Label) :
    ScannerClock.actions (program (C:=C) op .halt point)≤2 := by
  cases op <;> fin_cases point <;> exact of_decide_eq_true rfl
theorem program_pushes (op : Operation) (point : Label) :
    AuxWorkspace.pushes (program (C:=C) op .halt point)≤1 := by
  cases op <;> fin_cases point <;> exact of_decide_eq_true rfl
theorem program_readonly (op : Operation) (point : Label) :
    B23_4_RatWordPrep.RawGetter.Readonly (fun memory : Store C => memory.1) (program op .halt point) := by
  cases op <;> fin_cases point
  all_goals
    dsimp [program,body,entry,moving,roles,rawProgram,RuntimeCounter.Builder.program,
      RuntimeCounter.Builder.eraseBody,RatPacketTransport.program,RatPacketTransport.keepSource,
      StackIso.statement,B23_4_RatWordPrep.RawGetter.Readonly,RatDrop.capture,RatDrop.bit]
    repeat' constructor
    all_goals (intros;rfl)

theorem step_resources (op : Operation) (before after : State C) (bound : Nat)
    (edge : TM2.step (program op .halt) before=some after)
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    after.var.1=before.var.1 ∧ (∀ slot,(after.stk slot).length≤bound+1) ∧
      ∀ slot,¬Work op slot→after.stk slot=before.stk slot := by
  cases before with
  | mk position memory contents =>
    cases position with
    | none => cases edge
    | some point =>
      have same : after=TM2.stepAux (program op .halt point) memory contents := (Option.some.inj edge).symm
      subst after
      refine ⟨B23_4_RatWordPrep.RawGetter.nodes_readonly (fun v : Store C => v.1) _
        (program_readonly op point) memory contents _ (AuxWorkspace.endpoint_mem _ _ _),?_,?_⟩
      · intro slot
        exact (AuxWorkspace.endpoint_bound _ _ _ bound bounded slot).trans
          (Nat.add_le_add_left (program_pushes op point) bound)
      · intro slot untouched
        exact StackIso.nodes_frame _ _ (program_writes op point) memory contents slot untouched
          _ (AuxWorkspace.endpoint_mem _ _ _)

theorem trace_resources (op : Operation) (path : List (State C)) (before : State C) (bound : Nat)
    (first : path.head?=some before)
    (chain : path.IsChain (fun a b => TM2.step (program op .halt) a=some b))
    (bounded : ∀ slot,(before.stk slot).length≤bound) :
    ∀ current∈path,current.var.1=before.var.1 ∧
      (∀ slot,(current.stk slot).length≤bound+path.length) ∧
      ∀ slot,¬Work op slot→current.stk slot=before.stk slot := by
  induction path generalizing before bound with
  | nil => simp
  | cons start rest ih =>
    have same : start=before := Option.some.inj first
    subst start
    cases rest with
    | nil =>
      intro current member
      have equal:=List.mem_singleton.mp member
      subst current
      exact ⟨rfl,fun slot => (bounded slot).trans (Nat.le_add_right _ _),fun _ _ => rfl⟩
    | cons next rest =>
      obtain ⟨edge,later⟩:=List.isChain_cons_cons.mp chain
      have step:=step_resources op before next bound edge bounded
      intro current member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨rfl,fun slot => (bounded slot).trans (Nat.le_add_right _ _),fun _ _ => rfl⟩
      · have tail:=ih next (bound+1) rfl later step.2.1 current member
        refine ⟨tail.1.trans step.1,?_,?_⟩
        · intro slot
          have h:=tail.2.1 slot
          simp only [List.length_cons] at h ⊢
          omega
        · intro slot untouched
          exact (tail.2.2 slot untouched).trans (step.2.2 slot untouched)

def scale (before : Stack → List Bool) : Nat := RatInput.occupied before+1

structure Facts (op : Operation) (memory : Store C) (before : Stack → List Bool) (path : List (State C)) : Prop where
  first : path.head?=some (initial op memory before)
  chain : path.IsChain (fun a b => TM2.step (program op .halt) a=some b)
  last : path.getLast?=some (result op memory.1 before)
  count : path.length=(before (source op)).length+2
  time : path.length≤2*scale before
  boundaries : ∀ current∈path,current.var.1=memory.1 ∧
    (∀ slot,(current.stk slot).length≤3*scale before) ∧
    RatInput.occupied current.stk≤48*scale before ∧
    ∀ slot,¬Work op slot→current.stk slot=before slot
  proper : ∀ current∈path.dropLast,current.l=some (entry op) ∧
    ∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (program op .halt point) current.var current.stk,
        node.1.1=memory.1 ∧
        (∀ slot,(node.2 slot).length≤4*scale before) ∧
        RatInput.occupied node.2≤64*scale before ∧
        ∀ slot,¬Work op slot→node.2 slot=before slot) ∧
      ScannerStatement.clock (program op .halt point) current.var current.stk≤20*scale before

theorem actual_bounded (op : Operation) (memory : Store C) (before : Stack → List Bool) :
    Facts op memory before (trace op memory before) := by
  let path:=trace op memory before
  let M:=RatInput.occupied before
  let S:=scale before
  have count:=trace_length op memory before
  have sourceRoom : (before (source op)).length≤M := RatInput.Encoder.point_mass before (source op)
  have positive : 1≤S := by dsimp [S,scale];omega
  have short : path.length≤2*S := by dsimp only [path];dsimp only [S,scale,M] at *;omega
  have resources:=trace_resources op path (initial op memory before) M (trace_head _ _ _)
    (trace_chain op .halt memory before) (RatInput.Encoder.point_mass before)
  have bounded : ∀ current∈path,∀ slot,(current.stk slot).length≤3*S := by
    intro current member slot
    have bound:=(resources current member).2.1 slot
    dsimp only [S,scale,M] at *
    omega
  refine ⟨trace_head _ _ _,trace_chain op .halt memory before,trace_last _ _ _,count,short,?_,?_⟩
  · intro current member
    refine ⟨(resources current member).1,bounded current member,?_,(resources current member).2.2⟩
    have mass:=RatInput.Encoder.occupied_bound current.stk (3*S) (bounded current member)
    omega
  · intro current member
    refine ⟨trace_proper op memory before current member,?_⟩
    intro point selected
    have present:=List.mem_of_mem_dropLast member
    have currentBound:=bounded current present
    refine ⟨?_,?_⟩
    · intro node internal
      have nodeBound : ∀ slot,(node.2 slot).length≤4*S := by
        intro slot
        have cap:=(AuxWorkspace.node_bound (program op .halt point) current.var current.stk (3*S)
          currentBound node internal slot).trans (Nat.add_le_add_left (program_pushes op point) (3*S))
        omega
      refine ⟨(B23_4_RatWordPrep.RawGetter.nodes_readonly (fun v : Store C => v.1) _
        (program_readonly op point) current.var current.stk node internal).trans
        (resources current present).1,nodeBound,?_,?_⟩
      · have mass:=RatInput.Encoder.occupied_bound node.2 (4*S) nodeBound
        omega
      · intro slot untouched
        exact (StackIso.nodes_frame (Work op) _ (program_writes op point) current.var current.stk
          slot untouched node internal).trans ((resources current present).2.2 slot untouched)
    · have clock:=ScannerClock.clock_bound (program op .halt point) current.var current.stk (3*S) currentBound
      have cap:=clock.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (program_actions op point))
        (Nat.add_le_add_right (Nat.add_le_add_left (program_pushes op point) (3*S)) 1))
      omega

def statementClock (op : Operation) (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (program op .halt point) current.var current.stk
def clockSum (op : Operation) (path : List (State C)) : Nat :=
  (path.dropLast.map (statementClock op)).sum
def chargedCost (op : Operation) (path : List (State C)) : Nat := path.length+clockSum op path

theorem clockSum_le {op : Operation} {memory : Store C} {before : Stack → List Bool} {path : List (State C)}
    (facts : Facts op memory before path) : clockSum op path≤40*(scale before)^2 := by
  have term : ∀ value∈path.dropLast.map (statementClock op),value≤20*scale before := by
    intro value member
    obtain ⟨current,present,rfl⟩:=List.mem_map.mp member
    cases selected : current.l with
    | none => simp only [statementClock,selected,Nat.zero_le]
    | some point =>
      simp only [statementClock,selected]
      exact ((facts.proper current present).2 point selected).2
  have sum : clockSum op path≤path.dropLast.length*(20*scale before) := by
    simpa only [clockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (path.dropLast.map (statementClock op)) (20*scale before) term
  have count : path.dropLast.length≤2*scale before := by
    rw [List.length_dropLast]
    exact (Nat.sub_le path.length 1).trans facts.time
  exact (sum.trans (Nat.mul_le_mul_right (20*scale before) count)).trans_eq (by ring)

theorem chargedCost_le {op : Operation} {memory : Store C} {before : Stack → List Bool} {path : List (State C)}
    (facts : Facts op memory before path) : chargedCost op path≤42*(scale before)^2 := by
  have positive : 1≤scale before := by unfold scale;omega
  have square : scale before≤(scale before)^2 := by nlinarith
  have time:=facts.time
  have sum:=clockSum_le facts
  unfold chargedCost
  nlinarith

end RootB234.Cells
