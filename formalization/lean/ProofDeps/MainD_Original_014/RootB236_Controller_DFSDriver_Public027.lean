module
public import RootB236_Controller_DFSDriver_Mass026

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver.Machine
open Turing RootB23.GenericRank PaperProofs.Structure
open PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
open scoped BigOperators
variable {C : Type*}
attribute [local irreducible] pushProfile actionProfile nodeProfile

def spaceCoefficient (C : Type*) : Nat := 64+266240*pushProfile C
def timeCoefficient : Nat := 4259840
def clockCoefficient (C : Type*) : Nat := 2*actionProfile C*(spaceCoefficient C+pushProfile C+1)
def chargeCoefficient (C : Type*) : Nat := (timeCoefficient+1)*(clockCoefficient C+1)

private theorem space_algebra (push x : Nat) (positive : 1≤x) :
    64*x+push*(4096*(64*x+1))≤(64+266240*push)*x := by
  have reserve:=Nat.mul_le_mul_left (4096*push) positive
  nlinarith
private theorem time_algebra (x : Nat) (positive : 1≤x) : 16*(4096*(64*x+1))≤4259840*x := by omega
private theorem clock_algebra (action push width coefficient x : Nat) (positive : 1≤x) (bounded : width≤coefficient*x) :
    2*action*(width+push+1)≤(2*action*(coefficient+push+1))*x := by
  have reserve:=Nat.mul_le_mul_left (push+1) positive
  have localBound : width+push+1≤(coefficient+push+1)*x := by nlinarith
  calc
    2*action*(width+push+1)≤2*action*((coefficient+push+1)*x) := Nat.mul_le_mul_left (2*action) localBound
    _=(2*action*(coefficient+push+1))*x := by ring
private theorem product_algebra (first second a b x : Nat) (positive : 1≤x)
    (one : first≤a*x) (two : second≤b*x) : (first+1)*(second+1)≤((a+1)*(b+1))*x^2 := by
  have h1 : first+1≤(a+1)*x := by nlinarith
  have h2 : second+1≤(b+1)*x := by nlinarith
  calc
    (first+1)*(second+1)≤((a+1)*x)*((b+1)*x) := Nat.mul_le_mul h1 h2
    _=((a+1)*(b+1))*x^2 := by ring

/-- Explicit fixed coefficients: source workspace and per-step clock are quadratic in actual entry mass; aggregate charge has one F. -/
theorem resource_polynomials (inputMass : Nat) :
    workspace C inputMass≤spaceCoefficient C*(inputMass+1)^2 ∧
    duration inputMass≤timeCoefficient*(inputMass+1)^2 ∧
    clockEnvelope C inputMass≤clockCoefficient C*(inputMass+1)^2 ∧
    (duration inputMass+1)*(clockEnvelope C inputMass+1)≤chargeCoefficient C*(inputMass+1)^4 := by
  have positive : 1≤(inputMass+1)^2 := Nat.one_le_pow 2 _ (by omega)
  have width : workspace C inputMass≤spaceCoefficient C*(inputMass+1)^2 :=
    space_algebra (pushProfile C) ((inputMass+1)^2) positive
  have time : duration inputMass≤timeCoefficient*(inputMass+1)^2 := time_algebra _ positive
  have clock : clockEnvelope C inputMass≤clockCoefficient C*(inputMass+1)^2 :=
    clock_algebra (actionProfile C) (pushProfile C) (workspace C inputMass) (spaceCoefficient C) _ positive width
  refine ⟨width,time,clock,?_⟩
  have product:=product_algebra (duration inputMass) (clockEnvelope C inputMass) timeCoefficient (clockCoefficient C) _ positive time clock
  simpa only [chargeCoefficient,←pow_mul] using product

def Internal (finish : Statement C) (inputMass : Nat) (context : C) (current : State C) : Prop :=
  ∀ point,current.l=some point →
    (∀ node∈AuxWorkspace.nodes (program finish point) current.var current.stk,node.1.1=context ∧
      (∀ slot,(node.2 slot).length≤workspace C inputMass+pushProfile C) ∧
      (∑ slot : Stack,(node.2 slot).length)≤16*(workspace C inputMass+pushProfile C)) ∧
    (AuxWorkspace.nodes (program finish point) current.var current.stk).length≤nodeProfile C ∧
    ScannerClock.actions (program finish point)≤actionProfile C ∧ AuxWorkspace.pushes (program finish point)≤pushProfile C ∧
    ScannerStatement.clock (program finish point) current.var current.stk≤clockEnvelope C inputMass

structure Facts (finish : Statement C) (limit q : Nat) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q))
    (memory : Store C) (before : Stack → List Bool) (tail : List Bool) (trace : List (State C)) (final : State C) : Prop where
  first : trace.head?=some (state start memory before)
  chain : trace.IsChain (fun x y => TM2.step (program finish) x=some y)
  last : trace.getLast?=some final
  active : final.l=some (returnPort tail)
  rank : final.stk 15=unary (rankCode limit (genericRank stages remaining))
  bestFlag : final.stk 13=(originalPick q stages remaining).isSome::tail
  firstTool : final.stk 14=pickBits (originalPick q stages remaining)
  archive : final.stk 1=before 1
  limit_saved : final.stk 2=unary (limit+1)
  remaining_saved : final.stk 4=EraseSem.mask remaining
  width_saved : final.stk 11=unary q
  time : trace.length≤(duration (mass before)+1)*structuralFactor stages.length q
  proper : ∀ current∈trace.dropLast,current.l≠some done
  boundaries : ∀ current∈trace,current.var.1=memory.1 ∧
    (∀ slot,(current.stk slot).length≤workspace C (mass before)) ∧
    (∑ slot : Stack,(current.stk slot).length)≤16*workspace C (mass before)
  internal : ∀ current∈trace.dropLast,Internal finish (mass before) memory.1 current
  clock_sum : clockSum finish trace≤duration (mass before)*clockEnvelope C (mass before)*structuralFactor stages.length q
  charged : trace.length+clockSum finish trace≤
    (duration (mass before)+1)*(clockEnvelope C (mass before)+1)*structuralFactor stages.length q

theorem Facts.decoded_rank {finish : Statement C} {limit q : Nat} {stages : List (Finset (Fin q))} {remaining : Finset (Fin q)}
    {memory : Store C} {before : Stack → List Bool} {tail : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts finish limit q stages remaining memory before tail trace final) (depth : stages.length≤limit) :
    decodeRank limit (final.stk 15).length=genericRank stages remaining := by
  rw [facts.rank]
  simp only [unary,RankCompare.unary,List.length_replicate]
  exact (rank_code_correct limit _ ((RankMerge.generic_rank_bound q stages remaining).mono depth)).1

namespace Public
/-- One concrete source run simultaneously carries original semantics, exact stable ABI and all-prefix resources. -/
theorem actual (finish : Statement C) (limit q : Nat) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q))
    (depth : stages.length≤limit) (memory : Store C) (before : Stack → List Bool) (flag : Bool) (tail : List Bool)
    (r0 : before 0=rows q stages) (r2 : before 2=unary (limit+1)) (r4 : before 4=EraseSem.mask remaining)
    (r11 : before 11=unary q) (r13 : before 13=flag::tail) :
    ∃ trace final,Facts finish limit q stages remaining memory before tail trace final := by
  obtain ⟨steps,final,run,reply,rank,bestFlag,firstTool,time⟩:=measured_original finish limit q stages remaining depth memory before flag tail r0 r2 r4 r11 r13
  obtain ⟨trace,first,chain,last,count,proper,boundaries,internal,clocks,charge⟩:=run.clocked
  have factor : 1≤structuralFactor stages.length q := (evaluate_nodes_pos q stages remaining).trans (evaluate_nodes_one_factor q stages remaining)
  have lengthBound : trace.length≤(duration (mass before)+1)*structuralFactor stages.length q := by
    rw [count,Nat.add_mul,Nat.one_mul]
    omega
  refine ⟨trace,final,⟨first,chain,last,reply.active,rank,bestFlag,firstTool,reply.archive,
    reply.limit_saved,reply.remaining_saved,reply.width_saved,lengthBound,proper,?_,internal,?_,?_⟩⟩
  · intro current member
    have boundary:=boundaries current member
    refine ⟨boundary.1,boundary.2,?_⟩
    exact occupied_le current.stk (workspace C (mass before)) boundary.2
  · change clockSum finish trace≤duration (mass before)*(2*actionProfile C*(workspace C (mass before)+pushProfile C+1))*structuralFactor stages.length q
    exact clocks.trans ((Nat.mul_le_mul_right _ time).trans (by rw [Nat.mul_right_comm]))
  · change trace.length+clockSum finish trace≤(duration (mass before)+1)*
      (2*actionProfile C*(workspace C (mass before)+pushProfile C+1)+1)*structuralFactor stages.length q
    have countBound : steps+1≤(duration (mass before)+1)*structuralFactor stages.length q := by rw [←count];exact lengthBound
    exact charge.trans ((Nat.mul_le_mul_right _ countBound).trans (by rw [Nat.mul_right_comm]))

/-- Root stop is an ACTIVE caller port. No caller instruction is charged or reset for free. -/
theorem root (finish : Statement C) (limit q : Nat) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q))
    (depth : stages.length≤limit) (memory : Store C) (before : Stack → List Bool)
    (r0 : before 0=rows q stages) (r2 : before 2=unary (limit+1)) (r4 : before 4=EraseSem.mask remaining)
    (r11 : before 11=unary q) (r13 : before 13=[false]) :
    ∃ trace final,Facts finish limit q stages remaining memory before [] trace final ∧ final.l=some done := by
  obtain ⟨trace,final,facts⟩:=actual finish limit q stages remaining depth memory before false [] r0 r2 r4 r11 r13
  exact ⟨trace,final,facts,facts.active⟩

theorem label_count : Fintype.card Label=199 := by decide

theorem store_card (C : Type*) [Fintype C] : Fintype.card (Store C)=12*Fintype.card C := by
  change Fintype.card (C×(Bool×Bool×Ordering))=12*Fintype.card C
  simp only [Fintype.card_prod,Fintype.card_bool]
  rw [show Fintype.card Ordering=3 by decide]
  omega

/-- Literal program/support/store are chosen before any N,q,mask,history-derived staged data or counters. -/
theorem fixed_source (C : Type*) [Fintype C] :
    ∃ (fixed : Label → Statement C) (support : Finset Label),fixed=source ∧ support.card=199 ∧
      TM2.Supports fixed support ∧ Fintype.card (Store C)=12*Fintype.card C ∧
      ∀ (limit q : Nat) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q)),stages.length≤limit →
      ∀ (memory : Store C) (before : Stack → List Bool),before 0=rows q stages → before 2=unary (limit+1) →
      before 4=EraseSem.mask remaining → before 11=unary q → before 13=[false] →
      ∃ trace final,Facts .halt limit q stages remaining memory before [] trace final ∧ final.l=some done := by
  exact ⟨source,Finset.univ,rfl,by simpa using label_count,supports .halt,store_card C,root .halt⟩

/-- Real static caller splice for the entire same source path; none remains none under LabelMap. -/
theorem caller_actual {finish : Statement C} {limit q : Nat} {stages : List (Finset (Fin q))} {remaining : Finset (Fin q)}
    {memory : Store C} {before : Stack → List Bool} {tail : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts finish limit q stages remaining memory before tail trace final)
    {Ω : Type*} (mapping : Label → Ω) (caller : Ω → TM2.Stmt Alphabet Ω (Store C))
    (agrees : ∀ point,point≠done → caller (mapping point)=LabelMap.statement mapping (program finish point)) :
    (trace.map (LabelMap.configuration mapping)).head?=some (LabelMap.configuration mapping (state start memory before)) ∧
    (trace.map (LabelMap.configuration mapping)).IsChain (fun x y => TM2.step caller x=some y) ∧
    (trace.map (LabelMap.configuration mapping)).getLast?=some (LabelMap.configuration mapping final) ∧
    (trace.map (LabelMap.configuration mapping)).length=trace.length ∧
    ∀ current∈trace.map (LabelMap.configuration mapping),∃ old∈trace,current=LabelMap.configuration mapping old ∧ current.var=old.var ∧ current.stk=old.stk := by
  exact LabelMap.actual_path_on mapping (program finish) caller trace _ _ facts.first facts.chain facts.last
    (by intro current member point active;exact agrees point (by intro same;subst point;exact facts.proper current member active))
theorem caller_noearly {finish : Statement C} {limit q : Nat} {stages : List (Finset (Fin q))} {remaining : Finset (Fin q)}
    {memory : Store C} {before : Stack → List Bool} {tail : List Bool} {trace : List (State C)} {final : State C}
    (facts : Facts finish limit q stages remaining memory before tail trace final)
    {Ω : Type*} (mapping : Label ↪ Ω) :
    ∀ current∈(trace.map (LabelMap.configuration mapping)).dropLast,current.l≠some (mapping done) := by
  intro current member
  rw [←List.map_dropLast] at member
  obtain ⟨old,inTrace,rfl⟩:=List.mem_map.mp member
  change old.l.map mapping≠some (mapping done)
  cases active : old.l with
  | none => rw [Option.map_none];intro impossible;cases impossible
  | some point =>
    rw [Option.map_some]
    intro same
    have pointSame : point=done := mapping.injective (Option.some.inj same)
    exact facts.proper old inTrace (active.trans (congrArg some pointSame))
end Public
end RootB236.Controller.DFSDriver.Machine
