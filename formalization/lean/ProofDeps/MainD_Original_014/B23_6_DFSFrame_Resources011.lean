module
public import B23_6_DFSFrame_Structure010

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace B23_6.DFSFrame
open Turing PaperProofs.Common.Native.PSTRWordBool
variable {C : Type*}

def scale (before : Bank) : Nat := RatInput.occupied before+1
def statementClock (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (source point) current.var current.stk
def clockSum (path : List (State C)) : Nat := (path.dropLast.map statementClock).sum
def chargedCost (path : List (State C)) : Nat := path.length+clockSum path

structure Facts (entry exit : Label) (memory : Store C) (before output : Bank) (path : List (State C)) : Prop where
  first : path.head?=some (state entry memory before)
  chain : path.IsChain (fun a b => TM2.step source a=some b)
  last : path.getLast?=some (state exit (clean memory) output)
  time : path.length≤51*scale before
  boundaries : ∀ current∈path,current.var.1=memory.1 ∧
    (∀ slot,(current.stk slot).length≤155*scale before) ∧ RatInput.occupied current.stk≤2480*scale before
  proper : ∀ current∈path.dropLast,Active current ∧ ∀ point,current.l=some point→
    (∀ node∈AuxWorkspace.nodes (source point) current.var current.stk,node.1.1=memory.1 ∧
      (∀ slot,(node.2 slot).length≤160*scale before) ∧ RatInput.occupied node.2≤2560*scale before) ∧
    ScannerStatement.clock (source point) current.var current.stk≤1280*scale before

theorem bounded_run (entry exit : Label) (memory : Store C) (before output : Bank) (n : Nat)
    (run : Run (state entry memory before) (state exit (clean memory) output) n) (short : n≤50*scale before) :
    ∃ path,Facts entry exit memory before output path ∧ path.length=n+1 := by
  obtain ⟨path,first,last,chain,count,proper⟩:=run.witness
  let S:=scale before
  let M:=RatInput.occupied before
  have positive : 1≤S:=by dsimp [S,scale];omega
  have time : path.length≤51*S:=by dsimp [S] at *;omega
  have resources:=trace_resources path (state entry memory before) M first chain (RatInput.Encoder.point_mass before)
  have bounds : ∀ current∈path,∀ slot,(current.stk slot).length≤155*S := by
    intro current member slot
    have bound:=(resources current member).2 slot
    dsimp only [M,S,scale] at *
    omega
  refine ⟨path,⟨first,chain,last,time,?_,?_⟩,count⟩
  · intro current member
    refine ⟨(resources current member).1,bounds current member,?_⟩
    have mass:=RatInput.Encoder.occupied_bound current.stk (155*S) (bounds current member)
    omega
  · intro current member
    refine ⟨proper current member,?_⟩
    intro point selected
    have present:=List.mem_of_mem_dropLast member
    have currentBound:=bounds current present
    refine ⟨?_,?_⟩
    · intro node internal
      have nodeBound : ∀ slot,(node.2 slot).length≤160*S := by
        intro slot
        have cap:=(AuxWorkspace.node_bound (source point) current.var current.stk (155*S) currentBound node internal slot).trans
          (Nat.add_le_add_left (source_pushes point) (155*S))
        omega
      refine ⟨(B23_4_RatWordPrep.RawGetter.nodes_readonly (fun v : Store C => v.1) _
        (source_readonly point) current.var current.stk node internal).trans (resources current present).1,nodeBound,?_⟩
      have mass:=RatInput.Encoder.occupied_bound node.2 (160*S) nodeBound
      omega
    · have clock:=ScannerClock.clock_bound (source point) current.var current.stk (155*S) currentBound
      have cap:=clock.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (source_actions point))
        (Nat.add_le_add_right (Nat.add_le_add_left (source_pushes point) (155*S)) 1))
      omega

theorem clockSum_le {entry exit : Label} {memory : Store C} {before output : Bank} {path : List (State C)}
    (facts : Facts entry exit memory before output path) : clockSum path≤65536*(scale before)^2 := by
  have term : ∀ value∈path.dropLast.map statementClock,value≤1280*scale before := by
    intro value member
    obtain ⟨current,present,rfl⟩:=List.mem_map.mp member
    cases selected : current.l with
    | none => simp only [statementClock,selected,Nat.zero_le]
    | some point =>
      simp only [statementClock,selected]
      exact ((facts.proper current present).2 point selected).2
  have sum : clockSum path≤path.dropLast.length*(1280*scale before) := by
    simpa only [clockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (path.dropLast.map statementClock) (1280*scale before) term
  have count : path.dropLast.length≤51*scale before := by
    rw [List.length_dropLast]
    exact (Nat.sub_le path.length 1).trans facts.time
  have total:=sum.trans (Nat.mul_le_mul_right (1280*scale before) count)
  nlinarith

theorem chargedCost_le {entry exit : Label} {memory : Store C} {before output : Bank} {path : List (State C)}
    (facts : Facts entry exit memory before output path) : chargedCost path≤65600*(scale before)^2 := by
  have positive : 1≤scale before:=by unfold scale;omega
  have clock:=clockSum_le facts
  have time:=facts.time
  unfold chargedCost
  nlinarith

end B23_6.DFSFrame
