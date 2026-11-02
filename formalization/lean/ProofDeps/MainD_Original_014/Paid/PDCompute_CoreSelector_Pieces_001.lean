module
public import Paid.RootD27Core_SelectorZero_084

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000
@[expose] public section
namespace PDCompute.CoreSelector
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open PDLower.CoreSearch RootD27.Core PDCompute.CoreSearchLoop

/-- Small SAME-witness packaging used ONLY to assemble the actual180
selector. The actual state chain, not a resource-only witness, is stored. -/
structure Piece (program : Program) (input : List Cell) (P : Parameters) (fee : ℚ)
    (source : MultiplierState) (budget low high : ℕ) (before after : State) (cost : ℕ) where
  trace : List State
  head : trace.head?=some before
  last : trace.getLast?=some after
  chain : trace.IsChain (fun first later=>step program input first=some later)
  time : time program trace≤cost
  ready : Ready P fee after
  represented : SearchStateRep P fee after source
  counter : after.heap 28=before.heap 28
  output : after.output=before.output
  properties : ∀ state∈trace,RegionMemory before state scalarRegion ∧ RootD27.Bits.SafeBits state budget
  scope : ∀ state∈trace,low≤state.pc ∧ state.pc≤high
  proper : ∀ state∈trace.dropLast,state.pc<high

variable {program : Program} {input : List Cell} {P : Parameters} {fee : ℚ}
  {source : MultiplierState} {budget low high : ℕ} {before middle after : State} {c d : ℕ}

theorem ready_after_scalar (ready : Ready P fee before)
    (header : Header after 0 (fun slot=>after.heap slot)) (fresh : after.register .fresh=.natural 0)
    (memory : RegionMemory before after scalarRegion) : Ready P fee after := by
  refine ⟨header,fresh,?_,?_⟩
  · apply memory.heapList ready.prepared
    intro offset inside
    change offset<13 at inside
    simp only [scalarRegion,Finset.mem_Icc]
    omega
  · apply memory.heapList ready.cache
    intro offset _inside
    simp only [scalarRegion,Finset.mem_Icc]
    omega

def Piece.of_trace (trace : List State) (head : trace.head?=some before) (last : trace.getLast?=some after)
    (chain : trace.IsChain (fun first later=>step program input first=some later)) (cost : PaperProofs.Paid.Computation.time program trace≤c)
    (ready : Ready P fee before) (header : Header after 0 (fun slot=>after.heap slot))
    (fresh : after.register .fresh=.natural 0) (represented : SearchStateRep P fee after source)
    (counter : after.heap 28=before.heap 28) (output : after.output=before.output)
    (properties : ∀ state∈trace,RegionMemory before state scalarRegion ∧ RootD27.Bits.SafeBits state budget)
    (scope : ∀ state∈trace,low≤state.pc ∧ state.pc≤high) (proper : ∀ state∈trace.dropLast,state.pc<high) :
    Piece program input P fee source budget low high before after c := by
  have memory:=(properties after (List.mem_of_getLast? last)).1
  exact ⟨trace,head,last,chain,cost,ready_after_scalar ready header fresh memory,represented,
    counter,output,properties,scope,proper⟩

def Piece.join (first : Piece program input P fee source budget low high before middle c)
    (later : Piece program input P fee source budget low high middle after d) :
    Piece program input P fee source budget low high before after (c+d) := by
  have joined:=joinTrace_spec program input first.trace later.trace before middle after c d
    first.head first.last later.head later.last first.chain later.chain first.time later.time
  have memory:=RegionMemory.join_trace first.trace later.trace before middle scalarRegion first.last
    (fun state member=>(first.properties state member).1) (fun state member=>(later.properties state member).1)
  have bits:=PDCompute.Pack.joinTrace_invariant first.trace later.trace
    (fun state=>RootD27.Bits.SafeBits state budget)
    (fun state member=>(first.properties state member).2) (fun state member=>(later.properties state member).2)
  have nonempty : later.trace≠[]:=by
    intro empty
    have head:=later.head
    simp only [empty,List.head?_nil,reduceCtorEq] at head
  refine ⟨joinTrace first.trace later.trace,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    later.ready,later.represented,later.counter.trans first.counter,later.output.trans first.output,
    (fun state member=>⟨memory state member,bits state member⟩),?_,?_⟩
  · exact PDCompute.Pack.joinTrace_invariant first.trace later.trace _ first.scope later.scope
  · intro state member
    change state∈(first.trace.dropLast++later.trace).dropLast at member
    rw [List.dropLast_append_of_ne_nil nonempty] at member
    rcases List.mem_append.mp member with early|late
    · exact first.proper state early
    · exact later.proper state late

def Piece.bound (piece : Piece program input P fee source budget low high before after c) (larger : c≤d) :
    Piece program input P fee source budget low high before after d :=
  {piece with time:=piece.time.trans larger}

end PDCompute.CoreSelector
