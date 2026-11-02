module

public import Paid.PDCompute_CoreSearchLoop_Code_001
public import Paid.PDROC_CalibrationRow_OperandPrefix_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

@[expose] public section

namespace PDCompute.CoreSearchLoop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver hiding HeapList
open PDMenu.ComputeFrame PDROC.CalibrationRow.Operand PDROC.DataBits
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult storeSlot)

def decrementResult (before : State) (remaining : ℕ) : State :=
  {before with
    register:=Function.update (Function.update (Function.update before.register .address (.natural 28))
      .flag (.natural 1)) .index (.natural remaining)
    heap:=Function.update before.heap 28 (.natural remaining)
    live:=insert 28 before.live
    pc:=before.pc+8}

theorem decrement_straight : StraightCode decrementCode := by
  intro instruction member
  simp only [decrementCode,loadSlot,storeSlot,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((h|h|h)|(h|h))|(h|h|h) <;> subst instruction <;> trivial

theorem decrement_execute (input : List Cell) (before : State) (remaining : ℕ)
    (fresh : before.register .fresh=.natural 0) (live : 28∈before.live)
    (counter : before.heap 28=.natural (remaining+1)) :
    linearExecute input decrementCode before=some (decrementResult before remaining) := by
  simp [decrementCode,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
    fresh,live,counter,decrementResult,Nat.add_assoc]
  funext register
  cases register <;> simp

theorem decrement_prefix_memory (input : List Cell) (before after : State) (remaining count : ℕ)
    (fresh : before.register .fresh=.natural 0) (live : 28∈before.live)
    (counter : before.heap 28=.natural (remaining+1)) (short : count<8)
    (run : linearExecute input (decrementCode.take count) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  interval_cases count <;>
    simp [decrementCode,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
      fresh,live,counter] at run <;> subst after <;> exact ⟨rfl,rfl,rfl⟩

theorem decrement_prefix_safe (input : List Cell) (before : State) (remaining budget : ℕ)
    (header : Header before 0 (fun slot=>before.heap slot)) (fresh : before.register .fresh=.natural 0)
    (counter : before.heap 28=.natural (remaining+1)) (safe : RootD27.Bits.SafeBits before budget)
    (room : 7≤budget) (pcBits : natBits (before.pc+8)≤budget) :
    PrefixSafe input decrementCode before budget := by
  let loaded:=loadSlotResult before 0 28 .index
  let constant:=({loaded with pc:=loaded.pc+1}).set .flag (.natural 1)
  let subtracted:=({constant with pc:=constant.pc+1}).set .index (.natural remaining)
  have live : 28∈before.live:=by simpa only [Nat.zero_add] using header.live 28 (by decide)
  have addressBits : 1+natBits (0+28)≤budget:=(by decide : 1+natBits (0+28)≤7).trans room
  have oneBits : (.natural 1 : Cell).bits≤budget:=(by decide : (.natural 1 : Cell).bits≤7).trans room
  have loadRun:=(header.loadSlot_execute input 28 .index (by decide) fresh).1
  have loadSafe:=PrefixSafe.loadSlot input before 0 28 budget .index safe fresh
    (header.live 28 (by decide)) addressBits ((natBits_mono (by omega : before.pc+3≤before.pc+8)).trans pcBits)
  have loadedSafe:=loadSafe.final loadRun
  have constantRun : Instruction.execute input (.constant .flag (.natural 1)) loaded=some constant:=rfl
  have constantSafe:=PDCompute.Pack.constant_execute_safe input loaded constant .flag (.natural 1) budget loadedSafe oneBits
    ((natBits_mono (by change before.pc+3+1≤before.pc+8;omega)).trans pcBits) constantRun
  have loadedIndex : loaded.register .index=.natural (remaining+1):=by
    simpa only [loaded,loadSlotResult,State.set,Function.update_self,Nat.zero_add] using counter
  have constantIndex : constant.register .index=.natural (remaining+1):=by
    simpa only [constant,State.set,Function.update_of_ne (by decide : (.index : Register)≠.flag)] using loadedIndex
  have constantFlag : constant.register .flag=.natural 1:=by simp [constant,State.set]
  have evaluated : NatOp.subtract.eval (remaining+1) 1=some remaining:=by simp [NatOp.eval]
  have subtractRun : Instruction.execute input (.natOp .subtract .index .index .flag) constant=some subtracted:=by
    simp [Instruction.execute,constantIndex,constantFlag,Cell.nat?,evaluated,subtracted]
  have remainingBits : 1+natBits remaining≤budget:=by
    have countBits:=safe.heap 28 live
    rw [counter] at countBits
    exact (Nat.add_le_add_left (natBits_mono (by omega : remaining≤remaining+1)) 1).trans countBits
  have subtractSafe:=PDCompute.Pack.natOp_execute_safe input constant subtracted .subtract .index .index .flag
    (remaining+1) 1 remaining budget constantSafe constantIndex constantFlag evaluated remainingBits
    ((natBits_mono (by change before.pc+3+1+1≤before.pc+8;omega)).trans pcBits) subtractRun
  have pairSafe:=PrefixSafe.cons input (.constant .flag (.natural 1)) [.natOp .subtract .index .index .flag]
    loaded constant budget constantRun loadedSafe
    (PrefixSafe.singleton input _ constant subtracted budget subtractRun constantSafe subtractSafe)
  have pairRun : linearExecute input [.constant .flag (.natural 1),.natOp .subtract .index .index .flag] loaded=some subtracted:=by
    change (Instruction.execute input (.constant .flag (.natural 1)) loaded).bind
      (fun state=>(Instruction.execute input (.natOp .subtract .index .index .flag) state).bind some)=some subtracted
    rw [constantRun,Option.bind_some,subtractRun,Option.bind_some]
  have firstRun : linearExecute input (loadSlot 28 .index++[.constant .flag (.natural 1),.natOp .subtract .index .index .flag]) before=some subtracted:=by
    rw [PDLower.CalibrationCompute.linearExecute_append,loadRun,Option.bind_some]
    exact pairRun
  have firstSafe:=PrefixSafe.append input _ _ before loaded budget loadRun loadSafe pairSafe
  have subFresh : subtracted.register .fresh=.natural 0:=by
    simp [subtracted,constant,loaded,loadSlotResult,State.set,fresh]
  have storeSafe:=PrefixSafe.storeSlot input subtracted 0 28 budget .index subtractSafe subFresh (by decide)
    addressBits (by simpa only [subtracted,constant,loaded,loadSlotResult,State.set,Nat.add_assoc] using pcBits)
  exact PrefixSafe.append input _ _ before subtracted budget firstRun firstSafe storeSafe

theorem decrement_region (before : State) (remaining : ℕ) :
    RegionMemory before (decrementResult before remaining) {28} := by
  refine ⟨?_,?_,Finset.subset_insert _ _,rfl⟩
  · intro address outside
    exact Function.update_of_ne (by simpa only [Finset.mem_singleton] using outside) _ _
  · intro address member
    rcases Finset.mem_insert.mp member with same|old
    · exact Finset.mem_union_right _ (by simpa only [Finset.mem_singleton] using same)
    · exact Finset.mem_union_left _ old

/-- Literal eight-op successful decrement, same original full-state B and
one-cell physical region on EVERY prefix, including the actual final store. -/
theorem decrement_trace (program : Program) (input : List Cell) (before : State) (remaining budget : ℕ)
    (header : Header before 0 (fun slot=>before.heap slot)) (fresh : before.register .fresh=.natural 0)
    (counter : before.heap 28=.natural (remaining+1)) (safe : RootD27.Bits.SafeBits before budget)
    (room : 7≤budget) (pcBits : natBits (before.pc+8)≤budget)
    (fetch : FetchesCode program before.pc decrementCode) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (decrementResult before remaining) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤135 ∧
      (∀ state∈trace,RegionMemory before state {28}) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state budget) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+8) := by
  have live : 28∈before.live:=by simpa only [Nat.zero_add] using header.live 28 (by decide)
  have run:=decrement_execute input before remaining fresh live counter
  have bits:=decrement_prefix_safe input before remaining budget header fresh counter safe room pcBits
  obtain ⟨trace,head,last,chain,cost,prefixes,scope⟩:=linearExecute_trace_closedPC program input decrementCode
    decrement_straight before _ fetch run
  have invariant : ∀ state∈trace,RegionMemory before state {28} ∧ RootD27.Bits.SafeBits state budget:=by
    intro state member
    have split:=List.dropLast_append_getLast? (decrementResult before remaining) (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,bound,executed⟩:=prefixes state proper
      have memory:=decrement_prefix_memory input before state remaining count fresh live counter
        (by simpa only [decrement_length] using bound) executed
      refine ⟨⟨fun address _=>congrFun memory.1 address,?_,?_,memory.2.2⟩,bits count state executed⟩
      · rw [memory.2.1]
        exact Finset.subset_union_left
      · rw [memory.2.1]
    · have same : state=decrementResult before remaining:=List.mem_singleton.mp terminal
      subst state
      exact ⟨decrement_region before remaining,bits.final run⟩
  refine ⟨trace,head,last,chain,?_,fun state member=>(invariant state member).1,
    fun state member=>(invariant state member).2,?_⟩
  · simpa only [decrement_length] using cost
  · simpa only [decrement_length] using scope

end PDCompute.CoreSearchLoop
