module

public import Paid.PDCompute_CoreEmit_ScalarBits_012
public import Paid.PDCompute_SolverEmitLoopBits_209

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDCompute.CoreEmit
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute (HeapList linearExecute)
open PDROC.CalibrationRow.Operand
open PDROC.DataBits

private theorem buffer_base_ge99 (n k M : ℕ) (upper : Bool) : 99≤bufferBase n k M upper := by
  cases upper <;> unfold bufferBase RootD27.Core.retainedTableBase <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

private theorem guardLoad_prefix_safe (input : List Cell) (before : State) (tag budget : ℕ)
    (stored : HeapList before 13 [.natural tag]) (safe : RootD27.Bits.SafeBits before budget)
    (addressBits : 1+natBits 13≤budget) (counter : natBits (before.pc+2)≤budget) :
    PrefixSafe input guardLoadCode before budget := by
  have physical:=singleton_fields before 13 (.natural tag) stored
  let a:=({before with pc:=before.pc+1}).set .address (.natural 13)
  let b:=guardLoadResult before tag
  have firstPC : natBits (before.pc+1)≤budget:=(natBits_mono (by omega : before.pc+1≤before.pc+2)).trans counter
  have aSafe : RootD27.Bits.SafeBits a budget:=(safe.withPC _ firstPC).set .address (.natural 13) addressBits
  have secondPC : natBits (a.pc+1)≤budget:=by change natBits (before.pc+2)≤budget;exact counter
  have loadRun : Instruction.execute input (.load .index .address) a=some b := by
    simp [Instruction.execute,a,b,guardLoadResult,State.set,Cell.nat?,physical.1,physical.2]
  have bSafe : RootD27.Bits.SafeBits b budget := by
    have actual:=PDCompute.Pack.load_execute_safe input a b .index .address 13 budget aSafe rfl physical.1 secondPC loadRun
    exact actual
  have tail:=PrefixSafe.singleton input (.load .index .address) a b budget loadRun aSafe bSafe
  exact PrefixSafe.cons input (.constant .address (.natural 13)) [.load .index .address] before a budget rfl safe tail

/-- The actual3-op tag reread/branch, SAME fixed B including its genuine
static return label. Current dirty state is never compressed to a newI. -/
theorem guard_trace_resources (program : Program) (input : List Cell) (origin returnPC budget : ℕ) (before : State) (tag : ℕ)
    (position : before.pc=origin) (stored : HeapList before 13 [.natural tag])
    (safe : RootD27.Bits.SafeBits before budget) (addressBits : 1+natBits 13≤budget)
    (counter : natBits (origin+3)≤budget) (returnBits : natBits returnPC≤budget)
    (fetch : FetchesCode program origin (stateGuardCode (origin+3) returnPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤75 ∧
      after.pc=(if tag=0 then returnPC else origin+3) ∧ after.heap=before.heap ∧ after.live=before.live ∧
      ∀ state∈trace,state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output ∧ RootD27.Bits.SafeBits state budget := by
  let loaded:=guardLoadResult before tag
  let after : State:={loaded with pc:=if tag=0 then returnPC else origin+3}
  have literal : FetchesCode program origin (guardLoadCode++[.branchZero .index returnPC (origin+3)]) := fetch
  have loadFetch : FetchesCode program before.pc guardLoadCode := by rw [position];exact literal.append_left
  have loadPC : natBits (before.pc+2)≤budget := (natBits_mono (by omega : before.pc+2≤origin+3)).trans counter
  have bounded:=guardLoad_prefix_safe input before tag budget stored safe addressBits loadPC
  have executed:=guardLoad_execute input before tag stored
  obtain ⟨loading,loadHead,loadLast,loadChain,loadTime,loadResources⟩:=PDCompute.Pack.linearExecute_trace_invariant program input guardLoadCode
    guardLoad_straight before loaded loadFetch executed
    (fun state=>state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output ∧ RootD27.Bits.SafeBits state budget) (by
      intro count inside state actual
      have countBound : count≤2:=by simpa only [guardLoad_length] using inside
      have memory:=guardLoad_prefix_memory input before state tag count stored countBound actual
      exact ⟨memory.1,memory.2.1,memory.2.2,bounded count state actual⟩)
  have loadTime' : time program loading≤45:=by simpa only [guardLoad_length] using loadTime
  have loadedSafe:=(loadResources loaded (List.mem_of_getLast? loadLast)).2.2.2
  have instruction : program[origin+2]?=some (.branchZero .index returnPC (origin+3)) :=
    (fetch 2 (by rw [stateGuard_length];decide)).trans (by rfl)
  have loadedAt : loaded.pc=origin+2 := by change before.pc+2=origin+2;rw [position]
  have loadedIndex : loaded.register .index=.natural tag:=rfl
  have actual : Instruction.execute input (.branchZero .index returnPC (origin+3)) loaded=some after := by
    simp [Instruction.execute,loadedIndex,Cell.nat?,after]
  have control : step program input loaded=some after := by simp only [step,loadedAt,instruction];exact actual
  have afterSafe:=PDCompute.Pack.branch_execute_safe input loaded after .index tag returnPC (origin+3) budget loadedSafe loadedIndex returnBits counter actual
  have branchChain : [loaded,after].IsChain (fun first later=>step program input first=some later) :=
    List.isChain_cons_cons.mpr ⟨control,.singleton after⟩
  have branchTime : time program [loaded,after]≤30:=time_le_length program [loaded,after]
  have joined:=joinTrace_spec program input loading [loaded,after] before loaded after 45 30
    loadHead loadLast rfl rfl loadChain branchChain loadTime' branchTime
  refine ⟨joinTrace loading [loaded,after],after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,rfl,rfl,rfl,?_⟩
  intro state member
  rcases RootD27.Core.joinTrace_member member with loadingState|branching
  · exact loadResources state loadingState
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at branching
    rcases branching with same|same <;> subst state
    · exact ⟨rfl,rfl,rfl,loadedSafe⟩
    · exact ⟨rfl,rfl,rfl,afterSafe⟩

/-- Actual31-op price/table block on ONE fixed B, using the frozen real
209 seven-op output loop. Data bits are copied from existing liveheap. -/
theorem solve_trace_bits (program : Program) (input : List Cell) (origin returnPC : ℕ)
    (before : State) (n k M cap budget : ℕ) (upper : Bool) (solution : MultiplierSolve)
    (position : before.pc=origin) (dimensions : PreparedDimensions before n k M)
    (payload : SolvePayload before n k M upper solution) (safe : RootD27.Bits.SafeBits before budget)
    (endBound : bufferBase n k M upper+(encodeTable solution.table).length≤cap)
    (capBits : 1+natBits cap≤budget) (counter : natBits (origin+31)≤budget) (returnBits : natBits returnPC≤budget)
    (fetch : FetchesCode program origin (solveCode origin upper returnPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ after.pc=returnPC ∧
      after.heap=before.heap ∧ after.live=before.live ∧ ∀ state∈trace,RootD27.Bits.SafeBits state budget := by
  let price:=Cell.rational solution.multiplier
  let cells:=encodeTable solution.table
  let paid:=outputSlotResult before (priceSlot upper) price
  let ready:=pointerResult paid n k M cells.length upper
  have fixedCap : 99≤cap:=(buffer_base_ge99 n k M upper).trans (by omega)
  have small (value : ℕ) (inside : value≤99) : 1+natBits value≤budget:=
    (Nat.add_le_add_left (natBits_mono (inside.trans fixedCap)) 1).trans capBits
  have priceBits : 1+natBits (priceSlot upper)≤budget:=small _ (by cases upper <;> decide)
  have oneBits : (.natural 1 : Cell).bits≤budget:=small 1 (by decide)
  have pointerBits : 1+natBits (bufferBase n k M upper+cells.length)≤budget:=
    (Nat.add_le_add_left (natBits_mono endBound) 1).trans capBits
  have pricePC : natBits (before.pc+3)≤budget:=(natBits_mono (by omega : before.pc+3≤origin+31)).trans counter
  have pointerPC : natBits (paid.pc+21)≤budget:=(natBits_mono (by change before.pc+3+21≤origin+31;omega)).trans counter
  have emitPC : natBits ((origin+24)+7)≤budget:=counter
  have literal:=fetch
  rw [solveCode] at literal
  have priceFetch : FetchesCode program before.pc (outputSlotCode (priceSlot upper)) := by rw [position];exact literal.append_left.append_left
  obtain ⟨priceTrace,priceHead,priceLast,priceChain,priceTime,priceResources⟩:=
    outputSlot_trace_resources program input before (priceSlot upper) budget price payload.1 safe priceBits pricePC priceFetch
  have pointerFetch : FetchesCode program paid.pc (pointerCode upper) := by
    simpa only [paid,outputSlotResult,position,outputSlot_length] using literal.append_left.append_right
  obtain ⟨pointerTrace,pointerHead,pointerLast,pointerChain,pointerTime,pointerResources⟩:=
    pointer_trace_resources program input paid n k M cells.length cap budget upper dimensions payload.2.1
      (priceResources paid (List.mem_of_getLast? priceLast)).2 endBound capBits pointerPC pointerFetch
  have emitFetch : FetchesCode program (origin+24) (RootD27.Core.emitHeapCode (origin+24) returnPC) := by
    simpa only [List.length_append,outputSlot_length,pointer_length] using literal.append_right
  have readyPC : ready.pc=origin+24 := by change before.pc+3+21=origin+24;rw [position]
  obtain ⟨emitted,after,emitHead,emitLast,emitChain,emitTime,afterPC,_,_,afterHeap,afterLive,_,_,emitSafe⟩:=
    PDCompute.Solver.emitHeap_trace_resources program input (origin+24) returnPC budget emitFetch cells ready (bufferBase n k M upper)
      readyPC rfl rfl payload.2.2 (pointerResources ready (List.mem_of_getLast? pointerLast)).2.2.2
      oneBits pointerBits emitPC returnBits
  have first:=joinTrace_spec program input priceTrace pointerTrace before paid ready 60 330
    priceHead priceLast pointerHead pointerLast priceChain pointerChain priceTime pointerTime
  have joined:=joinTrace_spec program input (joinTrace priceTrace pointerTrace) emitted before ready after
    (60+330) (135*cells.length+30) first.1 first.2.1 emitHead emitLast first.2.2.1 emitChain first.2.2.2 emitTime
  have safePrice : ∀ state∈priceTrace,RootD27.Bits.SafeBits state budget:=fun state member=>(priceResources state member).2
  have safePointer : ∀ state∈pointerTrace,RootD27.Bits.SafeBits state budget:=fun state member=>(pointerResources state member).2.2.2
  have allSafe:=PDCompute.Pack.joinTrace_invariant (joinTrace priceTrace pointerTrace) emitted (fun state=>RootD27.Bits.SafeBits state budget)
    (PDCompute.Pack.joinTrace_invariant priceTrace pointerTrace (fun state=>RootD27.Bits.SafeBits state budget) safePrice safePointer) emitSafe
  exact ⟨joinTrace (joinTrace priceTrace pointerTrace) emitted,after,joined.1,joined.2.1,joined.2.2.1,afterPC,afterHeap,afterLive,allSafe⟩

end PDCompute.CoreEmit
