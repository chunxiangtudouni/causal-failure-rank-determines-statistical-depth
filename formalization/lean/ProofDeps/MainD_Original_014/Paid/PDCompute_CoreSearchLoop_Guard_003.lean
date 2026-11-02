module

public import Paid.PDCompute_CoreSearchLoop_Counter_002
public import Paid.PDCompute_Pack_SlotBitTrace_064

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

@[expose] public section

namespace PDCompute.CoreSearchLoop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver hiding HeapList
open PDMenu.ComputeFrame RootD27.Core PDROC.CalibrationRow.Operand PDROC.DataBits
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult HeapList)

theorem unchanged_region {before after : State} (region : Finset ℕ)
    (heap : after.heap=before.heap) (live : after.live=before.live) (output : after.output=before.output) :
    RegionMemory before after region := by
  refine ⟨fun address _=>congrFun heap address,?_,?_,output⟩
  · rw [live]
    exact Finset.subset_union_left
  · rw [live]

theorem representation_unchanged {P : Parameters} {fee : ℚ} {before after : State} {search : MultiplierState}
    (represented : SearchStateRep P fee before search)
    (heap : after.heap=before.heap) (live : after.live=before.live) :
    SearchStateRep P fee after search := by
  cases search <;> simpa only [SearchStateRep,SolvedBuffer,HeapList,heapSegment,heap,live] using represented

def guardResult (before : State) (origin : ℕ) (body : List Instruction) (remaining : ℕ) : State :=
  {loadSlotResult before 0 28 .index with pc:=if remaining=0 then exitPC origin body else bodyPC origin}

theorem guard_result_memory (before : State) (origin : ℕ) (body : List Instruction) (remaining : ℕ) :
    (guardResult before origin body remaining).heap=before.heap ∧
    (guardResult before origin body remaining).live=before.live ∧
    (guardResult before origin body remaining).output=before.output := ⟨rfl,rfl,rfl⟩

theorem guard_result_ready {P : Parameters} {fee : ℚ} {before : State}
    (ready : Ready P fee before) (origin : ℕ) (body : List Instruction) (remaining : ℕ) :
    Ready P fee (guardResult before origin body remaining) := by
  refine ⟨ready.header,?_,ready.prepared,ready.cache⟩
  simpa only [guardResult,loadSlotResult,State.set,
    Function.update_of_ne (by decide : (.fresh : Register)≠.index),
    Function.update_of_ne (by decide : (.fresh : Register)≠.address)] using ready.fresh

/-- Actual load-three/branch-one guard. The final state can still fetch
the caller's continuation; no terminal-next-none assumption is made. -/
theorem guard_trace (program : Program) (input : List Cell) (before : State)
    (origin : ℕ) (body : List Instruction) (remaining budget : ℕ)
    (header : Header before 0 (fun slot=>before.heap slot)) (fresh : before.register .fresh=.natural 0)
    (counter : before.heap 28=.natural remaining) (position : before.pc=origin)
    (safe : RootD27.Bits.SafeBits before budget) (room : 7≤budget)
    (pcBits : natBits (exitPC origin body)≤budget)
    (fetch : FetchesCode program origin (code origin body)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (guardResult before origin body remaining) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤90 ∧
      (∀ state∈trace,RegionMemory before state ∅) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state budget) ∧
      (∀ state∈trace,state.pc≤exitPC origin body) := by
  let loaded:=loadSlotResult before 0 28 .index
  let after:=guardResult before origin body remaining
  have loadFetch : FetchesCode program before.pc (loadSlot 28 .index):=by
    rw [position]
    exact fetch.append_left.append_left
  have loadRun:=(header.loadSlot_execute input 28 .index (by decide) fresh).1
  have addressBits : 1+natBits (0+28)≤budget:=(by decide : 1+natBits (0+28)≤7).trans room
  have loadPC : natBits (before.pc+3)≤budget:=
    (natBits_mono (by unfold exitPC;omega : before.pc+3≤exitPC origin body)).trans pcBits
  have loadSafe:=PrefixSafe.loadSlot input before 0 28 budget .index safe fresh
    (header.live 28 (by decide)) addressBits loadPC
  obtain ⟨trace,head,last,chain,cost,prefixes,scope⟩:=linearExecute_trace_closedPC program input (loadSlot 28 .index)
    (loadSlot_straight 28 .index) before loaded loadFetch loadRun
  have loadedIndex : loaded.register .index=.natural remaining:=by
    simpa only [loaded,loadSlotResult,State.set,Function.update_self,Nat.zero_add] using counter
  have branchFetch : program[loaded.pc]?=some (.branchZero .index (exitPC origin body) (bodyPC origin)):=by
    change program[before.pc+3]?=some _
    rw [position]
    exact guard_branch_fetch program origin body fetch
  have branch : Instruction.execute input (.branchZero .index (exitPC origin body) (bodyPC origin)) loaded=some after:=by
    simp [Instruction.execute,loadedIndex,Cell.nat?,after,guardResult,loaded]
  have stepRun : step program input loaded=some after:=by
    unfold step
    rw [branchFetch]
    exact branch
  have loadedSafe:=loadSafe.final loadRun
  have bodyBits : natBits (bodyPC origin)≤budget:=
    (natBits_mono (by unfold bodyPC exitPC;omega : bodyPC origin≤exitPC origin body)).trans pcBits
  have afterSafe:=PDCompute.Pack.branch_execute_safe input loaded after .index remaining
    (exitPC origin body) (bodyPC origin) budget loadedSafe loadedIndex pcBits bodyBits branch
  have loadInvariant : ∀ state∈trace,RegionMemory before state ∅ ∧ RootD27.Bits.SafeBits state budget:=by
    intro state member
    have split:=List.dropLast_append_getLast? loaded (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,bound,executed⟩:=prefixes state proper
      have memory:=loadSlot_prefix_memory input before state 0 28 .index fresh
        (header.live 28 (by decide)) count (by simpa only [loadSlot,List.length_cons,List.length_nil] using bound.le) executed
      exact ⟨unchanged_region ∅ memory.1 memory.2.1 memory.2.2,loadSafe count state executed⟩
    · have same : state=loaded:=List.mem_singleton.mp terminal
      subst state
      exact ⟨unchanged_region ∅ rfl rfl rfl,loadedSafe⟩
  have appended:=chain_append_control program input trace loaded after chain last stepRun
  have nonempty : trace≠[]:=by intro empty;simp only [empty,List.head?_nil,reduceCtorEq] at head
  refine ⟨trace++[after],?_,by simp [after],appended.1,?_,?_,?_,?_⟩
  · simpa only [List.head?_append_of_ne_nil _ nonempty] using head
  · have loadTime : time program trace≤60:=by simpa only [loadSlot,List.length_cons,List.length_nil] using cost
    exact appended.2.trans (by omega)
  · intro state member
    rcases List.mem_append.mp member with earlier|terminal
    · exact (loadInvariant state earlier).1
    · have same : state=after:=List.mem_singleton.mp terminal
      subst state
      exact unchanged_region ∅ rfl rfl rfl
  · intro state member
    rcases List.mem_append.mp member with earlier|terminal
    · exact (loadInvariant state earlier).2
    · have same : state=after:=List.mem_singleton.mp terminal
      subst state
      exact afterSafe
  · intro state member
    rcases List.mem_append.mp member with earlier|terminal
    · have bound:=(scope state earlier).2
      change state.pc≤before.pc+3 at bound
      unfold exitPC
      omega
    · have same : state=after:=List.mem_singleton.mp terminal
      subst state
      change (if remaining=0 then exitPC origin body else bodyPC origin)≤exitPC origin body
      split
      · exact le_refl _
      · unfold bodyPC exitPC
        omega

end PDCompute.CoreSearchLoop
