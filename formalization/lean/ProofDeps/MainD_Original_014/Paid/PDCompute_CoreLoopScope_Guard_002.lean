module
public import Paid.PDCompute_CoreLoopScope_Body_001
public import Paid.PDCompute_CoreSearchLoop_Guard_003
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000
@[expose] public section
namespace PDCompute.CoreLoopScope
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver hiding HeapList
open PDMenu.ComputeFrame RootD27.Core PDROC.CalibrationRow.Operand PDROC.DataBits PDCompute.CoreSearchLoop
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult HeapList)
/-- Same literal guard and frozen successful-prefix numeric producers.
Only the actual linear/branch lower-PC provenance is retained as well. -/
theorem guard_lower_trace (program : Program) (input : List Cell) (before : State)
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
      (∀ state∈trace,origin≤state.pc ∧ state.pc≤exitPC origin body) := by
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
    · have bounds:=scope state earlier
      change before.pc≤state.pc ∧ state.pc≤before.pc+3 at bounds
      unfold exitPC
      omega
    · have same : state=after:=List.mem_singleton.mp terminal
      subst state
      change origin≤(if remaining=0 then exitPC origin body else bodyPC origin) ∧
        (if remaining=0 then exitPC origin body else bodyPC origin)≤exitPC origin body
      split_ifs <;> simp only [bodyPC,exitPC] <;> omega

end PDCompute.CoreLoopScope
