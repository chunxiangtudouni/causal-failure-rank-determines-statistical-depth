module

public import Paid.PDCompute_SolverLinearPC_121
public import Paid.PDCompute_SolverHeaderFrame_099
public import Paid.RootD27Bits_SlotPrefix_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute storeSlot storeSlotResult)
open PDMenu.ComputeFrame

/-- Initialization may create a new Header cell. No prefilled Header or
fresh/live-disjointness condition is assumed for the genuine store. -/
theorem initialStore_prefix_region (input : List Cell) (before after : State)
    (base slot count : ℕ) (source : Register) (fresh : before.register .fresh=.natural base)
    (different : source ≠ .address) (inside : slot < headerWords) (bound : count ≤ 3)
    (executed : linearExecute input ((storeSlot slot source).take count) before=some after) :
    RegionMemory before after (cellRegion base headerWords) := by
  by_cases full : count=3
  · subst count
    change linearExecute input (storeSlot slot source) before=some after at executed
    rw [PDLower.CalibrationCompute.storeSlot_execute input before base slot source fresh different] at executed
    have same:=Option.some.inj executed
    subst after
    have targetInside : base+slot ∈ cellRegion base headerWords :=
      Finset.mem_image.mpr ⟨slot,Finset.mem_range.mpr inside,rfl⟩
    refine ⟨?_,?_,Finset.subset_insert _ _,rfl⟩
    · intro address outside
      have notTarget : address ≠ base+slot := by intro same; exact outside (same.symm ▸ targetInside)
      exact Function.update_of_ne notTarget _ _
    · intro address member
      rcases Finset.mem_insert.mp member with same|old
      · exact Finset.mem_union_right _ (same.symm ▸ targetInside)
      · exact Finset.mem_union_left _ old
  · have short : count ≤ 2 := by omega
    have unchanged : after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
      interval_cases count <;>
        simp [storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,fresh] at executed <;>
        subst after <;> exact ⟨rfl,rfl,rfl⟩
    exact RegionMemory.of_unchanged _ unchanged.1 unchanged.2.1 unchanged.2.2

/-- Actual storeSlot trace with SAME bit budget, precise Header region,
and actual closed PC interval at EVERY successful instruction prefix. -/
theorem initialStore_trace_resources (program : Program) (input : List Cell) (before : State)
    (base slot budget : ℕ) (source : Register) (fresh : before.register .fresh=.natural base)
    (different : source ≠ .address) (inside : slot < headerWords)
    (safe : RootD27.Bits.SafeBits before budget)
    (addressBits : 1+natBits (base+slot) ≤ budget) (pcBits : natBits (before.pc+3) ≤ budget)
    (fetch : FetchesCode program before.pc (storeSlot slot source)) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some (storeSlotResult before base slot source) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace ≤ 60 ∧
      ∀ state ∈ trace,RegionMemory before state (cellRegion base headerWords) ∧
        RootD27.Bits.SafeBits state budget ∧ before.pc ≤ state.pc ∧ state.pc ≤ before.pc+3 := by
  have execute:=PDLower.CalibrationCompute.storeSlot_execute input before base slot source fresh different
  obtain ⟨trace,head,last,chain,timeBound,prefixes,pcRange⟩:=linearExecute_trace_closedPC program input (storeSlot slot source)
    (by simp [StraightCode,storeSlot,StraightInstruction]) before _ fetch execute
  refine ⟨trace,head,last,chain,timeBound,?_⟩
  intro state member
  have split:=List.dropLast_append_getLast? (storeSlotResult before base slot source) (by rw [last]; simp)
  have statePrefix : ∃ count ≤ 3,linearExecute input ((storeSlot slot source).take count) before=some state := by
    rw [← split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,bound,run⟩:=prefixes state proper
      exact ⟨count,(Nat.le_of_lt bound),run⟩
    · have same : state=storeSlotResult before base slot source := List.mem_singleton.mp terminal
      subst state
      exact ⟨3,le_refl _,execute⟩
  obtain ⟨count,bound,run⟩:=statePrefix
  exact ⟨initialStore_prefix_region input before state base slot count source fresh different inside bound run,
    RootD27.Bits.storeSlot_prefix_safe input before state base slot budget count source safe fresh different addressBits pcBits bound run,
    pcRange state member⟩

end PDCompute.Solver
