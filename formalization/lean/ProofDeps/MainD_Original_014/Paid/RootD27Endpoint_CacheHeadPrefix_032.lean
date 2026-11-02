module

public import Paid.RootD27Endpoint_LoopPrefix_031
public import Paid.RootD27Endpoint_CacheHead_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot storeSlot)

theorem cacheHeader_prefix_region (input : List Cell) (before after : State)
    (base M E : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (fresh : before.register .fresh=.natural base) (hM : values 3=.natural M)
    (hE : values 0=.natural E) (count : ℕ) (bound : count≤12)
    (actual : linearExecute input (cacheHeaderCode.take count) before=some after) :
    RegionMemory before after (endpointLoopRegion base E M) := by
  have zeroLive : base∈before.live := by simpa only [Nat.add_zero] using header.live 0 (by decide)
  have zeroValue : before.heap base=.natural E := by
    simpa only [Nat.add_zero] using (header.value 0 (by decide)).trans hE
  have threeLive:=header.live 3 (by decide)
  have threeValue:=(header.value 3 (by decide)).trans hM
  let first : State := {before with heap:=Function.update before.heap (base+17) (.natural (M+1)),live:=insert (base+17) before.live}
  have firstInside : base+17∈endpointLoopRegion base E M := by
    apply Finset.mem_union_left
    apply (mem_cellRegion_iff base headerWords (base+17)).mpr
    change base≤base+17 ∧ base+17<base+48
    omega
  have cacheInside : E∈endpointLoopRegion base E M := by
    apply Finset.mem_union_right
    apply (mem_cellRegion_iff E (2*M+3) E).mpr
    omega
  have firstMemory : RegionMemory before first (endpointLoopRegion base E M) :=
    endpoint_store_region before _ _ _ firstInside
  have secondMemory:=endpoint_store_region first E (.natural (M+1)) _ cacheInside
  interval_cases count <;>
    simp [cacheHeaderCode,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,
      Cell.nat?,fresh,zeroLive,threeLive,zeroValue,threeValue,Nat.add_assoc] at actual <;>
    subst after
  all_goals
    first
    | exact RegionMemory.refl before (endpointLoopRegion base E M)
    | exact firstMemory
    | exact firstMemory.trans secondMemory

/-- The initial cache length is physically written, with every actual
prefix framed in the same final endpoint write region. -/
theorem cacheHeader_actual_region (program : Program) (input : List Cell) (before : State)
    (base M E : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (fresh : before.register .fresh=.natural base) (hM : values 3=.natural M)
    (hE : values 0=.natural E) (separated : base+48≤E)
    (fetched : FetchesCode program before.pc cacheHeaderCode) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (cacheHeaderResult before base M E) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤195 ∧
      Header (cacheHeaderResult before base M E) base (Function.update values 17 (.natural (M+1))) ∧
      E∈(cacheHeaderResult before base M E).live ∧
      (cacheHeaderResult before base M E).heap E=.natural (M+1) ∧
      ∀ state∈trace,RegionMemory before state (endpointLoopRegion base E M) := by
  have hz : base∈before.live := by simpa only [Nat.add_zero] using header.live 0 (by decide)
  have hv : before.heap base=.natural E := by
    simpa only [Nat.add_zero] using (header.value 0 (by decide)).trans hE
  have executed:=cacheHeader_execute input before base M E fresh hz (header.live 3 (by decide))
    ((header.value 3 (by decide)).trans hM) hv
  obtain ⟨trace,head,last,chain,cost,prefixes⟩:=linearExecute_trace_time program input cacheHeaderCode
    cacheHeader_straight before _ fetched executed
  refine ⟨trace,head,last,chain,cost,cacheHeader_header before base M E values header separated,
    (cacheHeader_cell before base M E).1,(cacheHeader_cell before base M E).2,?_⟩
  intro state member
  have split:=List.dropLast_append_getLast? (cacheHeaderResult before base M E) (by rw [last];simp)
  rw [←split] at member
  rcases List.mem_append.mp member with proper|terminal
  · obtain ⟨count,bound,actual⟩:=prefixes state proper
    apply cacheHeader_prefix_region input before state base M E values header fresh hM hE count
    · simpa only [cacheHeaderCode_length] using bound.le
    · exact actual
  · have same : state=cacheHeaderResult before base M E:=List.mem_singleton.mp terminal
    subst state
    apply cacheHeader_prefix_region input before _ base M E values header fresh hM hE 12 (by omega)
    simpa only [show cacheHeaderCode.take 12=cacheHeaderCode by rw [←cacheHeaderCode_length,List.take_length]] using executed

end RootD27.Endpoint
