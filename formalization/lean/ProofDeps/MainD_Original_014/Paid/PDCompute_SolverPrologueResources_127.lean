module

public import Paid.PDCompute_SolverHeaderStores_126
public import Paid.PDCompute_SolverPrologue_016
public import Paid.RootD27Endpoint_HeaderInit_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDLower.CalibrationCompute (linearExecute writeCell)
open PDMenu.ComputeFrame

def headerArgumentStores : List (ℕ × Register) := [(1,.old),(2,.total),(3,.index),(4,.value),(5,.flag)]

theorem headerArgumentStores_valid : ∀ spec ∈ headerArgumentStores,spec.1 < headerWords ∧ spec.2 ≠ .address := by
  intro spec member
  simp only [headerArgumentStores,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h <;> subst spec <;> dsimp only [headerWords] <;> decide

theorem solverPrologue_stores : solverPrologue=[.store .fresh .address]++headerStoresCode headerArgumentStores := by
  simp only [solverPrologue,headerArgumentStores,headerStoresCode,List.append_assoc,List.append_nil]

theorem firstArgument_store_execute (input : List Cell) (before : State) (base : ℕ)
    (fresh : before.register .fresh=.natural base) :
    Instruction.execute input (.store .fresh .address) before=some (writeCell before base (before.register .address)) := by
  simp [Instruction.execute,Cell.nat?,fresh,writeCell]

theorem firstArgument_store_region (before : State) (base : ℕ) :
    RegionMemory before (writeCell before base (before.register .address)) (cellRegion base headerWords) := by
  have inside : base ∈ cellRegion base headerWords := by
    exact Finset.mem_image.mpr ⟨0,Finset.mem_range.mpr (by decide),by omega⟩
  refine ⟨?_,?_,Finset.subset_insert _ _,rfl⟩
  · intro address outside
    have different : address ≠ base := by intro same; exact outside (same.symm ▸ inside)
    exact Function.update_of_ne different _ _
  · intro address member
    rcases Finset.mem_insert.mp member with same|old
    · exact Finset.mem_union_right _ (same.symm ▸ inside)
    · exact Finset.mem_union_left _ old

theorem firstArgument_store_safe (before : State) (base budget : ℕ) (safe : RootD27.Bits.SafeBits before budget)
    (addressBits : 1+natBits (base+headerWords) ≤ budget) (pcBits : natBits (before.pc+1) ≤ budget) :
    RootD27.Bits.SafeBits (writeCell before base (before.register .address)) budget := by
  have baseBits : natBits base ≤ budget := by
    have mono:=natBits_mono (by omega : base ≤ base+headerWords)
    omega
  have stored:=safe.store base (before.register .address) baseBits (safe.register .address)
  have counted:=stored.withPC (before.pc+1) pcBits
  simpa only [writeCell] using counted

/-- Every original prologue prefix, before the Header even exists.
Actual input register values are saved by the SAME16-op code. -/
theorem solverPrologue_prefix_resources (input : List Cell) (before after : State) (base budget count : ℕ)
    (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget)
    (addressBits : 1+natBits (base+headerWords) ≤ budget) (pcBits : natBits (before.pc+16) ≤ budget)
    (countBound : count ≤ 16)
    (executed : linearExecute input (solverPrologue.take count) before=some after) :
    RegionMemory before after (cellRegion base headerWords) ∧ RootD27.Bits.SafeBits after budget := by
  cases count with
  | zero =>
    have same : before=after := by simpa only [List.take_zero,linearExecute,Option.some.injEq] using executed
    subst after
    exact ⟨RegionMemory.refl before _,safe⟩
  | succ count =>
    let middle:=writeCell before base (before.register .address)
    have firstRun:=firstArgument_store_execute input before base fresh
    rw [solverPrologue_stores] at executed
    change linearExecute input ((.store .fresh .address::headerStoresCode headerArgumentStores).take (count+1)) before=some after at executed
    rw [List.take_succ_cons,linearExecute,firstRun,Option.bind_some] at executed
    have firstPC : natBits (before.pc+1) ≤ budget := (natBits_mono (by omega : before.pc+1 ≤ before.pc+16)).trans pcBits
    have middleSafe:=firstArgument_store_safe before base budget safe addressBits firstPC
    have middleFresh : middle.register .fresh=.natural base := fresh
    have tailSize : (headerStoresCode headerArgumentStores).length=15 := rfl
    have tailPC : natBits (middle.pc+(headerStoresCode headerArgumentStores).length) ≤ budget := by
      simpa only [middle,writeCell,tailSize,Nat.add_assoc] using pcBits
    have tailBound : count ≤ (headerStoresCode headerArgumentStores).length := by rw [tailSize]; omega
    have tail:=headerStores_prefix_resources headerArgumentStores input middle after base budget count middleSafe middleFresh
      headerArgumentStores_valid addressBits tailPC tailBound executed
    exact ⟨(firstArgument_store_region before base).trans tail.1,tail.2⟩

/-- Same canonical actual linear witness as the original functional
producer, now with EVERY-prefix memory, bits and closed PC interval. -/
theorem solverPrologue_trace_resources (program : Program) (input : List Cell) (before : State)
    (base budget : ℕ) (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget)
    (addressBits : 1+natBits (base+headerWords) ≤ budget) (pcBits : natBits (before.pc+16) ≤ budget)
    (fetch : FetchesCode program before.pc solverPrologue) :
    ∃ trace : List State,trace.head?=some before ∧ trace.getLast?=some (solverPrologueResult before base) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace ≤ 255 ∧
      ∀ state ∈ trace,RegionMemory before state (cellRegion base headerWords) ∧
        RootD27.Bits.SafeBits state budget ∧ before.pc ≤ state.pc ∧ state.pc ≤ before.pc+16 := by
  have execute:=solverPrologue_execute input before base fresh
  obtain ⟨trace,head,last,chain,timeBound,prefixes,pcRange⟩:=linearExecute_trace_closedPC program input solverPrologue
    RootD27.Endpoint.prologue_straight before _ fetch execute
  refine ⟨trace,head,last,chain,?_,?_⟩
  · simpa only [solverPrologue_length] using timeBound
  · intro state member
    have split:=List.dropLast_append_getLast? (solverPrologueResult before base) (by rw [last]; simp)
    have statePrefix : ∃ count ≤ 16,linearExecute input (solverPrologue.take count) before=some state := by
      rw [← split] at member
      rcases List.mem_append.mp member with proper|terminal
      · obtain ⟨count,bound,run⟩:=prefixes state proper
        exact ⟨count,(Nat.le_of_lt (by simpa only [solverPrologue_length] using bound)),run⟩
      · have same : state=solverPrologueResult before base := List.mem_singleton.mp terminal
        subst state
        exact ⟨16,le_refl _,execute⟩
    obtain ⟨count,bound,run⟩:=statePrefix
    have resources:=solverPrologue_prefix_resources input before state base budget count fresh safe addressBits pcBits bound run
    exact ⟨resources.1,resources.2,by simpa only [solverPrologue_length] using pcRange state member⟩

end PDCompute.Solver
