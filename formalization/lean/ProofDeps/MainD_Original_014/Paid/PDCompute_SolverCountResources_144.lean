module

public import Paid.PDCompute_SolverCountPrefix_143
public import Paid.PDCompute_SolverPaddingLead_139

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult storeSlot storeSlotResult)
open PDMenu.ComputeFrame

theorem endpointCountHeader_prefix_resources (mode : ReaderMode) (input : List Cell) (P : Parameters)
    (before : State) (base source budget : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (sourceValue : values 0=.natural source)
    (safe : RootD27.Bits.SafeBits before budget) (addressBits : 1+natBits (base+headerWords) ≤ budget)
    (lengthBits : 1+natBits (P.certificate.M+1) ≤ budget) (pcBits : natBits (before.pc+9) ≤ budget) :
    CodePrefixResources input (endpointCountHeaderCode mode) before (cellRegion base headerWords) budget := by
  let loaded:=loadSlotResult before base 0 .address
  let computed:=endpointCountComputed loaded P.certificate.M
  have loadRun:=(header.loadSlot_execute input 0 .address (by decide) fresh).1
  have loadResources : CodePrefixResources input (loadSlot 0 .address) before (cellRegion base headerWords) budget := by
    intro count bound state executed
    have countBound : count ≤ 3 := bound
    have memory:=loadSlot_prefix_memory input before state base 0 .address fresh (header.live 0 (by decide)) count countBound executed
    refine ⟨RegionMemory.of_unchanged _ memory.1 memory.2.1 memory.2.2,?_⟩
    exact RootD27.Bits.loadSlot_prefix_safe input before state base 0 budget count .address safe fresh
      (header.live 0 (by decide))
      ((Nat.add_le_add_left (natBits_mono (by omega : base+0 ≤ base+headerWords)) 1).trans addressBits)
      ((natBits_mono (by omega : before.pc+3 ≤ before.pc+9)).trans pcBits) countBound executed
  have loadedSafe:=(loadResources.full loadRun).2
  have loadedBase : loaded.register .fresh=.natural base :=
    (loadSlotResult_fresh before base 0 .address (by decide)).trans fresh
  have loadedAddress : loaded.register .address=.natural source :=
    (header.loadSlot_execute input 0 .address (by decide) fresh).2.trans sourceValue
  have loadedSource : EndpointSource mode input P source loaded := by cases mode <;> exact hsource
  have readRun:=readEndpointCount_execute mode input P source loaded .index loadedSource loadedAddress
  have middleRun : linearExecute input (endpointCountMiddleCode mode) loaded=some computed := by
    rw [endpointCountMiddleCode,linearExecute,readRun,Option.bind_some]
    simp [linearExecute,computed,endpointCountComputed,Instruction.execute,State.set,NatOp.eval,Cell.nat?]
  have middlePC : natBits (loaded.pc+3) ≤ budget :=
    (natBits_mono (by change before.pc+3+3 ≤ before.pc+9; omega)).trans pcBits
  have middleResources:=endpointCountMiddle_prefix_resources mode input P loaded source budget loadedSource loadedAddress
    loadedSafe lengthBits middlePC (cellRegion base headerWords)
  have computedSafe:=(middleResources.full middleRun).2
  have computedBase : computed.register .fresh=.natural base := loadedBase
  have computedHeader : Header computed base values := header
  have storeResources : CodePrefixResources input (storeSlot 6 .index) computed (cellRegion base headerWords) budget := by
    intro count bound state executed
    have countBound : count ≤ 3 := bound
    have memory:=storeSlot_prefix_memory input computed state base 6 .index values computedHeader (by decide) computedBase
      (by decide) count countBound executed
    exact ⟨memory.region _ (Finset.Subset.refl _),RootD27.Bits.storeSlot_prefix_safe input computed state base 6 budget count .index
      computedSafe computedBase (by decide)
      ((Nat.add_le_add_left (natBits_mono (by unfold headerWords; omega : base+6 ≤ base+headerWords)) 1).trans addressBits)
      (by simpa only [computed,endpointCountComputed,loaded,loadSlotResult,State.set,Nat.add_assoc] using pcBits) countBound executed⟩
  exact (loadResources.append middleResources loadRun).append storeResources
    (by rw [PDLower.CalibrationCompute.linearExecute_append,loadRun,Option.bind_some]; exact middleRun)

theorem endpointCountHeaderCode_straight (mode : ReaderMode) : StraightCode (endpointCountHeaderCode mode) := by
  intro instruction member
  cases mode <;>
    simp only [endpointCountHeaderCode,loadSlot,storeSlot,ReaderMode.read,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member <;>
    rcases member with ((h|h|h)|(h|h|h))|(h|h|h) <;> subst instruction <;> trivial

/-- Same actual9-op endpoint-count producer, functional Header6 plus
EVERY-prefix full-state bits, physical memory and literal PC range. -/
theorem endpointCountHeader_trace_resources (mode : ReaderMode) (program : Program) (input : List Cell) (P : Parameters)
    (before : State) (base source budget : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (sourceValue : values 0=.natural source)
    (safe : RootD27.Bits.SafeBits before budget) (addressBits : 1+natBits (base+headerWords) ≤ budget)
    (lengthBits : 1+natBits (P.certificate.M+1) ≤ budget) (pcBits : natBits (before.pc+9) ≤ budget)
    (fetch : FetchesCode program before.pc (endpointCountHeaderCode mode)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 150 ∧
      Header after base (Function.update values 6 (.natural P.certificate.M)) ∧ after.register .fresh=.natural base ∧ after.pc=before.pc+9 ∧
      (∀ state∈trace,RegionMemory before state (cellRegion base headerWords) ∧ RootD27.Bits.SafeBits state budget ∧
        before.pc ≤ state.pc ∧ state.pc ≤ before.pc+9) := by
  obtain ⟨after,executed,afterHeader,afterBase,afterPC,_⟩:=endpointCountHeaderCode_execute mode input P before base source values
    header fresh hsource sourceValue
  obtain ⟨trace,head,last,chain,bound,prefixes,pcRange⟩:=linearExecute_trace_closedPC program input (endpointCountHeaderCode mode)
    (endpointCountHeaderCode_straight mode) before after fetch executed
  have resources:=endpointCountHeader_prefix_resources mode input P before base source budget values header fresh hsource sourceValue
    safe addressBits lengthBits pcBits
  refine ⟨trace,after,head,last,chain,?_,afterHeader,afterBase,afterPC,?_⟩
  · simpa only [endpointCountHeaderCode_length] using bound
  · intro state member
    have split:=List.dropLast_append_getLast? after (by rw [last]; simp)
    have prefixRun : ∃ count ≤ 9,linearExecute input ((endpointCountHeaderCode mode).take count) before=some state := by
      rw [←split] at member
      rcases List.mem_append.mp member with proper|terminal
      · obtain ⟨count,countBound,run⟩:=prefixes state proper
        exact ⟨count,Nat.le_of_lt (by simpa only [endpointCountHeaderCode_length] using countBound),run⟩
      · have same:=List.mem_singleton.mp terminal
        subst state
        exact ⟨9,le_refl _,executed⟩
    obtain ⟨count,countBound,run⟩:=prefixRun
    have facts:=resources count countBound state run
    exact ⟨facts.1,facts.2,by simpa only [endpointCountHeaderCode_length] using pcRange state member⟩

end PDCompute.Solver
