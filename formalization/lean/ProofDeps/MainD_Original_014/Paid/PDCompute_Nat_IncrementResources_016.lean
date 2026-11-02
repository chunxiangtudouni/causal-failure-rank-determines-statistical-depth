module
public import Paid.PDCompute_Pack_IncrementBits_062
public import Paid.PDCompute_SolverLinearPC_121
public import Paid.PDCompute_SolverAdvanceMemory_067
public import Paid.PDCompute_SolverHeaderFrame_099
public import Paid.PDROC_CalibrationRow_OperandPrefix_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000
@[expose] public section
namespace PDCompute.NatControl
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)
open PDROC.CalibrationRow.Operand

/-- Original032 actual.index load/add/store, reusing frozenPack062.
Only actual amount and value+amount bits are bounded: ROM scan pointers
are never incorrectly forced below the n/k workspace endpoint. -/
theorem addNatSlot_prefix_safe (input : List Cell) (before : State) (base slot value amount budget : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (inside : slot<headerWords)
    (fresh : before.register .fresh=.natural base) (hvalue : values slot=.natural value)
    (safe : RootD27.Bits.SafeBits before budget) (addressBits : 1+natBits (base+slot)≤budget)
    (amountBits : (.natural amount : Cell).bits≤budget) (resultBits : (.natural (value+amount) : Cell).bits≤budget)
    (pcBits : natBits (before.pc+8)≤budget) : PrefixSafe input (addNatSlot slot amount) before budget := by
  apply PrefixSafe.of_bounded
  intro count bound state run
  exact PDCompute.Pack.increment_prefix_safe input before state base slot value amount budget count values header inside fresh hvalue
    safe addressBits amountBits resultBits pcBits bound run

/-- SAME actual original8-op trace carries exact Header/end fields,
physical Frame/dirty-live preservation, EVERY-prefix bits and closedPC. -/
theorem addNatSlot_trace_resources (program : Program) (input : List Cell) (before : State)
    (base n k slot value amount budget : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (fresh : before.register .fresh=.natural base) (inside : slot<headerWords) (hvalue : values slot=.natural value)
    (safe : RootD27.Bits.SafeBits before budget) (addressBits : 1+natBits (base+slot)≤budget)
    (amountBits : (.natural amount : Cell).bits≤budget) (resultBits : (.natural (value+amount) : Cell).bits≤budget)
    (pcBits : natBits (before.pc+8)≤budget) (fetch : FetchesCode program before.pc (addNatSlot slot amount)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (addNatSlotResult before base slot value amount) ∧
      trace.IsChain (fun a b=>step program input a=some b) ∧ time program trace≤135 ∧
      Header (addNatSlotResult before base slot value amount) base (Function.update values slot (.natural (value+amount))) ∧
      (addNatSlotResult before base slot value amount).register .fresh=.natural base ∧
      (addNatSlotResult before base slot value amount).pc=before.pc+8 ∧ Frame before (addNatSlotResult before base slot value amount) base n k ∧
      (addNatSlotResult before base slot value amount).output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget ∧ before.pc≤state.pc ∧ state.pc≤before.pc+8 := by
  have run:=addNatSlot_execute input before base slot value amount fresh (header.live slot inside) ((header.value slot inside).trans hvalue)
  have safePrefixes:=addNatSlot_prefix_safe input before base slot value amount budget values header inside fresh hvalue safe addressBits amountBits resultBits pcBits
  obtain ⟨trace,head,last,chain,cost,prefixes,pcRange⟩:=linearExecute_trace_closedPC program input (addNatSlot slot amount)
    (addNatSlot_straight slot amount) before _ fetch run
  have allResources : ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget:=by
    intro state member
    have split:=List.dropLast_append_getLast? (addNatSlotResult before base slot value amount) (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,bound,executed⟩:=prefixes state proper
      exact ⟨addNatSlot_header_memory input before state base slot value amount values header inside fresh hvalue count (Nat.le_of_lt bound) executed,
        safePrefixes count state executed⟩
    · have same : state=addNatSlotResult before base slot value amount:=List.mem_singleton.mp terminal
      subst state
      exact ⟨addNatSlot_header_memory input before _ base slot value amount values header inside fresh hvalue (addNatSlot slot amount).length (le_refl _)
        (by simpa only [List.take_length] using run),safePrefixes.final run⟩
  have fields:=addNatSlotResult_fields before base slot value amount
  have memory : ∀ state∈trace,HeaderMemory before state base:=fun state member=>(allResources state member).1
  have finalMemory : HeaderMemory before (addNatSlotResult before base slot value amount) base:=HeaderMemory.trace_last memory last
  exact ⟨trace,head,last,chain,cost,header.addNatSlot slot value amount,fields.2.2.1.trans fresh,fields.2.2.2.1,finalMemory.frame n k,
    fields.2.2.2.2,fun state member=>⟨(allResources state member).1,(allResources state member).2,pcRange state member⟩⟩

end PDCompute.NatControl
