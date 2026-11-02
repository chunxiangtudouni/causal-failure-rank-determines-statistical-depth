module

public import Paid.PDCompute_SolverCompareBits_164
public import Paid.PDCompute_SolverScanTestMemory_064
public import Paid.PDCompute_SolverHeaderFrame_099

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult)
open PDROC.CalibrationRow.Operand

/-- This is the ORIGINAL035 .index/.value comparison, not the different
generic .total/.value comparison. Frozen single-ISA primitives pay both
real reads and the actual lessEqual flag assignment. -/
theorem rangeCompareCode_prefix_safe (input : List Cell) (before : State) (base budget : ℕ) (values : ℕ → Cell)
    (index last : ℕ) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hi : values 25=.natural index) (hl : values 6=.natural last) (safe : RootD27.Bits.SafeBits before budget)
    (small : 4≤budget) (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (before.pc+7)≤budget) :
    PrefixSafe input rangeCompareCode before budget := by
  let first:=loadSlotResult before base 25 .index
  let loaded:=loadSlotResult first base 6 .value
  have slotBits (slot : ℕ) (inside : slot<headerWords) : 1+natBits (base+slot)≤budget :=
    (Nat.add_le_add_left (natBits_mono (by omega : base+slot≤base+headerWords)) 1).trans addressBits
  have firstRun:=(header.loadSlot_execute input 25 .index (by decide) fresh).1
  have firstSafe:=PrefixSafe.loadSlot input before base 25 budget .index safe fresh (header.live 25 (by decide)) (slotBits 25 (by decide))
    ((natBits_mono (by omega : before.pc+3≤before.pc+7)).trans pcBits)
  have firstBound:=firstSafe.final firstRun
  have firstFresh : first.register .fresh=.natural base := (loadSlotResult_fresh before base 25 .index (by decide)).trans fresh
  have firstHeader : Header first base values := header
  have secondRun:=(firstHeader.loadSlot_execute input 6 .value (by decide) firstFresh).1
  have secondSafe:=PrefixSafe.loadSlot input first base 6 budget .value firstBound firstFresh (firstHeader.live 6 (by decide)) (slotBits 6 (by decide))
    ((natBits_mono (by change before.pc+3+3≤before.pc+7; omega)).trans pcBits)
  have loadedBound:=secondSafe.final secondRun
  have firstIndex : first.register .index=.natural index := (header.loadSlot_execute input 25 .index (by decide) fresh).2.trans hi
  have loadedIndex : loaded.register .index=.natural index := by
    simpa only [loaded,loadSlotResult,State.set,Function.update_of_ne (by decide : (.index : Register)≠.value),
      Function.update_of_ne (by decide : (.index : Register)≠.address)] using firstIndex
  have loadedValue : loaded.register .value=.natural last := (firstHeader.loadSlot_execute input 6 .value (by decide) firstFresh).2.trans hl
  have zeroBits : (.natural 0 : Cell).bits≤budget := by norm_num [Cell.bits,natBits]; omega
  have oneBits : (.natural 1 : Cell).bits≤budget := by norm_num [Cell.bits,natBits]; omega
  have comparisonPC : natBits (loaded.pc+1)≤budget := by simpa only [loaded,first,loadSlotResult,Nat.add_assoc] using pcBits
  have compareSafe:=PrefixSafe.natCompare input loaded budget .lessEqual .flag .index .value index last loadedBound loadedIndex loadedValue zeroBits oneBits comparisonPC
  have leftRun : linearExecute input (loadSlot 25 .index++loadSlot 6 .value) before=some loaded := by
    rw [PDLower.CalibrationCompute.linearExecute_append,firstRun,Option.bind_some]
    exact secondRun
  exact PrefixSafe.append input _ _ before loaded budget leftRun
    (PrefixSafe.append input _ _ before first budget firstRun firstSafe secondSafe) compareSafe

/-- Actual112-op scan test, including the real loop-enter/loop-exit
control edge, at one complete-state caller budget. -/
theorem scanKernel_test_trace_bits (mode : ReaderMode) (program : Program) (input : List Cell) (origin : ℕ)
    (fetch : FetchesCode program origin (scanKernel mode origin)) (before : State)
    (base n k index last budget : ℕ) (values : ℕ → Cell)
    (hpc : before.pc=origin) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hi : values 25=.natural index) (hl : values 6=.natural last) (safe : RootD27.Bits.SafeBits before budget)
    (small : 4≤budget) (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (origin+112)≤budget) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤135 ∧
      Header after base values ∧ after.register .fresh=.natural base ∧ after.pc=(if index≤last then origin+8 else origin+112) ∧
      Frame before after base n k ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let compared:=rangeCompareResult before base index last
  let after : State:={compared with pc:=if index≤last then origin+8 else origin+112}
  have compareCounter : natBits (before.pc+7)≤budget :=
    (natBits_mono (by rw [hpc]; omega : before.pc+7≤origin+112)).trans pcBits
  have bounded:=rangeCompareCode_prefix_safe input before base budget values index last header fresh hi hl safe small addressBits compareCounter
  have run:=rangeCompareCode_execute input before base values index last header fresh hi hl
  obtain ⟨trace,head,lastState,chain,cost,resources⟩:=PDCompute.Pack.linearExecute_trace_invariant program input rangeCompareCode rangeCompareCode_straight
    before compared (scanKernel_range_fetch mode program origin fetch before hpc) run
    (fun state=>HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget) (by
      intro count bound state executed
      exact ⟨rangeCompareCode_memory input before state base index last values header fresh hi hl count bound executed,bounded count state executed⟩)
  have memory : ∀ state∈trace,HeaderMemory before state base := fun state member=>(resources state member).1
  have allSafe : ∀ state∈trace,RootD27.Bits.SafeBits state budget := fun state member=>(resources state member).2
  have fields:=rangeCompareResult_fields before base index last
  have branchFetch : program[compared.pc]?=some (.branchZero .flag (origin+112) (origin+8)) := by
    rw [fields.2.2.2.2.1,hpc]
    exact (fetch 7 (by rw [scanKernel_length]; omega)).trans (by rfl)
  have actual : step program input compared=some after := by
    unfold step
    rw [branchFetch]
    have flagValue : compared.register .flag=.natural (if index≤last then 1 else 0) := fields.2.2.2.1
    by_cases inside : index≤last <;> simp [Instruction.execute,flagValue,Cell.nat?,after,inside]
  have afterSafe : RootD27.Bits.SafeBits after budget := (allSafe compared (List.mem_of_getLast? lastState)).withPC _ (by
    split
    · exact (natBits_mono (by omega : origin+8≤origin+112)).trans pcBits
    · exact pcBits)
  have appended:=chain_append_control program input trace compared after chain lastState actual
  have nonempty : trace≠[] := by intro empty; rw [empty] at head; cases head
  have afterMemory : HeaderMemory before after base := (HeaderMemory.trace_last memory lastState).trans (HeaderMemory.of_unchanged base rfl rfl rfl)
  refine ⟨trace++[after],after,?_,by simp,appended.1,?_,header,fields.2.2.1.trans fresh,rfl,afterMemory.frame n k,rfl,
    appendTrace_memory trace before after base memory afterMemory,?_⟩
  · simpa only [List.head?_append_of_ne_nil trace nonempty] using head
  · have bound:=appended.2
    change time program trace≤120 at cost
    omega
  · intro state member
    rcases List.mem_append.mp member with old|new
    · exact allSafe state old
    · have same:=List.mem_singleton.mp new
      subst state
      exact afterSafe

end PDCompute.Solver
