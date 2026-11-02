module

public import Paid.PDCompute_SolverCompareBits_164
public import Paid.PDCompute_SolverRatBranch_098
public import Paid.PDCompute_SolverHeaderFrame_099

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult)
open PDROC.CalibrationRow.Operand

/-- Real generic rational comparison uses the frozen ISA bit primitive;
both original heap operands are loaded under the SAME caller budget. -/
theorem rationalCompareCode_prefix_safe (input : List Cell) (before : State) (base left right budget : ℕ) (values : ℕ → Cell)
    (x y : ℚ) (comparison : Comparison) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hl : left<headerWords) (hr : right<headerWords) (hx : values left=.rational x) (hy : values right=.rational y)
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (before.pc+7)≤budget) :
    PrefixSafe input (rationalCompareCode comparison left right) before budget := by
  let first:=loadSlotResult before base left .total
  let loaded:=loadSlotResult first base right .value
  let compared:=PDROC.D27Prepare.Program.comparisonResult before base left right (comparison.rat x y)
  have slotBits (slot : ℕ) (inside : slot<headerWords) : 1+natBits (base+slot)≤budget :=
    (Nat.add_le_add_left (natBits_mono (by omega : base+slot≤base+headerWords)) 1).trans addressBits
  have firstRun:=(header.loadSlot_execute input left .total hl fresh).1
  have firstSafe:=PrefixSafe.loadSlot input before base left budget .total safe fresh (header.live left hl) (slotBits left hl)
    ((natBits_mono (by omega : before.pc+3≤before.pc+7)).trans pcBits)
  have firstBound:=firstSafe.final firstRun
  have firstFresh : first.register .fresh=.natural base := (loadSlotResult_fresh before base left .total (by decide)).trans fresh
  have firstHeader : Header first base values := header
  have secondRun:=(firstHeader.loadSlot_execute input right .value hr firstFresh).1
  have secondSafe:=PrefixSafe.loadSlot input first base right budget .value firstBound firstFresh (firstHeader.live right hr) (slotBits right hr)
    ((natBits_mono (by change before.pc+3+3≤before.pc+7; omega)).trans pcBits)
  have loadedBound:=secondSafe.final secondRun
  have firstTotal : first.register .total=.rational x := (header.loadSlot_execute input left .total hl fresh).2.trans hx
  have loadedTotal : loaded.register .total=.rational x := by
    simpa only [loaded,loadSlotResult,State.set,Function.update_of_ne (by decide : (.total : Register)≠.value),
      Function.update_of_ne (by decide : (.total : Register)≠.address)] using firstTotal
  have loadedValue : loaded.register .value=.rational y := (firstHeader.loadSlot_execute input right .value hr firstFresh).2.trans hy
  have actual : Instruction.execute input (.ratCompare comparison .flag .total .value) loaded=some compared := by
    simp [Instruction.execute,loadedTotal,loadedValue,Cell.rat?,compared,PDROC.D27Prepare.Program.comparisonResult]
    rfl
  have zeroBits : (.natural 0 : Cell).bits≤budget := by norm_num [Cell.bits,natBits]; omega
  have oneBits : (.natural 1 : Cell).bits≤budget := by norm_num [Cell.bits,natBits]; omega
  have comparisonPC : natBits (loaded.pc+1)≤budget := by simpa only [loaded,first,loadSlotResult,Nat.add_assoc] using pcBits
  have comparedBound:=PDLower.CalibrationCompute.ratCompare_execute_safe input loaded compared comparison .flag .total .value x y budget
    loadedBound loadedTotal loadedValue zeroBits oneBits comparisonPC actual
  have compareSafe:=PrefixSafe.singleton input (.ratCompare comparison .flag .total .value) loaded compared budget actual loadedBound comparedBound
  have leftRun : linearExecute input (loadSlot left .total++loadSlot right .value) before=some loaded := by
    rw [PDLower.CalibrationCompute.linearExecute_append,firstRun,Option.bind_some]
    exact secondRun
  exact PrefixSafe.append input _ _ before loaded budget leftRun
    (PrefixSafe.append input _ _ before first budget firstRun firstSafe secondSafe) compareSafe

theorem rationalCompare_trace_bits (program : Program) (input : List Cell) (before : State)
    (base left right budget : ℕ) (x y : ℚ) (comparison : Comparison) (values : ℕ → Cell)
    (header : Header before base values) (hl : left<headerWords) (hr : right<headerWords)
    (hx : values left=.rational x) (hy : values right=.rational y) (fresh : before.register .fresh=.natural base)
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (before.pc+7)≤budget)
    (fetch : FetchesCode program before.pc (rationalCompareCode comparison left right)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (PDROC.D27Prepare.Program.comparisonResult before base left right (comparison.rat x y)) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤120 ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have run:=PDROC.D27Prepare.Program.ratCompareSlots_execute input before base left right x y comparison fresh
    (header.live left hl) (header.live right hr) ((header.value left hl).trans hx) ((header.value right hr).trans hy)
  have bounded:=rationalCompareCode_prefix_safe input before base left right budget values x y comparison header fresh hl hr hx hy safe small addressBits pcBits
  obtain ⟨trace,head,last,chain,cost,invariant⟩:=PDCompute.Pack.linearExecute_trace_invariant program input (rationalCompareCode comparison left right)
    (rationalCompareCode_straight comparison left right) before _ fetch run (fun state=>HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget) (by
      intro count bound state executed
      exact ⟨rationalCompareCode_prefix_memory input before state base left right x y comparison values header hl hr hx hy fresh count bound executed,
        bounded count state executed⟩)
  exact ⟨trace,head,last,chain,cost,invariant⟩

/-- Original8-op rational branch including BOTH actual jump targets.
Only the chosen true successor is appended; complete-state bits and
memory describe precisely this functional witness. -/
theorem rationalBranch_trace_bits (program : Program) (input : List Cell) (before : State)
    (base n k left right whenZero whenNonzero budget : ℕ) (x y : ℚ) (comparison : Comparison) (values : ℕ → Cell)
    (header : Header before base values) (hl : left<headerWords) (hr : right<headerWords)
    (hx : values left=.rational x) (hy : values right=.rational y) (fresh : before.register .fresh=.natural base)
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (before.pc+7)≤budget)
    (zeroBits : natBits whenZero≤budget) (nonzeroBits : natBits whenNonzero≤budget)
    (fetch : FetchesCode program before.pc (rationalBranchCode comparison left right whenZero whenNonzero)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤135 ∧ Header after base values ∧ after.register .fresh=.natural base ∧
      after.pc=(if comparison.rat x y then whenNonzero else whenZero) ∧ Frame before after base n k ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let compared:=PDROC.D27Prepare.Program.comparisonResult before base left right (comparison.rat x y)
  let after : State:={compared with pc:=if comparison.rat x y then whenNonzero else whenZero}
  obtain ⟨trace,head,last,chain,cost,resources⟩:=rationalCompare_trace_bits program input before base left right budget x y comparison values
    header hl hr hx hy fresh safe small addressBits pcBits fetch.append_left
  have memory : ∀ state∈trace,HeaderMemory before state base := fun state member=>(resources state member).1
  have bounded : ∀ state∈trace,RootD27.Bits.SafeBits state budget := fun state member=>(resources state member).2
  have fields:=PDROC.D27Prepare.Program.comparisonResult_fields before base left right (comparison.rat x y)
  have controlFetch : program[compared.pc]?=some (.branchZero .flag whenZero whenNonzero) := by
    rw [fields.2.2.2.2.1]
    exact fetch.append_right 0 (by change 0<1; decide)
  have actual : step program input compared=some after := by
    unfold step
    rw [controlFetch]
    have flagValue : compared.register .flag=.natural (if comparison.rat x y then 1 else 0) := fields.2.2.2.1
    cases boolean : comparison.rat x y <;> simp [Instruction.execute,flagValue,Cell.nat?,after,boolean]
  have afterSafe : RootD27.Bits.SafeBits after budget :=
    (bounded compared (List.mem_of_getLast? last)).withPC _ (by split <;> assumption)
  have appended:=chain_append_control program input trace compared after chain last actual
  have nonempty : trace≠[] := by intro empty; rw [empty] at head; cases head
  have afterMemory : HeaderMemory before after base := (HeaderMemory.trace_last memory last).trans (HeaderMemory.of_unchanged base rfl rfl rfl)
  refine ⟨trace++[after],after,?_,by simp,appended.1,?_,header,fresh,rfl,afterMemory.frame n k,rfl,
    appendTrace_memory trace before after base memory afterMemory,?_⟩
  · simpa only [List.head?_append_of_ne_nil trace nonempty] using head
  · have bound:=appended.2
    omega
  · intro state member
    rcases List.mem_append.mp member with old|new
    · exact bounded state old
    · have same:=List.mem_singleton.mp new
      subst state
      exact afterSafe

end PDCompute.Solver
