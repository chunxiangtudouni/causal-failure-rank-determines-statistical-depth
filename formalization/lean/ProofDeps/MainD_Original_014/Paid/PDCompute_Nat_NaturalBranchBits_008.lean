module
public import Paid.PDCompute_Nat_SlotBits_001
public import Paid.PDCompute_SolverNatBranch_089

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000
@[expose] public section
namespace PDCompute.NatControl
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute loadSlot loadSlotResult)
open PDROC.CalibrationRow.Operand

theorem naturalCompare_prefix_safe (input : List Cell) (before : State) (base budget left right : ℕ)
    (comparison : Comparison) (x y : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (fresh : before.register .fresh=.natural base) (leftInside : left<headerWords) (rightInside : right<headerWords)
    (leftValue : values left=.natural x) (rightValue : values right=.natural y) (safe : RootD27.Bits.SafeBits before budget)
    (oneBits : (.natural 1 : Cell).bits≤budget) (addressBits : 1+natBits (base+headerWords)≤budget)
    (pcBits : natBits (before.pc+7)≤budget) : PrefixSafe input (naturalCompareCode comparison left right) before budget := by
  let first:=loadSlotResult before base left .total
  let loaded:=loadSlotResult first base right .value
  have slotBits (slot : ℕ) (inside : slot<headerWords) : 1+natBits (base+slot)≤budget :=
    (Nat.add_le_add_left (natBits_mono (by omega : base+slot≤base+headerWords)) 1).trans addressBits
  have firstRun:=(header.loadSlot_execute input left .total leftInside fresh).1
  have firstSafe:=PrefixSafe.loadSlot input before base left budget .total safe fresh (header.live left leftInside) (slotBits left leftInside)
    ((natBits_mono (by omega : before.pc+3≤before.pc+7)).trans pcBits)
  have firstBound:=firstSafe.final firstRun
  have firstFresh : first.register .fresh=.natural base := (loadSlotResult_fresh before base left .total (by decide)).trans fresh
  have firstHeader : Header first base values := header
  have secondRun:=(firstHeader.loadSlot_execute input right .value rightInside firstFresh).1
  have secondPC : natBits (first.pc+3)≤budget :=
    (natBits_mono (by change before.pc+3+3≤before.pc+7; omega)).trans pcBits
  have secondSafe:=PrefixSafe.loadSlot input first base right budget .value firstBound firstFresh (firstHeader.live right rightInside)
    (slotBits right rightInside) secondPC
  have loadedBound:=secondSafe.final secondRun
  have loadedFresh : loaded.register .fresh=.natural base := (loadSlotResult_fresh first base right .value (by decide)).trans firstFresh
  have firstTotal : first.register .total=.natural x := (header.loadSlot_execute input left .total leftInside fresh).2.trans leftValue
  have loadedTotal : loaded.register .total=.natural x := by
    simpa only [loaded,loadSlotResult,State.set,Function.update_of_ne (by decide : (.total : Register)≠.value),
      Function.update_of_ne (by decide : (.total : Register)≠.address)] using firstTotal
  have loadedValue : loaded.register .value=.natural y := (firstHeader.loadSlot_execute input right .value rightInside firstFresh).2.trans rightValue
  have zeroBits : (.natural 0 : Cell).bits≤budget:=by
    have bound:=natBits_mono (by decide : 0≤1)
    change 1+natBits 1≤budget at oneBits
    change 1+natBits 0≤budget
    omega
  have comparePC : natBits (loaded.pc+1)≤budget:=by
    change natBits (before.pc+3+3+1)≤budget
    simpa only [Nat.add_assoc] using pcBits
  have comparedSafe:=PrefixSafe.natCompare input loaded budget comparison .flag .total .value x y loadedBound loadedTotal loadedValue zeroBits oneBits comparePC
  have firstParts:=PrefixSafe.append input (loadSlot left .total) (loadSlot right .value) before first budget firstRun firstSafe secondSafe
  have firstPartsRun : linearExecute input (loadSlot left .total++loadSlot right .value) before=some loaded:=by
    rw [PDLower.CalibrationCompute.linearExecute_append,firstRun,Option.bind_some]
    exact secondRun
  exact PrefixSafe.append input _ [.natCompare comparison .flag .total .value] before loaded budget firstPartsRun firstParts comparedSafe

theorem naturalCompare_trace_bits (program : Program) (input : List Cell) (before : State)
    (base left right x y budget : ℕ) (comparison : Comparison) (values : ℕ → Cell)
    (header : Header before base values) (leftInside : left<headerWords) (rightInside : right<headerWords)
    (leftValue : values left=.natural x) (rightValue : values right=.natural y) (fresh : before.register .fresh=.natural base)
    (safe : RootD27.Bits.SafeBits before budget) (oneBits : (.natural 1 : Cell).bits≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (before.pc+7)≤budget)
    (fetch : FetchesCode program before.pc (naturalCompareCode comparison left right)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (PDROC.D27Prepare.Program.comparisonResult before base left right (comparison.nat x y)) ∧
      trace.IsChain (fun a b=>step program input a=some b) ∧ time program trace≤120 ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have run:=PDROC.D27Prepare.Program.natCompareSlots_execute input before base left right x y comparison fresh
    (header.live left leftInside) (header.live right rightInside) ((header.value left leftInside).trans leftValue) ((header.value right rightInside).trans rightValue)
  have bounded:=naturalCompare_prefix_safe input before base budget left right comparison x y values header fresh leftInside rightInside leftValue rightValue safe oneBits addressBits pcBits
  obtain ⟨trace,head,last,chain,cost,invariant⟩:=PDCompute.Pack.linearExecute_trace_invariant program input (naturalCompareCode comparison left right)
    (naturalCompareCode_straight comparison left right) before _ fetch run (fun state=>HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget) (by
      intro count bound state execute
      exact ⟨naturalCompareCode_prefix_memory input before state base left right x y comparison values header leftInside rightInside leftValue rightValue fresh count bound execute,
        bounded count state execute⟩)
  exact ⟨trace,head,last,chain,cost,invariant⟩

theorem naturalBranch_trace_bits (program : Program) (input : List Cell) (before : State)
    (base n k left right x y whenZero whenNonzero budget : ℕ) (comparison : Comparison) (values : ℕ → Cell)
    (header : Header before base values) (hl : left < headerWords) (hr : right < headerWords)
    (hx : values left=.natural x) (hy : values right=.natural y) (hbase : before.register .fresh=.natural base)
    (safe : RootD27.Bits.SafeBits before budget) (oneBits : (.natural 1 : Cell).bits≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (before.pc+7)≤budget)
    (zeroPCBits : natBits whenZero≤budget) (nonzeroPCBits : natBits whenNonzero≤budget)
    (fetch : FetchesCode program before.pc (naturalBranchCode comparison left right whenZero whenNonzero)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 135 ∧ Header after base values ∧ after.register .fresh=.natural base ∧
      after.pc=(if comparison.nat x y then whenNonzero else whenZero) ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace, HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  let compared:=PDROC.D27Prepare.Program.comparisonResult before base left right (comparison.nat x y)
  let after : State:={compared with pc:=if comparison.nat x y then whenNonzero else whenZero}
  have compareFetch : FetchesCode program before.pc (naturalCompareCode comparison left right) := fetch.append_left
  obtain ⟨trace,head,last,chain,bound,invariant⟩:=
    naturalCompare_trace_bits program input before base left right x y budget comparison values header hl hr hx hy hbase safe oneBits addressBits pcBits compareFetch
  have memory : ∀ state∈trace,HeaderMemory before state base:=fun state member=>(invariant state member).1
  have comparedSafe : RootD27.Bits.SafeBits compared budget:=(invariant compared (List.mem_of_getLast? last)).2
  have afterBits : natBits (if comparison.nat x y then whenNonzero else whenZero)≤budget:=by split <;> assumption
  have afterSafe : RootD27.Bits.SafeBits after budget:=comparedSafe.withPC _ afterBits
  have fields:=PDROC.D27Prepare.Program.comparisonResult_fields before base left right (comparison.nat x y)
  have controlFetch : program[compared.pc]?=some (.branchZero .flag whenZero whenNonzero) := by
    rw [fields.2.2.2.2.1]
    have branchFetch:=fetch.append_right
    exact branchFetch 0 (by change 0 < 1; decide)
  have control : step program input compared=some after := by
    unfold step
    rw [controlFetch]
    have flagValue : compared.register .flag=.natural (if comparison.nat x y then 1 else 0) := fields.2.2.2.1
    cases boolean : comparison.nat x y <;> simp [Instruction.execute,flagValue,Cell.nat?,after,boolean]
  have appended:=chain_append_control program input trace compared after chain last control
  have nonempty : trace ≠ [] := by intro empty; simp only [empty,List.head?_nil,reduceCtorEq] at head
  have afterMemory : HeaderMemory before after base :=
    (HeaderMemory.trace_last memory last).trans (HeaderMemory.of_unchanged base rfl rfl rfl)
  refine ⟨trace++[after],after,?_,by simp,appended.1,?_,header,hbase,rfl,
    ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩,rfl,fun state member=>⟨appendTrace_memory trace before after base memory afterMemory state member,by
      rcases List.mem_append.mp member with earlier|last
      · exact (invariant state earlier).2
      · have same : state=after:=List.mem_singleton.mp last
        subst state
        exact afterSafe⟩⟩
  · simpa only [List.head?_append_of_ne_nil _ nonempty] using head
  · have cost:=appended.2
    omega


end PDCompute.NatControl
