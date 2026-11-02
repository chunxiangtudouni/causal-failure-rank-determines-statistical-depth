module

public import Paid.PDLower_CoreSearch_ClipBits_025
public import Paid.PDLower_CoreSearch_EntryBits_026

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch

theorem finalBracket_segment_bits (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (origin : ℕ) (before : State) (values : ℕ→Cell) (scale budget : ℕ)
    (position : before.pc=origin) (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (risk : values 3=.rational P.certificate.risk) (feeValue : values 5=.rational fee)
    (lowerPrice : values 14=.rational lower.multiplier) (upperPrice : values 15=.rational upper.multiplier)
    (lowerObs : values 16=.rational (P.solveRecord lower).observation)
    (lowerRep : values 17=.rational (P.solveRecord lower).repairs) (lowerRisk : values 18=.rational (P.solveRisk lower))
    (upperObs : values 19=.rational (P.solveRecord upper).observation)
    (upperRep : values 20=.rational (P.solveRecord upper).repairs) (upperRisk : values 21=.rational (P.solveRisk upper))
    (safe : RootD27.Bits.SafeBits before budget) (intrinsic : ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (origin+160)≤budget)
    (fetched : FetchesCode program origin (finalBracketCode origin)) :
    ∃ (after : State) (finalValues : ℕ→Cell),NumericSegment program input before after 3000 budget ∧
      Header after 0 finalValues ∧ KeepsLow values finalValues ∧ after.register .fresh=.natural 0 ∧ after.pc=origin+160 ∧
      after.heap 29=.rational (clipRat (P.mixtureWeight lower upper)) := by
  have codeEq : finalBracketCode origin=mixtureEntryCode origin++clipCode (origin+114) := by
    simp only [finalBracketCode,mixtureEntryCode,List.append_assoc]
  rw [codeEq] at fetched
  have clipFetch : FetchesCode program (origin+114) (clipCode (origin+114)) := by
    simpa only [mixtureEntryCode_length] using fetched.append_right
  obtain ⟨s1,run1,header1,keep1,fresh1,pc1⟩ := mixtureEntry_segment_bits P fee lower upper program input origin before values scale budget
    position header fresh risk feeValue lowerPrice upperPrice lowerObs lowerRep lowerRisk upperObs upperRep upperRisk safe intrinsic room addressBits
    ((natBits_mono (by omega : origin+114≤origin+160)).trans pcBits) fetched.append_left
  let v1 := mixtureEntryValues P fee lower upper values
  have small : 4≤budget := by unfold scalarValueBudget at room;omega
  obtain ⟨after,finalValues,run2,afterHeader,keep2,afterFresh,pc2,value⟩ := clip_segment_bits program input (origin+114) s1 v1
    (P.mixtureWeight lower upper) budget pc1 header1 fresh1 (by simp [v1,mixtureEntryValues]) run1.final.2 small addressBits
    (by simpa only [Nat.add_assoc] using pcBits) clipFetch
  exact ⟨after,finalValues,(run1.trans run2).mono (by decide),afterHeader,keep1.trans keep2,afterFresh,
    by simpa only [Nat.add_assoc] using pc2,value⟩

/-- Original complete final-bracket160-op producer, time/heap/output
and EVERY physical+numerical prefix on the same actualtrace. -/
theorem finalBracket_trace_bits (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (origin : ℕ) (before : State) (values : ℕ→Cell) (scale budget : ℕ)
    (position : before.pc=origin) (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (risk : values 3=.rational P.certificate.risk) (feeValue : values 5=.rational fee)
    (lowerPrice : values 14=.rational lower.multiplier) (upperPrice : values 15=.rational upper.multiplier)
    (lowerObs : values 16=.rational (P.solveRecord lower).observation)
    (lowerRep : values 17=.rational (P.solveRecord lower).repairs) (lowerRisk : values 18=.rational (P.solveRisk lower))
    (upperObs : values 19=.rational (P.solveRecord upper).observation)
    (upperRep : values 20=.rational (P.solveRecord upper).repairs) (upperRisk : values 21=.rational (P.solveRisk upper))
    (safe : RootD27.Bits.SafeBits before budget) (intrinsic : ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (origin+160)≤budget)
    (fetched : FetchesCode program origin (finalBracketCode origin)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤3000 ∧
      after.register .fresh=.natural 0 ∧ after.pc=origin+160 ∧ after.heap 29=.rational (clipRat (P.mixtureWeight lower upper)) ∧
      after.output=before.output ∧ (∀ slot<29,after.heap slot=before.heap slot) ∧
      ∀ state∈trace,(MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0) ∧ RootD27.Bits.SafeBits state budget := by
  obtain ⟨after,finalValues,actual,afterHeader,kept,afterFresh,pc,value⟩ := finalBracket_segment_bits P fee lower upper
    program input origin before values scale budget position header fresh risk feeValue lowerPrice upperPrice lowerObs lowerRep lowerRisk
    upperObs upperRep upperRisk safe intrinsic room addressBits pcBits fetched
  have finalMemory := actual.final.1
  obtain ⟨trace,head,last,chain,cost,properties⟩ := actual
  exact ⟨trace,after,head,last,chain,cost,afterFresh,pc,value,finalMemory.2.2.2,kept.heap header afterHeader,properties⟩

theorem selectorZero_trace_bits (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell) (budget : ℕ)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0) (safe : RootD27.Bits.SafeBits before budget)
    (small : 4≤budget) (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (before.pc+4)≤budget)
    (fetched : FetchesCode program before.pc (headerCode selectorZeroCommands)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤75 ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+4 ∧ after.heap 29=.rational 0 ∧
      after.output=before.output ∧ (∀ slot<29,after.heap slot=before.heap slot) ∧
      ∀ state∈trace,(MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0) ∧ RootD27.Bits.SafeBits state budget := by
  have valueBits : (.rational (0:ℚ) : Cell).bits≤budget := by
    norm_num [Cell.bits,ratEncodingBits,ratNumBits,ratDenBits,natBits]
    omega
  obtain ⟨after,actual,afterHeader,afterFresh,pc⟩ := literal_segment_bits program input before values 29 budget (.rational 0) (by decide)
    header fresh safe valueBits addressBits pcBits fetched
  have kept : KeepsLow values (Function.update values 29 (.rational 0)) := (KeepsLow.refl values).update 29 _ (by decide)
  have value := afterHeader.value 29 (by decide)
  have finalMemory := actual.final.1
  obtain ⟨trace,head,last,chain,cost,properties⟩ := actual
  exact ⟨trace,after,head,last,chain,cost,afterFresh,pc,by simpa only [Nat.zero_add,Function.update_self] using value,
    finalMemory.2.2.2,kept.heap header afterHeader,properties⟩

theorem selectorZeroRisk_trace_bits (P : Parameters) (fee : ℚ) (frontend : CachedFrontend)
    (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell) (budget : ℕ)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0) (guard : P.zeroChargeRisk fee≤P.certificate.risk)
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+4)≤budget) (fetched : FetchesCode program before.pc (headerCode selectorZeroCommands)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤75 ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+4 ∧ after.heap 29=.rational (selectorWeightRat P fee frontend) ∧
      after.output=before.output ∧ (∀ slot<29,after.heap slot=before.heap slot) ∧
      ∀ state∈trace,(MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0) ∧ RootD27.Bits.SafeBits state budget := by
  simpa only [selector_source_zero P fee frontend guard] using
    selectorZero_trace_bits program input before values budget header fresh safe small addressBits pcBits fetched

theorem selectorExact_trace_bits (P : Parameters) (fee : ℚ) (frontend : CachedFrontend) (solution : MultiplierSolve)
    (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell) (budget : ℕ)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0) (exactState : frontend.state=.exact solution)
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+4)≤budget) (fetched : FetchesCode program before.pc (headerCode selectorZeroCommands)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤75 ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+4 ∧ after.heap 29=.rational (selectorWeightRat P fee frontend) ∧
      after.output=before.output ∧ (∀ slot<29,after.heap slot=before.heap slot) ∧
      ∀ state∈trace,(MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0) ∧ RootD27.Bits.SafeBits state budget := by
  simpa only [selector_source_exact P fee frontend solution exactState] using
    selectorZero_trace_bits program input before values budget header fresh safe small addressBits pcBits fetched

end PDLower.CoreSearch
