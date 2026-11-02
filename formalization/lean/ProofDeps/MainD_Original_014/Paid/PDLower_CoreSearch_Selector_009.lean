module

public import Paid.PDLower_CoreSearch_SelectorBodies_008
public import Paid.PDLower_CoreSearch_Compare_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch

theorem clip_zero (weight : ℚ) (below : weight<0) : clipRat weight=0 := by
  have one : weight≤1 := below.le.trans (by norm_num)
  unfold clipRat
  rw [min_eq_right one,max_eq_left below.le]

theorem clip_one (weight : ℚ) (above : 1<weight) : clipRat weight=1 := by
  unfold clipRat
  rw [min_eq_left above.le]
  norm_num

theorem clip_inside (weight : ℚ) (notBelow : ¬weight<0) (notAbove : ¬1<weight) : clipRat weight=weight := by
  unfold clipRat
  rw [min_eq_right (le_of_not_gt notAbove),max_eq_right (le_of_not_gt notBelow)]

theorem selector_source_zero (P : Parameters) (fee : ℚ) (frontend : CachedFrontend)
    (guard : P.zeroChargeRisk fee≤P.certificate.risk) : selectorWeightRat P fee frontend=0 := by
  simp only [selectorWeightRat,ite_eq_left guard]

theorem selector_source_exact (P : Parameters) (fee : ℚ) (frontend : CachedFrontend) (solution : MultiplierSolve)
    (exactState : frontend.state=.exact solution) : selectorWeightRat P fee frontend=0 := by
  simp [selectorWeightRat,exactState]

theorem selector_source_bracket (P : Parameters) (fee : ℚ) (frontend : CachedFrontend) (lower upper : MultiplierSolve)
    (guard : ¬P.zeroChargeRisk fee≤P.certificate.risk) (bracket : frontend.state=.bracket lower upper) :
    selectorWeightRat P fee frontend=clipRat (P.mixtureWeight lower upper) := by
  simp only [selectorWeightRat,ite_eq_right guard,bracket]

theorem zeroRiskGuard_trace (P : Parameters) (fee : ℚ) (program : Program) (input : List Cell)
    (before : State) (values : ℕ→Cell) (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (zeroRisk : values 12=.rational (P.zeroChargeRisk fee)) (risk : values 3=.rational P.certificate.risk)
    (fetched : FetchesCode program before.pc (comparisonStoredCode .lessEqual 12 3)) :
    ∃ trace : List State,trace.head?=some before ∧
      trace.getLast?=some (comparisonStoredResult before 12 3 (decide (P.zeroChargeRisk fee≤P.certificate.risk))) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤165 ∧
      Header (comparisonStoredResult before 12 3 (decide (P.zeroChargeRisk fee≤P.certificate.risk))) 0
        (Function.update values 40 (.natural (if P.zeroChargeRisk fee≤P.certificate.risk then 1 else 0))) ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  simpa only [Comparison.rat,decide_eq_true_eq] using
    comparisonStored_trace .lessEqual 12 3 (P.zeroChargeRisk fee) P.certificate.risk program input before values header
    (by decide) (by decide) zeroRisk risk fresh fetched

theorem clipLowerGuard_trace (weight : ℚ) (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (ratio : values 31=.rational weight) (zero : values 41=.rational 0)
    (fetched : FetchesCode program before.pc (comparisonStoredCode .less 31 41)) :
    ∃ trace : List State,trace.head?=some before ∧
      trace.getLast?=some (comparisonStoredResult before 31 41 (decide (weight<0))) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤165 ∧
      Header (comparisonStoredResult before 31 41 (decide (weight<0))) 0
        (Function.update values 40 (.natural (if weight<0 then 1 else 0))) ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  exact comparisonStored_trace .less 31 41 weight 0 program input before values header (by decide) (by decide) ratio zero fresh fetched

theorem clipUpperGuard_trace (weight : ℚ) (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (one : values 42=.rational 1) (ratio : values 31=.rational weight)
    (fetched : FetchesCode program before.pc (comparisonStoredCode .less 42 31)) :
    ∃ trace : List State,trace.head?=some before ∧
      trace.getLast?=some (comparisonStoredResult before 42 31 (decide (1<weight))) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤165 ∧
      Header (comparisonStoredResult before 42 31 (decide (1<weight))) 0
        (Function.update values 40 (.natural (if 1<weight then 1 else 0))) ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  exact comparisonStored_trace .less 42 31 1 weight program input before values header (by decide) (by decide) one ratio fresh fetched

theorem clipZero_trace (weight : ℚ) (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0) (below : weight<0)
    (fetched : FetchesCode program before.pc (headerCode selectorZeroCommands)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤75 ∧
      Header after 0 (Function.update values 29 (.rational (clipRat weight))) ∧ after.register .fresh=.natural 0 ∧
      after.pc=before.pc+4 ∧ after.output=before.output ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  simpa only [clip_zero weight below] using selectorZero_trace program input before values header fresh fetched

theorem clipOne_trace (weight : ℚ) (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0) (above : 1<weight)
    (fetched : FetchesCode program before.pc (headerCode selectorOneCommands)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤75 ∧
      Header after 0 (Function.update values 29 (.rational (clipRat weight))) ∧ after.register .fresh=.natural 0 ∧
      after.pc=before.pc+4 ∧ after.output=before.output ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  simpa only [clip_one weight above] using selectorOne_trace program input before values header fresh fetched

theorem clipCopy_trace (weight : ℚ) (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0) (ratio : values 31=.rational weight)
    (notBelow : ¬weight<0) (notAbove : ¬1<weight)
    (fetched : FetchesCode program before.pc (headerCode selectorCopyCommands)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤105 ∧
      Header after 0 (Function.update values 29 (.rational (clipRat weight))) ∧ after.register .fresh=.natural 0 ∧
      after.pc=before.pc+6 ∧ after.output=before.output ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  simpa only [clip_inside weight notBelow notAbove] using selectorCopy_trace program input before values weight header fresh ratio fetched

end PDLower.CoreSearch
