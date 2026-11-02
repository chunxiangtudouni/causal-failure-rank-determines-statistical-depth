module

public import Paid.PDLower_CoreSearch_LiteralBits_022
public import Paid.PDLower_CoreSearch_CompareBits_021
public import Paid.PDLower_CoreSearch_ClipTrace_012

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch

theorem zeroLiteral_segment_bits (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell) (budget : ℕ)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0) (safe : RootD27.Bits.SafeBits before budget)
    (small : 4≤budget) (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (before.pc+4)≤budget)
    (fetched : FetchesCode program before.pc (headerCode zeroLiteralCommands)) :
    ∃ after : State,NumericSegment program input before after 75 budget ∧ Header after 0 (Function.update values 42 (.rational 0)) ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+4 := by
  have valueBits : (.rational (0:ℚ) : Cell).bits≤budget := by
    norm_num [Cell.bits,ratEncodingBits,ratNumBits,ratDenBits,natBits]
    omega
  exact literal_segment_bits program input before values 42 budget (.rational 0) (by decide) header fresh safe valueBits addressBits pcBits fetched

theorem clipZero_segment_bits (weight : ℚ) (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell) (budget : ℕ)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0) (below : weight<0)
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+4)≤budget) (fetched : FetchesCode program before.pc (headerCode selectorZeroCommands)) :
    ∃ after : State,NumericSegment program input before after 75 budget ∧ Header after 0 (Function.update values 29 (.rational (clipRat weight))) ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+4 := by
  have valueBits : (.rational (0:ℚ) : Cell).bits≤budget := by
    norm_num [Cell.bits,ratEncodingBits,ratNumBits,ratDenBits,natBits]
    omega
  simpa only [clip_zero weight below] using
    literal_segment_bits program input before values 29 budget (.rational 0) (by decide) header fresh safe valueBits addressBits pcBits fetched

theorem clipOne_segment_bits (weight : ℚ) (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell) (budget : ℕ)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0) (above : 1<weight)
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+4)≤budget) (fetched : FetchesCode program before.pc (headerCode selectorOneCommands)) :
    ∃ after : State,NumericSegment program input before after 75 budget ∧ Header after 0 (Function.update values 29 (.rational (clipRat weight))) ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+4 := by
  have valueBits : (.rational (1:ℚ) : Cell).bits≤budget := by
    norm_num [Cell.bits,ratEncodingBits,ratNumBits,ratDenBits,natBits]
    omega
  simpa only [clip_one weight above] using
    literal_segment_bits program input before values 29 budget (.rational 1) (by decide) header fresh safe valueBits addressBits pcBits fetched

theorem clipCopy_segment_bits (weight : ℚ) (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell) (budget : ℕ)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0) (ratio : values 31=.rational weight)
    (notBelow : ¬weight<0) (notAbove : ¬1<weight) (safe : RootD27.Bits.SafeBits before budget)
    (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (before.pc+6)≤budget)
    (fetched : FetchesCode program before.pc (headerCode selectorCopyCommands)) :
    ∃ after : State,NumericSegment program input before after 105 budget ∧ Header after 0 (Function.update values 29 (.rational (clipRat weight))) ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+6 := by
  simpa only [clip_inside weight notBelow notAbove,ratio] using
    copy_segment_bits program input before values 31 29 budget (by decide) (by decide) header fresh safe addressBits pcBits fetched

end PDLower.CoreSearch
