module

public import Paid.PDLower_CoreSearch_Guards_007
public import Paid.PDLower_CoreSearch_Selector_009
public import Paid.PDLower_CoreSearch_ScalarSegment_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch

theorem selectorConstants_length : (headerCode selectorConstantsCommands).length=8 := rfl
theorem selectorCopy_length : (headerCode selectorCopyCommands).length=6 := rfl
theorem selectorOne_length : (headerCode selectorOneCommands).length=4 := rfl
theorem selectorZero_length : (headerCode selectorZeroCommands).length=4 := rfl
theorem zeroLiteral_length : (headerCode zeroLiteralCommands).length=4 := rfl

/-- Actual clipping control, with both comparison constants produced at
entry and each true branch writing the original selector scalar to29. -/
def clipCode (origin : ℕ) : List Instruction :=
  headerCode selectorConstantsCommands++comparisonStoredCode .less 31 41++
  [.branchZero .flag (origin+19) (origin+42)]++comparisonStoredCode .less 42 31++
  [.branchZero .flag (origin+30) (origin+37)]++headerCode selectorCopyCommands++
  [.jump (origin+46)]++headerCode selectorOneCommands++[.jump (origin+46)]++headerCode selectorZeroCommands

theorem clipCode_length (origin : ℕ) : (clipCode origin).length=46 := rfl

/-- Final bracket entry REALLY recomputes the CURRENT weight. It never
reads incoming31/41/42 before the corresponding actual producer. -/
def finalBracketCode (origin : ℕ) : List Instruction :=
  headerCode mixturePrepareCommands++headerCode zeroLiteralCommands++comparisonStoredCode .equal 30 42++
  [.branchZero .flag (origin+99) (origin+110)]++headerCode mixtureRatioCommands++
  [.jump (origin+114)]++headerCode mixtureZeroCommands++clipCode (origin+114)

theorem finalBracketCode_length (origin : ℕ) : (finalBracketCode origin).length=160 := by
  simp only [finalBracketCode,List.length_append,mixturePrepareCode_length,zeroLiteral_length,comparisonStored_length,
    List.length_singleton,mixtureRatio_length,mixtureZero_length,clipCode_length]

theorem single_fetch {program : Program} {position : ℕ} {instruction : Instruction}
    (fetched : FetchesCode program position [instruction]) : program[position]?=some instruction := by
  simpa using fetched 0 (by change 0<1;decide)

structure ClipFetch (program : Program) (origin : ℕ) : Prop where
  constants : FetchesCode program origin (headerCode selectorConstantsCommands)
  lower : FetchesCode program (origin+8) (comparisonStoredCode .less 31 41)
  lowerBranch : program[origin+18]?=some (.branchZero .flag (origin+19) (origin+42))
  upper : FetchesCode program (origin+19) (comparisonStoredCode .less 42 31)
  upperBranch : program[origin+29]?=some (.branchZero .flag (origin+30) (origin+37))
  copy : FetchesCode program (origin+30) (headerCode selectorCopyCommands)
  copyJump : program[origin+36]?=some (.jump (origin+46))
  one : FetchesCode program (origin+37) (headerCode selectorOneCommands)
  oneJump : program[origin+41]?=some (.jump (origin+46))
  zero : FetchesCode program (origin+42) (headerCode selectorZeroCommands)

theorem clipCode_fetches (program : Program) (origin : ℕ) (fetched : FetchesCode program origin (clipCode origin)) :
    ClipFetch program origin := by
  simp only [clipCode,List.append_assoc] at fetched
  have f1 := fetched.append_right
  have f2 := f1.append_right
  have f3 := f2.append_right
  have f4 := f3.append_right
  have f5 := f4.append_right
  have f6 := f5.append_right
  have f7 := f6.append_right
  have f8 := f7.append_right
  have f9 := f8.append_right
  refine ⟨fetched.append_left,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [selectorConstants_length] using f1.append_left
  · simpa only [selectorConstants_length,comparisonStored_length,Nat.add_assoc] using single_fetch f2.append_left
  · simpa only [selectorConstants_length,comparisonStored_length,List.length_singleton,Nat.add_assoc] using f3.append_left
  · simpa only [selectorConstants_length,comparisonStored_length,List.length_singleton,Nat.add_assoc] using single_fetch f4.append_left
  · simpa only [selectorConstants_length,comparisonStored_length,List.length_singleton,Nat.add_assoc] using f5.append_left
  · simpa only [selectorConstants_length,comparisonStored_length,List.length_singleton,selectorCopy_length,Nat.add_assoc] using single_fetch f6.append_left
  · simpa only [selectorConstants_length,comparisonStored_length,List.length_singleton,selectorCopy_length,Nat.add_assoc] using f7.append_left
  · simpa only [selectorConstants_length,comparisonStored_length,List.length_singleton,selectorCopy_length,selectorOne_length,Nat.add_assoc] using single_fetch f8.append_left
  · simpa only [selectorConstants_length,comparisonStored_length,List.length_singleton,selectorCopy_length,selectorOne_length,Nat.add_assoc] using f9

structure FinalBracketFetch (program : Program) (origin : ℕ) : Prop where
  prepare : FetchesCode program origin (headerCode mixturePrepareCommands)
  zeroLiteral : FetchesCode program (origin+84) (headerCode zeroLiteralCommands)
  denominator : FetchesCode program (origin+88) (comparisonStoredCode .equal 30 42)
  branch : program[origin+98]?=some (.branchZero .flag (origin+99) (origin+110))
  ratio : FetchesCode program (origin+99) (headerCode mixtureRatioCommands)
  ratioJump : program[origin+109]?=some (.jump (origin+114))
  zero : FetchesCode program (origin+110) (headerCode mixtureZeroCommands)
  clip : FetchesCode program (origin+114) (clipCode (origin+114))

theorem finalBracketCode_fetches (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (finalBracketCode origin)) : FinalBracketFetch program origin := by
  simp only [finalBracketCode,List.append_assoc] at fetched
  have f1 := fetched.append_right
  have f2 := f1.append_right
  have f3 := f2.append_right
  have f4 := f3.append_right
  have f5 := f4.append_right
  have f6 := f5.append_right
  have f7 := f6.append_right
  refine ⟨fetched.append_left,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [mixturePrepareCode_length] using f1.append_left
  · simpa only [mixturePrepareCode_length,zeroLiteral_length,Nat.add_assoc] using f2.append_left
  · simpa only [mixturePrepareCode_length,zeroLiteral_length,comparisonStored_length,Nat.add_assoc] using single_fetch f3.append_left
  · simpa only [mixturePrepareCode_length,zeroLiteral_length,comparisonStored_length,List.length_singleton,Nat.add_assoc] using f4.append_left
  · simpa only [mixturePrepareCode_length,zeroLiteral_length,comparisonStored_length,List.length_singleton,mixtureRatio_length,Nat.add_assoc] using single_fetch f5.append_left
  · simpa only [mixturePrepareCode_length,zeroLiteral_length,comparisonStored_length,List.length_singleton,mixtureRatio_length,Nat.add_assoc] using f6.append_left
  · simpa only [mixturePrepareCode_length,zeroLiteral_length,comparisonStored_length,List.length_singleton,mixtureRatio_length,mixtureZero_length,Nat.add_assoc] using f7

end PDLower.CoreSearch
