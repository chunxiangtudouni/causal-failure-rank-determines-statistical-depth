module

public import Paid.PDLower_CoreSearch_MixtureEntry_015
public import Paid.PDLower_CoreSearch_RatioFinishBits_023
public import Paid.PDLower_CoreSearch_ClipBodiesBits_024

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch

/-- The entire original114-op weight producer, real zero denominator
branch included, with one unchanged complete-state operand budget. -/
theorem mixtureEntry_segment_bits (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (origin : ℕ) (before : State) (values : ℕ→Cell) (scale budget : ℕ)
    (position : before.pc=origin) (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (risk : values 3=.rational P.certificate.risk) (feeValue : values 5=.rational fee)
    (lowerPrice : values 14=.rational lower.multiplier) (upperPrice : values 15=.rational upper.multiplier)
    (lowerObs : values 16=.rational (P.solveRecord lower).observation)
    (lowerRep : values 17=.rational (P.solveRecord lower).repairs) (lowerRisk : values 18=.rational (P.solveRisk lower))
    (upperObs : values 19=.rational (P.solveRecord upper).observation)
    (upperRep : values 20=.rational (P.solveRecord upper).repairs) (upperRisk : values 21=.rational (P.solveRisk upper))
    (safe : RootD27.Bits.SafeBits before budget) (intrinsic : ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (origin+114)≤budget)
    (fetched : FetchesCode program origin (mixtureEntryCode origin)) :
    ∃ after : State,NumericSegment program input before after 1740 budget ∧ Header after 0 (mixtureEntryValues P fee lower upper values) ∧
      KeepsLow values (mixtureEntryValues P fee lower upper values) ∧ after.register .fresh=.natural 0 ∧ after.pc=origin+114 := by
  have fetch := mixtureEntryCode_fetches program origin fetched
  have pcBound (counter : ℕ) (bounded : counter≤origin+114) : natBits counter≤budget := (natBits_mono bounded).trans pcBits
  have small : 4≤budget := by unfold scalarValueBudget at room;omega
  let v1 := mixturePrepareValues P fee lower upper values
  obtain ⟨s1,run1,header1,fresh1,pc1⟩ := mixturePrepare_segment_bits P fee lower upper program input before values scale budget header fresh
    risk feeValue lowerPrice upperPrice lowerObs lowerRep lowerRisk upperObs upperRep upperRisk safe intrinsic room addressBits
    (pcBound _ (by rw [position];omega)) (by rw [position];exact fetch.prepare)
  have keep1 : KeepsLow values v1 := mixturePrepare_keepsLow P fee lower upper values
  let v2 := Function.update v1 42 (.rational 0)
  obtain ⟨s2,run2,header2,fresh2,pc2⟩ := zeroLiteral_segment_bits program input s1 v1 budget header1 fresh1 run1.final.2 small addressBits
    (pcBound _ (by rw [pc1,position];omega)) (by rw [pc1,position];exact fetch.zeroLiteral)
  have keep2 : KeepsLow values v2 := keep1.update 42 _ (by decide)
  have denominator2 : v2 30=.rational (P.solveRisk lower-P.solveRisk upper) := by simp [v2,v1,mixturePrepareValues]
  have numerator2 : v2 41=.rational (P.certificate.risk-P.solveRisk upper) := by simp [v2,v1,mixturePrepareValues]
  have same : (P.solveRisk lower-P.solveRisk upper==0)=decide (P.solveRisk lower-P.solveRisk upper=0) := by
    by_cases zero : P.solveRisk lower-P.solveRisk upper=0 <;> simp [zero]
  have compared := comparisonStored_segment_bits .equal 30 42 (P.solveRisk lower-P.solveRisk upper) 0 program input s2 v2 budget
    header2 (by decide) (by decide) denominator2 (by simp [v2]) fresh2 run2.final.2 small addressBits
    (pcBound _ (by rw [pc2,pc1,position];omega)) (by rw [pc2,pc1,position];exact fetch.denominator)
  simp only [Comparison.rat,same,decide_eq_true_eq] at compared
  obtain ⟨run3,header3⟩ := compared
  let s3 := comparisonStoredResult s2 30 42 (decide (P.solveRisk lower-P.solveRisk upper=0))
  let v3 := Function.update v2 40 (.natural (if P.solveRisk lower-P.solveRisk upper=0 then 1 else 0))
  have keep3 : KeepsLow values v3 := keep2.update 40 _ (by decide)
  have fields3 := comparisonStored_fields s2 30 42 (decide (P.solveRisk lower-P.solveRisk upper=0))
  have fresh3 : s3.register .fresh=.natural 0 := fields3.2.2.1.trans fresh2
  have pc3 : s3.pc=origin+98 := by
    dsimp only [s3]
    rw [fields3.2.2.2.2.1,pc2,pc1,position]
  let v4 := Function.update v3 31 (.rational (P.mixtureWeight lower upper))
  have prepared : ∃ s4 : State,NumericSegment program input before s4 1740 budget ∧
      Header s4 0 v4 ∧ s4.register .fresh=.natural 0 ∧ s4.pc=origin+114 := by
    by_cases zero : P.solveRisk lower-P.solveRisk upper=0
    · let entered : State := {s3 with pc:=origin+110}
      have flag : s3.register .flag=.natural 1 := by simpa [s3,zero] using fields3.2.2.2.1
      have control : NumericSegment program input s3 entered 30 budget :=
        NumericSegment.control program input s3 (.branchZero .flag (origin+99) (origin+110)) (origin+110) budget
          (by rw [pc3];exact fetch.branch) (by simp [Instruction.execute,Cell.nat?,flag]) run3.final.2 (pcBound _ (by omega))
      obtain ⟨s4,run4,header4,fresh4,pc4⟩ := mixtureZero_segment_bits P lower upper program input entered v3 budget header3 fresh3 zero
        control.final.2 small addressBits (pcBound _ (by change origin+110+4≤origin+114;omega)) (by exact fetch.zero)
      refine ⟨s4,((((run1.trans run2).trans run3).trans control).trans run4).mono (by decide),header4,fresh4,?_⟩
      dsimp only [entered] at pc4
      omega
    · let entered : State := {s3 with pc:=origin+99}
      have flag : s3.register .flag=.natural 0 := by simpa [s3,zero] using fields3.2.2.2.1
      have control : NumericSegment program input s3 entered 30 budget :=
        NumericSegment.control program input s3 (.branchZero .flag (origin+99) (origin+110)) (origin+99) budget
          (by rw [pc3];exact fetch.branch) (by simp [Instruction.execute,Cell.nat?,flag]) run3.final.2 (pcBound _ (by omega))
      have denominator3 : v3 30=.rational (P.solveRisk lower-P.solveRisk upper) := by simp [v3,denominator2]
      have numerator3 : v3 41=.rational (P.certificate.risk-P.solveRisk upper) := by simp [v3,numerator2]
      obtain ⟨s4,run4,header4,fresh4,pc4⟩ := mixtureRatio_segment_bits P fee lower upper program input entered v3 scale budget header3 fresh3 numerator3
        denominator3 zero control.final.2 intrinsic room addressBits (pcBound _ (by change origin+99+10≤origin+114;omega)) (by exact fetch.ratio)
      let after : State := {s4 with pc:=origin+114}
      have jumpPC : s4.pc=origin+109 := by dsimp only [entered] at pc4;omega
      have jump : NumericSegment program input s4 after 30 budget :=
        NumericSegment.control program input s4 (.jump (origin+114)) (origin+114) budget (by rw [jumpPC];exact fetch.ratioJump) rfl run4.final.2 pcBits
      exact ⟨after,(((((run1.trans run2).trans run3).trans control).trans run4).trans jump).mono (by decide),header4,fresh4,rfl⟩
  obtain ⟨s4,preparedRun,header4,fresh4,pc4⟩ := prepared
  exact ⟨s4,preparedRun,header4,keep3.update 31 _ (by decide),fresh4,pc4⟩

end PDLower.CoreSearch
