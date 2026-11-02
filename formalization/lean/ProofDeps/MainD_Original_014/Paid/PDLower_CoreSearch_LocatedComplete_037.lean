module

public import Paid.PDLower_CoreSearch_LocatedArithmetic_031
public import Paid.PDLower_CoreSearch_LocatedBodies_032
public import Paid.PDLower_CoreSearch_ClipBits_025
public import Paid.PDLower_CoreSearch_EntryBits_026
public import Paid.PDLower_CoreSearch_StopBits_027
public import Paid.PDLower_CoreSearch_FinalBits_028

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch.Located

/-- The SAME46 clipping ISA, real constants/branches and exact original
result, carrying one complete-state operand budget at EVERY prefix. -/
theorem clip_segment_bits (program : Program) (input : List Cell) (origin : ℕ) (before : State) (values : ℕ→Cell) (weight : ℚ) (budget : ℕ)
    (position : before.pc=origin) (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (ratio : values 31=.rational weight) (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (origin+46)≤budget)
    (fetched : FetchesCode program origin (clipCode origin))
    (low high : ℕ) (pcLower : low≤origin) (pcUpper : origin+46≤high) :
    ∃ (after : State) (finalValues : ℕ→Cell),LocatedSegment program input before after 660 budget low high ∧
      Header after 0 finalValues ∧ KeepsLow values finalValues ∧ after.register .fresh=.natural 0 ∧
      after.pc=origin+46 ∧ after.heap 29=.rational (clipRat weight) := by
  have fetch := clipCode_fetches program origin fetched
  have pcBound (counter : ℕ) (bounded : counter≤origin+46) : natBits counter≤budget := (natBits_mono bounded).trans pcBits
  let v1 := Function.update (Function.update values 41 (.rational 0)) 42 (.rational 1)
  obtain ⟨s1,run1,header1,fresh1,pc1⟩ := selectorConstants_segment_bits program input before values budget header fresh safe small addressBits
    (pcBound _ (by rw [position];omega)) (by rw [position];exact fetch.constants) low high (by rw [position];omega) (by rw [position];omega)
  have keep1 : KeepsLow values v1 := ((KeepsLow.refl values).update 41 _ (by decide)).update 42 _ (by decide)
  have ratio1 : v1 31=.rational weight := by simp [v1,ratio]
  obtain ⟨run2,header2⟩ := comparisonStored_segment_bits .less 31 41 weight 0 program input s1 v1 budget header1
    (by decide) (by decide) ratio1 (by simp [v1]) fresh1 run1.final.2 small addressBits
    (pcBound _ (by rw [pc1,position];omega)) (by rw [pc1,position];exact fetch.lower) low high (by rw [pc1,position];omega) (by rw [pc1,position];omega)
  let s2 := comparisonStoredResult s1 31 41 (decide (weight<0))
  let v2 := Function.update v1 40 (.natural (if weight<0 then 1 else 0))
  have keep2 : KeepsLow values v2 := keep1.update 40 _ (by decide)
  have fields2 := comparisonStored_fields s1 31 41 (decide (weight<0))
  have fresh2 : s2.register .fresh=.natural 0 := fields2.2.2.1.trans fresh1
  have pc2 : s2.pc=origin+18 := by
    dsimp only [s2]
    rw [fields2.2.2.2.2.1,pc1,position]
  by_cases below : weight<0
  · let s3 : State := {s2 with pc:=origin+42}
    have flag : s2.register .flag=.natural 1 := by simpa [s2,below] using fields2.2.2.2.1
    have run3 : LocatedSegment program input s2 s3 30 budget low high :=
      LocatedSegment.control program input s2 (.branchZero .flag (origin+19) (origin+42)) (origin+42) budget
        (by rw [pc2];exact fetch.lowerBranch) (by simp [Instruction.execute,Cell.nat?,flag]) run2.final.2 (pcBound _ (by omega)) low high (by rw [pc2];omega) (by rw [pc2];omega) (by omega) (by omega)
    obtain ⟨s4,run4,header4,fresh4,pc4⟩ := clipZero_segment_bits weight program input s3 v2 budget header2 fresh2 below run3.final.2 small addressBits
      (pcBound _ (by change origin+42+4≤origin+46;omega)) (by exact fetch.zero) low high (by change low≤origin+42;omega) (by change origin+42+4≤high;omega)
    let v4 := Function.update v2 29 (.rational (clipRat weight))
    have value := header4.value 29 (by decide)
    refine ⟨s4,v4,(((run1.trans run2).trans run3).trans run4).mono (by decide),header4,
      keep2.update 29 _ (by decide),fresh4,?_,?_⟩
    · dsimp only [s3] at pc4
      omega
    · simpa only [Nat.zero_add,Function.update_self] using value
  · let s3 : State := {s2 with pc:=origin+19}
    have flag : s2.register .flag=.natural 0 := by simpa [s2,below] using fields2.2.2.2.1
    have run3 : LocatedSegment program input s2 s3 30 budget low high :=
      LocatedSegment.control program input s2 (.branchZero .flag (origin+19) (origin+42)) (origin+19) budget
        (by rw [pc2];exact fetch.lowerBranch) (by simp [Instruction.execute,Cell.nat?,flag]) run2.final.2 (pcBound _ (by omega)) low high (by rw [pc2];omega) (by rw [pc2];omega) (by omega) (by omega)
    have ratio2 : v2 31=.rational weight := by simp [v2,ratio1]
    have one2 : v2 42=.rational 1 := by simp [v2,v1]
    obtain ⟨run4,header4⟩ := comparisonStored_segment_bits .less 42 31 1 weight program input s3 v2 budget header2
      (by decide) (by decide) one2 ratio2 fresh2 run3.final.2 small addressBits
      (pcBound _ (by change origin+19+10≤origin+46;omega)) (by exact fetch.upper) low high (by change low≤origin+19;omega) (by change origin+19+10≤high;omega)
    let s4 := comparisonStoredResult s3 42 31 (decide (1<weight))
    let v4 := Function.update v2 40 (.natural (if 1<weight then 1 else 0))
    have keep4 : KeepsLow values v4 := keep2.update 40 _ (by decide)
    have fields4 := comparisonStored_fields s3 42 31 (decide (1<weight))
    have fresh4 : s4.register .fresh=.natural 0 := fields4.2.2.1.trans fresh2
    have pc4 : s4.pc=origin+29 := by
      dsimp only [s4]
      rw [fields4.2.2.2.2.1]
    by_cases above : 1<weight
    · let s5 : State := {s4 with pc:=origin+37}
      have flag : s4.register .flag=.natural 1 := by simpa [s4,above] using fields4.2.2.2.1
      have run5 : LocatedSegment program input s4 s5 30 budget low high :=
        LocatedSegment.control program input s4 (.branchZero .flag (origin+30) (origin+37)) (origin+37) budget
          (by rw [pc4];exact fetch.upperBranch) (by simp [Instruction.execute,Cell.nat?,flag]) run4.final.2 (pcBound _ (by omega)) low high (by rw [pc4];omega) (by rw [pc4];omega) (by omega) (by omega)
      obtain ⟨s6,run6,header6,fresh6,pc6⟩ := clipOne_segment_bits weight program input s5 v4 budget header4 fresh4 above run5.final.2 small addressBits
        (pcBound _ (by change origin+37+4≤origin+46;omega)) (by exact fetch.one) low high (by change low≤origin+37;omega) (by change origin+37+4≤high;omega)
      let v6 := Function.update v4 29 (.rational (clipRat weight))
      let after : State := {s6 with pc:=origin+46}
      have jumpPC : s6.pc=origin+41 := by dsimp only [s5] at pc6;omega
      have jump : LocatedSegment program input s6 after 30 budget low high :=
        LocatedSegment.control program input s6 (.jump (origin+46)) (origin+46) budget
          (by rw [jumpPC];exact fetch.oneJump) rfl run6.final.2 pcBits low high (by rw [jumpPC];omega) (by rw [jumpPC];omega) (by omega) (by omega)
      have value := header6.value 29 (by decide)
      refine ⟨after,v6,((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans jump).mono (by decide),
        header6,keep4.update 29 _ (by decide),fresh6,rfl,?_⟩
      simpa only [Nat.zero_add,Function.update_self] using value
    · let s5 : State := {s4 with pc:=origin+30}
      have flag : s4.register .flag=.natural 0 := by simpa [s4,above] using fields4.2.2.2.1
      have run5 : LocatedSegment program input s4 s5 30 budget low high :=
        LocatedSegment.control program input s4 (.branchZero .flag (origin+30) (origin+37)) (origin+30) budget
          (by rw [pc4];exact fetch.upperBranch) (by simp [Instruction.execute,Cell.nat?,flag]) run4.final.2 (pcBound _ (by omega)) low high (by rw [pc4];omega) (by rw [pc4];omega) (by omega) (by omega)
      have ratio4 : v4 31=.rational weight := by simp [v4,ratio2]
      obtain ⟨s6,run6,header6,fresh6,pc6⟩ := clipCopy_segment_bits weight program input s5 v4 budget header4 fresh4 ratio4 below above run5.final.2 addressBits
        (pcBound _ (by change origin+30+6≤origin+46;omega)) (by exact fetch.copy) low high (by change low≤origin+30;omega) (by change origin+30+6≤high;omega)
      let v6 := Function.update v4 29 (.rational (clipRat weight))
      let after : State := {s6 with pc:=origin+46}
      have jumpPC : s6.pc=origin+36 := by dsimp only [s5] at pc6;omega
      have jump : LocatedSegment program input s6 after 30 budget low high :=
        LocatedSegment.control program input s6 (.jump (origin+46)) (origin+46) budget
          (by rw [jumpPC];exact fetch.copyJump) rfl run6.final.2 pcBits low high (by rw [jumpPC];omega) (by rw [jumpPC];omega) (by omega) (by omega)
      have value := header6.value 29 (by decide)
      refine ⟨after,v6,((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans jump).mono (by decide),
        header6,keep4.update 29 _ (by decide),fresh6,rfl,?_⟩
      simpa only [Nat.zero_add,Function.update_self] using value

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
    (fetched : FetchesCode program origin (mixtureEntryCode origin))
    (low high : ℕ) (pcLower : low≤origin) (pcUpper : origin+114≤high) :
    ∃ after : State,LocatedSegment program input before after 1740 budget low high ∧ Header after 0 (mixtureEntryValues P fee lower upper values) ∧
      KeepsLow values (mixtureEntryValues P fee lower upper values) ∧ after.register .fresh=.natural 0 ∧ after.pc=origin+114 := by
  have fetch := mixtureEntryCode_fetches program origin fetched
  have pcBound (counter : ℕ) (bounded : counter≤origin+114) : natBits counter≤budget := (natBits_mono bounded).trans pcBits
  have small : 4≤budget := by unfold scalarValueBudget at room;omega
  let v1 := mixturePrepareValues P fee lower upper values
  obtain ⟨s1,run1,header1,fresh1,pc1⟩ := mixturePrepare_segment_bits P fee lower upper program input before values scale budget header fresh
    risk feeValue lowerPrice upperPrice lowerObs lowerRep lowerRisk upperObs upperRep upperRisk safe intrinsic room addressBits
    (pcBound _ (by rw [position];omega)) (by rw [position];exact fetch.prepare) low high (by omega) (by omega)
  have keep1 : KeepsLow values v1 := mixturePrepare_keepsLow P fee lower upper values
  let v2 := Function.update v1 42 (.rational 0)
  obtain ⟨s2,run2,header2,fresh2,pc2⟩ := zeroLiteral_segment_bits program input s1 v1 budget header1 fresh1 run1.final.2 small addressBits
    (pcBound _ (by rw [pc1,position];omega)) (by rw [pc1,position];exact fetch.zeroLiteral) low high (by omega) (by omega)
  have keep2 : KeepsLow values v2 := keep1.update 42 _ (by decide)
  have denominator2 : v2 30=.rational (P.solveRisk lower-P.solveRisk upper) := by simp [v2,v1,mixturePrepareValues]
  have numerator2 : v2 41=.rational (P.certificate.risk-P.solveRisk upper) := by simp [v2,v1,mixturePrepareValues]
  have same : (P.solveRisk lower-P.solveRisk upper==0)=decide (P.solveRisk lower-P.solveRisk upper=0) := by
    by_cases zero : P.solveRisk lower-P.solveRisk upper=0 <;> simp [zero]
  have compared := comparisonStored_segment_bits .equal 30 42 (P.solveRisk lower-P.solveRisk upper) 0 program input s2 v2 budget
    header2 (by decide) (by decide) denominator2 (by simp [v2]) fresh2 run2.final.2 small addressBits
    (pcBound _ (by rw [pc2,pc1,position];omega)) (by rw [pc2,pc1,position];exact fetch.denominator) low high (by omega) (by omega)
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
  have prepared : ∃ s4 : State,LocatedSegment program input before s4 1740 budget low high ∧
      Header s4 0 v4 ∧ s4.register .fresh=.natural 0 ∧ s4.pc=origin+114 := by
    by_cases zero : P.solveRisk lower-P.solveRisk upper=0
    · let entered : State := {s3 with pc:=origin+110}
      have flag : s3.register .flag=.natural 1 := by simpa [s3,zero] using fields3.2.2.2.1
      have control : LocatedSegment program input s3 entered 30 budget low high :=
        LocatedSegment.control program input s3 (.branchZero .flag (origin+99) (origin+110)) (origin+110) budget
          (by rw [pc3];exact fetch.branch) (by simp [Instruction.execute,Cell.nat?,flag]) run3.final.2 (pcBound _ (by omega)) low high (by rw [pc3];omega) (by rw [pc3];omega) (by omega) (by omega)
      obtain ⟨s4,run4,header4,fresh4,pc4⟩ := mixtureZero_segment_bits P lower upper program input entered v3 budget header3 fresh3 zero
        control.final.2 small addressBits (pcBound _ (by change origin+110+4≤origin+114;omega)) (by exact fetch.zero) low high (by change low≤origin+110;omega) (by change origin+110+4≤high;omega)
      refine ⟨s4,((((run1.trans run2).trans run3).trans control).trans run4).mono (by decide),header4,fresh4,?_⟩
      dsimp only [entered] at pc4
      omega
    · let entered : State := {s3 with pc:=origin+99}
      have flag : s3.register .flag=.natural 0 := by simpa [s3,zero] using fields3.2.2.2.1
      have control : LocatedSegment program input s3 entered 30 budget low high :=
        LocatedSegment.control program input s3 (.branchZero .flag (origin+99) (origin+110)) (origin+99) budget
          (by rw [pc3];exact fetch.branch) (by simp [Instruction.execute,Cell.nat?,flag]) run3.final.2 (pcBound _ (by omega)) low high (by rw [pc3];omega) (by rw [pc3];omega) (by omega) (by omega)
      have denominator3 : v3 30=.rational (P.solveRisk lower-P.solveRisk upper) := by simp [v3,denominator2]
      have numerator3 : v3 41=.rational (P.certificate.risk-P.solveRisk upper) := by simp [v3,numerator2]
      obtain ⟨s4,run4,header4,fresh4,pc4⟩ := mixtureRatio_segment_bits P fee lower upper program input entered v3 scale budget header3 fresh3 numerator3
        denominator3 zero control.final.2 intrinsic room addressBits (pcBound _ (by change origin+99+10≤origin+114;omega)) (by exact fetch.ratio) low high (by change low≤origin+99;omega) (by change origin+99+10≤high;omega)
      let after : State := {s4 with pc:=origin+114}
      have jumpPC : s4.pc=origin+109 := by dsimp only [entered] at pc4;omega
      have jump : LocatedSegment program input s4 after 30 budget low high :=
        LocatedSegment.control program input s4 (.jump (origin+114)) (origin+114) budget (by rw [jumpPC];exact fetch.ratioJump) rfl run4.final.2 pcBits low high (by rw [jumpPC];omega) (by rw [jumpPC];omega) (by omega) (by omega)
      exact ⟨after,(((((run1.trans run2).trans run3).trans control).trans run4).trans jump).mono (by decide),header4,fresh4,rfl⟩
  obtain ⟨s4,preparedRun,header4,fresh4,pc4⟩ := prepared
  exact ⟨s4,preparedRun,header4,keep3.update 31 _ (by decide),fresh4,pc4⟩

theorem bracketStop_segment_bits (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (origin : ℕ) (before : State) (values : ℕ→Cell) (scale budget : ℕ)
    (position : before.pc=origin) (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (risk : values 3=.rational P.certificate.risk) (feeValue : values 5=.rational fee)
    (lowerPrice : values 14=.rational lower.multiplier) (upperPrice : values 15=.rational upper.multiplier)
    (lowerObs : values 16=.rational (P.solveRecord lower).observation)
    (lowerRep : values 17=.rational (P.solveRecord lower).repairs) (lowerRisk : values 18=.rational (P.solveRisk lower))
    (upperObs : values 19=.rational (P.solveRecord upper).observation)
    (upperRep : values 20=.rational (P.solveRecord upper).repairs) (upperRisk : values 21=.rational (P.solveRisk upper))
    (safe : RootD27.Bits.SafeBits before budget) (intrinsic : ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (origin+182)≤budget)
    (fetched : FetchesCode program origin (bracketStopCode origin)) :
    ∃ (after : State) (finalValues : ℕ→Cell),LocatedSegment program input before after 3000 budget origin (origin+182) ∧
      Header after 0 finalValues ∧ KeepsLow values finalValues ∧ after.register .fresh=.natural 0 ∧ after.pc=origin+182 ∧
      after.register .flag=.natural (if P.searchStopped fee (.bracket lower upper) then 1 else 0) ∧
      after.heap 40=.natural (if P.searchStopped fee (.bracket lower upper) then 1 else 0) ∧
      after.heap 36=.rational (P.mixtureCost fee lower upper) := by
  have pcBound (counter : ℕ) (bounded : counter≤origin+182) : natBits counter≤budget := (natBits_mono bounded).trans pcBits
  have small : 4≤budget := by unfold scalarValueBudget at room;omega
  have arranged : FetchesCode program origin
      (mixtureEntryCode origin++(headerCode mixtureFinishCommands++comparisonStoredCode .lessEqual 38 41)) := by
    simpa only [bracketStopCode,List.append_assoc] using fetched
  have restFetch : FetchesCode program (origin+114)
      (headerCode mixtureFinishCommands++comparisonStoredCode .lessEqual 38 41) := by
    simpa only [mixtureEntryCode_length] using arranged.append_right
  obtain ⟨s1,run1,header1,keep1,fresh1,pc1⟩ :=
    mixtureEntry_segment_bits P fee lower upper program input origin before values scale budget position header fresh risk feeValue lowerPrice upperPrice
      lowerObs lowerRep lowerRisk upperObs upperRep upperRisk safe intrinsic room addressBits (pcBound _ (by omega)) arranged.append_left origin (origin+182) (by omega) (by omega)
  let v1 := mixtureEntryValues P fee lower upper values
  have ratio1 : v1 31=.rational (P.mixtureWeight lower upper) := by simp [v1,mixtureEntryValues]
  have costL1 : v1 32=.rational (P.solveCost fee lower) := by simp [v1,mixtureEntryValues,mixturePrepareValues]
  have costU1 : v1 33=.rational (P.solveCost fee upper) := by simp [v1,mixtureEntryValues,mixturePrepareValues]
  have gap1 : v1 38=.rational ((upper.multiplier-lower.multiplier)*P.certificate.risk) := by
    simp [v1,mixtureEntryValues,mixturePrepareValues]
  obtain ⟨s2,run2,header2,fresh2,pc2⟩ := mixtureFinish_segment_bits P fee lower upper program input s1 v1 scale budget header1 fresh1 ratio1 costL1 costU1
    run1.final.2 intrinsic room addressBits (pcBound _ (by rw [pc1];omega)) (by rw [pc1];exact restFetch.append_left) origin (origin+182) (by omega) (by omega)
  let v2 := mixtureFinishValues P fee lower upper v1
  have finishFields := mixtureFinish_fields P fee lower upper v1
  have gap2 : v2 38=.rational ((upper.multiplier-lower.multiplier)*P.certificate.risk) := finishFields.2.2.trans gap1
  have compareFetch : FetchesCode program s2.pc (comparisonStoredCode .lessEqual 38 41) := by
    rw [pc2,pc1]
    simpa only [mixtureFinish_length] using restFetch.append_right
  obtain ⟨run3,header3⟩ := comparisonStored_segment_bits .lessEqual 38 41 ((upper.multiplier-lower.multiplier)*P.certificate.risk)
    (P.mixtureCost fee lower upper/2) program input s2 v2 budget header2 (by decide) (by decide) gap2 finishFields.2.1 fresh2 run2.final.2
    small addressBits (pcBound _ (by rw [pc2,pc1])) compareFetch origin (origin+182) (by omega) (by omega)
  let after := comparisonStoredResult s2 38 41 (P.searchStopped fee (.bracket lower upper))
  let v3 := Function.update v2 40 (.natural (if P.searchStopped fee (.bracket lower upper) then 1 else 0))
  have actual : LocatedSegment program input before after 3000 budget origin (origin+182) := ((run1.trans run2).trans run3).mono (by decide)
  have fields3 := comparisonStored_fields s2 38 41 (P.searchStopped fee (.bracket lower upper))
  have kept : KeepsLow values v3 := (keep1.trans (mixtureFinish_keepsLow P fee lower upper v1)).update 40 _ (by decide)
  have finalPC : after.pc=origin+182 := by
    dsimp only [after]
    rw [fields3.2.2.2.2.1,pc2,pc1]
  have flag : after.register .flag=.natural (if P.searchStopped fee (.bracket lower upper) then 1 else 0) := fields3.2.2.2.1
  have fresh3 : after.register .fresh=.natural 0 := fields3.2.2.1.trans fresh2
  refine ⟨after,v3,actual,header3,kept,fresh3,finalPC,flag,?_,?_⟩
  · dsimp only [after]
    rw [fields3.1,Function.update_self]
  · dsimp only [after]
    rw [fields3.1,Function.update_of_ne (by decide : (36:ℕ)≠40)]
    have value := (header2.value 36 (by decide)).trans finishFields.1
    simpa only [Nat.zero_add] using value

/-- Same actual182-op stopping trace, original source Bool/cost/time,
all physical prefixes AND complete stateCellBits under one fixedB. -/
theorem bracketStop_trace_bits (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (origin : ℕ) (before : State) (values : ℕ→Cell) (scale budget : ℕ)
    (position : before.pc=origin) (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (risk : values 3=.rational P.certificate.risk) (feeValue : values 5=.rational fee)
    (lowerPrice : values 14=.rational lower.multiplier) (upperPrice : values 15=.rational upper.multiplier)
    (lowerObs : values 16=.rational (P.solveRecord lower).observation)
    (lowerRep : values 17=.rational (P.solveRecord lower).repairs) (lowerRisk : values 18=.rational (P.solveRisk lower))
    (upperObs : values 19=.rational (P.solveRecord upper).observation)
    (upperRep : values 20=.rational (P.solveRecord upper).repairs) (upperRisk : values 21=.rational (P.solveRisk upper))
    (safe : RootD27.Bits.SafeBits before budget) (intrinsic : ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (origin+182)≤budget)
    (fetched : FetchesCode program origin (bracketStopCode origin)) :
    ∃ (trace : List State) (after : State) (finalValues : ℕ→Cell),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤3000 ∧
      Header after 0 finalValues ∧ KeepsLow values finalValues ∧ after.register .fresh=.natural 0 ∧ after.pc=origin+182 ∧
      after.register .flag=.natural (if P.searchStopped fee (.bracket lower upper) then 1 else 0) ∧
      after.heap 40=.natural (if P.searchStopped fee (.bracket lower upper) then 1 else 0) ∧
      after.heap 36=.rational (P.mixtureCost fee lower upper) ∧ after.output=before.output ∧
      (∀ slot<29,after.heap slot=before.heap slot) ∧
      (∀ state∈trace,(MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0) ∧ RootD27.Bits.SafeBits state budget) ∧
      (∀ state∈trace,origin≤state.pc ∧ state.pc≤origin+182) ∧
      ∀ state∈trace.dropLast,state.pc<origin+182 := by
  obtain ⟨after,finalValues,actual,afterHeader,kept,afterFresh,pc,flag,stored,costValue⟩ := bracketStop_segment_bits P fee lower upper
    program input origin before values scale budget position header fresh risk feeValue lowerPrice upperPrice lowerObs lowerRep lowerRisk
    upperObs upperRep upperRisk safe intrinsic room addressBits pcBits fetched
  have finalMemory := actual.final.1
  obtain ⟨trace,head,last,chain,cost,properties,proper⟩ := actual
  exact ⟨trace,after,finalValues,head,last,chain,cost,afterHeader,kept,afterFresh,pc,flag,stored,costValue,
    finalMemory.2.2.2,kept.heap header afterHeader,(fun state member => (properties state member).1),
    (fun state member => (properties state member).2),proper⟩

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
    ∃ (after : State) (finalValues : ℕ→Cell),LocatedSegment program input before after 3000 budget origin (origin+160) ∧
      Header after 0 finalValues ∧ KeepsLow values finalValues ∧ after.register .fresh=.natural 0 ∧ after.pc=origin+160 ∧
      after.heap 29=.rational (clipRat (P.mixtureWeight lower upper)) := by
  have codeEq : finalBracketCode origin=mixtureEntryCode origin++clipCode (origin+114) := by
    simp only [finalBracketCode,mixtureEntryCode,List.append_assoc]
  rw [codeEq] at fetched
  have clipFetch : FetchesCode program (origin+114) (clipCode (origin+114)) := by
    simpa only [mixtureEntryCode_length] using fetched.append_right
  obtain ⟨s1,run1,header1,keep1,fresh1,pc1⟩ := mixtureEntry_segment_bits P fee lower upper program input origin before values scale budget
    position header fresh risk feeValue lowerPrice upperPrice lowerObs lowerRep lowerRisk upperObs upperRep upperRisk safe intrinsic room addressBits
    ((natBits_mono (by omega : origin+114≤origin+160)).trans pcBits) fetched.append_left origin (origin+160) (by omega) (by omega)
  let v1 := mixtureEntryValues P fee lower upper values
  have small : 4≤budget := by unfold scalarValueBudget at room;omega
  obtain ⟨after,finalValues,run2,afterHeader,keep2,afterFresh,pc2,value⟩ := clip_segment_bits program input (origin+114) s1 v1
    (P.mixtureWeight lower upper) budget pc1 header1 fresh1 (by simp [v1,mixtureEntryValues]) run1.final.2 small addressBits
    (by simpa only [Nat.add_assoc] using pcBits) clipFetch origin (origin+160) (by omega) (by omega)
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
      (∀ state∈trace,(MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0) ∧ RootD27.Bits.SafeBits state budget) ∧
      (∀ state∈trace,origin≤state.pc ∧ state.pc≤origin+160) ∧
      ∀ state∈trace.dropLast,state.pc<origin+160 := by
  obtain ⟨after,finalValues,actual,afterHeader,kept,afterFresh,pc,value⟩ := finalBracket_segment_bits P fee lower upper
    program input origin before values scale budget position header fresh risk feeValue lowerPrice upperPrice lowerObs lowerRep lowerRisk
    upperObs upperRep upperRisk safe intrinsic room addressBits pcBits fetched
  have finalMemory := actual.final.1
  obtain ⟨trace,head,last,chain,cost,properties,proper⟩ := actual
  exact ⟨trace,after,head,last,chain,cost,afterFresh,pc,value,finalMemory.2.2.2,kept.heap header afterHeader,(fun state member => (properties state member).1),
    (fun state member => (properties state member).2),proper⟩

theorem midpoint_trace_bits (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (lower upper : ℚ) (scale budget : ℕ) (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (lowerValue : values 14=.rational lower) (upperValue : values 15=.rational upper)
    (safe : RootD27.Bits.SafeBits before budget) (lowerBits : ratEncodingBits lower≤scale) (upperBits : ratEncodingBits upper≤scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+24)≤budget) (fetched : FetchesCode program before.pc (headerCode midpointCommands)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤375 ∧
      Header after 0 (midpointValues values lower upper) ∧ after.register .fresh=.natural 0 ∧ after.pc=before.pc+24 ∧
      after.register .total=.rational ((lower+upper)/2) ∧ after.heap 24=.rational ((lower+upper)/2) ∧ after.output=before.output ∧
      (∀ state∈trace,(MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0) ∧ RootD27.Bits.SafeBits state budget) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+24) ∧ ∀ state∈trace.dropLast,state.pc<before.pc+24 := by
  obtain ⟨after,actual,afterHeader,afterFresh,pc,total,value⟩ := midpoint_segment_bits program input before values lower upper scale budget header fresh
    lowerValue upperValue safe lowerBits upperBits room addressBits pcBits fetched before.pc (before.pc+24) (by omega) (by omega)
  have finalMemory := actual.final.1
  obtain ⟨trace,head,last,chain,cost,properties,proper⟩ := actual
  exact ⟨trace,after,head,last,chain,cost,afterHeader,afterFresh,pc,total,value,finalMemory.2.2.2,
    (fun state member => (properties state member).1),(fun state member => (properties state member).2),proper⟩

end PDLower.CoreSearch.Located
