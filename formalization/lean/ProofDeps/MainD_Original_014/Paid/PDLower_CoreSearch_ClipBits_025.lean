module

public import Paid.PDLower_CoreSearch_ClipBodiesBits_024

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch

/-- The SAME46 clipping ISA, real constants/branches and exact original
result, carrying one complete-state operand budget at EVERY prefix. -/
theorem clip_segment_bits (program : Program) (input : List Cell) (origin : ℕ) (before : State) (values : ℕ→Cell) (weight : ℚ) (budget : ℕ)
    (position : before.pc=origin) (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (ratio : values 31=.rational weight) (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (origin+46)≤budget)
    (fetched : FetchesCode program origin (clipCode origin)) :
    ∃ (after : State) (finalValues : ℕ→Cell),NumericSegment program input before after 660 budget ∧
      Header after 0 finalValues ∧ KeepsLow values finalValues ∧ after.register .fresh=.natural 0 ∧
      after.pc=origin+46 ∧ after.heap 29=.rational (clipRat weight) := by
  have fetch := clipCode_fetches program origin fetched
  have pcBound (counter : ℕ) (bounded : counter≤origin+46) : natBits counter≤budget := (natBits_mono bounded).trans pcBits
  let v1 := Function.update (Function.update values 41 (.rational 0)) 42 (.rational 1)
  obtain ⟨s1,run1,header1,fresh1,pc1⟩ := selectorConstants_segment_bits program input before values budget header fresh safe small addressBits
    (pcBound _ (by rw [position];omega)) (by rw [position];exact fetch.constants)
  have keep1 : KeepsLow values v1 := ((KeepsLow.refl values).update 41 _ (by decide)).update 42 _ (by decide)
  have ratio1 : v1 31=.rational weight := by simp [v1,ratio]
  obtain ⟨run2,header2⟩ := comparisonStored_segment_bits .less 31 41 weight 0 program input s1 v1 budget header1
    (by decide) (by decide) ratio1 (by simp [v1]) fresh1 run1.final.2 small addressBits
    (pcBound _ (by rw [pc1,position];omega)) (by rw [pc1,position];exact fetch.lower)
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
    have run3 : NumericSegment program input s2 s3 30 budget :=
      NumericSegment.control program input s2 (.branchZero .flag (origin+19) (origin+42)) (origin+42) budget
        (by rw [pc2];exact fetch.lowerBranch) (by simp [Instruction.execute,Cell.nat?,flag]) run2.final.2 (pcBound _ (by omega))
    obtain ⟨s4,run4,header4,fresh4,pc4⟩ := clipZero_segment_bits weight program input s3 v2 budget header2 fresh2 below run3.final.2 small addressBits
      (pcBound _ (by change origin+42+4≤origin+46;omega)) (by exact fetch.zero)
    let v4 := Function.update v2 29 (.rational (clipRat weight))
    have value := header4.value 29 (by decide)
    refine ⟨s4,v4,(((run1.trans run2).trans run3).trans run4).mono (by decide),header4,
      keep2.update 29 _ (by decide),fresh4,?_,?_⟩
    · dsimp only [s3] at pc4
      omega
    · simpa only [Nat.zero_add,Function.update_self] using value
  · let s3 : State := {s2 with pc:=origin+19}
    have flag : s2.register .flag=.natural 0 := by simpa [s2,below] using fields2.2.2.2.1
    have run3 : NumericSegment program input s2 s3 30 budget :=
      NumericSegment.control program input s2 (.branchZero .flag (origin+19) (origin+42)) (origin+19) budget
        (by rw [pc2];exact fetch.lowerBranch) (by simp [Instruction.execute,Cell.nat?,flag]) run2.final.2 (pcBound _ (by omega))
    have ratio2 : v2 31=.rational weight := by simp [v2,ratio1]
    have one2 : v2 42=.rational 1 := by simp [v2,v1]
    obtain ⟨run4,header4⟩ := comparisonStored_segment_bits .less 42 31 1 weight program input s3 v2 budget header2
      (by decide) (by decide) one2 ratio2 fresh2 run3.final.2 small addressBits
      (pcBound _ (by change origin+19+10≤origin+46;omega)) (by exact fetch.upper)
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
      have run5 : NumericSegment program input s4 s5 30 budget :=
        NumericSegment.control program input s4 (.branchZero .flag (origin+30) (origin+37)) (origin+37) budget
          (by rw [pc4];exact fetch.upperBranch) (by simp [Instruction.execute,Cell.nat?,flag]) run4.final.2 (pcBound _ (by omega))
      obtain ⟨s6,run6,header6,fresh6,pc6⟩ := clipOne_segment_bits weight program input s5 v4 budget header4 fresh4 above run5.final.2 small addressBits
        (pcBound _ (by change origin+37+4≤origin+46;omega)) (by exact fetch.one)
      let v6 := Function.update v4 29 (.rational (clipRat weight))
      let after : State := {s6 with pc:=origin+46}
      have jumpPC : s6.pc=origin+41 := by dsimp only [s5] at pc6;omega
      have jump : NumericSegment program input s6 after 30 budget :=
        NumericSegment.control program input s6 (.jump (origin+46)) (origin+46) budget
          (by rw [jumpPC];exact fetch.oneJump) rfl run6.final.2 pcBits
      have value := header6.value 29 (by decide)
      refine ⟨after,v6,((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans jump).mono (by decide),
        header6,keep4.update 29 _ (by decide),fresh6,rfl,?_⟩
      simpa only [Nat.zero_add,Function.update_self] using value
    · let s5 : State := {s4 with pc:=origin+30}
      have flag : s4.register .flag=.natural 0 := by simpa [s4,above] using fields4.2.2.2.1
      have run5 : NumericSegment program input s4 s5 30 budget :=
        NumericSegment.control program input s4 (.branchZero .flag (origin+30) (origin+37)) (origin+30) budget
          (by rw [pc4];exact fetch.upperBranch) (by simp [Instruction.execute,Cell.nat?,flag]) run4.final.2 (pcBound _ (by omega))
      have ratio4 : v4 31=.rational weight := by simp [v4,ratio2]
      obtain ⟨s6,run6,header6,fresh6,pc6⟩ := clipCopy_segment_bits weight program input s5 v4 budget header4 fresh4 ratio4 below above run5.final.2 addressBits
        (pcBound _ (by change origin+30+6≤origin+46;omega)) (by exact fetch.copy)
      let v6 := Function.update v4 29 (.rational (clipRat weight))
      let after : State := {s6 with pc:=origin+46}
      have jumpPC : s6.pc=origin+36 := by dsimp only [s5] at pc6;omega
      have jump : NumericSegment program input s6 after 30 budget :=
        NumericSegment.control program input s6 (.jump (origin+46)) (origin+46) budget
          (by rw [jumpPC];exact fetch.copyJump) rfl run6.final.2 pcBits
      have value := header6.value 29 (by decide)
      refine ⟨after,v6,((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans jump).mono (by decide),
        header6,keep4.update 29 _ (by decide),fresh6,rfl,?_⟩
      simpa only [Nat.zero_add,Function.update_self] using value

end PDLower.CoreSearch
