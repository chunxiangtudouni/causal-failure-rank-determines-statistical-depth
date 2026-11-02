module

public import Paid.PDLower_CoreSearch_ClipTrace_012

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch

theorem mixturePrepare_keepsLow (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve) (values : ℕ→Cell) :
    KeepsLow values (mixturePrepareValues P fee lower upper values) := by
  unfold mixturePrepareValues
  exact (((((((((KeepsLow.refl values).update 30 _ (by decide)).update 41 _ (by decide)).update 32 _ (by decide)).update 32 _
    (by decide)).update 33 _ (by decide)).update 33 _ (by decide)).update 37 _ (by decide)).update 38 _ (by decide)).update 39 _ (by decide)

/-- Complete original final-bracket scalar entry. The old31/41/42 cells
are unrestricted: prepare, the actual denominator branch, ratio-or-zero,
constant producers and clipping all REALLY execute on this ONE trace.
The true lower/upper records and prices below29 remain unchanged. -/
theorem finalBracket_segment (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (origin : ℕ) (before : State) (values : ℕ→Cell)
    (position : before.pc=origin) (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (risk : values 3=.rational P.certificate.risk) (feeValue : values 5=.rational fee)
    (lowerPrice : values 14=.rational lower.multiplier) (upperPrice : values 15=.rational upper.multiplier)
    (lowerObs : values 16=.rational (P.solveRecord lower).observation)
    (lowerRep : values 17=.rational (P.solveRecord lower).repairs) (lowerRisk : values 18=.rational (P.solveRisk lower))
    (upperObs : values 19=.rational (P.solveRecord upper).observation)
    (upperRep : values 20=.rational (P.solveRecord upper).repairs) (upperRisk : values 21=.rational (P.solveRisk upper))
    (fetched : FetchesCode program origin (finalBracketCode origin)) :
    ∃ (after : State) (finalValues : ℕ→Cell),ScalarSegment program input before after 3000 ∧
      Header after 0 finalValues ∧ KeepsLow values finalValues ∧ after.register .fresh=.natural 0 ∧
      after.pc=origin+160 ∧ after.heap 29=.rational (clipRat (P.mixtureWeight lower upper)) := by
  have fetch := finalBracketCode_fetches program origin fetched
  let v1 := mixturePrepareValues P fee lower upper values
  obtain ⟨t1,s1,h1,l1,c1,time1,header1,fresh1,pc1,_out1,mem1⟩ :=
    mixturePrepare_trace P fee lower upper program input before values header fresh risk feeValue lowerPrice upperPrice
      lowerObs lowerRep lowerRisk upperObs upperRep upperRisk (by rw [position];exact fetch.prepare)
  have run1 : ScalarSegment program input before s1 1275 := ⟨t1,h1,l1,c1,time1,mem1⟩
  have keep1 : KeepsLow values v1 := mixturePrepare_keepsLow P fee lower upper values
  let v2 := Function.update v1 42 (.rational 0)
  obtain ⟨t2,s2,h2,l2,c2,time2,header2,fresh2,pc2,_out2,mem2⟩ :=
    zeroLiteral_trace program input s1 v1 header1 fresh1 (by rw [pc1,position];exact fetch.zeroLiteral)
  have run2 : ScalarSegment program input s1 s2 75 := ⟨t2,h2,l2,c2,time2,mem2⟩
  have keep2 : KeepsLow values v2 := keep1.update 42 _ (by decide)
  have denominator2 : v2 30=.rational (P.solveRisk lower-P.solveRisk upper) := by simp [v2,v1,mixturePrepareValues]
  have numerator2 : v2 41=.rational (P.certificate.risk-P.solveRisk upper) := by simp [v2,v1,mixturePrepareValues]
  obtain ⟨t3,h3,l3,c3,time3,header3,mem3⟩ :=
    denominatorGuard_trace P lower upper program input s2 v2 header2 fresh2 denominator2 (by simp [v2])
      (by rw [pc2,pc1,position];exact fetch.denominator)
  let s3 := comparisonStoredResult s2 30 42 (decide (P.solveRisk lower-P.solveRisk upper=0))
  let v3 := Function.update v2 40 (.natural (if P.solveRisk lower-P.solveRisk upper=0 then 1 else 0))
  have run3 : ScalarSegment program input s2 s3 165 := ⟨t3,h3,l3,c3,time3,mem3⟩
  have keep3 : KeepsLow values v3 := keep2.update 40 _ (by decide)
  have fields3 := comparisonStored_fields s2 30 42 (decide (P.solveRisk lower-P.solveRisk upper=0))
  have fresh3 : s3.register .fresh=.natural 0 := fields3.2.2.1.trans fresh2
  have pc3 : s3.pc=origin+98 := by
    dsimp only [s3]
    rw [fields3.2.2.2.2.1,pc2,pc1,position]
  let v4 := Function.update v3 31 (.rational (P.mixtureWeight lower upper))
  have prepared : ∃ s4 : State,ScalarSegment program input before s4 1740 ∧
      Header s4 0 v4 ∧ s4.register .fresh=.natural 0 ∧ s4.pc=origin+114 := by
    by_cases zero : P.solveRisk lower-P.solveRisk upper=0
    · let entered : State := {s3 with pc:=origin+110}
      have flag : s3.register .flag=.natural 1 := by simpa [s3,zero] using fields3.2.2.2.1
      have control : ScalarSegment program input s3 entered 30 :=
        ScalarSegment.control program input s3 (.branchZero .flag (origin+99) (origin+110)) (origin+110)
          (by rw [pc3];exact fetch.branch) (by simp [Instruction.execute,Cell.nat?,flag])
      obtain ⟨t4,s4,h4,l4,c4,time4,header4,fresh4,pc4,_out4,mem4⟩ :=
        mixtureZero_trace P lower upper program input entered v3 header3 fresh3 zero (by exact fetch.zero)
      have run4 : ScalarSegment program input entered s4 75 := ⟨t4,h4,l4,c4,time4,mem4⟩
      refine ⟨s4,((((run1.trans run2).trans run3).trans control).trans run4).mono (by decide),header4,fresh4,?_⟩
      dsimp only [entered] at pc4
      omega
    · let entered : State := {s3 with pc:=origin+99}
      have flag : s3.register .flag=.natural 0 := by simpa [s3,zero] using fields3.2.2.2.1
      have control : ScalarSegment program input s3 entered 30 :=
        ScalarSegment.control program input s3 (.branchZero .flag (origin+99) (origin+110)) (origin+99)
          (by rw [pc3];exact fetch.branch) (by simp [Instruction.execute,Cell.nat?,flag])
      have denominator3 : v3 30=.rational (P.solveRisk lower-P.solveRisk upper) := by simp [v3,denominator2]
      have numerator3 : v3 41=.rational (P.certificate.risk-P.solveRisk upper) := by simp [v3,numerator2]
      obtain ⟨t4,s4,h4,l4,c4,time4,header4,fresh4,pc4,_out4,mem4⟩ :=
        mixtureRatio_trace P lower upper program input entered v3 header3 fresh3 numerator3 denominator3 zero (by exact fetch.ratio)
      have run4 : ScalarSegment program input entered s4 165 := ⟨t4,h4,l4,c4,time4,mem4⟩
      let after : State := {s4 with pc:=origin+114}
      have jumpPC : s4.pc=origin+109 := by dsimp only [entered] at pc4;omega
      have jump : ScalarSegment program input s4 after 30 :=
        ScalarSegment.control program input s4 (.jump (origin+114)) (origin+114) (by rw [jumpPC];exact fetch.ratioJump) rfl
      exact ⟨after,(((((run1.trans run2).trans run3).trans control).trans run4).trans jump).mono (by decide),header4,fresh4,rfl⟩
  obtain ⟨s4,preparedRun,header4,fresh4,pc4⟩ := prepared
  have keep4 : KeepsLow values v4 := keep3.update 31 _ (by decide)
  obtain ⟨after,finalValues,clipped,finalHeader,kept,finalFresh,finalPC,finalValue⟩ :=
    clip_trace program input (origin+114) s4 v4 (P.mixtureWeight lower upper) pc4 header4 fresh4
      (by simp [v4]) fetch.clip
  refine ⟨after,finalValues,(preparedRun.trans clipped).mono (by decide),finalHeader,keep4.trans kept,finalFresh,?_,finalValue⟩
  omega

/-- Public one-entry, one-actual-trace boundary for the final bracket.
Only the Root-produced actual current two solutions are supplied. There
is no initial31=w, answer, successful search, or optimality premise. -/
theorem finalBracket_trace (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (origin : ℕ) (before : State) (values : ℕ→Cell)
    (position : before.pc=origin) (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (risk : values 3=.rational P.certificate.risk) (feeValue : values 5=.rational fee)
    (lowerPrice : values 14=.rational lower.multiplier) (upperPrice : values 15=.rational upper.multiplier)
    (lowerObs : values 16=.rational (P.solveRecord lower).observation)
    (lowerRep : values 17=.rational (P.solveRecord lower).repairs) (lowerRisk : values 18=.rational (P.solveRisk lower))
    (upperObs : values 19=.rational (P.solveRecord upper).observation)
    (upperRep : values 20=.rational (P.solveRecord upper).repairs) (upperRisk : values 21=.rational (P.solveRisk upper))
    (fetched : FetchesCode program origin (finalBracketCode origin)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤3000 ∧
      after.register .fresh=.natural 0 ∧ after.pc=origin+160 ∧
      after.heap 29=.rational (clipRat (P.mixtureWeight lower upper)) ∧ after.output=before.output ∧
      (∀ slot<29,after.heap slot=before.heap slot) ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  obtain ⟨after,finalValues,actual,finalHeader,kept,finalFresh,finalPC,finalValue⟩ :=
    finalBracket_segment P fee lower upper program input origin before values position header fresh risk feeValue lowerPrice upperPrice
      lowerObs lowerRep lowerRisk upperObs upperRep upperRisk fetched
  have finalMemory := actual.final
  obtain ⟨trace,head,last,chain,cost,memory⟩ := actual
  exact ⟨trace,after,head,last,chain,cost,finalFresh,finalPC,finalValue,finalMemory.2.2.2,kept.heap header finalHeader,memory⟩

end PDLower.CoreSearch
