module

public import Paid.PDLower_CoreSearch_Stop_016
public import Paid.PDLower_CoreSearch_EntryBits_026

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch

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
    ∃ (after : State) (finalValues : ℕ→Cell),NumericSegment program input before after 3000 budget ∧
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
      lowerObs lowerRep lowerRisk upperObs upperRep upperRisk safe intrinsic room addressBits (pcBound _ (by omega)) arranged.append_left
  let v1 := mixtureEntryValues P fee lower upper values
  have ratio1 : v1 31=.rational (P.mixtureWeight lower upper) := by simp [v1,mixtureEntryValues]
  have costL1 : v1 32=.rational (P.solveCost fee lower) := by simp [v1,mixtureEntryValues,mixturePrepareValues]
  have costU1 : v1 33=.rational (P.solveCost fee upper) := by simp [v1,mixtureEntryValues,mixturePrepareValues]
  have gap1 : v1 38=.rational ((upper.multiplier-lower.multiplier)*P.certificate.risk) := by
    simp [v1,mixtureEntryValues,mixturePrepareValues]
  obtain ⟨s2,run2,header2,fresh2,pc2⟩ := mixtureFinish_segment_bits P fee lower upper program input s1 v1 scale budget header1 fresh1 ratio1 costL1 costU1
    run1.final.2 intrinsic room addressBits (pcBound _ (by rw [pc1];omega)) (by rw [pc1];exact restFetch.append_left)
  let v2 := mixtureFinishValues P fee lower upper v1
  have finishFields := mixtureFinish_fields P fee lower upper v1
  have gap2 : v2 38=.rational ((upper.multiplier-lower.multiplier)*P.certificate.risk) := finishFields.2.2.trans gap1
  have compareFetch : FetchesCode program s2.pc (comparisonStoredCode .lessEqual 38 41) := by
    rw [pc2,pc1]
    simpa only [mixtureFinish_length] using restFetch.append_right
  obtain ⟨run3,header3⟩ := comparisonStored_segment_bits .lessEqual 38 41 ((upper.multiplier-lower.multiplier)*P.certificate.risk)
    (P.mixtureCost fee lower upper/2) program input s2 v2 budget header2 (by decide) (by decide) gap2 finishFields.2.1 fresh2 run2.final.2
    small addressBits (pcBound _ (by rw [pc2,pc1])) compareFetch
  let after := comparisonStoredResult s2 38 41 (P.searchStopped fee (.bracket lower upper))
  let v3 := Function.update v2 40 (.natural (if P.searchStopped fee (.bracket lower upper) then 1 else 0))
  have actual : NumericSegment program input before after 3000 budget := ((run1.trans run2).trans run3).mono (by decide)
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
      ∀ state∈trace,(MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0) ∧ RootD27.Bits.SafeBits state budget := by
  obtain ⟨after,finalValues,actual,afterHeader,kept,afterFresh,pc,flag,stored,costValue⟩ := bracketStop_segment_bits P fee lower upper
    program input origin before values scale budget position header fresh risk feeValue lowerPrice upperPrice lowerObs lowerRep lowerRisk
    upperObs upperRep upperRisk safe intrinsic room addressBits pcBits fetched
  have finalMemory := actual.final.1
  obtain ⟨trace,head,last,chain,cost,properties⟩ := actual
  exact ⟨trace,after,finalValues,head,last,chain,cost,afterHeader,kept,afterFresh,pc,flag,stored,costValue,
    finalMemory.2.2.2,kept.heap header afterHeader,properties⟩

end PDLower.CoreSearch
