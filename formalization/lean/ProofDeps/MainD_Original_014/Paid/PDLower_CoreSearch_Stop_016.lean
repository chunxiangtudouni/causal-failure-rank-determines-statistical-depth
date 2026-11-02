module

public import Paid.PDLower_CoreSearch_MixtureEntry_015

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch

/-- The ORIGINAL bracket stopping expression, with its entire actual
weight/cost producer. Incoming30..42 are arbitrary Header cells. -/
def bracketStopCode (origin : ℕ) : List Instruction :=
  mixtureEntryCode origin++headerCode mixtureFinishCommands++comparisonStoredCode .lessEqual 38 41

theorem bracketStopCode_length (origin : ℕ) : (bracketStopCode origin).length=182 := by
  simp only [bracketStopCode,List.length_append,mixtureEntryCode_length,mixtureFinish_length,comparisonStored_length]

theorem mixtureFinish_keepsLow (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve) (values : ℕ→Cell) :
    KeepsLow values (mixtureFinishValues P fee lower upper values) := by
  unfold mixtureFinishValues
  exact (((((((KeepsLow.refl values).update 41 _ (by decide)).update 41 _ (by decide)).update 34 _ (by decide)).update 35 _
    (by decide)).update 36 _ (by decide)).update 39 _ (by decide)).update 41 _ (by decide)

theorem bracketStop_trace (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (input : List Cell) (origin : ℕ) (before : State) (values : ℕ→Cell)
    (position : before.pc=origin) (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (risk : values 3=.rational P.certificate.risk) (feeValue : values 5=.rational fee)
    (lowerPrice : values 14=.rational lower.multiplier) (upperPrice : values 15=.rational upper.multiplier)
    (lowerObs : values 16=.rational (P.solveRecord lower).observation)
    (lowerRep : values 17=.rational (P.solveRecord lower).repairs) (lowerRisk : values 18=.rational (P.solveRisk lower))
    (upperObs : values 19=.rational (P.solveRecord upper).observation)
    (upperRep : values 20=.rational (P.solveRecord upper).repairs) (upperRisk : values 21=.rational (P.solveRisk upper))
    (fetched : FetchesCode program origin (bracketStopCode origin)) :
    ∃ (trace : List State) (after : State) (finalValues : ℕ→Cell),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤3000 ∧
      Header after 0 finalValues ∧ KeepsLow values finalValues ∧ after.register .fresh=.natural 0 ∧ after.pc=origin+182 ∧
      after.register .flag=.natural (if P.searchStopped fee (.bracket lower upper) then 1 else 0) ∧
      after.heap 40=.natural (if P.searchStopped fee (.bracket lower upper) then 1 else 0) ∧
      after.heap 36=.rational (P.mixtureCost fee lower upper) ∧ after.output=before.output ∧
      (∀ slot<29,after.heap slot=before.heap slot) ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  have arranged : FetchesCode program origin
      (mixtureEntryCode origin++(headerCode mixtureFinishCommands++comparisonStoredCode .lessEqual 38 41)) := by
    simpa only [bracketStopCode,List.append_assoc] using fetched
  have entryFetch : FetchesCode program origin (mixtureEntryCode origin) := arranged.append_left
  have restFetch : FetchesCode program (origin+114)
      (headerCode mixtureFinishCommands++comparisonStoredCode .lessEqual 38 41) := by
    simpa only [mixtureEntryCode_length] using arranged.append_right
  obtain ⟨s1,run1,header1,keep1,fresh1,pc1⟩ :=
    mixtureEntry_segment P fee lower upper program input origin before values position header fresh risk feeValue lowerPrice upperPrice
      lowerObs lowerRep lowerRisk upperObs upperRep upperRisk entryFetch
  let v1 := mixtureEntryValues P fee lower upper values
  have ratio1 : v1 31=.rational (P.mixtureWeight lower upper) := by simp [v1,mixtureEntryValues]
  have costL1 : v1 32=.rational (P.solveCost fee lower) := by simp [v1,mixtureEntryValues,mixturePrepareValues]
  have costU1 : v1 33=.rational (P.solveCost fee upper) := by simp [v1,mixtureEntryValues,mixturePrepareValues]
  have gap1 : v1 38=.rational ((upper.multiplier-lower.multiplier)*P.certificate.risk) := by
    simp [v1,mixtureEntryValues,mixturePrepareValues]
  obtain ⟨t2,s2,h2,l2,c2,time2,header2,fresh2,pc2,_out2,mem2⟩ :=
    mixtureFinish_trace P fee lower upper program input s1 v1 header1 fresh1 ratio1 costL1 costU1
      (by rw [pc1];exact restFetch.append_left)
  let v2 := mixtureFinishValues P fee lower upper v1
  have run2 : ScalarSegment program input s1 s2 885 := ⟨t2,h2,l2,c2,time2,mem2⟩
  have finishFields := mixtureFinish_fields P fee lower upper v1
  have gap2 : v2 38=.rational ((upper.multiplier-lower.multiplier)*P.certificate.risk) := finishFields.2.2.trans gap1
  have compareFetch : FetchesCode program s2.pc (comparisonStoredCode .lessEqual 38 41) := by
    rw [pc2,pc1]
    simpa only [mixtureFinish_length] using restFetch.append_right
  obtain ⟨t3,h3,l3,c3,time3,header3,mem3⟩ :=
    bracketStopped_trace P fee lower upper program input s2 v2 header2 fresh2 gap2 finishFields.2.1 compareFetch
  let after := comparisonStoredResult s2 38 41 (P.searchStopped fee (.bracket lower upper))
  let v3 := Function.update v2 40 (.natural (if P.searchStopped fee (.bracket lower upper) then 1 else 0))
  have run3 : ScalarSegment program input s2 after 165 := ⟨t3,h3,l3,c3,time3,mem3⟩
  have actual : ScalarSegment program input before after 3000 := ((run1.trans run2).trans run3).mono (by decide)
  have fields3 := comparisonStored_fields s2 38 41 (P.searchStopped fee (.bracket lower upper))
  have kept : KeepsLow values v3 := (keep1.trans (mixtureFinish_keepsLow P fee lower upper v1)).update 40 _ (by decide)
  have finalPC : after.pc=origin+182 := by
    dsimp only [after]
    rw [fields3.2.2.2.2.1,pc2,pc1]
  have flag : after.register .flag=.natural (if P.searchStopped fee (.bracket lower upper) then 1 else 0) :=
    fields3.2.2.2.1
  have stored := header3.value 40 (by decide)
  have mixture := header3.value 36 (by decide)
  have fresh3 : after.register .fresh=.natural 0 := fields3.2.2.1.trans fresh2
  have finalMemory := actual.final
  obtain ⟨trace,head,last,chain,cost,memory⟩ := actual
  refine ⟨trace,after,v3,head,last,chain,cost,header3,kept,fresh3,finalPC,flag,?_,?_,
    finalMemory.2.2.2,kept.heap header header3,memory⟩
  · simpa only [Nat.zero_add,Function.update_self] using stored
  · have value : v3 36=.rational (P.mixtureCost fee lower upper) := by simp [v3,v2,mixtureFinishValues]
    simpa only [Nat.zero_add] using mixture.trans value

end PDLower.CoreSearch
