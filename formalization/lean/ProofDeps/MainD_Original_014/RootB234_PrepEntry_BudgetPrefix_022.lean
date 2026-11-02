module

public import RootB234_PrepEntry_RawData_019

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.Raw

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PSTRTMWordPreparationFront214 PSTRSymbolicLaneScan PSTRSymbolicLaneArchive
open PSTRSymbolicCursorArchive PA17TMRatArithmeticParse002

variable {I : Instance}

def beforeBudget (input : StatisticalInput I) (contract : Contract I) : List Datum :=
  rawInstance input++rawContract contract

def budgetPairBits (budget : Rat) : List Bool := (navigationCells (datumPairs (.rational budget))).reverse

def reversedDataCells (digits : List Bool) : List Bool := digits.reverse.flatMap (fun bit => [bit,false])

theorem beforeBudget_nonempty (input : StatisticalInput I) (contract : Contract I) :
    beforeBudget input contract≠[] := by
  have room : 7≤(beforeBudget input contract).length := by
    simp only [beforeBudget,rawInstance,rawContract,List.length_append,List.length_cons,List.length_nil]
    omega
  intro empty
  rw [empty,List.length_nil] at room
  omega

private theorem cells_single (flag bit : Bool) : navigationCells [(flag,bit)]=[flag,bit] := rfl

theorem reverse_falsePairs (digits : List Bool) :
    (navigationCells (falsePairs digits)).reverse=reversedDataCells digits := by
  induction digits with
  | nil => rfl
  | cons digit later ih =>
    change (false::digit::navigationCells (falsePairs later)).reverse=reversedDataCells (digit::later)
    rw [List.reverse_cons,List.reverse_cons,ih]
    simp only [reversedDataCells,List.reverse_cons,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.append_assoc,List.singleton_append]

/-- The actual paired representation, deliberately not RawGetter's raw
leftBlocks/bothLeft ABI. TRUE TRUE terminates the last original Datum. -/
theorem budget_pair_layout (budget : Rat) (firstDen : Bool) (laterDen : List Bool)
    (denominator : denominatorDigits budget=firstDen::laterDen) :
    budgetPairBits budget=[true,true]++reversedDataCells laterDen++[firstDen,true]++
      reversedDataCells (numeratorDigits budget)++[sign budget,false] := by
  simp only [budgetPairBits,datumPairs,denominator,rationalPairs,navigationCells_append]
  simp only [cells_single,List.reverse_append]
  rw [reverse_falsePairs,reverse_falsePairs]
  simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.append_assoc,List.singleton_append]

/-- Every preparation has a preceding genuine Datum, including N=0.
Its last paired flag is a TRUE and therefore protects the whole finite
budget prefix against ListBlank trailing-FALSE truncation. -/
theorem archive_budget_boundary (input : StatisticalInput I) (contract : Contract I) (budget : Rat)
    (digits : List Bool) :
    ∃ (boundary : Bool) (tail : List Bool),
      (archiveTape (preparationData input contract budget) [] digits [] true).left=
        ListBlank.mk (budgetPairBits budget++boundary::true::tail) := by
  obtain ⟨earlier,boundary,previous⟩:=allDatumPairs_end (beforeBudget input contract) (beforeBudget_nonempty input contract)
  let tail:=(navigationCells earlier).reverse++false::(PSTRTMRawNat010.leftBlocks digits.reverse++[false])
  refine ⟨boundary,tail,?_⟩
  have data : allDatumPairs (preparationData input contract budget)=
      allDatumPairs (beforeBudget input contract)++datumPairs (.rational budget) := by
    simp only [preparationData,beforeBudget,allDatumPairs,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil]
  simp only [archiveTape,Tape.mk₂,Tape.mk'_left]
  rw [data,previous,navigationCells_append,navigationCells_append]
  simp only [cells_single,List.reverse_append,List.reverse_cons,List.nil_append,
    List.cons_append,budgetPairBits,tail,List.append_assoc]

theorem finite_budget_prefix (input : StatisticalInput I) (contract : Contract I) (budget : Rat)
    (digits actual : List Bool)
    (wholeLeft : ListBlank.mk actual=(archiveTape (preparationData input contract budget) [] digits [] true).left) :
    ∃ (boundary : Bool) (tail : List Bool),actual=budgetPairBits budget++boundary::true::tail := by
  obtain ⟨boundary,oldTail,shape⟩:=archive_budget_boundary input contract budget digits
  have marked : ListBlank.mk actual=ListBlank.mk ((budgetPairBits budget++[boundary])++true::oldTail) := by
    simpa only [List.append_assoc,List.singleton_append] using wholeLeft.trans shape
  obtain ⟨tail,physical⟩:=PSTRSymbolicNaturalExport.finite_marked_prefix
    (budgetPairBits budget++[boundary]) oldTail actual marked
  refine ⟨boundary,tail,?_⟩
  simpa only [List.append_assoc,List.singleton_append] using physical

end RootB234.PrepEntry.Raw
