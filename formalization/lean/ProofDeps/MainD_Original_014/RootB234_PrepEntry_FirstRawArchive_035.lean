module

public import RootB234_PrepEntry_FirstRawCode_034

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.FirstRaw

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep PSTRTMWordPreparationFront214

variable {I : Instance}

def lastNatural (input : StatisticalInput I) (contract : Contract I) : Nat :=
  (firstNumbers input contract).getLast (firstNumbers_nonempty input contract)

theorem lastNatural_positive (input : StatisticalInput I) (contract : Contract I) (positive : 0<I.stageCount) :
    lastNatural input contract=(input.experiment ⟨0,positive⟩).alphabetSize := by
  unfold lastNatural
  simp only [firstNumbers,dite_eq_left positive,List.getLast_concat]

theorem lastNatural_zero (input : StatisticalInput I) (contract : Contract I) (zero : I.stageCount=0) :
    lastNatural input contract=contract.normalCallBound := by
  have noPositive : ¬0<I.stageCount := by omega
  unfold lastNatural
  simp only [firstNumbers,dite_eq_right noPositive,contractNumbers,List.getLast_cons_cons,List.getLast_singleton]

theorem nextLeft_marker (left : List Bool) (number : Nat) :
    ∃ tail,Alpha.nextLeft left number=false::true::tail :=
  Alpha.count_marker_tail (false::left) number

theorem archived_marker (left : List Bool) (numbers : List Nat)
    (marker : ∃ tail,left=false::true::tail) :
    ∃ tail,NatPrefix.archived left numbers=false::true::tail := by
  induction numbers generalizing left with
  | nil => exact marker
  | cons number numbers ih => exact ih (Alpha.nextLeft left number) (nextLeft_marker left number)

theorem archived_last (left : List Bool) (input : StatisticalInput I) (contract : Contract I) :
    NatPrefix.archived left (firstNumbers input contract)=
      Alpha.nextLeft (NatPrefix.archived left (firstNumbers input contract).dropLast) (lastNatural input contract) := by
  have shape:=List.dropLast_concat_getLast (firstNumbers_nonempty input contract)
  change NatPrefix.archived left (firstNumbers input contract)=_
  conv_lhs => rw [←shape]
  simp only [NatPrefix.archived,List.foldl_append,List.foldl_cons,List.foldl_nil,lastNatural]

/-- A genuine TRUE in the preceding original natural archive recovers the
physical finite source prefix; quotient-Tape equality is never used as a
free tape reload or an arbitrary RawGetter-coordinate conversion. -/
theorem finite_current (bank : RatInput.Stack → List Bool) (left : List Bool) (number : Nat)
    (marker : ∃ tail,left=false::true::tail)
    (whole : ListBlank.mk (bank 1)=ListBlank.mk (Alpha.nextLeft left number)) :
    ∃ tail,bank 1=false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload number).reverse++false::tail) := by
  obtain ⟨tail,shape⟩:=marker
  rw [Alpha.nextLeft,shape] at whole
  let marked:=false::(PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload number).reverse++[false,false])
  obtain ⟨physical,actual⟩:=PSTRSymbolicNaturalExport.finite_marked_prefix marked tail (bank 1)
    (by simpa only [marked,List.cons_append,List.append_assoc,List.nil_append] using whole)
  refine ⟨false::true::physical,?_⟩
  simpa only [marked,List.cons_append,List.append_assoc,List.nil_append] using actual

theorem firstNatural_physical (input : StatisticalInput I) (contract : Contract I) (budget : Rat)
    (bank : RatInput.Stack → List Bool)
    (whole : ListBlank.mk (bank 1)=ListBlank.mk (NatPrefix.archived (NJ.finalLeft input contract budget)
      (firstNumbers input contract))) :
    ∃ tail,bank 1=false::(PSTRTMRawNat010.leftBlocks
      (PSTRTMNatValue017.rawPayload (lastNatural input contract)).reverse++false::tail) := by
  rw [archived_last] at whole
  exact finite_current bank _ _ (archived_marker _ _ (nextLeft_marker _ _)) whole

theorem firstRat_length_le (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    (encodeDatum (.rational (firstValue input budget))).length≤(preparationInput input contract budget).length := by
  obtain ⟨suffix,shape⟩:=afterTools_split input contract budget
  have sub : (NJ.afterTools input contract budget).length≤(preparationInput input contract budget).length := by
    change (((preparationData input contract budget).drop 2).flatMap encodeDatum++[true]).length≤
      (encode (preparationData input contract budget)).length
    have pieces:=List.take_append_drop 2 (preparationData input contract budget)
    have encoded:=congrArg (fun data : List Datum => data.flatMap encodeDatum) pieces
    have lengths:=congrArg List.length encoded
    simp only [List.flatMap_append,List.length_append] at lengths
    simp only [encode,List.length_append]
    omega
  rw [shape] at sub
  simp only [List.length_append] at sub
  omega

end RootB234.PrepEntry.FirstRaw
