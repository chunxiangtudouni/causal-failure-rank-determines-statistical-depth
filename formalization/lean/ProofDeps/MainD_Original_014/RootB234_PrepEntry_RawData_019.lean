module

public import RootB234_PrepEntry_RestorePublic_017
public import Common.PSTR_SYM_RawEOFPolynomial_064

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.Raw

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PSTRTMWordPreparationFront214 PSTRTMSeq005 PSTRTMIncrement009
open PSTRSymbolicRawBootstrap PSTRSymbolicCounter PSTRSymbolicRawLoop PSTRSymbolicLaneArchive

variable {I : Instance}

def remaining (input : StatisticalInput I) (contract : Contract I) (budget : Rat) : List Datum :=
  (preparationData input contract budget).tail.tail

theorem preparation_fields (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    preparationData input contract budget=.natural I.stageCount::.natural I.toolCount::remaining input contract budget := rfl

theorem remaining_room (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    6≤(remaining input contract budget).length := by
  simp only [remaining,preparationData,rawInstance,rawContract,List.cons_append,List.nil_append,
    List.tail_cons,List.length_append,List.length_cons,List.length_nil]
  omega

theorem count_room (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    8≤(preparationData input contract budget).length := by
  have room:=remaining_room input contract budget
  have length:=congrArg List.length (preparation_fields input contract budget)
  simp only [List.length_cons] at length
  omega

theorem preparation_bits (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    preparationInput input contract budget=bootstrapInput
      (preparationData input contract budget).length I.stageCount I.toolCount
      ((remaining input contract budget).flatMap encodeDatum++[true]) := by
  change encode (preparationData input contract budget)=_
  have encoded:=congrArg (fun data : List Datum => data.flatMap encodeDatum) (preparation_fields input contract budget)
  unfold encode bootstrapInput
  rw [encoded]
  simp only [List.flatMap_cons,List.append_assoc]

theorem remaining_count (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    valueDigits (afterTwo (preparationData input contract budget).length)=(remaining input contract budget).length := by
  have counted:=(two_count_rounds (preparationData input contract budget).length (by
    have room:=count_room input contract budget; omega)).2.2.1
  have length:=congrArg List.length (preparation_fields input contract budget)
  simp only [List.length_cons] at length
  omega

theorem header_room (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    3≤(afterTwo (preparationData input contract budget).length).length := by
  let count:=(preparationData input contract budget).length
  have countRoom : 4≤count := by have h:=count_room input contract budget; omega
  have width:=(two_count_rounds count (by omega)).2.2.2
  have logRoom : natBits 4≤natBits count := by
    simp only [natBits,Nat.log2_eq_log_two]
    exact Nat.add_le_add_right (Nat.log_mono_right countRoom) 1
  have four : natBits 4=3 := by decide
  rw [four] at logRoom
  change 3≤(afterTwo count).length
  rw [width,PSTRSymbolicLocator.rawPayload_length]
  exact logRoom

/-- The real frozen bootstrap reads outer M and both N/J fields on the
actual preparation wire, including N=0. No count/width is supplied to code. -/
theorem preparation_bootstrap (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ (trace : List (MachineState bootSupport.card)) (final : MachineState bootSupport.card),
      Runs bootstrapMachine (preparationInput input contract budget) trace final ∧
      final.Tape=bootstrapTape (preparationData input contract budget).length I.stageCount I.toolCount
        ((remaining input contract budget).flatMap encodeDatum++[true]) ∧
      valueDigits (afterTwo (preparationData input contract budget).length)=(remaining input contract budget).length ∧
      trace.length≤1024*((preparationInput input contract budget).length+1)^2 ∧
      ∀ clock,visitedSpace bootstrapMachine (preparationInput input contract budget).length (trace.take clock)≤
        4096*((preparationInput input contract budget).length+1)^2 := by
  obtain ⟨trace,final,actual,tape,_value,time,cells⟩:=bootstrap_polynomial
    (preparationData input contract budget).length I.stageCount I.toolCount
      ((remaining input contract budget).flatMap encodeDatum++[true]) (by
        have room:=count_room input contract budget; omega)
  rw [←preparation_bits input contract budget] at actual time cells
  exact ⟨trace,final,actual,tape,remaining_count input contract budget,time,cells⟩

end RootB234.PrepEntry.Raw
