module

public import Paid.RootD27Core_MidpointState_072

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList loadSlot)
open PDLower.CoreSearch

def midpointSaveCode (origin entry : ℕ) : List Instruction :=
  headerCode midpointCommands++solverRuntimeDispatchCode (origin+39) entry++
    rootStatisticsCode 25++saveSolverResultCode

theorem midpointSave_length (origin entry : ℕ) : (midpointSaveCode origin entry).length=64 := by
  simp only [midpointSaveCode,List.length_append,midpointCode_length,solverRuntimeDispatch_length,
    rootStatistics_length,saveSolverResult_length]

def branchUpdateCode (origin : ℕ) (upper isExact : Bool) (decrementPC : ℕ) : List Instruction :=
  copySavedResultCode origin upper++headerCode (selectedMetadataCommands upper isExact)++[.jump decrementPC]

theorem branchUpdate_length (origin decrementPC : ℕ) (upper isExact : Bool) :
    (branchUpdateCode origin upper isExact decrementPC).length=81 := by
  simp only [branchUpdateCode,List.length_append,copySavedResult_length,selectedMetadata_length,
    List.length_cons,List.length_nil]

def tagDecisionCode (origin decrementPC : ℕ) : List Instruction :=
  loadSlot 13 .flag++[.branchZero .flag decrementPC (origin+4)]

theorem tagDecision_length (origin decrementPC : ℕ) : (tagDecisionCode origin decrementPC).length=4:=rfl

def stopDecisionCode (origin midpointPC decrementPC : ℕ) : List Instruction :=
  bracketStopCode origin++[.branchZero .flag midpointPC decrementPC]

theorem stopDecision_length (origin midpointPC decrementPC : ℕ) :
    (stopDecisionCode origin midpointPC decrementPC).length=183 := by
  simp only [stopDecisionCode,List.length_append,bracketStopCode_length,List.length_cons,List.length_nil]

def midpointDecisionCode (origin entry lessPC exactPC : ℕ) : List Instruction :=
  midpointSaveCode origin entry++comparisonStoredCode .equal 27 3++[.branchZero .flag lessPC exactPC]

theorem midpointDecision_length (origin entry lessPC exactPC : ℕ) :
    (midpointDecisionCode origin entry lessPC exactPC).length=75 := by
  simp only [midpointDecisionCode,List.length_append,midpointSave_length,comparisonStored_length,
    List.length_cons,List.length_nil]

def riskDecisionCode (lowerPC upperPC : ℕ) : List Instruction :=
  comparisonStoredCode .less 3 27++[.branchZero .flag upperPC lowerPC]

theorem riskDecision_length (lowerPC upperPC : ℕ) : (riskDecisionCode lowerPC upperPC).length=11 := by
  simp only [riskDecisionCode,List.length_append,comparisonStored_length,List.length_cons,List.length_nil]

/-- Literal fixed code for one original cachedMultiplierStep. Every
branch really jumps; the three updates share the actual returned table
descriptor but write the source-selected buffer and source tag. -/
def bisectionBodyCode (origin entry decrementPC : ℕ) : List Instruction :=
  tagDecisionCode origin decrementPC++
  stopDecisionCode (origin+4) (origin+187) decrementPC++
  midpointDecisionCode (origin+187) entry (origin+262) (origin+273)++
  riskDecisionCode (origin+354) (origin+435)++
  branchUpdateCode (origin+273) false true decrementPC++
  branchUpdateCode (origin+354) false false decrementPC++
  branchUpdateCode (origin+435) true false decrementPC

theorem bisectionBody_length (origin entry decrementPC : ℕ) :
    (bisectionBodyCode origin entry decrementPC).length=516 := by
  simp only [bisectionBodyCode,List.length_append,tagDecision_length,stopDecision_length,
    midpointDecision_length,riskDecision_length,branchUpdate_length]

/-- Static decoding of the actual literal516-op body; no per-block
fetch/trace oracle is supplied by an original caller. -/
theorem bisectionBody_fetch_parts (program : Program) (origin entry decrementPC : ℕ)
    (fetched : FetchesCode program origin (bisectionBodyCode origin entry decrementPC)) :
    FetchesCode program origin (tagDecisionCode origin decrementPC) ∧
    FetchesCode program (origin+4) (stopDecisionCode (origin+4) (origin+187) decrementPC) ∧
    FetchesCode program (origin+187) (midpointDecisionCode (origin+187) entry (origin+262) (origin+273)) ∧
    FetchesCode program (origin+262) (riskDecisionCode (origin+354) (origin+435)) ∧
    FetchesCode program (origin+273) (branchUpdateCode (origin+273) false true decrementPC) ∧
    FetchesCode program (origin+354) (branchUpdateCode (origin+354) false false decrementPC) ∧
    FetchesCode program (origin+435) (branchUpdateCode (origin+435) true false decrementPC) := by
  change FetchesCode program origin
    (tagDecisionCode origin decrementPC++stopDecisionCode (origin+4) (origin+187) decrementPC++
      midpointDecisionCode (origin+187) entry (origin+262) (origin+273)++riskDecisionCode (origin+354) (origin+435)++
      branchUpdateCode (origin+273) false true decrementPC++branchUpdateCode (origin+354) false false decrementPC++
      branchUpdateCode (origin+435) true false decrementPC) at fetched
  simp only [List.append_assoc] at fetched
  have stopFetch:=fetched.append_right
  have middleFetch:=stopFetch.append_right
  have riskFetch:=middleFetch.append_right
  have exactFetch:=riskFetch.append_right
  have lowerFetch:=exactFetch.append_right
  have upperFetch:=lowerFetch.append_right
  refine ⟨fetched.append_left,?_,?_,?_,?_,?_,?_⟩
  · simpa only [tagDecision_length] using stopFetch.append_left
  · simpa only [tagDecision_length,stopDecision_length,Nat.add_assoc] using middleFetch.append_left
  · simpa only [tagDecision_length,stopDecision_length,midpointDecision_length,Nat.add_assoc] using riskFetch.append_left
  · simpa only [tagDecision_length,stopDecision_length,midpointDecision_length,riskDecision_length,Nat.add_assoc] using exactFetch.append_left
  · simpa only [tagDecision_length,stopDecision_length,midpointDecision_length,riskDecision_length,branchUpdate_length,Nat.add_assoc] using lowerFetch.append_left
  · simpa only [tagDecision_length,stopDecision_length,midpointDecision_length,riskDecision_length,branchUpdate_length,Nat.add_assoc] using upperFetch

end RootD27.Core
