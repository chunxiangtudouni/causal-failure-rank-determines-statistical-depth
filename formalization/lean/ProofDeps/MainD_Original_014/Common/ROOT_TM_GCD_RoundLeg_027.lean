module
public import Common.ROOT_TM_GCD_ControlValue_026

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDRoundLeg027
open PaperProofs.Common.Native.RationalControllerComputation
open PA17TMDivisionCompose006 ROOTTMGCDDispatch018 ROOTTMGCDLeg021 ROOTTMGCDSwapLeg022 ROOTTMGCDMacroLeg023
open ROOTTMGCDBranchLeg024 ROOTTMGCDDispatchLeg025 ROOTTMGCDControlValue026 ROOTTMGCDPairStep019
local notation "AVal" => PSTRTMBinaryAdd024.firstValue
local notation "BVal" => PSTRTMBinaryAdd024.secondValue

def oddDispatchTrace (n : Nat) (pairs : List Pair) (suffix : List Bool) : List (MachineState 3219) :=
  compareTrace n pairs suffix++if (PSTRTMCompareCode054.resultRelation 0 pairs).val=1
    then lessTrace n pairs suffix else greaterTrace n pairs suffix
theorem oddDispatch_leg (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    Leg (cfgAt 11 n pairs suffix) (oddDispatchTrace n pairs suffix)
      (cfgAt 0 n (if AVal pairs<BVal pairs then oddLess pairs else oddGreater pairs) suffix) := by
  have h1:=compare_leg n pairs suffix
  by_cases hc : (PSTRTMCompareCode054.resultRelation 0 pairs).val=1
  · have hlt:=(compare_less_iff pairs).mp hc
    have h1' : Leg (cfgAt 11 n pairs suffix) (compareTrace n pairs suffix) (atEnd 12 n pairs suffix) := by
      simpa [compareNext,hc] using h1
    have h:=Leg.append _ _ _ _ _ h1' (less_leg n pairs suffix)
    simpa [oddDispatchTrace,compareNext,hc,hlt] using h
  · have hlt : ¬AVal pairs<BVal pairs := fun h=>hc ((compare_less_iff pairs).mpr h)
    have h1' : Leg (cfgAt 11 n pairs suffix) (compareTrace n pairs suffix) (atEnd 13 n pairs suffix) := by
      simpa [compareNext,hc] using h1
    have h:=Leg.append _ _ _ _ _ h1' (greater_leg n pairs suffix)
    simpa [oddDispatchTrace,compareNext,hc,hlt] using h

def branchTrace (n : Nat) : List Pair → List Bool → List (MachineState 3219)
  | [],_ => []
  | (a,b)::later,suffix => parityTrace n a b later suffix++
      if a then if b then oddDispatchTrace n ((a,b)::later) suffix else halfTrace 2 n ((a,b)::later) suffix
      else if b then evenATrace n ((a,b)::later) suffix else bothTrace n ((a,b)::later) suffix

theorem branch_leg (n : Nat) (a b : Bool) (later : List Pair) (suffix : List Bool) :
    Leg (cfgAt 1 n ((a,b)::later) suffix) (branchTrace n ((a,b)::later) suffix)
      (cfgAt 0 (ROOTTMGCDSteinStep015.nextTwos (AVal ((a,b)::later)) (BVal ((a,b)::later)) n)
        (nextPairs ((a,b)::later)) suffix) := by
  have h1:=parity_leg n a b later suffix
  have hm:=parity_mod a b later
  cases a <;> cases b
  · have h:=Leg.append _ _ _ _ _ h1 (both_leg n ((false,false)::later) suffix)
    simpa [branchTrace,parityNext,nextPairs,ROOTTMGCDSteinStep015.nextTwos,hm.1,hm.2] using h
  · have h:=Leg.append _ _ _ _ _ h1 (evenA_leg n ((false,true)::later) suffix)
    simpa [branchTrace,parityNext,nextPairs,ROOTTMGCDSteinStep015.nextTwos,hm.1,hm.2] using h
  · have h:=Leg.append _ _ _ _ _ h1 (evenB_leg n ((true,false)::later) suffix)
    simpa [branchTrace,parityNext,nextPairs,ROOTTMGCDSteinStep015.nextTwos,hm.1,hm.2] using h
  · have h:=Leg.append _ _ _ _ _ h1 (oddDispatch_leg n ((true,true)::later) suffix)
    simpa [branchTrace,parityNext,nextPairs,ROOTTMGCDSteinStep015.nextTwos,hm.1,hm.2] using h

def roundTrace (n : Nat) (pairs : List Pair) (suffix : List Bool) : List (MachineState 3219) :=
  zeroTrace n pairs suffix++branchTrace n pairs suffix

/-- One real whole nonterminal round, including both scans and the actual
finite-control even/odd/comparison branches. Source positivity is used only
to identify the actual zero-scan control, not supplied to the machine. -/
theorem round_leg (n : Nat) (pairs : List Pair) (suffix : List Bool)
    (ha : AVal pairs≠0) (hb : BVal pairs≠0) :
    Leg (cfgAt 0 n pairs suffix) (roundTrace n pairs suffix)
      (cfgAt 0 (ROOTTMGCDSteinStep015.nextTwos (AVal pairs) (BVal pairs) n) (nextPairs pairs) suffix) := by
  have h1:=zero_leg n pairs suffix
  rw [nonzero_control pairs ha hb] at h1
  cases pairs with
  | nil => exact (ha rfl).elim
  | cons pair later =>
    obtain ⟨a,b⟩:=pair
    exact Leg.append _ _ _ _ _ h1 (branch_leg n a b later suffix)

theorem oddDispatchTrace_length_le (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    (oddDispatchTrace n pairs suffix).length ≤ 58*pairs.length+30 := by
  unfold oddDispatchTrace
  split_ifs
  · rw [List.length_append,compareTrace_length,lessTrace_length]
    omega
  · rw [List.length_append,compareTrace_length,greaterTrace_length]
    omega

theorem branchTrace_length_le (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    (branchTrace n pairs suffix).length ≤ 58*pairs.length+2*n+35 := by
  cases pairs with
  | nil => simp only [branchTrace,List.length_nil];omega
  | cons pair later =>
    obtain ⟨a,b⟩:=pair
    have ho:=oddDispatchTrace_length_le n ((a,b)::later) suffix
    cases a <;> cases b
    · simp only [branchTrace,Bool.false_eq_true,ite_false,List.length_append,parityTrace_length,bothTrace_length]
      omega
    · simp only [branchTrace,Bool.false_eq_true,ite_false,ite_true,List.length_append,
        parityTrace_length,evenATrace_length]
      omega
    · simp only [branchTrace,Bool.false_eq_true,ite_false,ite_true,List.length_append,
        parityTrace_length,halfTrace_length]
      omega
    · simp only [branchTrace,ite_true,List.length_append,parityTrace_length]
      omega

theorem roundTrace_length_le (n : Nat) (pairs : List Pair) (suffix : List Bool) :
    (roundTrace n pairs suffix).length ≤ 128*(pairs.length+n+1) := by
  have hb:=branchTrace_length_le n pairs suffix
  simp only [roundTrace,List.length_append,zeroTrace_length]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDRoundLeg027
