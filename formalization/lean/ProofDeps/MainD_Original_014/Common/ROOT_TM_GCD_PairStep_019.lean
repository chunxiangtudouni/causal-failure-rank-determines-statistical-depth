module
public import Common.ROOT_TM_GCD_HalfResident_014
public import Common.ROOT_TM_GCD_SteinStep_015

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDPairStep019
open PaperProofs.Common.Native.RationalControllerComputation
local notation "AVal" => PSTRTMBinaryAdd024.firstValue
local notation "BVal" => PSTRTMBinaryAdd024.secondValue
abbrev Pair:=Bool × Bool
def swap (pairs : List Pair) : List Pair:=pairs.map ROOTTMGCDMap004.swapPair
abbrev half:=ROOTTMGCDHalf001.halfPairs
def halfA (pairs : List Pair) : List Pair:=swap (half (swap pairs))
def halfBoth (pairs : List Pair) : List Pair:=halfA (half pairs)
def oddGreater (pairs : List Pair) : List Pair:=half (swap (PA17TMDivisionSub001.subPairs false pairs))
def oddLess (pairs : List Pair) : List Pair:=oddGreater (swap pairs)

theorem swap_length (pairs : List Pair) : (swap pairs).length=pairs.length := List.length_map _
theorem half_length (pairs : List Pair) : (half pairs).length=pairs.length := by
  simp only [half,ROOTTMGCDHalf001.halfPairs,List.length_reverse,ROOTTMGCDHalf001.result_length]
theorem halfA_length (pairs : List Pair) : (halfA pairs).length=pairs.length := by
  simp only [halfA,swap_length,half_length]
theorem halfBoth_length (pairs : List Pair) : (halfBoth pairs).length=pairs.length := by
  simp only [halfBoth,halfA_length,half_length]
theorem oddGreater_length (pairs : List Pair) : (oddGreater pairs).length=pairs.length := by
  simp only [oddGreater,half_length,swap_length,PA17TMDivisionSub001.subPairs_length]
theorem oddLess_length (pairs : List Pair) : (oddLess pairs).length=pairs.length := by
  simp only [oddLess,oddGreater_length,swap_length]

theorem swap_values (pairs : List Pair) : AVal (swap pairs)=BVal pairs ∧ BVal (swap pairs)=AVal pairs :=
  ⟨ROOTTMGCDMap004.firstValue_swap pairs,ROOTTMGCDMap004.secondValue_swap pairs⟩
theorem half_values (pairs : List Pair) : AVal (half pairs)=AVal pairs ∧ BVal (half pairs)=BVal pairs/2 :=
  ROOTTMGCDHalf001.half_values pairs
theorem halfA_values (pairs : List Pair) : AVal (halfA pairs)=AVal pairs/2 ∧ BVal (halfA pairs)=BVal pairs := by
  have h:=half_values (swap pairs)
  have hs:=swap_values (half (swap pairs))
  have hp:=swap_values pairs
  change AVal (halfA pairs)=BVal (half (swap pairs)) ∧ BVal (halfA pairs)=AVal (half (swap pairs)) at hs
  rw [h.1,h.2,hp.1,hp.2] at hs
  exact hs
theorem halfBoth_values (pairs : List Pair) :
    AVal (halfBoth pairs)=AVal pairs/2 ∧ BVal (halfBoth pairs)=BVal pairs/2 := by
  have h:=halfA_values (half pairs)
  have hh:=half_values pairs
  change AVal (halfBoth pairs)=AVal (half pairs)/2 ∧ BVal (halfBoth pairs)=BVal (half pairs) at h
  rw [hh.1,hh.2] at h
  exact h
theorem oddGreater_values (pairs : List Pair) (hle : BVal pairs ≤ AVal pairs) :
    AVal (oddGreater pairs)=BVal pairs ∧ BVal (oddGreater pairs)=(AVal pairs-BVal pairs)/2 := by
  have hsub:=PA17TMDivisionSub001.subtraction_exact pairs hle
  have hb:=PA17TMDivisionSub001.secondValue_subPairs false pairs
  have hs:=swap_values (PA17TMDivisionSub001.subPairs false pairs)
  have hh:=half_values (swap (PA17TMDivisionSub001.subPairs false pairs))
  change AVal (oddGreater pairs)=AVal (swap (PA17TMDivisionSub001.subPairs false pairs)) ∧
    BVal (oddGreater pairs)=BVal (swap (PA17TMDivisionSub001.subPairs false pairs))/2 at hh
  rw [hs.1,hs.2,hsub.2,hb] at hh
  exact hh
theorem oddLess_values (pairs : List Pair) (hle : AVal pairs ≤ BVal pairs) :
    AVal (oddLess pairs)=AVal pairs ∧ BVal (oddLess pairs)=(BVal pairs-AVal pairs)/2 := by
  have hs:=swap_values pairs
  have he : BVal (swap pairs) ≤ AVal (swap pairs) := by rw [hs.1,hs.2];exact hle
  have h:=oddGreater_values (swap pairs) he
  change AVal (oddLess pairs)=BVal (swap pairs) ∧ BVal (oddLess pairs)=(AVal (swap pairs)-BVal (swap pairs))/2 at h
  rw [hs.1,hs.2] at h
  exact h

def nextPairs (pairs : List Pair) : List Pair:=
  if AVal pairs%2=0 then if BVal pairs%2=0 then halfBoth pairs else halfA pairs
  else if BVal pairs%2=0 then half pairs
  else if AVal pairs<BVal pairs then oddLess pairs else oddGreater pairs

theorem next_length (pairs : List Pair) : (nextPairs pairs).length=pairs.length := by
  unfold nextPairs
  split_ifs <;> first | exact halfBoth_length pairs | exact halfA_length pairs |
    exact half_length pairs | exact oddLess_length pairs | exact oddGreater_length pairs

theorem next_values (pairs : List Pair) :
    (AVal (nextPairs pairs),BVal (nextPairs pairs))=ROOTTMGCDSteinStep015.nextPair (AVal pairs) (BVal pairs) := by
  unfold nextPairs ROOTTMGCDSteinStep015.nextPair
  split_ifs with h1 h2 h3 h4
  · exact Prod.ext (halfBoth_values pairs).1 (halfBoth_values pairs).2
  · exact Prod.ext (halfA_values pairs).1 (halfA_values pairs).2
  · exact Prod.ext (half_values pairs).1 (half_values pairs).2
  · exact Prod.ext (oddLess_values pairs (by omega)).1 (oddLess_values pairs (by omega)).2
  · exact Prod.ext (oddGreater_values pairs (by omega)).1 (oddGreater_values pairs (by omega)).2

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDPairStep019
