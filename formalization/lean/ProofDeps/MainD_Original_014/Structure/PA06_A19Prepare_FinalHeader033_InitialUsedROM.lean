module

public import PaperProofs.Structure.CompactControllerClaims
public import PaperProofs.Structure.RawIncidenceLaminarRAM
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

/-! Candidate original controllerInput tail facts only. These do not
implement the loop or turn a packedWriter call into a free operation. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareFinalHeader033InitialUsedROM

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims RawIncidenceLaminarRAM CompactControllerClaims

theorem raw_input_length (q : Nat) (full : List (Finset (Fin q))) :
    (rawIncidenceROM q full).input.length = 2 + full.length * q := by
  simp only [rawIncidenceROM, List.length_append, List.length_cons, List.length_nil, incidence_length]

theorem input_length (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) :
    (controllerInput q full used).input.length = 2 + full.length * q + q := by
  simp only [controllerInput, List.length_append, raw_input_length, List.length_map, List.length_finRange]

theorem used_bit_read (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) (tool : Fin q) :
    (controllerInput q full used).semantic.read .input (2 + full.length * q + tool.val) = bit (decide (tool ∈ used)) := by
  change ((rawIncidenceROM q full).input ++ (List.finRange q).map (fun tool => bit (decide (tool ∈ used)))).getD _ 0 = _
  rw [List.getD_append_right _ _ _ _ (by rw [raw_input_length]; omega), raw_input_length]
  rw [show 2 + full.length * q + tool.val - (2 + full.length * q) = tool.val by omega,
    List.getD_eq_getElem _ _ (by simpa only [List.length_map, List.length_finRange] using tool.isLt)]
  simp only [List.getElem_map, List.getElem_finRange]
  congr 3

theorem used_bit_le_one (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) (tool : Fin q) :
    (controllerInput q full used).semantic.read .input (2 + full.length * q + tool.val) ≤ 1 := by
  rw [used_bit_read q full used tool]
  unfold bit
  split_ifs <;> omega

theorem used_address_lt (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) (tool : Fin q) :
    2 + full.length * q + tool.val < (controllerInput q full used).input.length := by
  rw [input_length q full used]
  have hh := tool.isLt
  omega

end PaperProofs.Structure.LaminarTree.PA06A19PrepareFinalHeader033InitialUsedROM
