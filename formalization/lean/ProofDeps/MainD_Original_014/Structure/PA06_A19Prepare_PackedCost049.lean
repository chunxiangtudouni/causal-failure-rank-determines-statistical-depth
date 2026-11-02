module

public import PaperProofs.Structure.CompactControllerClaims
public import PaperProofs.Structure.PA17_PackingBounds_043
public import Mathlib.Algebra.Order.Floor.Div

set_option autoImplicit false
set_option warningAsError true

/-! Tight physical packed-word bound for the original preparation cost.
The real rounded-up division is used, so no extra width(q) factor remains.
The selected-width corollaries include zero tools and zero stages. This
module is a source candidate until the parent's strict/public/audit checks. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PreparePackedCost049

open IndexedRAM IndexedClosureRAM AlgorithmClaims

/-- When one scalar fits in a word, packing C scalars needs at most C words.
This uses the actual ceiling-division definition of packedCapacityWords. -/
theorem packedCapacityWords_le_capacity (q capWords bits : Nat)
    (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits) :
    packedCapacityWords q capWords bits ≤ capWords := by
  change (capWords * CapacityBits.width q + bits - 1) / bits ≤ capWords
  rw [← Nat.ceilDiv_eq_add_pred_div]
  apply (ceilDiv_le_iff_le_mul (a := bits)
    (b := capWords * CapacityBits.width q) (c := capWords) hbits).mpr
  exact (Nat.mul_le_mul_left capWords hwidth).trans_eq (Nat.mul_comm capWords bits)

/-- Original selected word factor32; both eligibility facts are proved
by the existing public layout bounds, not supplied by the raw caller. -/
theorem selected_packedCapacityWords_le_capacity (N q capWords : Nat) :
    packedCapacityWords q capWords (indexWidth 32 N q) ≤ capWords :=
  packedCapacityWords_le_capacity q capWords (indexWidth 32 N q)
    (PA17PackingBounds043.bits_pos N q) (PA17PackingBounds043.width_le_bits N q)

/-- The actual original capacity with scratchFactor8192. No positivity
assumption on N, q or t is added; q0 uses the original zero-capacity branch. -/
theorem actual_packedCapacityWords_le_capacity (N q t : Nat) :
    packedCapacityWords q (CompactControllerClaims.capacityWords 8192 N q t)
      (indexWidth 32 N q) ≤ CompactControllerClaims.capacityWords 8192 N q t :=
  selected_packedCapacityWords_le_capacity N q
    (CompactControllerClaims.capacityWords 8192 N q t)

/-- Direct original-raw-instance specialization, keeping the true treeSize
definition and exactly the capacity used by Stage141 and prebuild044. -/
theorem prepared_packedCapacityWords_le_capacity (q : Nat) (full : List (Finset (Fin q))) :
    packedCapacityWords q
      (CompactControllerClaims.capacityWords 8192 full.length q (CompactControllerClaims.treeSize q full))
      (indexWidth 32 full.length q) ≤
        CompactControllerClaims.capacityWords 8192 full.length q (CompactControllerClaims.treeSize q full) :=
  actual_packedCapacityWords_le_capacity full.length q (CompactControllerClaims.treeSize q full)

end PaperProofs.Structure.LaminarTree.PA06A19PreparePackedCost049
