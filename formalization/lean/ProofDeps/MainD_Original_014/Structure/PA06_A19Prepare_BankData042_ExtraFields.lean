module

public import Structure.PA06_A19Prepare_BankData042

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareBankData042

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PA06A19PrepareRuntimeLayout026

/-- The two permanent fields not needed by the small032/037 consumer
records. Both are read from the actual reached heap, without wraparound. -/
theorem embedded_extra_bankData (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc.toNat = 5 * left.length) (ha : state.halted = false)
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1)
    (ht : (state.heap (BitVec.ofNat _ (20 + 4 * (full.length + q + 1)))).toNat = treeSize q full)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ sequence left.length ++ right)))
    (hend : Fits (indexWidth 32 full.length q) (5 * (left ++ sequence left.length ++ right).length)) :
    let bits := indexWidth 32 full.length q
    let t := treeSize q full
    let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
    let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
    let after := packingRun (controllerInput q full used) (left ++ sequence left.length ++ right)
      (sequenceClock full.length q) state
    (after.heap (BitVec.ofNat bits (CB + 3))).toNat = PA06A19PreparePackedView013.oldCapacity full.length q t ∧
      (after.heap (BitVec.ofNat bits (CB + 6))).toNat = 4 + P := by
  let bits := indexWidth 32 full.length q
  let t := treeSize q full
  let C := capacityWords 8192 full.length q t
  let P := packedCapacityWords q C bits
  let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
  let moved := PA06A19PrepareControlBank017.relocatedHeap
    (lowFields full.length q t (CapacityBits.width q) bits (PA06A19PrepareRuntimeHeader019.natView state).heap)
    0 (PA06A19PrepareControlBank017.cacheBase full.length q t P)
    (PA06A19PrepareControlBank017.cacheLength full.length q)
  let expected := bankFields full.length q t P CB moved
  have actual := PA06A19PrepareRuntimeSequence041.embedded_sequence_data q full used hq left right state
    hpc ha hM ht hh hcode hend
  dsimp only at actual
  have hC : Fits bits C := by
    have bound := actual_capacity_fits q full hq
    rw [capacityExpr_eq _ _ _ hq] at bound
    exact bound
  have hOld : Fits bits (PA06A19PreparePackedView013.oldCapacity full.length q t) :=
    (PA06A19PreparePackedView013.oldCapacity_le_capacity full.length q t hq).trans_lt hC
  have hCB : Fits bits CB := by
    simpa only [Nat.add_zero] using actual_bank_field_fits q full hq 0 (by decide)
  have hBase : Fits bits (4 + P) := by
    apply Nat.lt_of_le_of_lt _ hCB
    dsimp only [CB, PA06A19PrepareControlBank017.controlBase]
    omega
  have cell (offset value : Nat) (ho : offset ≤ 6)
      (he : expected (CB + offset) = value) (hv : Fits bits value) :
      ((packingRun (controllerInput q full used) (left ++ sequence left.length ++ right)
        (sequenceClock full.length q) state).heap (BitVec.ofNat bits (CB + offset))).toNat = value := by
    have hf : Fits bits (CB + offset) := actual_bank_field_fits q full hq offset ho
    have hp : (BitVec.ofNat bits (CB + offset)).toNat = CB + offset := Nat.mod_eq_of_lt hf
    rw [actual.2.2.2]
    change (BitVec.ofNat bits (expected (BitVec.ofNat bits (CB + offset)).toNat)).toNat = value
    simp only [hp, he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  dsimp only
  constructor
  · exact cell 3 _ (by decide)
      (by simp +decide [expected, bankFields, oldCapacityExpr, PA06A19PreparePackedView013.oldCapacity, t]) hOld
  · exact cell 6 _ (by decide)
      (by simp +decide [expected, bankFields, Nat.add_comm, P, C, t, bits]) hBase

end PaperProofs.Structure.LaminarTree.PA06A19PrepareBankData042
