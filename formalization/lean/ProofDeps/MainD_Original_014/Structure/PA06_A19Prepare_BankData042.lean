module

public import Structure.PA06_A19Prepare_RuntimeSequence041_Embedded
public import Structure.PA06_A19Prepare_InitialUsed037_Setup
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Candidate interfaces from the actual embedded134-op producer. Both
consumer records describe the same reached physical state. In particular
the used-bit loop receives Cnew from the actual bank+4 store; no bank/cache
contents or execution-safety oracle is added to the raw caller. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareBankData042

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PA06A19PrepareRuntimeLayout026

theorem embedded_bankData_pair (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc.toNat = 5 * left.length) (ha : state.halted = false)
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1)
    (ht : (state.heap (BitVec.ofNat _ (20 + 4 * (full.length + q + 1)))).toNat = treeSize q full)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ sequence left.length ++ right)))
    (hend : Fits (indexWidth 32 full.length q) (5 * (left ++ sequence left.length ++ right).length)) :
    let after := packingRun (controllerInput q full used) (left ++ sequence left.length ++ right)
      (sequenceClock full.length q) state
    PA06A19PrepareFiniteInit032.BankData q full after ∧ PA06A19PrepareInitialUsed037.BankData q full after := by
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
  have hCB : Fits bits CB := by
    simpa only [Nat.add_zero] using actual_bank_field_fits q full hq 0 (by decide)
  have small_value (value : Nat) (hle : value ≤ CB) : Fits bits value := hle.trans_lt hCB
  have hN : Fits bits full.length := by
    apply small_value
    dsimp only [CB, PA06A19PrepareControlBank017.controlBase,
      PA06A19PrepareControlBank017.dimensions, PA06A19PrepareControlBank017.mass]
    omega
  have hQ : Fits bits q := by
    apply small_value
    dsimp only [CB, PA06A19PrepareControlBank017.controlBase,
      PA06A19PrepareControlBank017.dimensions, PA06A19PrepareControlBank017.mass]
    omega
  have hT : Fits bits t := by
    apply small_value
    dsimp only [CB, PA06A19PrepareControlBank017.controlBase,
      PA06A19PrepareControlBank017.dimensions, PA06A19PrepareControlBank017.mass]
    omega
  have hP : Fits bits P := by
    apply small_value
    dsimp only [CB, PA06A19PrepareControlBank017.controlBase]
    omega
  have hC : Fits bits C := by
    have hc := actual_capacity_fits q full hq
    rw [capacityExpr_eq _ _ _ hq] at hc
    exact hc
  have cell (offset value : Nat) (ho : offset ≤ 6)
      (he : expected (CB + offset) = value) (hv : Fits bits value) :
      ((packingRun (controllerInput q full used) (left ++ sequence left.length ++ right)
        (sequenceClock full.length q) state).heap (BitVec.ofNat bits (CB + offset))).toNat = value := by
    have hf : Fits bits (CB + offset) := actual_bank_field_fits q full hq offset ho
    have hp : (BitVec.ofNat bits (CB + offset)).toNat = CB + offset := Nat.mod_eq_of_lt hf
    have written : (packingRun (controllerInput q full used) (left ++ sequence left.length ++ right)
        (sequenceClock full.length q) state).heap (BitVec.ofNat bits (CB + offset)) = BitVec.ofNat bits value := by
      calc
        _ = BitVec.ofNat bits (expected ((BitVec.ofNat bits (CB + offset)).toNat)) := actual.2.2.2 _
        _ = BitVec.ofNat bits value := by rw [hp, he]
    exact (congrArg BitVec.toNat written).trans (Nat.mod_eq_of_lt hv)
  have h0 := cell 0 full.length (by decide) (by simp +decide [expected, bankFields]) hN
  have h1 := cell 1 q (by decide) (by simp +decide [expected, bankFields]) hQ
  have h2 := cell 2 t (by decide) (by simp +decide [expected, bankFields]) hT
  have h4 := cell 4 C (by decide)
    (by simpa only [capacityExpr_eq _ _ _ hq] using (show expected (CB + 4) = capacityExpr full.length q t by
      simp +decide [expected, bankFields])) hC
  have h5 := cell 5 P (by decide) (by simp +decide [expected, bankFields]) hP
  dsimp only
  refine ⟨⟨actual.2.2.1, ?_, h1, h2, h5⟩, ⟨actual.2.2.1, h0, h1, h2, h4⟩⟩
  simpa only [Nat.add_zero] using h0

theorem embedded_init_bankData (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc.toNat = 5 * left.length) (ha : state.halted = false)
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1)
    (ht : (state.heap (BitVec.ofNat _ (20 + 4 * (full.length + q + 1)))).toNat = treeSize q full)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ sequence left.length ++ right)))
    (hend : Fits (indexWidth 32 full.length q) (5 * (left ++ sequence left.length ++ right).length)) :
    PA06A19PrepareFiniteInit032.BankData q full
      (packingRun (controllerInput q full used) (left ++ sequence left.length ++ right) (sequenceClock full.length q) state) :=
  (embedded_bankData_pair q full used hq left right state hpc ha hM ht hh hcode hend).1

theorem embedded_used_bankData (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc.toNat = 5 * left.length) (ha : state.halted = false)
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1)
    (ht : (state.heap (BitVec.ofNat _ (20 + 4 * (full.length + q + 1)))).toNat = treeSize q full)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ sequence left.length ++ right)))
    (hend : Fits (indexWidth 32 full.length q) (5 * (left ++ sequence left.length ++ right).length)) :
    PA06A19PrepareInitialUsed037.BankData q full
      (packingRun (controllerInput q full used) (left ++ sequence left.length ++ right) (sequenceClock full.length q) state) :=
  (embedded_bankData_pair q full used hq left right state hpc ha hM ht hh hcode hend).2

end PaperProofs.Structure.LaminarTree.PA06A19PrepareBankData042
