module

public import Structure.PA06_A19Prepare_RuntimeLayout026_Sequence
public import Structure.PA06_A19Prepare_FiniteInit032_Word

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeSequence041

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PA17UniformGenerator035j PA17UniformGenerator035m
  PA17UniformGenerator035p PA06A19PrepareRuntimeLayout026

/-! These are interfaces for the actual sequence inside one containing program.
The incoming PC is the genuine preceding endpoint; the state is never reset. -/

theorem embedded_sequence_word (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc.toNat = 5 * left.length) (ha : state.halted = false)
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1)
    (ht : (state.heap (BitVec.ofNat _ (20 + 4 * (full.length + q + 1)))).toNat = treeSize q full)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ sequence left.length ++ right)))
    (hend : Fits (indexWidth 32 full.length q) (5 * (left ++ sequence left.length ++ right).length))
    (count : Nat) (hc : count ≤ sequenceClock full.length q) :
    packingRun (controllerInput q full used) (left ++ sequence left.length ++ right) count state =
      (natRun (controllerInput q full used) (left ++ sequence left.length ++ right) count
        (PA06A19PrepareRuntimeHeader019.natView state)).toWord (indexWidth 32 full.length q) := by
  let start := PA06A19PrepareRuntimeHeader019.natView state
  have hv := header_layout_values q full hq state hh
  have hwords (position : Nat) (_hp : position < PA06A19PrepareControlBank017.cacheLength full.length q) :
      start.heap position ≤ 2 ^ indexWidth 32 full.length q - 1 := by
    have hs := (state.heap (BitVec.ofNat _ position)).toNat_lt_twoPow_of_le
      (Nat.le_refl (indexWidth 32 full.length q))
    change (state.heap (BitVec.ofNat _ position)).toNat ≤ _
    omega
  have hendLE : 5 * (left ++ sequence left.length ++ right).length ≤ 2 ^ indexWidth 32 full.length q - 1 := by
    unfold AlgorithmClaims.Fits at hend
    omega
  have hs := sequence_safe q full used hq left right start hpc ha
    (PA06A19PrepareRuntimeHeader019.natView_registers state) hM ht hv.1 hv.2 hwords hendLE
  have hw := actual_word_run _ _ _ _ _ (sequenceClock full.length q) start hs
    (PA17GeneratorStatic048.maxWord_fits _) hcode hend count hc
  simpa only [start, PA06A19PrepareRuntimeHeader019.natView_toWord] using hw

theorem embedded_sequence_prefix_access (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc.toNat = 5 * left.length) (ha : state.halted = false)
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1)
    (ht : (state.heap (BitVec.ofNat _ (20 + 4 * (full.length + q + 1)))).toNat = treeSize q full)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ sequence left.length ++ right)))
    (hend : Fits (indexWidth 32 full.length q) (5 * (left ++ sequence left.length ++ right).length))
    (count : Nat) (hc : count < sequenceClock full.length q) :
    let code := left ++ sequence left.length ++ right
    let actual := packingRun (controllerInput q full used) code count state
    actual.halted = false ∧ actual.pc.toNat + 4 < (packingCode code).length ∧
    let fetched := physicalFetch (indexWidth 32 full.length q) (packingCode code) actual.pc.toNat
    ∃ op, PackingOp.decode fetched = some op ∧
      packingAccessFits (controllerInput q full used)
        (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full)) actual op := by
  let start := PA06A19PrepareRuntimeHeader019.natView state
  have hv := header_layout_values q full hq state hh
  have hwords (position : Nat) (_hp : position < PA06A19PrepareControlBank017.cacheLength full.length q) :
      start.heap position ≤ 2 ^ indexWidth 32 full.length q - 1 := by
    have hs := (state.heap (BitVec.ofNat _ position)).toNat_lt_twoPow_of_le
      (Nat.le_refl (indexWidth 32 full.length q))
    change (state.heap (BitVec.ofNat _ position)).toNat ≤ _
    omega
  have hendLE : 5 * (left ++ sequence left.length ++ right).length ≤ 2 ^ indexWidth 32 full.length q - 1 := by
    unfold AlgorithmClaims.Fits at hend
    omega
  have hs := sequence_safe q full used hq left right start hpc ha
    (PA06A19PrepareRuntimeHeader019.natView_registers state) hM ht hv.1 hv.2 hwords hendLE
  have hw := actual_word_fetch_access _ _ _ _ _ (sequenceClock full.length q) start hs
    (PA17GeneratorStatic048.maxWord_fits _) hcode hend count hc
  simpa only [start, PA06A19PrepareRuntimeHeader019.natView_toWord] using hw

theorem embedded_sequence_data (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc.toNat = 5 * left.length) (ha : state.halted = false)
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1)
    (ht : (state.heap (BitVec.ofNat _ (20 + 4 * (full.length + q + 1)))).toNat = treeSize q full)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ sequence left.length ++ right)))
    (hend : Fits (indexWidth 32 full.length q) (5 * (left ++ sequence left.length ++ right).length)) :
    let t := treeSize q full
    let bits := indexWidth 32 full.length q
    let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
    let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
    let originalLayout := lowFields full.length q t (CapacityBits.width q) bits
      (PA06A19PrepareRuntimeHeader019.natView state).heap
    let moved := PA06A19PrepareControlBank017.relocatedHeap originalLayout 0
      (PA06A19PrepareControlBank017.cacheBase full.length q t P) (PA06A19PrepareControlBank017.cacheLength full.length q)
    let fresh := packingRun (controllerInput q full used) (left ++ sequence left.length ++ right)
      (sequenceClock full.length q) state
    fresh.halted = false ∧ fresh.pc.toNat = 5 * (left.length + 134) ∧ (fresh.register .address).toNat = CB ∧
      ∀ address, fresh.heap address = BitVec.ofNat bits (bankFields full.length q t P CB moved address.toNat) := by
  let start := PA06A19PrepareRuntimeHeader019.natView state
  let t := treeSize q full
  let bits := indexWidth 32 full.length q
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
  let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
  let expectedHeap := bankFields full.length q t P CB
    (PA06A19PrepareControlBank017.relocatedHeap
      (lowFields full.length q t (CapacityBits.width q) bits start.heap) 0
      (PA06A19PrepareControlBank017.cacheBase full.length q t P) (PA06A19PrepareControlBank017.cacheLength full.length q))
  have hv := header_layout_values q full hq state hh
  have hn := sequence_run q full used hq left right start hpc ha hM ht hv.1 hv.2
  have hn' :
      (natRun (controllerInput q full used) (left ++ sequence left.length ++ right) (sequenceClock full.length q) start).halted = false ∧
      (natRun (controllerInput q full used) (left ++ sequence left.length ++ right) (sequenceClock full.length q) start).pc = 5 * (left.length + 134) ∧
      (natRun (controllerInput q full used) (left ++ sequence left.length ++ right) (sequenceClock full.length q) start).register .address = CB ∧
      (natRun (controllerInput q full used) (left ++ sequence left.length ++ right) (sequenceClock full.length q) start).heap = expectedHeap := hn
  have hCBfit : Fits bits CB := by
    dsimp only [CB, P, t, bits]
    simpa only [Nat.add_zero] using actual_bank_field_fits q full hq 0 (by decide)
  have hpFit : Fits bits (5 * (left.length + 134)) := by
    apply Nat.lt_of_le_of_lt _ hend
    simp only [List.length_append, sequence_length]
    omega
  dsimp only
  simp only [embedded_sequence_word q full used hq left right state hpc ha hM ht hh hcode hend
    (sequenceClock full.length q) le_rfl]
  refine ⟨hn'.1, ?_, ?_, ?_⟩
  · change (BitVec.ofNat bits (natRun _ _ _ start).pc).toNat = _
    rw [hn'.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpFit]
  · change (BitVec.ofNat bits ((natRun _ _ _ start).register .address)).toNat = _
    rw [hn'.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hCBfit]
  · intro address
    change BitVec.ofNat bits ((natRun _ _ _ start).heap address.toNat) = _
    rw [hn'.2.2.2]

theorem embedded_sequence_frame (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc.toNat = 5 * left.length) (ha : state.halted = false)
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1)
    (ht : (state.heap (BitVec.ofNat _ (20 + 4 * (full.length + q + 1)))).toNat = treeSize q full)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ sequence left.length ++ right)))
    (hend : Fits (indexWidth 32 full.length q) (5 * (left ++ sequence left.length ++ right).length))
    (address : BitVec (indexWidth 32 full.length q)) (hlow : address.toNat < 9 ∨ 16 ≤ address.toNat)
    (haddr : address.toNat < PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full)
      (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q))) :
    (packingRun (controllerInput q full used) (left ++ sequence left.length ++ right) (sequenceClock full.length q) state).heap address = state.heap address := by
  have hne (offset : Nat) : address.toNat ≠
      PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full)
        (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)) + offset := by
    omega
  have hd := (embedded_sequence_data q full used hq left right state hpc ha hM ht hh hcode hend).2.2.2 address
  rw [hd]
  unfold bankFields
  rw [Function.update_of_ne (hne 6), Function.update_of_ne (hne 5),
    Function.update_of_ne (hne 4), Function.update_of_ne (hne 3),
    Function.update_of_ne (hne 2), Function.update_of_ne (hne 1), Function.update_of_ne (hne 0)]
  rw [PA06A19PrepareControlBank017.relocatedHeap_frame _ _ _ _ address.toNat (Or.inl (by
    unfold PA06A19PrepareControlBank017.cacheBase
    omega))]
  unfold lowFields
  simp only [Function.update_of_ne (show address.toNat ≠ 9 by omega),
    Function.update_of_ne (show address.toNat ≠ 10 by omega),
    Function.update_of_ne (show address.toNat ≠ 11 by omega),
    Function.update_of_ne (show address.toNat ≠ 12 by omega),
    Function.update_of_ne (show address.toNat ≠ 13 by omega),
    Function.update_of_ne (show address.toNat ≠ 14 by omega),
    Function.update_of_ne (show address.toNat ≠ 15 by omega)]
  simp only [PA06A19PrepareRuntimeHeader019.natView, BitVec.ofNat_toNat, BitVec.setWidth_eq]


theorem embedded_sequence_header (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc.toNat = 5 * left.length) (ha : state.halted = false)
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1)
    (ht : (state.heap (BitVec.ofNat _ (20 + 4 * (full.length + q + 1)))).toNat = treeSize q full)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ sequence left.length ++ right)))
    (hend : Fits (indexWidth 32 full.length q) (5 * (left ++ sequence left.length ++ right).length)) :
    PA06A19PrepareRuntimePacked016.Header q
      (packingRun (controllerInput q full used) (left ++ sequence left.length ++ right)
        (sequenceClock full.length q) state).heap := by
  let bits := indexWidth 32 full.length q
  let CB := PA06A19PrepareControlBank017.controlBase full.length q (treeSize q full)
    (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) bits)
  have hfour : 4 ≤ CB := by
    dsimp only [CB, PA06A19PrepareControlBank017.controlBase]
    omega
  have hsmall : Fits bits 3 :=
    (by decide : 3 ≤ 8).trans_lt (PA17WordBounds023.small_word_fit full.length q)
  have cell (n : Nat) (hn : n < 4) :
      (packingRun (controllerInput q full used) (left ++ sequence left.length ++ right)
        (sequenceClock full.length q) state).heap (BitVec.ofNat bits n) = state.heap (BitVec.ofNat bits n) := by
    have point : (BitVec.ofNat bits n).toNat = n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((by omega : n ≤ 3).trans_lt hsmall)]
    exact embedded_sequence_frame q full used hq left right state hpc ha hM ht hh hcode hend _
      (Or.inl (by rw [point]; omega)) (by change (BitVec.ofNat bits n).toNat < CB; rw [point]; omega)
  constructor
  · rw [cell 0 (by decide)]
    exact hh.width
  · rw [cell 1 (by decide)]
    exact hh.mask
  · rw [cell 2 (by decide)]
    exact hh.ones
  · rw [cell 3 (by decide)]
    exact hh.wordBits

theorem embedded_sequence_trace_bound (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (left right : List PackingOp) (state : WordState (indexWidth 32 full.length q)) :
    (packingDynamicTrace (controllerInput q full used) (left ++ sequence left.length ++ right)
      (sequenceClock full.length q) state).length ≤
      108 * PA06A19PrepareControlBank017.cacheLength full.length q + 1524 := by
  exact (packingDynamicTrace_length_le _ _ _ state).trans_eq (by rw [sequenceClock_eq]; omega)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeSequence041
