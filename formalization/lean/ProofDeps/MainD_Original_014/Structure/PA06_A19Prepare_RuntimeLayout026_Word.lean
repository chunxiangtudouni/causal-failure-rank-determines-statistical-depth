module

public import Structure.PA06_A19Prepare_RuntimeLayout026_Numeric
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Candidate: actual Word execution of the fixed 65-op layout. Incoming
register bounds come from the Word state itself. Only upstream internal
raw-cache and temporary-header data are required; no safety oracle occurs. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeLayout026

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PA17UniformGenerator035j PA17UniformGenerator035m
  PA17UniformGenerator035p

theorem layout_code_le : ∀ value ∈ packingCode layout, value ≤ 8192 := by decide

theorem layout_code_fit (N q : Nat) (hq : 0 < q) : WordsFit (indexWidth 32 N q) (packingCode layout) := by
  intro value hv
  exact ((layout_code_le value hv).trans (maxWord_8192 N q hq)).trans_lt
    (PA17GeneratorStatic048.maxWord_fits _)

theorem layout_pc_fit (N q : Nat) (hq : 0 < q) : Fits (indexWidth 32 N q) (5 * layout.length) := by
  rw [layout_length]
  exact ((by decide : 5 * 65 ≤ 8192).trans (maxWord_8192 N q hq)).trans_lt
    (PA17GeneratorStatic048.maxWord_fits _)

theorem layout_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    natRun rom (left ++ layout ++ right) 65 state = runOps rom layout state := by
  exact natRun_of_straight_segment rom (left ++ layout ++ right) layout left.length
    (by simp only [List.length_append]; omega) (PA17UniformGenerator035a.segment_index left layout right)
    layout_noJump state hpc ha

/-- Relocatable internal interface. The whole fixed producer supplies its
own encoded-code/PC fit; numeric/access safety is proved by layout_safe. -/
theorem layout_word (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hr : RegistersLE (2 ^ indexWidth 32 full.length q - 1) state)
    (hM : state.heap 16 = full.length + q + 1)
    (ht : state.heap (20 + 4 * (full.length + q + 1)) = treeSize q full)
    (hw : state.heap 0 = CapacityBits.width q) (hb : state.heap 3 = indexWidth 32 full.length q)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ layout ++ right)))
    (hpcFit : Fits (indexWidth 32 full.length q) (5 * (left ++ layout ++ right).length)) :
    packingRun (controllerInput q full used) (left ++ layout ++ right) 65
      (state.toWord (indexWidth 32 full.length q)) =
        (runOps (controllerInput q full used) layout state).toWord (indexWidth 32 full.length q) := by
  have hs := layout_safe q full used hq left right state hpc ha hr hM ht hw hb
  rw [actual_word_run _ _ _ _ _ 65 state hs (PA17GeneratorStatic048.maxWord_fits _) hcode hpcFit 65 le_rfl,
    layout_run _ left right state hpc ha]

theorem actual_control_fits (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    Fits (indexWidth 32 full.length q)
      (controlExpr (packedExpr (capacityExpr full.length q (treeSize q full))
        (CapacityBits.width q) (indexWidth 32 full.length q))
        (dimensionsExpr full.length q (treeSize q full))) := by
  rw [packedExpr_eq full.length q (treeSize q full) hq, controlExpr_eq]
  simpa only [Nat.add_zero] using actual_bank_field_fits q full hq 0 (by decide)

/-- The actual temporary header supplies exactly the values loaded at
physical cells 0 and 3. Its other fields are not read by layout. -/
theorem header_layout_values (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (state : WordState (indexWidth 32 full.length q))
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) :
    (PA06A19PrepareRuntimeHeader019.natView state).heap 0 = CapacityBits.width q ∧
    (PA06A19PrepareRuntimeHeader019.natView state).heap 3 = indexWidth 32 full.length q := by
  have hbits := PA17GeneratorStatic048.bits_le_maxWord full.length q 0 hq (by omega)
  have hwidth := (PA17PackingBounds043.width_le_bits full.length q).trans hbits
  have hB := PA17GeneratorStatic048.maxWord_fits (indexWidth 32 full.length q)
  constructor
  · change (state.heap (BitVec.ofNat _ 0)).toNat = _
    rw [hh.width, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hwidth.trans_lt hB)]
  · change (state.heap (BitVec.ofNat _ 3)).toNat = _
    rw [hh.wordBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hbits.trans_lt hB)]

/-- Closed fixed-code body simulation for an arbitrary actual Word state.
The only data premises are the upstream raw cache and actual tempHeader. -/
theorem actual_layout_word (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc = BitVec.ofNat _ 0) (ha : state.halted = false)
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1)
    (ht : (state.heap (BitVec.ofNat _ (20 + 4 * (full.length + q + 1)))).toNat = treeSize q full)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) :
    packingRun (controllerInput q full used) layout 65 state =
      (runOps (controllerInput q full used) layout (PA06A19PrepareRuntimeHeader019.natView state)).toWord
        (indexWidth 32 full.length q) := by
  let start := PA06A19PrepareRuntimeHeader019.natView state
  have hstartPC : start.pc = 5 * ([] : List PackingOp).length := by
    change state.pc.toNat = 0
    rw [hpc]
    rfl
  have hvals := header_layout_values q full hq state hh
  have hw := layout_word q full used hq [] [] start hstartPC ha
    (PA06A19PrepareRuntimeHeader019.natView_registers state) hM ht hvals.1 hvals.2
    (by simpa only [List.nil_append, List.append_nil] using layout_code_fit full.length q hq)
    (by simpa only [List.nil_append, List.append_nil] using layout_pc_fit full.length q hq)
  simpa only [List.nil_append, List.append_nil, start, PA06A19PrepareRuntimeHeader019.natView_toWord] using hw

theorem actual_layout_data (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc = BitVec.ofNat _ 0) (ha : state.halted = false)
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1)
    (ht : (state.heap (BitVec.ofNat _ (20 + 4 * (full.length + q + 1)))).toNat = treeSize q full)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) :
    let fresh := packingRun (controllerInput q full used) layout 65 state
    fresh.halted = false ∧ fresh.pc.toNat = 325 ∧
    (fresh.register .address).toNat =
      controlExpr (packedExpr (capacityExpr full.length q (treeSize q full))
        (CapacityBits.width q) (indexWidth 32 full.length q))
        (dimensionsExpr full.length q (treeSize q full)) ∧
    ∀ address, fresh.heap address = BitVec.ofNat _
      (lowFields full.length q (treeSize q full) (CapacityBits.width q) (indexWidth 32 full.length q)
        (PA06A19PrepareRuntimeHeader019.natView state).heap address.toNat) := by
  let bits := indexWidth 32 full.length q
  let start := PA06A19PrepareRuntimeHeader019.natView state
  let rom := controllerInput q full used
  have hv := header_layout_values q full hq state hh
  have hdata := layout_data q full used start (full.length + q + 1) (treeSize q full)
    (CapacityBits.width q) bits hM ht hv.1 hv.2
  have he := actual_layout_word q full used hq state hpc ha hM ht hh
  dsimp only
  simp only [he]
  refine ⟨(runOps_halted rom layout start).trans ha, ?_, ?_, ?_⟩
  · change (BitVec.ofNat bits (runOps rom layout start).pc).toNat = 325
    rw [runOps_pc rom layout start layout_noJump, layout_length]
    have hs : start.pc = 0 := by change state.pc.toNat = 0; rw [hpc]; rfl
    rw [hs, Nat.zero_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simpa only [layout_length, AlgorithmClaims.Fits, bits] using layout_pc_fit full.length q hq)]
  · change (BitVec.ofNat bits ((runOps rom layout start).register .address)).toNat = _
    rw [hdata.2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (actual_control_fits q full hq)]
  · intro address
    change BitVec.ofNat bits ((runOps rom layout start).heap address.toNat) = _
    rw [hdata.1]

theorem actual_layout_frame (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc = BitVec.ofNat _ 0) (ha : state.halted = false)
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1)
    (ht : (state.heap (BitVec.ofNat _ (20 + 4 * (full.length + q + 1)))).toNat = treeSize q full)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap)
    (address : BitVec (indexWidth 32 full.length q)) (haddr : address.toNat < 9 ∨ 16 ≤ address.toNat) :
    (packingRun (controllerInput q full used) layout 65 state).heap address = state.heap address := by
  have hv := header_layout_values q full hq state hh
  rw [actual_layout_word q full used hq state hpc ha hM ht hh]
  change BitVec.ofNat _ ((runOps (controllerInput q full used) layout
    (PA06A19PrepareRuntimeHeader019.natView state)).heap address.toNat) = _
  rw [layout_frame q full used (PA06A19PrepareRuntimeHeader019.natView state)
    (full.length + q + 1) (treeSize q full) (CapacityBits.width q) (indexWidth 32 full.length q)
    hM ht hv.1 hv.2 address.toNat haddr]
  simp only [PA06A19PrepareRuntimeHeader019.natView, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem actual_layout_prefix_access (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc = BitVec.ofNat _ 0) (ha : state.halted = false)
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1)
    (ht : (state.heap (BitVec.ofNat _ (20 + 4 * (full.length + q + 1)))).toNat = treeSize q full)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (count : Nat) (hc : count < 65) :
    let fresh := packingRun (controllerInput q full used) layout count state
    fresh.halted = false ∧ fresh.pc.toNat + 4 < (packingCode layout).length ∧
      let fetched := physicalFetch (indexWidth 32 full.length q) (packingCode layout) fresh.pc.toNat
      ∃ op, PackingOp.decode fetched = some op ∧
        packingAccessFits (controllerInput q full used)
          (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full)) fresh op := by
  let start := PA06A19PrepareRuntimeHeader019.natView state
  have hv := header_layout_values q full hq state hh
  have hs := layout_safe q full used hq [] [] start
    (by change state.pc.toNat = 0; rw [hpc]; rfl) ha
    (PA06A19PrepareRuntimeHeader019.natView_registers state) hM ht hv.1 hv.2
  have hs' : RunSafe (2 ^ indexWidth 32 full.length q - 1)
      (PA06A19PrepareRuntimeHeader019.heapWords full.length q (treeSize q full))
      (controllerInput q full used) layout 65 start := by
    simpa only [List.nil_append, List.append_nil] using hs
  have hout := actual_word_fetch_access _ _ _ _ _ 65 start hs'
    (PA17GeneratorStatic048.maxWord_fits _) (layout_code_fit full.length q hq)
    (layout_pc_fit full.length q hq) count hc
  simpa only [start, PA06A19PrepareRuntimeHeader019.natView_toWord] using hout

end PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeLayout026
