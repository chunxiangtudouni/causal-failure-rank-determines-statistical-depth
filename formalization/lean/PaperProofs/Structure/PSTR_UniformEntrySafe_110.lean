module

public import PaperProofs.Structure.PSTR_UniformWidthEntry_106
public import PaperProofs.Structure.PSTR_WidthAccess_097
public import PaperProofs.Structure.PSTR_WidthPrefix_035
public import PaperProofs.Structure.PSTR_LiveHeaderSafety_004

/-! Every real raw-header/width/guard clock of NEW bootstrap63, on both q
branches and arbitrary registers. Entire heap identity, real fetch/access;
no initialized scratch, failure flag, tree or register oracle is assumed. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRUniformEntrySafe

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRUniformBootstrapCode PSTRCountKernel PSTRWordSegments PSTROuterStoreAccess

theorem heading {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (state : WordState (indexWidth 32 full.length q))
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) 0) (ha : state.halted = false) :
    let headed := executeOps (callInput q full command) PSTRLiveHeader.program state
    (headed.register .fresh).toNat = q ∧ headed.pc = BitVec.ofNat (indexWidth 32 full.length q) 40 ∧
      headed.halted = false ∧ headed.heap = state.heap := by
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have raw := PSTROriginalCountRoom.raw_rooms full.length q
  have qfit := (PSTROriginalCountRoom.dimension_rooms full).2.2.2.2
  have regs := PSTRLiveHeader.execute_registers full command state (by omega) raw.1 qfit raw.2.1
  refine ⟨?_, ?_, ?_, PSTRLiveHeader.execute_heap _ _⟩
  · rw [regs.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt qfit]
  · rw [executeOps_pc _ _ state PSTRLiveHeader.program_straight, hp,
      PSTRLiveHeader.program_length, BitVec.zero_add]
  · rw [executeOps_halted, ha]

theorem width_prefix_heap {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (whole : List PackingOp) (zeroTarget : Nat) (cb : Contains whole zeroTarget)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (state : WordState (indexWidth 32 full.length q))
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) 0) (ha : state.halted = false)
    (clock : Nat) (hclock : clock ≤ 8 * CapacityBits.width q + 16) :
    (packingRun (callInput q full command) whole clock state).heap = state.heap := by
  let rom := callInput q full command
  have headed := heading full command state hp ha
  by_cases hearly : clock ≤ 8
  · have slice := header_contains whole zeroTarget cb
    rw [fetched_prefix rom whole PSTRLiveHeader.program 0 slice.bound slice.code
      PSTRLiveHeader.program_straight hwords hpcfit state hp ha clock hearly]
    exact PSTRLiveHeader.execute_prefix_heap rom state clock
  · rw [show clock = 8 + (clock - 8) by omega, run_add,
      header_run rom whole zeroTarget cb hwords hpcfit state hp ha]
    exact (PSTRWidthPrefix.width_mask_prefix_heap rom whole 8 (width_contains whole zeroTarget cb)
      hwords hpcfit (by have h := cb.bound; rw [program_length] at h; omega)
      (mask_code whole zeroTarget cb) q _ headed.1 headed.2.1 headed.2.2.1
      (PSTROriginalCountRoom.raw_rooms full.length q).2.2 (clock - 8) (by omega)).trans headed.2.2.2

theorem entry_prefix_heap {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (whole : List PackingOp) (zeroTarget : Nat) (cb : Contains whole zeroTarget)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (state : WordState (indexWidth 32 full.length q))
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) 0) (ha : state.halted = false)
    (clock : Nat) (hclock : clock ≤ 8 * CapacityBits.width q + 18) :
    (packingRun (callInput q full command) whole clock state).heap = state.heap := by
  let rom := callInput q full command
  let wide := packingRun rom whole (8 * CapacityBits.width q + 16) state
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have raw := PSTROriginalCountRoom.raw_rooms full.length q
  have width := PSTRUniformWidthEntry.width_run full command whole zeroTarget cb hwords hpcfit
    state hp ha (by omega) raw.1 raw.2.1 raw.2.2
  by_cases hearly : clock ≤ 8 * CapacityBits.width q + 16
  · exact width_prefix_heap full command whole zeroTarget cb hwords hpcfit state hp ha clock hearly
  · rw [show clock = (8 * CapacityBits.width q + 16) + (clock - (8 * CapacityBits.width q + 16)) by omega, run_add]
    exact (PSTRZeroWidthGuard.prefix_heap rom whole 21 zeroTarget (guard_contains whole zeroTarget cb)
      hwords hpcfit wide width.2.1 width.1 _ (by omega)).trans width.2.2.2.2

theorem entry_safe {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (whole : List PackingOp) (zeroTarget heapWords : Nat) (cb : Contains whole zeroTarget)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (state : WordState (indexWidth 32 full.length q))
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) 0) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < 8 * CapacityBits.width q + 18) :
    AtSafe (callInput q full command) whole heapWords (packingRun (callInput q full command) whole clock state) := by
  let rom := callInput q full command
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have raw := PSTROriginalCountRoom.raw_rooms full.length q
  have qfit := (PSTROriginalCountRoom.dimension_rooms full).2.2.2.2
  by_cases hwide : clock < 8 * CapacityBits.width q + 16
  · by_cases hearly : clock < 8
    · have slice := header_contains whole zeroTarget cb
      exact (straight_prefix_safe rom whole PSTRLiveHeader.program heapWords 0 (fun _ => False)
        slice.bound slice.code PSTRLiveHeader.program_straight hwords hpcfit state hp ha
        (access_only _ _ _ state (PSTRLiveHeaderSafety.access_prefix full command heapWords state
          (by omega) raw.1 qfit raw.2.1)) clock hearly).1
    · have headed := heading full command state hp ha
      rw [show clock = 8 + (clock - 8) by omega, run_add,
        header_run rom whole zeroTarget cb hwords hpcfit state hp ha]
      exact PSTRWidthAccess.width_mask_safe rom whole 8 heapWords (width_contains whole zeroTarget cb)
        hwords hpcfit (by have h := cb.bound; rw [program_length] at h; omega)
        (mask_code whole zeroTarget cb) q _ headed.1 headed.2.1 headed.2.2.1 raw.2.2 _ (by omega)
  · let wide := packingRun rom whole (8 * CapacityBits.width q + 16) state
    have width := PSTRUniformWidthEntry.width_run full command whole zeroTarget cb hwords hpcfit
      state hp ha (by omega) raw.1 raw.2.1 raw.2.2
    rw [show clock = (8 * CapacityBits.width q + 16) + (clock - (8 * CapacityBits.width q + 16)) by omega, run_add]
    exact PSTRZeroWidthGuard.actual_safe rom whole 21 zeroTarget heapWords (guard_contains whole zeroTarget cb)
      hwords hpcfit wide width.2.1 width.1 _ (by omega)

end PaperProofs.Structure.LaminarTree.PSTRUniformEntrySafe
