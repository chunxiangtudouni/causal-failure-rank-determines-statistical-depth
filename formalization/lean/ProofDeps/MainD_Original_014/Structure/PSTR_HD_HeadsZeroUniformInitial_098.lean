module

public import Structure.PSTR_HD_HeadsZeroUniformReturn_097

/-! Actual first-return q0 initialization in the UNIFORM heads program.
All incoming scratch is arbitrary. Original stage0/used/failed and real
endpoint46 output are materialized by the same actual code, N0 included. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem zero_uniform_initial_scan {bits : Nat} (full : List (Finset (Fin 0))) (hl : LaminarSchedule full)
    (used : Finset (Fin 0)) (queryBody : List PackingOp)
    (hwords : WordsFit bits (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length))
    (state : WordState bits) (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 ⟨0, used, false⟩ state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * queryBody.length)) (ha : state.halted = false)
    (hvalue : state.register .value = BitVec.ofNat bits (encodeRank 0 (PSTRHeadScan.initialRank 0 full used)))
    (he : Fits bits (46 + 10 + full.length)) :
    ∃ steps ≤ 41,
    let after := packingRun (callInput 0 full .query) (uniformHeadsProgram queryBody) steps state
    after.pc = BitVec.ofNat bits (5 * (queryBody.length + 48)) ∧ after.halted = false ∧
    HeapRepresents 0 full 0 ⟨0, used, false⟩ after.heap ∧
    RecordedHeads 46 0 (encodeRank 0 (PSTRHeadScan.initialRank 0 full used)) (scanPrefix 0 full used 0) after.heap ∧
    after.register .old = BitVec.ofNat bits 0 ∧ after.register .index = BitVec.ofNat bits full.length ∧
    after.register .fresh = state.register .fresh ∧ after.register .address = BitVec.ofNat bits 46 := by
  let rom := callInput 0 full .query
  let whole := uniformHeadsProgram queryBody
  let R := encodeRank 0 (PSTRHeadScan.initialRank 0 full used)
  have hpow : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have hq2 : Fits bits (0 + 2) := by unfold Fits; omega
  have hR : Fits bits R := (initial_encoded_bound 0 full hl used).trans_lt hq2
  have hN : Fits bits full.length := (show full.length ≤ 46 + 10 + full.length by omega).trans_lt he
  have he3 : Fits bits (46 + 3) := (show 46 + 3 ≤ 46 + 10 + full.length by omega).trans_lt he
  have he8 : Fits bits (46 + 8) := (show 46 + 8 ≤ 46 + 10 + full.length by omega).trans_lt he
  obtain ⟨r, hreturn, returned⟩ := zero_uniform_return full ⟨0, used, false⟩ queryBody hwords hpcfit state hp ha hb rep
    (by change 0 ≤ full.length; exact Nat.zero_le _) hN
  dsimp only at returned
  let entered := packingRun rom whole r state
  have entered_rep : HeapRepresents 0 full 0 ⟨0, used, false⟩ entered.heap := by
    change HeapRepresents 0 full 0 ⟨0, used, false⟩ (packingRun rom whole r state).heap
    rw [returned.2.2.1]
    exact rep
  have entered_pc : entered.pc = BitVec.ofNat bits (5 * (queryBody.length + 88)) := by simpa only [↓reduceIte] using returned.1
  have entered_value : entered.register .value = BitVec.ofNat bits R := returned.2.2.2.1.trans hvalue
  have initialized := initial_scan_entry full (queryBody.length + 8) 46 R whole (uniform_tail_bound queryBody) (uniform_tail_code queryBody)
    hwords hpcfit entered hb he8 hR hq2 entered_pc returned.2.1 returned.2.2.2.2.2.2.2 entered_value
  have initialized_rep : HeapRepresents 0 full 0 ⟨0, used, false⟩ (packingRun rom whole 24 entered).heap := by
    rw [initialized.2.2.1]
    have hpure := zero_init_prefix_rep full ⟨0, used, false⟩ entered hb entered_rep he8 returned.2.2.2.2.2.2.2 21 (by decide)
    change HeapRepresents 0 full 0 ⟨0, used, false⟩ (executeOps rom headsInit entered).heap at hpure
    rw [(execute_headsInit rom 46 0 R entered hb he3 hR hq2 returned.2.2.2.2.2.2.2 entered_value rfl).1] at hpure
    exact hpure
  refine ⟨r + 24, by omega, ?_⟩
  dsimp only
  rw [run_add]
  refine ⟨initialized.1, initialized.2.1, initialized_rep, ?_,
    initialized.2.2.2.2.2.1.trans returned.2.2.2.2.1,
    initialized.2.2.2.2.2.2.2.1.trans returned.2.2.2.2.2.2.1,
    initialized.2.2.2.2.2.2.1.trans returned.2.2.2.2.2.1, initialized.2.2.2.2.2.2.2.2⟩
  simpa only [scanPrefix_zero] using initialized.2.2.2.1

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
