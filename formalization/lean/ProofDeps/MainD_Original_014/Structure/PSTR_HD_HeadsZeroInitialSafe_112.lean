module

public import Structure.PSTR_HD_HeadsZeroOriginalIterationSafe_110

/-! q0 first return from the real stage-probe label: actual9op probe/branch
then initialization21 and jump3. SAME33 clocks give original data, arbitrary
scratch initialization and every proper-clock safety, including N0. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem zero_original_initial_scan_safe {bits : Nat} (full : List (Finset (Fin 0))) (hl : LaminarSchedule full)
    (used : Finset (Fin 0)) (origin heapWords : Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 ⟨0, used, false⟩ state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 31))) (ha : state.halted = false)
    (haddr : state.register .address = BitVec.ofNat bits 46)
    (hvalue : state.register .value = BitVec.ofNat bits (encodeRank 0 (PSTRHeadScan.initialRank 0 full used)))
    (he : Fits bits (46 + 10 + full.length)) (hroom : 46 + 10 + full.length < heapWords) :
    (let after := packingRun (callInput 0 full .query) whole 33 state;
      after.pc = BitVec.ofNat bits (5 * (origin + 40)) ∧ after.halted = false ∧
      HeapRepresents 0 full 0 ⟨0, used, false⟩ after.heap ∧
      RecordedHeads 46 0 (encodeRank 0 (PSTRHeadScan.initialRank 0 full used)) (scanPrefix 0 full used 0) after.heap ∧
      after.register .old = BitVec.ofNat bits 0 ∧ after.register .index = BitVec.ofNat bits full.length ∧
      after.register .fresh = state.register .fresh ∧ after.register .address = BitVec.ofNat bits 46) ∧
    (∀ clock < 33, AtSafe (callInput 0 full .query) whole heapWords
      (packingRun (callInput 0 full .query) whole clock state)) := by
  let rom := callInput 0 full .query
  let R := encodeRank 0 (PSTRHeadScan.initialRank 0 full used)
  have hpow : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have hq2 : Fits bits (0 + 2) := by unfold Fits; omega
  have hR : Fits bits R := (initial_encoded_bound 0 full hl used).trans_lt hq2
  have hN : Fits bits full.length := (show full.length ≤ 46 + 10 + full.length by omega).trans_lt he
  have he3 : Fits bits (46 + 3) := (show 46 + 3 ≤ 46 + 10 + full.length by omega).trans_lt he
  have he8 : Fits bits (46 + 8) := (show 46 + 8 ≤ 46 + 10 + full.length by omega).trans_lt he
  have returned := zero_return_prefix full ⟨0, used, false⟩ origin whole hbound hcode hwords hpcfit state hb rep hp ha
    (by change 0 ≤ full.length; exact Nat.zero_le _) hN
  let entered := packingRun rom whole 9 state
  have entered_rep : HeapRepresents 0 full 0 ⟨0, used, false⟩ entered.heap := by
    change HeapRepresents 0 full 0 ⟨0, used, false⟩ (packingRun rom whole 9 state).heap
    rw [returned.2.2.1]
    exact rep
  have entered_pc : entered.pc = BitVec.ofNat bits (5 * (origin + 80)) := by simpa only [↓reduceIte] using returned.1
  have entered_value : entered.register .value = BitVec.ofNat bits R := returned.2.2.2.1.trans hvalue
  have entered_addr : entered.register .address = BitVec.ofNat bits 46 := returned.2.2.2.2.2.2.2.trans haddr
  have initialized := initial_scan_entry full origin 46 R whole hbound hcode hwords hpcfit entered hb he8 hR hq2
    entered_pc returned.2.1 entered_addr entered_value
  have initialized_rep : HeapRepresents 0 full 0 ⟨0, used, false⟩ (packingRun rom whole 24 entered).heap := by
    rw [initialized.2.2.1]
    have hpure := zero_init_prefix_rep full ⟨0, used, false⟩ entered hb entered_rep he8 entered_addr 21 (by decide)
    change HeapRepresents 0 full 0 ⟨0, used, false⟩ (executeOps rom headsInit entered).heap at hpure
    rw [(execute_headsInit rom 46 0 R entered hb he3 hR hq2 entered_addr entered_value rfl).1] at hpure
    exact hpure
  constructor
  · dsimp only
    rw [show 33 = 9 + 24 from rfl, run_add]
    refine ⟨initialized.1, initialized.2.1, initialized_rep, ?_,
      initialized.2.2.2.2.2.1.trans returned.2.2.2.2.1,
      initialized.2.2.2.2.2.2.2.1.trans returned.2.2.2.2.2.2.1,
      initialized.2.2.2.2.2.2.1.trans returned.2.2.2.2.2.1, initialized.2.2.2.2.2.2.2.2⟩
    simpa only [scanPrefix_zero] using initialized.2.2.2.1
  · have returnSafe (clock : Nat) (hc : clock < 9) : AtSafe rom whole heapWords (packingRun rom whole clock state) :=
      (zero_return_prefix_safe full ⟨0, used, false⟩ origin heapWords whole hbound hcode hwords hpcfit state hb rep hp ha (by omega) clock hc).1
    have initSafe (clock : Nat) (hc : clock < 24) : AtSafe rom whole heapWords (packingRun rom whole clock entered) :=
      (initial_prefix_safe full origin 46 heapWords whole hbound hcode hwords hpcfit entered hb he8
        (by omega) entered_addr entered_pc returned.2.1 clock hc).1
    exact heads_safe_add rom whole heapWords 9 24 state returnSafe initSafe

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
