module

public import PaperProofs.Structure.PSTR_HD_HeadsZeroIteration_094

/-! ORIGINAL q0 callback/rank and scanPrefix successor for the actual shared
iteration. The actual bad register is the upstream query obligation; there
is no tree/bitmap/sum/answer oracle or external correct invocation. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem zero_original_scan_iteration {bits : Nat} (full : List (Finset (Fin 0))) (hl : LaminarSchedule full)
    (used : Finset (Fin 0)) (stage : Fin full.length) (origin : Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 ⟨stage.val, used, false⟩ state.heap)
    (recorded : RecordedHeads 46 0 (encodeRank 0 (PSTRHeadScan.initialRank 0 full used)) (scanPrefix 0 full used stage.val) state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 40))) (ha : state.halted = false)
    (haddr : state.register .address = BitVec.ofNat bits 46) (hold : state.register .old = BitVec.ofNat bits stage.val)
    (hindex : state.register .index = BitVec.ofNat bits full.length)
    (hbad : state.register .fresh = BitVec.ofNat bits (encodeRank 0 (badAt 0 full used stage)))
    (he : Fits bits (46 + 10 + full.length)) :
    ∃ steps ≤ 40,
    let after := packingRun (callInput 0 full .query) whole steps state
    after.pc = BitVec.ofNat bits 0 ∧ after.halted = false ∧
    HeapRepresents 0 full 0 ⟨stage.val + 1, used, false⟩ after.heap ∧
    RecordedHeads 46 0 (encodeRank 0 (PSTRHeadScan.initialRank 0 full used)) (scanPrefix 0 full used (stage.val + 1)) after.heap := by
  let R := encodeRank 0 (PSTRHeadScan.initialRank 0 full used)
  let B := encodeRank 0 (badAt 0 full used stage)
  let entries := scanPrefix 0 full used stage.val
  have hpow : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have hN : Fits bits full.length := (show full.length ≤ 46 + 10 + full.length by omega).trans_lt he
  have hlen : entries.length ≤ stage.val := scanPrefix_length_le 0 full used stage.val
  have heEntry : Fits bits (46 + 10 + entries.length + 1) :=
    (show 46 + 10 + entries.length + 1 ≤ 46 + 10 + full.length by have h := stage.isLt; omega).trans_lt he
  have hB : Fits bits (B + 1) := by
    have h := bad_encoded_bound 0 full hl used stage
    unfold Fits
    omega
  have hR := initial_encoded_bound 0 full hl used
  have hgate : headAt 0 full used stage.val = headGate 0 R B := by rw [headAt, dite_eq_left stage.isLt]
  have hlist : (if headGate 0 R B then entries ++ [stage.val] else entries) = scanPrefix 0 full used (stage.val + 1) := by
    rw [scanPrefix_succ, hgate]
    by_cases hg : headGate 0 R B = true <;> simp [hg, entries]
  obtain ⟨steps, hsteps, result⟩ := zero_scan_iteration full ⟨stage.val, used, false⟩ origin R B entries whole hbound hcode hwords hpcfit
    state hb rep recorded hp ha haddr hold hindex hbad stage.isLt hN hR hB heEntry
  refine ⟨steps, hsteps, ?_⟩
  dsimp only at result ⊢
  simpa only [hlist, nextConfiguration] using result

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
