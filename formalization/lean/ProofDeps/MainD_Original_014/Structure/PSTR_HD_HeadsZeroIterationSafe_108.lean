module

public import Structure.PSTR_HD_HeadsIterationSafe_107
public import Structure.PSTR_HD_HeadsZeroIteration_094

/-! q0 COMPLETE common-scan controller iteration with SAME-witness actual
proper-clock safety. This uses the real endpoint46/low6 representation and
the SAME shared fixed code; no positive metadata or query oracle is used. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem zero_scan_iteration_safe {bits : Nat} (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (origin rank bad heapWords : Nat) (entries : List Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 configuration state.heap)
    (recorded : RecordedHeads 46 0 rank entries state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 40))) (ha : state.halted = false)
    (haddr : state.register .address = BitVec.ofNat bits 46)
    (hold : state.register .old = BitVec.ofNat bits configuration.stage)
    (hindex : state.register .index = BitVec.ofNat bits full.length) (hbad : state.register .fresh = BitVec.ofNat bits bad)
    (hs : configuration.stage < full.length) (hN : Fits bits full.length) (hrank : rank ≤ 2) (hbfit : Fits bits (bad + 1))
    (he : Fits bits (46 + 10 + entries.length + 1)) (hroom : 46 + 10 + entries.length + 1 < heapWords) :
    ∃ steps ≤ 40,
    (let after := packingRun (callInput 0 full .query) whole steps state;
      after.pc = BitVec.ofNat bits 0 ∧ after.halted = false ∧
      HeapRepresents 0 full 0 (nextConfiguration 0 full configuration .correct) after.heap ∧
      RecordedHeads 46 0 rank (if headGate 0 rank bad then entries ++ [configuration.stage] else entries) after.heap) ∧
    (∀ clock < steps, AtSafe (callInput 0 full .query) whole heapWords
      (packingRun (callInput 0 full .query) whole clock state)) := by
  let rom := callInput 0 full .query
  have hpow : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have hq2 : Fits bits (0 + 2) := by unfold Fits; omega
  obtain ⟨k, hk, decision⟩ := common_scan_decision_safe rom whole origin 46 0 rank bad configuration.stage full.length heapWords entries
    hbound hcode hwords hpcfit state hp ha haddr hold hindex hbad recorded hs hN hrank hq2 hbfit (by omega)
  dsimp only at decision
  obtain ⟨pcD, activeD, heapD, oldD, indexD, addressD, recordD, safeD⟩ := decision
  let decided := packingRun rom whole k state
  have repD : HeapRepresents 0 full 0 configuration decided.heap := by
    change HeapRepresents 0 full 0 configuration (packingRun rom whole k state).heap
    rw [heapD]
    exact rep
  have hnext : Fits bits (configuration.stage + 1) := (Nat.succ_le_of_lt hs).trans_lt hN
  have hE : Fits bits 46 := (show 46 ≤ 46 + 10 + entries.length + 1 by omega).trans_lt he
  by_cases hg : headGate 0 rank bad = true
  · have hpcD : decided.pc = BitVec.ofNat bits (5 * (origin + 67)) := by simpa [hg] using pcD
    have ha13 := append_scan_entry rom whole origin 46 0 rank configuration.stage entries hbound hcode hwords hpcfit
      decided he recordD hpcD activeD addressD oldD
    let appended := packingRun rom whole 13 decided
    have repA : HeapRepresents 0 full 0 configuration appended.heap := by
      change HeapRepresents 0 full 0 configuration (packingRun rom whole 13 decided).heap
      rw [ha13.2.2.1]
      exact zero_append_prefix_rep full configuration rank entries decided repD recordD he addressD 10 (by decide)
    have heA : Fits bits (46 + 10 + (entries ++ [configuration.stage]).length) := by
      simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_assoc] using he
    have hadv := zero_advance_query_entry full configuration origin rank (entries ++ [configuration.stage]) whole
      hbound hcode hwords hpcfit appended hb repA ha13.2.2.2.1 ha13.1 ha13.2.1 hnext heA
    have appendSafe (clock : Nat) (hc : clock < 13) : AtSafe rom whole heapWords (packingRun rom whole clock decided) := by
      exact (append_prefix_safe rom origin 46 (46 + 10 + entries.length) heapWords whole hbound hcode hwords hpcfit
        decided ((show 46 + 2 ≤ 46 + 10 + entries.length + 1 by omega).trans_lt he)
        ((show 46 + 10 + entries.length ≤ 46 + 10 + entries.length + 1 by omega).trans_lt he)
        (by omega) (by omega) (by omega) addressD recordD.cursor hpcD activeD clock hc).1
    have advanceSafe (clock : Nat) (hc : clock < 11) : AtSafe rom whole heapWords (packingRun rom whole clock appended) :=
      (zero_advance_prefix_safe full configuration origin heapWords whole hbound hcode hwords hpcfit
        appended hb repA hE (by omega) ha13.1 ha13.2.1 clock hc).1
    have safeTail := heads_safe_add rom whole heapWords 13 11 decided appendSafe advanceSafe
    have safeAll := heads_safe_add rom whole heapWords k (13 + 11) state (fun clock hc => (safeD clock hc).1) safeTail
    refine ⟨k + (13 + 11), by omega, ?_, safeAll⟩
    dsimp only
    rw [run_add, run_add]
    simpa [hg] using hadv
  · have hpcD : decided.pc = BitVec.ofNat bits (5 * (origin + 56)) := by simpa [hg] using pcD
    have hadv := zero_advance_query_entry full configuration origin rank entries whole hbound hcode hwords hpcfit decided hb
      repD recordD hpcD activeD hnext ((Nat.le_add_right _ 1).trans_lt he)
    have advanceSafe (clock : Nat) (hc : clock < 11) : AtSafe rom whole heapWords (packingRun rom whole clock decided) :=
      (zero_advance_prefix_safe full configuration origin heapWords whole hbound hcode hwords hpcfit
        decided hb repD hE (by omega) hpcD activeD clock hc).1
    have safeAll := heads_safe_add rom whole heapWords k 11 state (fun clock hc => (safeD clock hc).1) advanceSafe
    refine ⟨k + 11, by omega, ?_, safeAll⟩
    dsimp only
    rw [run_add]
    simpa [hg] using hadv

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
