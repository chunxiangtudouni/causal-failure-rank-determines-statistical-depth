module

public import Structure.PSTR_HD_HeadsZeroAdvanceSafe_106
public import Structure.PSTR_HD_HeadsTerminalSafe_102

/-! Positive-q COMPLETE controller iteration, including SAME-witness
proper-clock fetch/access. Actual decision8/16, optional append13, actual
stage update8 and jump0 share the same whole program, heap and QUERY ROM.
Incoming bad remains an internal register result of the actual query. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem scan_iteration_safe {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords origin rank bad heapWords : Nat) (entries : List Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (recorded : RecordedHeads (endpoint full capWords bits) q rank entries state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 40))) (ha : state.halted = false)
    (haddr : state.register .address = BitVec.ofNat bits (endpoint full capWords bits))
    (hold : state.register .old = BitVec.ofNat bits configuration.stage)
    (hindex : state.register .index = BitVec.ofNat bits full.length) (hbad : state.register .fresh = BitVec.ofNat bits bad)
    (hs : configuration.stage < full.length) (hN : Fits bits full.length) (hrank : rank ≤ q + 2)
    (hqfit : Fits bits (q + 2)) (hbfit : Fits bits (bad + 1))
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hi : ∀ offset < 2 + (staticMetadata q full).length, Fits bits (4 + packedCapacityWords q capWords bits + offset))
    (he : Fits bits (endpoint full capWords bits + 10 + entries.length + 1))
    (hroom : endpoint full capWords bits + 10 + entries.length + 1 < heapWords) :
    ∃ steps ≤ 40,
    (let after := packingRun (callInput q full .query) whole steps state;
      after.pc = BitVec.ofNat bits 0 ∧ after.halted = false ∧
      HeapRepresents q full capWords (nextConfiguration q full configuration .correct) after.heap ∧
      RecordedHeads (endpoint full capWords bits) q rank
        (if headGate q rank bad then entries ++ [configuration.stage] else entries) after.heap) ∧
    (∀ clock < steps, AtSafe (callInput q full .query) whole heapWords
      (packingRun (callInput q full .query) whole clock state)) := by
  let rom := callInput q full .query
  let E := endpoint full capWords bits
  obtain ⟨k, hk, decision⟩ := common_scan_decision_safe rom whole origin E q rank bad configuration.stage full.length heapWords entries
    hbound hcode hwords hpcfit state hp ha haddr hold hindex hbad recorded hs hN hrank hqfit hbfit (by omega)
  dsimp only at decision
  obtain ⟨pcD, activeD, heapD, oldD, indexD, addressD, recordD, safeD⟩ := decision
  let decided := packingRun rom whole k state
  have repD : HeapRepresents q full capWords configuration decided.heap := by
    change HeapRepresents q full capWords configuration (packingRun rom whole k state).heap
    rw [heapD]
    exact rep
  have hnext : Fits bits (configuration.stage + 1) := (Nat.succ_le_of_lt hs).trans_lt hN
  have hE : Fits bits E := (show E ≤ E + 10 + entries.length + 1 by omega).trans_lt he
  by_cases hg : headGate q rank bad = true
  · have hpcD : decided.pc = BitVec.ofNat bits (5 * (origin + 67)) := by simpa [hg] using pcD
    have ha13 := append_scan_entry rom whole origin E q rank configuration.stage entries hbound hcode hwords hpcfit
      decided he recordD hpcD activeD addressD oldD
    let appended := packingRun rom whole 13 decided
    have repA : HeapRepresents q full capWords configuration appended.heap := by
      change HeapRepresents q full capWords configuration (packingRun rom whole 13 decided).heap
      rw [ha13.2.2.1]
      exact headsAppend_prefix_rep full configuration capWords rank entries decided (by omega) hq repD bitmap hr he
        addressD recordD 10 (by decide)
    have heA : Fits bits (E + 10 + (entries ++ [configuration.stage]).length) := by
      simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_assoc] using he
    have hadv := advance_query_entry full configuration capWords origin rank (entries ++ [configuration.stage]) whole
      hbound hcode hwords hpcfit appended hb hq repA ha13.2.2.2.1 ha13.1 ha13.2.1 bitmap hr hi hnext heA
    have appendSafe (clock : Nat) (hc : clock < 13) : AtSafe rom whole heapWords (packingRun rom whole clock decided) := by
      exact (append_prefix_safe rom origin E (E + 10 + entries.length) heapWords whole hbound hcode hwords hpcfit
        decided ((show E + 2 ≤ E + 10 + entries.length + 1 by omega).trans_lt he)
        ((show E + 10 + entries.length ≤ E + 10 + entries.length + 1 by omega).trans_lt he)
        (by omega) (by omega) (by omega) addressD recordD.cursor hpcD activeD clock hc).1
    have advanceSafe (clock : Nat) (hc : clock < 11) : AtSafe rom whole heapWords (packingRun rom whole clock appended) :=
      (advance_prefix_safe full configuration capWords origin heapWords whole hbound hcode hwords hpcfit
        appended hq repA hE (by omega) ha13.1 ha13.2.1 clock hc).1
    have safeTail := heads_safe_add rom whole heapWords 13 11 decided appendSafe advanceSafe
    have safeAll := heads_safe_add rom whole heapWords k (13 + 11) state (fun clock hc => (safeD clock hc).1) safeTail
    refine ⟨k + (13 + 11), by omega, ?_, safeAll⟩
    dsimp only
    rw [run_add, run_add]
    simpa [hg] using hadv
  · have hpcD : decided.pc = BitVec.ofNat bits (5 * (origin + 56)) := by simpa [hg] using pcD
    have hadv := advance_query_entry full configuration capWords origin rank entries whole hbound hcode hwords hpcfit decided hb hq
      repD recordD hpcD activeD bitmap hr hi hnext ((Nat.le_add_right _ 1).trans_lt he)
    have advanceSafe (clock : Nat) (hc : clock < 11) : AtSafe rom whole heapWords (packingRun rom whole clock decided) :=
      (advance_prefix_safe full configuration capWords origin heapWords whole hbound hcode hwords hpcfit
        decided hq repD hE (by omega) hpcD activeD clock hc).1
    have safeAll := heads_safe_add rom whole heapWords k 11 state (fun clock hc => (safeD clock hc).1) advanceSafe
    refine ⟨k + 11, by omega, ?_, safeAll⟩
    dsimp only
    rw [run_add]
    simpa [hg] using hadv

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
