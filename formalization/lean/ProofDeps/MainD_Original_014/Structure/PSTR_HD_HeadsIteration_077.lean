module

public import Structure.PSTR_HD_HeadsAppendRun_076

/-! One COMPLETE actual nonterminal heads scan iteration from the common
label to the unique query-body entry0. At most40 true instructions implement
the exact encoded headGate, optional ordered write, stage bump and backjump.
The incoming bad register is still an internal same-run query obligation. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem scan_iteration {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords origin rank bad : Nat) (entries : List Nat) (whole : List PackingOp)
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
    (he : Fits bits (endpoint full capWords bits + 10 + entries.length + 1)) :
    ∃ steps ≤ 40,
    let after := packingRun (callInput q full .query) whole steps state
    after.pc = BitVec.ofNat bits 0 ∧ after.halted = false ∧
    HeapRepresents q full capWords (nextConfiguration q full configuration .correct) after.heap ∧
    RecordedHeads (endpoint full capWords bits) q rank
      (if headGate q rank bad then entries ++ [configuration.stage] else entries) after.heap := by
  let rom := callInput q full .query
  let E := endpoint full capWords bits
  obtain ⟨k, hk, hd⟩ := common_scan_decision rom whole origin E q rank bad configuration.stage full.length entries
    hbound hcode hwords hpcfit state hp ha haddr hold hindex hbad recorded hs hN hrank hqfit hbfit
  dsimp only at hd
  let decided := packingRun rom whole k state
  have repD : HeapRepresents q full capWords configuration decided.heap := by
    change HeapRepresents q full capWords configuration (packingRun rom whole k state).heap
    rw [hd.2.2.1]
    exact rep
  have hnext : Fits bits (configuration.stage + 1) := (Nat.succ_le_of_lt hs).trans_lt hN
  by_cases hg : headGate q rank bad = true
  · have hpcD : decided.pc = BitVec.ofNat bits (5 * (origin + 67)) := by simpa [hg] using hd.1
    have ha13 := append_scan_entry rom whole origin E q rank configuration.stage entries hbound hcode hwords hpcfit
      decided he hd.2.2.2.2.2.2 hpcD hd.2.1 hd.2.2.2.2.2.1 hd.2.2.2.1
    let appended := packingRun rom whole 13 decided
    have repA : HeapRepresents q full capWords configuration appended.heap := by
      change HeapRepresents q full capWords configuration (packingRun rom whole 13 decided).heap
      rw [ha13.2.2.1]
      exact headsAppend_prefix_rep full configuration capWords rank entries decided (by omega) hq repD bitmap hr he
        hd.2.2.2.2.2.1 hd.2.2.2.2.2.2 10 (by decide)
    have heA : Fits bits (E + 10 + (entries ++ [configuration.stage]).length) := by
      simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_assoc] using he
    have hadv := advance_query_entry full configuration capWords origin rank (entries ++ [configuration.stage]) whole
      hbound hcode hwords hpcfit appended hb hq repA ha13.2.2.2.1 ha13.1 ha13.2.1 bitmap hr hi hnext heA
    refine ⟨k + (13 + 11), by omega, ?_⟩
    dsimp only
    rw [run_add, run_add]
    simpa [hg] using hadv
  · have hpcD : decided.pc = BitVec.ofNat bits (5 * (origin + 56)) := by simpa [hg] using hd.1
    have hadv := advance_query_entry full configuration capWords origin rank entries whole hbound hcode hwords hpcfit decided hb hq
      repD hd.2.2.2.2.2.2 hpcD hd.2.1 bitmap hr hi hnext ((Nat.le_add_right _ 1).trans_lt he)
    refine ⟨k + 11, by omega, ?_⟩
    dsimp only
    rw [run_add]
    simpa [hg] using hadv

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
