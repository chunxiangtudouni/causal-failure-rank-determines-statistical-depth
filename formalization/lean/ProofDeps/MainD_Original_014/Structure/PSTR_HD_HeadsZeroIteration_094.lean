module

public import Structure.PSTR_HD_HeadsZeroWriteRep_093

/-! q=0's COMPLETE nonterminal shared controller iteration. Same literal
common/append/advance code and QUERY ROM; real endpoint46 and original low
heap semantics replace positive metadata. No original input fields are added. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem zero_scan_iteration {bits : Nat} (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (origin rank bad : Nat) (entries : List Nat) (whole : List PackingOp)
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
    (he : Fits bits (46 + 10 + entries.length + 1)) :
    ∃ steps ≤ 40,
    let after := packingRun (callInput 0 full .query) whole steps state
    after.pc = BitVec.ofNat bits 0 ∧ after.halted = false ∧
    HeapRepresents 0 full 0 (nextConfiguration 0 full configuration .correct) after.heap ∧
    RecordedHeads 46 0 rank (if headGate 0 rank bad then entries ++ [configuration.stage] else entries) after.heap := by
  let rom := callInput 0 full .query
  have hpow : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have hq2 : Fits bits (0 + 2) := by unfold Fits; omega
  obtain ⟨k, hk, hd⟩ := common_scan_decision rom whole origin 46 0 rank bad configuration.stage full.length entries
    hbound hcode hwords hpcfit state hp ha haddr hold hindex hbad recorded hs hN hrank hq2 hbfit
  dsimp only at hd
  let decided := packingRun rom whole k state
  have repD : HeapRepresents 0 full 0 configuration decided.heap := by
    change HeapRepresents 0 full 0 configuration (packingRun rom whole k state).heap
    rw [hd.2.2.1]
    exact rep
  have hnext : Fits bits (configuration.stage + 1) := (Nat.succ_le_of_lt hs).trans_lt hN
  by_cases hg : headGate 0 rank bad = true
  · have hpcD : decided.pc = BitVec.ofNat bits (5 * (origin + 67)) := by simpa [hg] using hd.1
    have ha13 := append_scan_entry rom whole origin 46 0 rank configuration.stage entries hbound hcode hwords hpcfit
      decided he hd.2.2.2.2.2.2 hpcD hd.2.1 hd.2.2.2.2.2.1 hd.2.2.2.1
    let appended := packingRun rom whole 13 decided
    have repA : HeapRepresents 0 full 0 configuration appended.heap := by
      change HeapRepresents 0 full 0 configuration (packingRun rom whole 13 decided).heap
      rw [ha13.2.2.1]
      exact zero_append_prefix_rep full configuration rank entries decided repD hd.2.2.2.2.2.2 he hd.2.2.2.2.2.1 10 (by decide)
    have heA : Fits bits (46 + 10 + (entries ++ [configuration.stage]).length) := by
      simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_assoc] using he
    have hadv := zero_advance_query_entry full configuration origin rank (entries ++ [configuration.stage]) whole
      hbound hcode hwords hpcfit appended hb repA ha13.2.2.2.1 ha13.1 ha13.2.1 hnext heA
    refine ⟨k + (13 + 11), by omega, ?_⟩
    dsimp only
    rw [run_add, run_add]
    simpa [hg] using hadv
  · have hpcD : decided.pc = BitVec.ofNat bits (5 * (origin + 56)) := by simpa [hg] using hd.1
    have hadv := zero_advance_query_entry full configuration origin rank entries whole hbound hcode hwords hpcfit decided hb
      repD hd.2.2.2.2.2.2 hpcD hd.2.1 hnext ((Nat.le_add_right _ 1).trans_lt he)
    refine ⟨k + 11, by omega, ?_⟩
    dsimp only
    rw [run_add]
    simpa [hg] using hadv

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
