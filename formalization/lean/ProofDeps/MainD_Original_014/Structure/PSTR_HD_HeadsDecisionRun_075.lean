module

public import Structure.PSTR_HD_HeadsDecision_074

/-! Actual common-scan decision from current-stage registers and the real
recorded heap. At most16 fetched instructions choose the real append/advance
label exactly by the ORIGINAL encoded headGate. No query is invoked here. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem common_scan_decision {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (origin endpoint q rank bad stage N : Nat) (entries : List Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (origin + 40))) (ha : state.halted = false)
    (haddr : state.register .address = BitVec.ofNat bits endpoint)
    (hold : state.register .old = BitVec.ofNat bits stage) (hindex : state.register .index = BitVec.ofNat bits N)
    (hbad : state.register .fresh = BitVec.ofNat bits bad)
    (recorded : RecordedHeads endpoint q rank entries state.heap)
    (hs : stage < N) (hN : Fits bits N) (hr : rank ≤ q + 2)
    (hq : Fits bits (q + 2)) (hb : Fits bits (bad + 1)) :
    ∃ steps ≤ 16,
    let after := packingRun rom whole steps state
    after.pc = (if headGate q rank bad then BitVec.ofNat bits (5 * (origin + 67)) else BitVec.ofNat bits (5 * (origin + 56))) ∧
    after.halted = false ∧ after.heap = state.heap ∧ after.register .old = BitVec.ofNat bits stage ∧
    after.register .index = BitVec.ofNat bits N ∧ after.register .address = BitVec.ofNat bits endpoint ∧
    RecordedHeads endpoint q rank entries after.heap := by
  let middle := packingRun rom whole 3 state
  let finite := packingRun rom whole 5 middle
  have ht := terminal_continue rom whole origin stage N hbound hcode hwords hpcfit state hp ha hs hN hindex hold
  have hmaddr : middle.register .address = BitVec.ofNat bits endpoint := ht.2.2.2.2.2.2.2.trans haddr
  have hmflag : middle.heap (BitVec.ofNat bits (endpoint + 3)) = BitVec.ofNat bits (q + 2 - rank) := by
    rw [ht.2.2.1]
    exact recorded.finiteFlag
  have hf := finite_decision rom whole origin endpoint q rank hbound hcode hwords hpcfit middle ht.1 ht.2.1 hmaddr hmflag hr hq
  have hheap : finite.heap = state.heap := hf.2.2.1.trans ht.2.2.1
  have hfold : finite.register .old = BitVec.ofNat bits stage := hf.2.2.2.2.1.trans (ht.2.2.2.2.1.trans hold)
  have hfindex : finite.register .index = BitVec.ofNat bits N := hf.2.2.2.2.2.2.1.trans (ht.2.2.2.2.2.2.1.trans hindex)
  have hfaddr : finite.register .address = BitVec.ofNat bits endpoint := hf.2.2.2.2.2.2.2.trans hmaddr
  have run8 : packingRun rom whole 8 state = finite := by
    rw [show 8 = 3 + 5 from rfl, run_add]
  by_cases hz : rank = q + 2
  · refine ⟨8, by omega, ?_⟩
    dsimp only
    rw [run8]
    refine ⟨?_, hf.2.1, hheap, hfold, hfindex, hfaddr, ?_⟩
    · simpa [headGate, hz] using hf.1
    · rw [hheap]
      exact recorded
  · have hflt : rank < q + 2 := by omega
    have hfpc : finite.pc = BitVec.ofNat bits (5 * (origin + 48)) := by simpa only [hz, ↓reduceIte] using hf.1
    have hfrank : finite.heap (BitVec.ofNat bits endpoint) = BitVec.ofNat bits rank := by
      rw [hheap]
      exact recorded.initialRank
    have hfbad : finite.register .fresh = BitVec.ofNat bits bad :=
      hf.2.2.2.2.2.1.trans (ht.2.2.2.2.2.1.trans hbad)
    have hg := guard_decision rom whole origin endpoint rank bad hbound hcode hwords hpcfit finite hfpc hf.2.1 hfaddr hfrank hfbad (hr.trans_lt hq) hb
    refine ⟨16, le_refl _, ?_⟩
    dsimp only
    rw [show 16 = 8 + 8 from rfl, run_add, run8]
    refine ⟨?_, hg.2.1, hg.2.2.1.trans hheap,
      hg.2.2.2.1.trans hfold, hg.2.2.2.2.1.trans hfindex, hg.2.2.2.2.2.trans hfaddr, ?_⟩
    · by_cases heq : bad + 1 = rank <;> simpa [headGate, hflt, heq] using hg.1
    · rw [hg.2.2.1, hheap]
      exact recorded

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
