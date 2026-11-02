module

public import PaperProofs.Structure.PSTR_HD_HeadsTests_059

/-! A proof invariant over the REAL heads control/output heap. It is not an
input field or a ROM oracle. The actual21/10/7-op blocks establish, extend,
and serialize this invariant, respectively. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM RawTreePreprocessingClaims

structure RecordedHeads {bits : Nat} (endpoint q rank : Nat) (entries : List Nat)
    (heap : BitVec bits → BitVec bits) : Prop where
  initialRank : heap (BitVec.ofNat bits endpoint) = BitVec.ofNat bits rank
  count : heap (BitVec.ofNat bits (endpoint + 1)) = BitVec.ofNat bits entries.length
  cursor : heap (BitVec.ofNat bits (endpoint + 2)) = BitVec.ofNat bits (endpoint + 10 + entries.length)
  finiteFlag : heap (BitVec.ofNat bits (endpoint + 3)) = BitVec.ofNat bits (q + 2 - rank)
  outputRank : heap (BitVec.ofNat bits (endpoint + 8)) = BitVec.ofNat bits rank
  outputEntries : ∀ position < entries.length,
    heap (BitVec.ofNat bits (endpoint + 10 + position)) = BitVec.ofNat bits (entries.getD position 0)

theorem word_inj_below {bits : Nat} (ceiling left right : Nat) (hf : Fits bits ceiling)
    (hl : left ≤ ceiling) (hr : right ≤ ceiling) :
    BitVec.ofNat bits left = BitVec.ofNat bits right ↔ left = right :=
  ofNat_injective_of_fit left right (hl.trans_lt hf) (hr.trans_lt hf)

theorem initHeap_recorded {bits : Nat} (endpoint q rank : Nat) (heap : BitVec bits → BitVec bits)
    (he : Fits bits (endpoint + 8)) : RecordedHeads endpoint q rank [] (initHeap endpoint q rank heap) := by
  have hinj := word_inj_below (endpoint + 8) (hf := he)
  constructor <;>
    simp (disch := omega) [initHeap, Function.update_apply, hinj]

theorem initialize_recorded {bits : Nat} (rom : PhysicalROM) (endpoint q rank : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (he : Fits bits (endpoint + 8)) (hr : Fits bits rank) (hq : Fits bits (q + 2))
    (hp : state.register .address = BitVec.ofNat bits endpoint) (hv : state.register .value = BitVec.ofNat bits rank)
    (hraw : (rom.words .input).getD 1 0 = q) :
    RecordedHeads endpoint q rank [] (executeOps rom headsInit state).heap := by
  rw [(execute_headsInit rom endpoint q rank state hb ((by omega : endpoint + 3 ≤ endpoint + 8).trans_lt he)
    hr hq hp hv hraw).1]
  exact initHeap_recorded endpoint q rank state.heap he

theorem appendHeap_recorded {bits : Nat} (endpoint q rank stage : Nat) (entries : List Nat)
    (heap : BitVec bits → BitVec bits) (he : Fits bits (endpoint + 10 + entries.length + 1))
    (recorded : RecordedHeads endpoint q rank entries heap) :
    RecordedHeads endpoint q rank (entries ++ [stage])
      (appendHeap endpoint (endpoint + 10 + entries.length) stage entries.length heap) := by
  have hinj := word_inj_below (endpoint + 10 + entries.length + 1) (hf := he)
  constructor
  · simpa +arith (disch := omega) [appendHeap, Function.update_apply, hinj] using recorded.initialRank
  · simp (disch := omega) [appendHeap, Function.update_apply, hinj]
  · simp [appendHeap, Nat.add_assoc]
  · simpa +arith (disch := omega) [appendHeap, Function.update_apply, hinj] using recorded.finiteFlag
  · simpa +arith (disch := omega) [appendHeap, Function.update_apply, hinj] using recorded.outputRank
  · intro position hposition
    have hpos : position ≤ entries.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hposition
      omega
    by_cases hlt : position < entries.length
    · rw [List.getD_append _ _ _ _ hlt]
      simpa +arith (disch := omega) [appendHeap, Function.update_apply, hinj, ne_of_lt hlt] using recorded.outputEntries position hlt
    · have heq : position = entries.length := by omega
      subst position
      simp +arith (disch := omega) [appendHeap, Function.update_apply, hinj]

theorem append_recorded {bits : Nat} (rom : PhysicalROM) (endpoint q rank stage : Nat) (entries : List Nat)
    (state : WordState bits) (he : Fits bits (endpoint + 10 + entries.length + 1))
    (recorded : RecordedHeads endpoint q rank entries state.heap)
    (hp : state.register .address = BitVec.ofNat bits endpoint)
    (hs : state.register .old = BitVec.ofNat bits stage) :
    RecordedHeads endpoint q rank (entries ++ [stage]) (executeOps rom headsAppend state).heap := by
  rw [(execute_headsAppend rom endpoint (endpoint + 10 + entries.length) stage entries.length state hp hs
    recorded.count recorded.cursor).1]
  exact appendHeap_recorded endpoint q rank stage entries state.heap he recorded

theorem finish_recorded_rank {bits : Nat} (rom : PhysicalROM) (endpoint q rank : Nat) (entries : List Nat)
    (state : WordState bits) (recorded : RecordedHeads endpoint q rank entries state.heap)
    (hp : state.register .address = BitVec.ofNat bits endpoint) (he : Fits bits (endpoint + 9)) :
    (executeOps rom headsFinish state).heap (BitVec.ofNat bits (endpoint + 8)) = BitVec.ofNat bits rank := by
  rw [(execute_headsFinish rom endpoint entries.length state hp recorded.count).1]
  have hinj := word_inj_below (endpoint + 9) (hf := he)
  simpa +arith (disch := omega) [Function.update_apply, hinj] using recorded.outputRank

theorem finish_recorded_count {bits : Nat} (rom : PhysicalROM) (endpoint q rank : Nat) (entries : List Nat)
    (state : WordState bits) (recorded : RecordedHeads endpoint q rank entries state.heap)
    (hp : state.register .address = BitVec.ofNat bits endpoint) :
    (executeOps rom headsFinish state).heap (BitVec.ofNat bits (endpoint + 9)) = BitVec.ofNat bits entries.length := by
  rw [(execute_headsFinish rom endpoint entries.length state hp recorded.count).1, Function.update_self]

theorem finish_recorded_entries {bits : Nat} (rom : PhysicalROM) (endpoint q rank : Nat) (entries : List Nat)
    (state : WordState bits) (recorded : RecordedHeads endpoint q rank entries state.heap)
    (hp : state.register .address = BitVec.ofNat bits endpoint) (he : Fits bits (endpoint + 10 + entries.length))
    (position : Nat) (hposition : position < entries.length) :
    (executeOps rom headsFinish state).heap (BitVec.ofNat bits (endpoint + 10 + position)) =
      BitVec.ofNat bits (entries.getD position 0) := by
  rw [(execute_headsFinish rom endpoint entries.length state hp recorded.count).1]
  have hinj := word_inj_below (endpoint + 10 + entries.length) (hf := he)
  simpa +arith (disch := omega) [Function.update_apply, hinj] using recorded.outputEntries position hposition

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
