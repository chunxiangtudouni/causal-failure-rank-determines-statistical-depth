module
public import Structure.PA17_A19QueryBridge_RuntimeReply_016c

/-! The REAL32-op footer produces finite Nat reply registers. Its final
select performs the H7 mask; disabled tool slots may contain arbitrary words. -/
@[expose] public section
set_option maxRecDepth 24000
set_option maxHeartbeats 2400000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeReplyCorrect022
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

structure FooterRegisters {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp)
    (workspace size q good bad toolWord activeValue origin : Nat) (before after : WordState bits) : Prop where
  active : after.halted = false
  pc : after.pc = BitVec.ofNat bits (5 * (origin + 32))
  header : after.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size)
  old : (after.register .old).toNat = if activeValue = 0 then q + 2 else good
  fresh : (after.register .fresh).toNat = if activeValue = 0 then 0 else bad
  value : (after.register .value).toNat = if activeValue = 0 then q + 2 else min good (bad + 1)
  index : (after.register .index).toNat = if activeValue = 0 then 0 else if bad = 0 then 0 else toolWord
  heap_eq : after.heap = before.heap
  prefix_heap : ∀ clock ≤ 32, (packingRun rom containing clock before).heap = before.heap
  trace : (packingDynamicTrace rom containing 32 before).length ≤ 384

theorem actual_footer_registers {bits origin : Nat} {containing : List PackingOp}
    (em : PA17A19RuntimeReply016.Embedded bits origin containing) (rom : PhysicalROM)
    (workspace size q good bad toolWord : Nat) (state : WordState bits)
    (hroom : Fits bits (PSTRQueryLayout.endpoint workspace size q))
    (hq : (rom.words .input).getD 1 0 = q)
    (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size))
    (hgood : state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 4)) = BitVec.ofNat bits good)
    (hbad : state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 5)) = BitVec.ofNat bits bad)
    (hg : good ≤ q + 2) (hb : bad ≤ q + 2) (ht : toolWord ≤ q)
    (hflag : state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 7)) =
      BitVec.ofNat bits (if (state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 2))).toNat = 0 then 0
        else if bad = 0 then 0 else 1))
    (htool : (if (state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 2))).toNat = 0 then 0
        else if bad = 0 then 0 else 1) ≠ 0 →
      state.heap (BitVec.ofNat bits (PSTRQueryLayout.childBase workspace size q + size + 2)) = BitVec.ofNat bits toolWord)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    FooterRegisters rom containing workspace size q good bad toolWord
      (state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 2))).toNat origin state
      (packingRun rom containing 32 state) := by
  let header := PSTRQueryLayout.header workspace size
  let activeValue := (state.heap (BitVec.ofNat bits (header + 2))).toNat
  let enabled := if activeValue = 0 then 0 else if bad = 0 then 0 else 1
  let after := packingRun rom containing 32 state
  have result := PA17A19RuntimeReply016.actual_reply em rom workspace size q good bad state hroom hq hsize hh hgood hbad hg hb hp ha
  rcases result with ⟨hactive, hpc, hheader, hold, hfresh, hvalue, hindex, hheap⟩
  have hqRoom : q + 3 ≤ PSTRQueryLayout.endpoint workspace size q := by
    unfold PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags
    omega
  have hqfit : Fits bits (q + 2) := (show q + 2 < PSTRQueryLayout.endpoint workspace size q by omega).trans hroom
  have h1fit : Fits bits 1 := (show 1 ≤ q + 2 by omega).trans_lt hqfit
  have henabled : enabled ≤ 1 := by unfold enabled; split_ifs <;> omega
  have hefit : Fits bits enabled := henabled.trans_lt h1fit
  change after.register .index = (if (state.heap (BitVec.ofNat bits (header + 7))).toNat = 0 then BitVec.ofNat bits 0 else
    state.heap (BitVec.ofNat bits (PSTRQueryLayout.childBase workspace size q + size + 2))) at hindex
  rw [hflag, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hefit] at hindex
  have hindexWord : after.register .index = BitVec.ofNat bits
      (if activeValue = 0 then 0 else if bad = 0 then 0 else toolWord) := by
    by_cases hz : activeValue = 0
    · simpa [enabled, hz] using hindex
    · by_cases hb0 : bad = 0
      · simpa [enabled, hz, hb0] using hindex
      · have he : enabled ≠ 0 := by simp [enabled, hz, hb0]
        have hi : after.register .index = state.heap
            (BitVec.ofNat bits (PSTRQueryLayout.childBase workspace size q + size + 2)) := by
          simpa only [he, ite_false] using hindex
        rw [htool he] at hi
        simpa only [hz, hb0, ite_false] using hi
  have oldFit : Fits bits (if activeValue = 0 then q + 2 else good) := by
    apply (show (if activeValue = 0 then q + 2 else good) ≤ q + 2 by split_ifs <;> omega).trans_lt hqfit
  have freshFit : Fits bits (if activeValue = 0 then 0 else bad) := by
    apply (show (if activeValue = 0 then 0 else bad) ≤ q + 2 by split_ifs <;> omega).trans_lt hqfit
  have valueFit : Fits bits (if activeValue = 0 then q + 2 else min good (bad + 1)) := by
    apply (show (if activeValue = 0 then q + 2 else min good (bad + 1)) ≤ q + 2 by split_ifs <;> omega).trans_lt hqfit
  have indexFit : Fits bits (if activeValue = 0 then 0 else if bad = 0 then 0 else toolWord) := by
    apply (show (if activeValue = 0 then 0 else if bad = 0 then 0 else toolWord) ≤ q + 2 by split_ifs <;> omega).trans_lt hqfit
  refine ⟨hactive, hpc, hheader, ?_, ?_, ?_, ?_, hheap, ?_, PA17A19RuntimeReply016.inline_trace_bound rom containing state⟩
  · change (after.register .old).toNat = _
    rw [hold, BitVec.toNat_ofNat, Nat.mod_eq_of_lt oldFit]
  · change (after.register .fresh).toNat = _
    rw [hfresh, BitVec.toNat_ofNat, Nat.mod_eq_of_lt freshFit]
  · change (after.register .value).toNat = _
    rw [hvalue, BitVec.toNat_ofNat, Nat.mod_eq_of_lt valueFit]
  · rw [hindexWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexFit]
  · intro clock hc
    exact PA17A19RuntimeReply016.actual_prefix_heap em rom state hp ha clock hc

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeReplyCorrect022
