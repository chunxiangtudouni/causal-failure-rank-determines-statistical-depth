module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009i

/-! Access/frame facts for the runtime-generated local header and reverse
scan controls. Every accessed header offset is a fixed allocated address. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

theorem payloadRead_access {bits : Nat} (rom : PhysicalROM) (header heapWords : Nat) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header) (halloc : header + 9 < heapWords)
    (clock : Nat) (hc : clock < payloadRead.length) :
    packingAccessFits rom heapWords (executeOps rom (payloadRead.take clock) state) payloadRead[clock] := by
  change clock < 9 at hc
  interval_cases clock <;> try exact True.intro
  all_goals simp +decide only [payloadRead, List.take_succ_cons, List.take_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, packingAccessFits, AccessFits, hh, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
  all_goals exact (Nat.mod_le _ _).trans_lt (by omega)

theorem reverseTest_access {bits : Nat} (rom : PhysicalROM) (origin header heapWords : Nat) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header) (halloc : header + 8 < heapWords)
    (clock : Nat) (hc : clock < (reverseTest origin).length) :
    packingAccessFits rom heapWords (executeOps rom ((reverseTest origin).take clock) state) (reverseTest origin)[clock] := by
  change clock < 5 at hc
  interval_cases clock <;> try exact True.intro
  change (state.register .address + BitVec.ofNat bits 8).toNat < heapWords
  rw [hh, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
  exact (Nat.mod_le _ _).trans_lt halloc

theorem reverseFoot_access {bits : Nat} (rom : PhysicalROM) (origin header heapWords : Nat) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header) (halloc : header + 8 < heapWords)
    (clock : Nat) (hc : clock < (reverseFoot origin).length) :
    packingAccessFits rom heapWords (executeOps rom ((reverseFoot origin).take clock) state) (reverseFoot origin)[clock] := by
  change clock < 9 at hc
  interval_cases clock <;> try exact True.intro
  all_goals simp +decide [reverseFoot, reverseFootLead, executeOps, packingExecuteOp,
    wordOp, wordInstruction, packingAccessFits, AccessFits, hh, BitVec.ofNat_add_ofNat]
  all_goals exact (Nat.mod_le _ _).trans_lt halloc

theorem preparePush_access {bits : Nat} (rom : PhysicalROM) (header heapWords : Nat) (state : WordState bits)
    (h1 : Fits bits 1) (hh : state.register .address = BitVec.ofNat bits header)
    (hinput : 1 < rom.input.length) (halloc : header + 12 < heapWords)
    (clock : Nat) (hc : clock < preparePush.length) :
    packingAccessFits rom heapWords (executeOps rom (preparePush.take clock) state) preparePush[clock] := by
  have hheap : 0 < heapWords := by omega
  change clock < 38 at hc
  interval_cases clock <;> try exact True.intro
  all_goals simp +decide only [preparePush, List.take_succ_cons, List.take_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, packingAccessFits, AccessFits, hh, PhysicalROM.words,
    BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.zero_mod]
  all_goals first | omega | exact (Nat.mod_le _ _).trans_lt (by omega)

theorem preparePush_step_frame {bits : Nat} (rom : PhysicalROM) (header : Nat) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header)
    (address : BitVec bits) (hprotect : ClearProtected (header + 8) 5 address)
    (clock : Nat) (hc : clock < preparePush.length) :
    (packingExecuteOp rom preparePush[clock] (executeOps rom (preparePush.take clock) state)).heap address =
      (executeOps rom (preparePush.take clock) state).heap address := by
  have h8 : address ≠ BitVec.ofNat bits (header + 8) := by simpa only [Nat.add_zero] using hprotect 0 (by decide)
  have h9 : address ≠ BitVec.ofNat bits (header + 9) := by simpa only [Nat.add_assoc, Nat.reduceAdd] using hprotect 1 (by decide)
  have h10 : address ≠ BitVec.ofNat bits (header + 10) := by simpa only [Nat.add_assoc, Nat.reduceAdd] using hprotect 2 (by decide)
  have h11 : address ≠ BitVec.ofNat bits (header + 11) := by simpa only [Nat.add_assoc, Nat.reduceAdd] using hprotect 3 (by decide)
  have h12 : address ≠ BitVec.ofNat bits (header + 12) := by simpa only [Nat.add_assoc, Nat.reduceAdd] using hprotect 4 (by decide)
  by_cases hs : clock = 6 ∨ clock = 11 ∨ clock = 15 ∨ clock = 26 ∨ clock = 37
  · rcases hs with rfl | rfl | rfl | rfl | rfl <;>
      simp_all +decide [preparePush, executeOps, packingExecuteOp, wordOp, wordInstruction,
        Function.update_apply, BitVec.ofNat_add_ofNat]
  · have hn : HeapPreservingOp preparePush[clock] := by
      change clock < 38 at hc
      interval_cases clock <;> simp_all [preparePush, HeapPreservingOp]
    exact congrFun (PA17A19RuntimeRanks008.preserving_step_heap rom preparePush[clock] _ hn) address

theorem preparePush_actual_point {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp)
    (origin header heapWords : Nat) (state : WordState bits)
    (hbound : origin + preparePush.length ≤ containing.length)
    (hcode : ∀ i (hi : i < preparePush.length), containing[origin + i]'(by omega) = preparePush[i])
    (hw : WordsFit bits (packingCode containing)) (hpc : Fits bits (5 * containing.length))
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (h1 : Fits bits 1) (hh : state.register .address = BitVec.ofNat bits header)
    (hinput : 1 < rom.input.length) (halloc : header + 12 < heapWords)
    (clock : Nat) (hc : clock < preparePush.length) :
    ClearPoint rom containing heapWords (header + 8) 5 (packingRun rom containing clock state) := by
  exact clear_point_of_phase rom containing preparePush origin heapWords (header + 8) 5 hbound hcode hw hpc state ha clock hc
    (PA17A19RuntimeRanks008.straight_prefix rom containing preparePush origin hbound hcode preparePush_straight hw hpc state hp ha clock hc.le)
    (PA17A19RuntimeRanks008.prefix_pc rom preparePush origin preparePush_straight state hp clock hc.le)
    (preparePush_access rom header heapWords state h1 hh hinput halloc clock hc)
    (fun address hprotect => preparePush_step_frame rom header state hh address hprotect clock hc)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
