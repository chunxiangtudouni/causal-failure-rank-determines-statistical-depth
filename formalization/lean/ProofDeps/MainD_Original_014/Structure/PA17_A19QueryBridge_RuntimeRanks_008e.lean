module

public import Structure.PA17_A19QueryBridge_RuntimeRanks_008d
import Mathlib.Tactic.IntervalCases

/-! Local actual Word access and physical frame certificates. All addresses
come from the header pointer and the kernel's own bounded runtime counter.
No prefix-safety predicate is an entry premise of these certificates. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeRanks008

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM

def Protected {bits : Nat} (header : Nat) (address : BitVec bits) : Prop :=
  address ≠ BitVec.ofNat bits (header + 4) ∧ address ≠ BitVec.ofNat bits (header + 5) ∧
    address ≠ BitVec.ofNat bits (header + 6) ∧ address ≠ BitVec.ofNat bits (header + 7)

theorem preserving_step_heap {bits : Nat} (rom : PhysicalROM) (op : PackingOp) (state : WordState bits)
    (hn : HeapPreservingOp op) : (packingExecuteOp rom op state).heap = state.heap := by
  simpa only [executeOps] using executeOps_heap_of_no_store rom [op] state
    (by intro item hi; have he := List.mem_singleton.mp hi; subst item; exact hn)

theorem setup_access {bits : Nat} (rom : PhysicalROM) (heapWords : Nat) (state : WordState bits)
    (h1 : Fits bits 1) (hinput : 1 < rom.input.length) (count : Nat) (hc : count < setup.length) :
    packingAccessFits rom heapWords (executeOps rom (setup.take count) state) setup[count] := by
  change count < 8 at hc
  interval_cases count <;>
    simp_all +decide [setup, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits,
      AccessFits, PhysicalROM.words, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]

theorem test_access {bits : Nat} (rom : PhysicalROM) (origin heapWords : Nat) (state : WordState bits)
    (count : Nat) (hc : count < (testBlock origin).length) :
    packingAccessFits rom heapWords (executeOps rom ((testBlock origin).take count) state) (testBlock origin)[count] := by
  change count < 2 at hc
  interval_cases count <;> trivial

theorem body_access {bits : Nat} (rom : PhysicalROM) (origin q header remaining heapWords : Nat) (state : WordState bits)
    (hroom : Fits bits (header + 16 + 2 * (q + 2)))
    (halloc : header + 16 + 2 * (q + 2) ≤ heapWords) (hr : remaining < q + 2)
    (hp : state.register .address = BitVec.ofNat bits header)
    (hi : state.register .index = BitVec.ofNat bits (remaining + 1))
    (hq : state.register .total = BitVec.ofNat bits (q + 2))
    (count : Nat) (hc : count < (bodyBlock origin).length) :
    packingAccessFits rom heapWords (executeOps rom ((bodyBlock origin).take count) state) (bodyBlock origin)[count] := by
  have h1 : Fits bits 1 := (show 1 ≤ header + 16 + 2 * (q + 2) by omega).trans_lt hroom
  have hrf : Fits bits (remaining + 1) := (show remaining + 1 ≤ header + 16 + 2 * (q + 2) by omega).trans_lt hroom
  have hg : Fits bits (header + 16 + remaining) := (show header + 16 + remaining ≤ header + 16 + 2 * (q + 2) by omega).trans_lt hroom
  have hb : Fits bits (header + 16 + remaining + (q + 2)) :=
    (show header + 16 + remaining + (q + 2) ≤ header + 16 + 2 * (q + 2) by omega).trans_lt hroom
  have hga : header + 16 + remaining < heapWords := by omega
  have hba : header + 16 + remaining + (q + 2) < heapWords := by omega
  change count < 13 at hc
  interval_cases count <;>
    simp_all +decide [bodyBlock, bodyLead, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, BitVec.toNat_ofNat,
      BitVec.ofNat_add_ofNat, Nat.add_assoc, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hrf]
      <;> exact (Nat.mod_le _ _).trans_lt (by omega)

theorem footer_access {bits : Nat} (rom : PhysicalROM) (header heapWords : Nat) (state : WordState bits)
    (hp : state.register .address = BitVec.ofNat bits header) (halloc : header + 8 ≤ heapWords)
    (count : Nat) (hc : count < footer.length) :
    packingAccessFits rom heapWords (executeOps rom (footer.take count) state) footer[count] := by
  have haddr (offset : Nat) (ho : offset ≤ 7) : (BitVec.ofNat bits (header + offset)).toNat < heapWords :=
    (Nat.mod_le _ _).trans_lt (by omega)
  have h2 := haddr 2 (by decide)
  have h4 := haddr 4 (by decide)
  have h5 := haddr 5 (by decide)
  have h6 := haddr 6 (by decide)
  have h7 := haddr 7 (by decide)
  change count < 28 at hc
  interval_cases count <;>
    simp_all +decide [footer, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, Function.update_apply, BitVec.ofNat_add_ofNat, Nat.add_assoc]

theorem footer_step_frame {bits : Nat} (rom : PhysicalROM) (header : Nat) (state : WordState bits)
    (hp : state.register .address = BitVec.ofNat bits header)
    (address : BitVec bits) (hprotect : Protected header address)
    (count : Nat) (hc : count < footer.length) :
    (packingExecuteOp rom footer[count] (executeOps rom (footer.take count) state)).heap address =
      (executeOps rom (footer.take count) state).heap address := by
  rcases hprotect with ⟨h4, h5, h6, h7⟩
  by_cases hs : count = 2 ∨ count = 5 ∨ count = 8 ∨ count = 17
  · rcases hs with rfl | rfl | rfl | rfl <;>
      simp_all +decide [footer, executeOps, packingExecuteOp, wordOp, wordInstruction,
        Function.update_apply, BitVec.ofNat_add_ofNat, Nat.add_assoc]
  · have hn : HeapPreservingOp footer[count] := by
      have hcount : count < 28 := by simpa only [footer_length] using hc
      interval_cases count <;> simp_all [footer, HeapPreservingOp]
    exact congrFun (preserving_step_heap rom footer[count] _ hn) address

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeRanks008
