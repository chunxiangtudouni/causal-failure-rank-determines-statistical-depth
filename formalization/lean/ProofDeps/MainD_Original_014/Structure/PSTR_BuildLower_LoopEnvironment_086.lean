module

public import Structure.PSTR_BuildLower_LoopData_082
public import Structure.PSTR_BuildLower_CopyData_078

/-! Actual Word countdown and restore give the source lexical environments.
Only the counter's source value needs its original Nat bound. No all-register
Nat transport is imposed on the real packed backend or on scratch registers. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.LoopEnvironment
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem tail_environment (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (counter : Nat) (hc : counter < 21) (entry : Nat)
    (environment : Nat → Nat) (state : WordState (bits q full))
    (henv : ∀ address < 21, state.heap (state.register .address + BitVec.ofNat _ (64 + address)) = BitVec.ofNat _ (environment address))
    (hvalue : Fits (bits q full) (environment counter)) :
    ∀ address < 21,
      (executeOps physical (relativeLoopTail (64 + counter) entry) state).heap
        ((executeOps physical (relativeLoopTail (64 + counter) entry) state).register .address + BitVec.ofNat _ (64 + address)) =
      BitVec.ofNat _ (Function.update environment counter (environment counter - 1) address) := by
  have room := bank_offset_fits q full hq 128 (by decide)
  change controlBase q full + 128 < 2 ^ bits q full at room
  have one : (BitVec.ofNat (bits q full) 1).toNat = 1 := Nat.mod_eq_of_lt (by omega)
  intro address had
  rw [relativeLoopTail_word_base, relativeLoopTail_word_heap]
  by_cases he : address = counter
  · subst address
    rw [Function.update_self, Function.update_self, henv counter hc, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hvalue, one]
  · rw [Function.update_of_ne (ControlDataFrame.offset_ne _ _ _
      (by change 64 + address < 2 ^ bits q full; omega)
      (by change 64 + counter < 2 ^ bits q full; omega) (by omega)), Function.update_of_ne he]
    exact henv address had

theorem restore_environment (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (counter depth : Nat) (hc : counter < 21)
    (environment : Nat → Nat) (state : WordState (bits q full))
    (other : ∀ address < 21, address ≠ counter →
      state.heap (state.register .address + BitVec.ofNat _ (64 + address)) = BitVec.ofNat _ (environment address))
    (saved : state.heap (state.register .address + BitVec.ofNat _ (96 + depth)) = BitVec.ofNat _ (environment counter)) :
    ∀ address < 21,
      (executeOps physical (relativeCopy (96 + depth) (64 + counter)) state).heap
        ((executeOps physical (relativeCopy (96 + depth) (64 + counter)) state).register .address + BitVec.ofNat _ (64 + address)) =
      BitVec.ofNat _ (environment address) := by
  have room := bank_offset_fits q full hq 128 (by decide)
  change controlBase q full + 128 < 2 ^ bits q full at room
  have base : (executeOps physical (relativeCopy (96 + depth) (64 + counter)) state).register .address = state.register .address := by
    simpa only [List.take_length] using relativeCopy_base_prefix physical (96 + depth) (64 + counter)
      state (relativeCopy (96 + depth) (64 + counter)).length
  intro address had
  rw [base, relativeCopy_heap]
  by_cases he : address = counter
  · subst address
    rw [Function.update_self]
    exact saved
  · rw [Function.update_of_ne (ControlDataFrame.offset_ne _ _ _
      (by change 64 + address < 2 ^ bits q full; omega)
      (by change 64 + counter < 2 ^ bits q full; omega) (by omega))]
    exact other address had he

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.LoopEnvironment
