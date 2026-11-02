module

public import Structure.PA17_A19QueryBridge_RuntimeRanks_008g
public import Structure.PSTR_QueryLayout_041

/-! The frozen actual rank loop preserves every Fits physical word at or
beyond the shared exclusive endpoint E, including the HD heads controller
and output area. No upper bound by the allocated heap is needed for a
protected word: this theorem does not access that word. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17A19RankSuffix014

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem actual_endpoint_frame {bits origin : Nat} {containing : List PackingOp}
    (em : PA17A19RuntimeRanks008.Embedded bits origin containing)
    (rom : PhysicalROM) (workspace size q heapWords : Nat) (good bad : Nat → Bool)
    (state : WordState bits)
    (hroom : Fits bits (PSTRQueryLayout.header workspace size + 16 + 2 * (q + 2)))
    (halloc : PSTRQueryLayout.header workspace size + 16 + 2 * (q + 2) ≤ heapWords)
    (hinput : 1 < rom.input.length) (hq : (rom.words .input).getD 1 0 = q)
    (hgood : ∀ budget < q + 2, state.heap
        (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 16 + budget)) =
      BitVec.ofNat bits (bit (good budget)))
    (hbad : ∀ budget < q + 2, state.heap
        (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 16 + budget + (q + 2))) =
      BitVec.ofNat bits (bit (bad budget)))
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size))
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (clock : Nat) (hc : clock ≤ PA17A19RuntimeRanks008.steps q)
    (physical : Nat) (hf : Fits bits physical)
    (he : PSTRQueryLayout.endpoint workspace size q ≤ physical) :
    (packingRun rom containing clock state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  let header := PSTRQueryLayout.header workspace size
  have hlast : header + 7 < PSTRQueryLayout.endpoint workspace size q := by
    change PSTRQueryLayout.header workspace size + 7 <
      PSTRQueryLayout.header workspace size + 16 + q + 2 + q + 2 + size + 3
    omega
  have hne (offset : Nat) (ho : 4 ≤ offset) (hu : offset ≤ 7) :
      BitVec.ofNat bits physical ≠ BitVec.ofNat bits (header + offset) := by
    have ht : Fits bits (header + offset) :=
      (show header + offset ≤ header + 16 + 2 * (q + 2) by omega).trans_lt hroom
    apply (ofNat_injective_of_fit _ _ hf ht).not.mpr
    omega
  exact PA17A19RuntimeRanks008.actual_prefix_frame em rom q header heapWords good bad state
    hroom halloc hinput hq hgood hbad hh hp ha clock hc _
    ⟨hne 4 (by decide) (by decide), hne 5 (by decide) (by decide),
      hne 6 (by decide) (by decide), hne 7 (by decide) (by decide)⟩

end PaperProofs.Structure.LaminarTree.PA17A19RankSuffix014
