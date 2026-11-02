module

public import Structure.PSTR_BuildLower_LoadData_064
public import Structure.PSTR_BuildLower_LexicalFrame_063

/-! Physical lexical/temporary-bank execution is disjoint from the original
seven-word VM and finite packed/ordinary source view, and from producer data.
This local frame theorem will be instantiated by the real loop setup and
expression instructions, rather than imposed on the original prepare caller. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem lexical_range_data (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (block : List PackingOp) (lo hi : Nat)
    (hlo : 39 ≤ lo) (horder : lo ≤ hi) (hhi : hi ≤ 512)
    (frame : BankRangeFrame (bits := bits q full) physical block lo hi)
    (logical : State) (state : WordState (bits q full)) (hrep : Prepared q full logical state)
    (data : RuntimeData.Data q full state.heap) (count : Nat) :
    Prepared q full logical (executeOps physical (block.take count) state) ∧
      RuntimeData.Data q full (executeOps physical (block.take count) state).heap := by
  let after := executeOps physical (block.take count) state
  have hend : Fits (bits q full) (controlBase q full + hi) := bank_offset_fits q full hq hi hhi
  have hiWord : hi ≤ 2 ^ bits q full := by change controlBase q full + hi < 2 ^ bits q full at hend; omega
  refine ⟨⟨(frame.1 state count).trans hrep.address, ?_, ?_⟩, ?_⟩
  · funext reg
    have hreg := (registerSlot_bounds reg).2
    change registerOffset reg < 39 at hreg
    have hfit : Fits (bits q full) (registerOffset reg) :=
      lt_of_le_of_lt (by omega) (bank_offset_fits q full hq 39 (by decide))
    have hh := ControlDataFrame.range_offset physical block lo hi frame hiWord
      (registerOffset reg) hfit (Or.inl (by omega)) state count
    rw [hrep.address] at hh
    change after.heap (BitVec.ofNat _ (controlBase q full) + BitVec.ofNat _ (registerOffset reg)) = _
    simpa only [after, portRegisters] using hh.trans (congrFun hrep.registers reg)
  · intro a had
    have hh := ViewFrame.bankRange_view physical block lo hi frame horder
      q (oldCapacity q full) (capacity q full) (indexBase q full) (indexWords q full) (controlBase q full)
      state hrep.address hend (by have hb := bits_room q full; omega) (oldCapacity_le q full hq) le_rfl
      (by have hr := ordinary_before_control q full; omega) count a had
    exact hh.trans (hrep.heap a had)
  · apply RuntimeData.Data.of_frame q full hq state.heap after.heap data
    · intro point hp
      exact ViewFrame.bankRange_below physical block lo hi frame horder state (controlBase q full) point
        hrep.address hend (by unfold controlBase; omega) count
    · intro offset ho
      have hfit : Fits (bits q full) offset := lt_of_le_of_lt (by omega) (bank_offset_fits q full hq 32 (by decide))
      have hh := ControlDataFrame.range_offset physical block lo hi frame hiWord offset hfit (Or.inl (by omega)) state count
      simpa only [after, hrep.address, BitVec.ofNat_add_ofNat] using hh
    · intro point hp hfit
      apply frame.2
      intro offset hol hoh
      rw [hrep.address, BitVec.ofNat_add_ofNat]
      exact word_address_ne hfit (bank_offset_fits q full hq offset (by omega)) (by omega)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
