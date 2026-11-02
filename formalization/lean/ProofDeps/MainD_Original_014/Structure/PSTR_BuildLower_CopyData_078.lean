module

public import Structure.PSTR_BuildLower_LoadData_064
public import Structure.PSTR_BuildLower_LexicalFrame_063

/-! Real counter save/restore copies protect the source VM, finite old heap
view and materialized producer data. Only the selected lexical target changes;
the physical copy is executed inside the same containing Word program. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem copy_straight (source target : Nat) : StraightProgram (relativeCopy source target) := by
  intro op hm
  rcases List.mem_append.mp hm with hr | hw
  · exact relativeRead_straight source .value op hr
  · exact relativeWrite_straight target op hw

theorem copy_prefix_data (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (source target : Nat) (htlo : 64 ≤ target) (hthi : target < 128)
    (logical : State) (state : WordState (bits q full)) (hrep : Prepared q full logical state)
    (data : RuntimeData.Data q full state.heap) (count : Nat) :
    Prepared q full logical (executeOps physical ((relativeCopy source target).take count) state) ∧
      RuntimeData.Data q full (executeOps physical ((relativeCopy source target).take count) state).heap := by
  let after := executeOps physical ((relativeCopy source target).take count) state
  have hf := ControlDataFrame.copy_range (bits := bits q full) physical source target
  have hend : Fits (bits q full) (controlBase q full + (target + 1)) := bank_offset_fits q full hq _ (by omega)
  have targetFit : Fits (bits q full) target := lt_of_le_of_lt (by omega) hend
  have frame (offset : Nat) (ho : offset ≤ 512) (hn : offset ≠ target) :
      after.heap (BitVec.ofNat _ (controlBase q full + offset)) = state.heap (BitVec.ofNat _ (controlBase q full + offset)) := by
    have offFit : Fits (bits q full) offset := lt_of_le_of_lt (by omega) (bank_offset_fits q full hq offset ho)
    have hh := ControlDataFrame.copy_offset_frame physical source target offset targetFit offFit hn state count
    simpa only [hrep.address, BitVec.ofNat_add_ofNat, after] using hh
  refine ⟨⟨(hf.1 state count).trans hrep.address, ?_, ?_⟩, ?_⟩
  · funext reg
    have hlo := (registerSlot_bounds reg).1
    have hhi := (registerSlot_bounds reg).2
    change 32 ≤ registerOffset reg at hlo
    change registerOffset reg < 39 at hhi
    change after.heap (BitVec.ofNat _ (controlBase q full) + BitVec.ofNat _ (registerOffset reg)) = _
    rw [BitVec.ofNat_add_ofNat, frame (registerOffset reg) (by omega) (by omega)]
    simpa only [portRegisters, BitVec.ofNat_add_ofNat] using congrFun hrep.registers reg
  · intro a had
    have hh := ViewFrame.bankRange_view physical (relativeCopy source target) target (target + 1) hf (by omega)
      q (oldCapacity q full) (capacity q full) (indexBase q full) (indexWords q full) (controlBase q full)
      state hrep.address hend (by have hb := bits_room q full; omega) (oldCapacity_le q full hq) le_rfl
      (by have hr := ordinary_before_control q full; omega) count a had
    exact hh.trans (hrep.heap a had)
  · apply RuntimeData.Data.of_frame q full hq state.heap after.heap data
    · intro point hp
      exact ViewFrame.bankRange_below physical (relativeCopy source target) target (target + 1) hf (by omega)
        state (controlBase q full) point hrep.address hend (by unfold controlBase; omega) count
    · intro offset ho
      exact frame offset (by omega) (by omega)
    · intro point hp hfit
      apply hf.2
      intro offset hlo hhi
      rw [hrep.address, BitVec.ofNat_add_ofNat]
      exact word_address_ne hfit (bank_offset_fits q full hq offset (by omega)) (by omega)

theorem copy_data (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (source target : Nat) (htlo : 64 ≤ target) (hthi : target < 128)
    (logical : State) (state : WordState (bits q full)) (hrep : Prepared q full logical state)
    (data : RuntimeData.Data q full state.heap)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ relativeCopy source target ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ relativeCopy source target ++ right).length)) :
    let after := packingRun physical (left ++ relativeCopy source target ++ right) 6 state
    Prepared q full logical after ∧ RuntimeData.Data q full after.heap ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + 6)) ∧ after.halted = false ∧
      after.heap = Function.update state.heap (BitVec.ofNat _ (controlBase q full + target))
        (state.heap (BitVec.ofNat _ (controlBase q full + source))) := by
  have hr := straight_prefix physical left (relativeCopy source target) right state (copy_straight source target)
    hcode hpcfit hpc ha 6 (by rw [relativeCopy_length])
  rw [List.take_of_length_le (by rw [relativeCopy_length])] at hr
  have result := copy_prefix_data q full hq physical source target htlo hthi logical state hrep data 6
  rw [List.take_of_length_le (by rw [relativeCopy_length])] at result
  dsimp only
  rw [hr]
  refine ⟨result.1, result.2, ?_, (executeOps_halted physical _ state).trans ha, ?_⟩
  · rw [executeOps_pc physical _ state (copy_straight source target), hpc, relativeCopy_length, BitVec.ofNat_add_ofNat]
    congr 1
  · simp only [relativeCopy_heap, hrep.address, BitVec.ofNat_add_ofNat]

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
