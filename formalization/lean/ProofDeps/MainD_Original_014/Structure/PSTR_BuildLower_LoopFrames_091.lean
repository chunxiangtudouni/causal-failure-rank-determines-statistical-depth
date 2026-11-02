module

public import Structure.PSTR_BuildLower_LoopSetup_088

/-! Fine physical lexical frames for setup and restore. Counter and save
cells are kept separate from expression temporaries; a single wide frame
would incorrectly permit overwriting other live lexical counters. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.LoopFrames
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open PA17UniformGenerator035b PA17ProgramTemplates041

theorem setup_straight (counter saved : Nat) (bound : Expr) :
    StraightProgram (relativeRepeatPrefix counter saved bound) := by
  intro op hm
  rcases List.mem_append.mp hm with hprefix | hwrite
  · rcases List.mem_append.mp hprefix with hcopy | hexpr
    · exact SourceRep.copy_straight counter saved op hcopy
    · exact bankCompile_noJump _ 128 op hexpr
  · exact relativeWrite_straight counter op hwrite

theorem setup_offset (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (physical : PhysicalROM)
    (counter depth : Nat) (hc : counter < 21) (hd : depth < 3) (bound : Expr) (hs : bound.size ≤ 29)
    (offset : Nat) (ho : offset < 128) (hne : offset ≠ 64 + counter) (hns : offset ≠ 96 + depth)
    (state : WordState (bits q full)) (left right : List PackingOp)
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ relativeRepeatPrefix (64 + counter) (96 + depth) bound ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ relativeRepeatPrefix (64 + counter) (96 + depth) bound ++ right).length)) :
    (packingRun physical (left ++ relativeRepeatPrefix (64 + counter) (96 + depth) bound ++ right)
      (relativeRepeatPrefix (64 + counter) (96 + depth) bound).length state).heap
      (state.register .address + BitVec.ofNat _ offset) = state.heap (state.register .address + BitVec.ofNat _ offset) := by
  have hr := SourceRep.straight_prefix physical left (relativeRepeatPrefix (64 + counter) (96 + depth) bound) right
    state (setup_straight _ _ _) hcode hpcfit hpc ha _ le_rfl
  rw [List.take_length] at hr
  rw [hr]
  let middle := executeOps physical (relativeCopy (64 + counter) (96 + depth)) state
  have base : middle.register .address = state.register .address := by
    simpa only [List.take_length] using relativeCopy_base_prefix physical (64 + counter) (96 + depth)
      state (relativeCopy (64 + counter) (96 + depth)).length
  have room : 128 + bound.size ≤ 2 ^ bits q full := by
    have hh := bank_offset_fits q full hq (128 + bound.size) (by omega)
    change controlBase q full + (128 + bound.size) < 2 ^ bits q full at hh
    omega
  have assign := LexicalSet.prefix_offset physical counter hc bound offset ho hne room middle (LexicalSet.code counter bound).length
  rw [List.take_length, base] at assign
  have copied := ControlDataFrame.copy_offset_frame physical (64 + counter) (96 + depth) offset
    (by have hh := bank_offset_fits q full hq (96 + depth) (by omega); change 96 + depth < 2 ^ bits q full; omega)
    (by have hh := bank_offset_fits q full hq offset (by omega); change offset < 2 ^ bits q full; omega)
    hns state (relativeCopy (64 + counter) (96 + depth)).length
  rw [List.take_length] at copied
  change (executeOps physical (relativeCopy (64 + counter) (96 + depth) ++ LexicalSet.code counter bound) state).heap _ = _
  rw [executeOps_append]
  exact assign.trans copied

theorem restore_offset (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (physical : PhysicalROM)
    (counter depth offset : Nat) (hc : counter < 21) (ho : offset < 128) (hne : offset ≠ 64 + counter)
    (state : WordState (bits q full)) (left right : List PackingOp)
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ relativeCopy (96 + depth) (64 + counter) ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ relativeCopy (96 + depth) (64 + counter) ++ right).length)) :
    (packingRun physical (left ++ relativeCopy (96 + depth) (64 + counter) ++ right) 6 state).heap
      (state.register .address + BitVec.ofNat _ offset) = state.heap (state.register .address + BitVec.ofNat _ offset) := by
  rw [SourceRep.straight_prefix physical left _ right state (SourceRep.copy_straight _ _) hcode hpcfit hpc ha
    6 (by rw [relativeCopy_length]), List.take_of_length_le (by rw [relativeCopy_length])]
  have hh := ControlDataFrame.copy_offset_frame physical (96 + depth) (64 + counter) offset
    (lt_of_le_of_lt (by omega) (bank_offset_fits q full hq (64 + counter) (by omega)))
    (lt_of_le_of_lt (by omega) (bank_offset_fits q full hq offset (by omega)))
    hne state 6
  simpa only [List.take_of_length_le (by rw [relativeCopy_length] : (relativeCopy (96 + depth) (64 + counter)).length ≤ 6)] using hh

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.LoopFrames
