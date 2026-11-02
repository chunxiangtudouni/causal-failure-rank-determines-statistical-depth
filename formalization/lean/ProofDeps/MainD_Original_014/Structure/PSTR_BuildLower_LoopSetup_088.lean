module

public import Structure.PSTR_BuildLower_LexicalSet_080
public import Structure.PSTR_BuildLower_GlobalCapacity_085

/-! The real repeat prelude saves the old counter, computes its runtime
bound and stores the new counter. The save survives the real expression
compiler; the entire prelude also transports global NEW-C capacity. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.LoopSetup
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open PA17UniformGenerator035b PA17ProgramTemplates041

theorem core_run (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (physical : PhysicalROM)
    (counter depth : Nat) (hc : counter < 21) (hdepth : depth < 3) (bound : Expr) (environment : Nat → Nat)
    (hcell : expressionCellLimit bound ≤ 21) (hinput : expressionInputLimit bound ≤ 3) (hsize : bound.size ≤ 29)
    (logical : State) (state : WordState (bits q full)) (hrep : SourceRep.Prepared q full logical state)
    (data : RuntimeData.Data q full state.heap)
    (henv : ∀ address < 21, state.heap (state.register .address + BitVec.ofNat _ (64 + address)) = BitVec.ofNat _ (environment address))
    (hvalues : ExprBounds.nodesFit (bits q full) (dimensionROM full.length q (t q full)) environment bound)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ relativeRepeatPrefix (64 + counter) (96 + depth) bound ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ relativeRepeatPrefix (64 + counter) (96 + depth) bound ++ right).length)) :
    let block := relativeRepeatPrefix (64 + counter) (96 + depth) bound
    let after := packingRun physical (left ++ block ++ right) block.length state
    block.length ≤ 212 ∧ SourceRep.Prepared q full logical after ∧ RuntimeData.Data q full after.heap ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + block.length)) ∧ after.halted = false ∧
      (∀ address < 21, after.heap (after.register .address + BitVec.ofNat _ (64 + address)) =
        BitVec.ofNat _ (Function.update environment counter (bound.eval (dimensionROM full.length q (t q full)) environment) address)) ∧
      after.heap (BitVec.ofNat _ (controlBase q full + (96 + depth))) = BitVec.ofNat _ (environment counter) := by
  let first := relativeCopy (64 + counter) (96 + depth)
  let assign := LexicalSet.code counter bound
  let block := relativeRepeatPrefix (64 + counter) (96 + depth) bound
  change WordsFit (bits q full) (packingCode (left ++ block ++ right)) at hcode
  change Fits (bits q full) (5 * (left ++ block ++ right).length) at hpcfit
  have split : block = first ++ assign := by
    simp only [block, first, assign, relativeRepeatPrefix, LexicalSet.code, List.append_assoc]
  have firstLength : first.length = 6 := rfl
  have firstResult := SourceRep.copy_data q full hq physical (64 + counter) (96 + depth)
    (by omega) (by omega) logical state hrep data left (assign ++ right) hpc ha
    (by simpa only [split, List.append_assoc] using hcode) (by simpa only [split, List.append_assoc] using hpcfit)
  let middle := packingRun physical (left ++ block ++ right) 6 state
  have firstPost : SourceRep.Prepared q full logical middle ∧ RuntimeData.Data q full middle.heap ∧
      middle.pc = BitVec.ofNat _ (5 * (left.length + 6)) ∧ middle.halted = false ∧
      middle.heap = Function.update state.heap (BitVec.ofNat _ (controlBase q full + (96 + depth)))
        (state.heap (BitVec.ofNat _ (controlBase q full + (64 + counter)))) := by
    simpa only [middle, split, first, List.append_assoc] using firstResult
  have middleEnv : ∀ address < 21, middle.heap (middle.register .address + BitVec.ofNat _ (64 + address)) =
      BitVec.ofNat _ (environment address) := by
    intro address had
    rw [firstPost.1.address, BitVec.ofNat_add_ofNat, firstPost.2.2.2.2,
      Function.update_of_ne (word_address_ne (bank_offset_fits q full hq (64 + address) (by omega))
        (bank_offset_fits q full hq (96 + depth) (by omega)) (by omega))]
    simpa only [hrep.address, BitVec.ofNat_add_ofNat] using henv address had
  have saved : middle.heap (BitVec.ofNat _ (controlBase q full + (96 + depth))) = BitVec.ofNat _ (environment counter) := by
    rw [firstPost.2.2.2.2, Function.update_self]
    simpa only [hrep.address, BitVec.ofNat_add_ofNat] using henv counter hc
  have last := LexicalSet.run q full hq physical counter hc bound environment hcell hinput hsize logical middle
    firstPost.1 firstPost.2.1 middleEnv hvalues (left ++ first) right
    (by simpa only [List.length_append, firstLength] using firstPost.2.2.1) firstPost.2.2.2.1
    (by simpa only [split, List.append_assoc, assign] using hcode)
    (by simpa only [split, List.append_assoc, assign] using hpcfit)
  have tempRoom : 128 + bound.size ≤ 2 ^ bits q full := by
    have hh := bank_offset_fits q full hq (128 + bound.size) (by omega)
    change controlBase q full + (128 + bound.size) < 2 ^ bits q full at hh
    omega
  have saveFrame := LexicalSet.actual_prefix_offset physical counter hc bound (96 + depth) (by omega) (by omega)
    tempRoom middle (left ++ first) right
    (by simpa only [List.length_append, firstLength] using firstPost.2.2.1) firstPost.2.2.2.1
    (by simpa only [split, List.append_assoc, assign] using hcode)
    (by simpa only [split, List.append_assoc, assign] using hpcfit)
    assign.length le_rfl
  have runSplit : packingRun physical (left ++ block ++ right) block.length state =
      packingRun physical ((left ++ first) ++ assign ++ right) assign.length middle := by
    have hl : block.length = 6 + assign.length := by rw [split, List.length_append, firstLength]
    rw [hl, PSTRWordSegments.run_add]
    simp only [split, List.append_assoc, middle]
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hh := fixedExprCode_length bound
    rw [relativeRepeatPrefix_length]
    omega
  · rw [runSplit]
    exact last.2.1
  · rw [runSplit]
    exact last.2.2.1
  · rw [runSplit]
    calc
      _ = BitVec.ofNat _ (5 * ((left ++ first).length + assign.length)) := last.2.2.2.1
      _ = BitVec.ofNat _ (5 * (left.length + block.length)) := by
        congr 1
        rw [split, List.length_append, List.length_append]
        omega
  · rw [runSplit]
    exact last.2.2.2.2.1
  · rw [runSplit]
    exact last.2.2.2.2.2
  · rw [runSplit]
    have savedAtBase : middle.heap (middle.register .address + BitVec.ofNat _ (96 + depth)) =
        BitVec.ofNat _ (environment counter) := by
      rw [firstPost.1.address, BitVec.ofNat_add_ofNat]
      exact saved
    have hh := saveFrame.trans savedAtBase
    rw [firstPost.1.address, BitVec.ofNat_add_ofNat] at hh
    exact hh

theorem run (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (physical : PhysicalROM)
    (counter depth : Nat) (hc : counter < 21) (hdepth : depth < 3) (bound : Expr) (environment : Nat → Nat)
    (hcell : expressionCellLimit bound ≤ 21) (hinput : expressionInputLimit bound ≤ 3) (hsize : bound.size ≤ 29)
    (logical : State) (state : WordState (bits q full)) (hrep : SourceRep.Prepared q full logical state)
    (data : RuntimeData.Data q full state.heap) (bounded : GlobalCapacity.Bounded q full state.heap)
    (henv : ∀ address < 21, state.heap (state.register .address + BitVec.ofNat _ (64 + address)) = BitVec.ofNat _ (environment address))
    (hvalues : ExprBounds.nodesFit (bits q full) (dimensionROM full.length q (t q full)) environment bound)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ relativeRepeatPrefix (64 + counter) (96 + depth) bound ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ relativeRepeatPrefix (64 + counter) (96 + depth) bound ++ right).length)) :
    let block := relativeRepeatPrefix (64 + counter) (96 + depth) bound
    let after := packingRun physical (left ++ block ++ right) block.length state
    block.length ≤ 212 ∧ SourceRep.Prepared q full logical after ∧ RuntimeData.Data q full after.heap ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + block.length)) ∧ after.halted = false ∧
      (∀ address < 21, after.heap (after.register .address + BitVec.ofNat _ (64 + address)) =
        BitVec.ofNat _ (Function.update environment counter (bound.eval (dimensionROM full.length q (t q full)) environment) address)) ∧
      after.heap (BitVec.ofNat _ (controlBase q full + (96 + depth))) = BitVec.ofNat _ (environment counter) ∧
      ∀ clock ≤ block.length, GlobalCapacity.Bounded q full (packingRun physical (left ++ block ++ right) clock state).heap := by
  have result := core_run q full hq physical counter depth hc hdepth bound environment hcell hinput hsize
    logical state hrep data henv hvalues left right hpc ha hcode hpcfit
  refine ⟨result.1, result.2.1, result.2.2.1, result.2.2.2.1, result.2.2.2.2.1, result.2.2.2.2.2.1,
    result.2.2.2.2.2.2, ?_⟩
  have split : relativeRepeatPrefix (64 + counter) (96 + depth) bound =
      relativeCopy (64 + counter) (96 + depth) ++ LexicalSet.code counter bound := by
    simp only [relativeRepeatPrefix, LexicalSet.code, List.append_assoc]
  have frame : BankRangeFrame (bits := bits q full) physical
      (relativeRepeatPrefix (64 + counter) (96 + depth) bound) 64 (128 + bound.size) := by
    rw [split]
    apply bankRangeFrame_append
    · exact bankRangeFrame_mono physical _ (96 + depth) (96 + depth + 1) 64 (128 + bound.size)
        (by omega) (by omega) (ControlDataFrame.copy_range physical (64 + counter) (96 + depth))
    · exact LexicalSet.code_range physical counter bound hc
  have straight : StraightProgram (relativeRepeatPrefix (64 + counter) (96 + depth) bound) := by
    rw [split]
    intro op hm
    rcases List.mem_append.mp hm with hf | hs
    · exact SourceRep.copy_straight _ _ op hf
    · exact LexicalSet.code_straight counter bound op hs
  intro clock hclock
  exact GlobalCapacity.bank_actual_prefix q full hq physical _ 64 (128 + bound.size) (by omega) (by omega)
    frame straight state hrep.address bounded left right hpc ha hcode hpcfit clock hclock

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.LoopSetup
