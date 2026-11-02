module

public import Structure.PSTR_BuildLower_CounterInit_036
public import Structure.PSTR_BuildLower_LexicalRange_079
public import Structure.PSTR_BuildLower_ResourceTrace_094

/-! Real sixty-four-instruction counter initialization connects producer
data to the typed AST's zero environment. The caller need not supply any
zero lexical cell; all21 cells are physically written after the producer. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.CounterEntry
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem run (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (physical : PhysicalROM)
    (logical : State) (state : WordState (bits q full)) (hrep : SourceRep.Prepared q full logical state)
    (data : RuntimeData.Data q full state.heap) (bounded : GlobalCapacity.Bounded q full state.heap)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ CounterInit.code ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ CounterInit.code ++ right).length)) :
    let after := packingRun physical (left ++ CounterInit.code ++ right) 64 state
    SourceRep.Prepared q full logical after ∧ RuntimeData.Data q full after.heap ∧
      GlobalCapacity.Bounded q full after.heap ∧
      (∀ address < 21, after.heap (after.register .address + BitVec.ofNat _ (64 + address)) = 0) ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + 64)) ∧ after.halted = false ∧
      ResourceTrace.Keeps q full physical (left ++ CounterInit.code ++ right) state 64 := by
  have actual := CounterInit.run physical left right state hpc ha hcode hpcfit
  have frame := CounterInit.code_range (bits := bits q full) physical
  have source := SourceRep.lexical_range_data q full hq physical CounterInit.code 64 85
    (by decide) (by decide) (by decide) frame logical state hrep data 64
  rw [List.take_of_length_le (by rw [CounterInit.code_length])] at source
  have keeps := ResourceTrace.bank_actual_keeps q full hq physical CounterInit.code 64 85 (by decide) (by decide)
    frame CounterInit.code_straight state hrep.address bounded left right hpc ha hcode hpcfit
  rw [CounterInit.code_length] at keeps
  dsimp only
  refine ⟨?_, ?_, (keeps 64 le_rfl).1, ?_, ?_, ?_, keeps⟩
  · rw [actual]
    exact source.1
  · rw [actual]
    exact source.2
  · intro address had
    rw [actual]
    have base := frame.1 state 64
    rw [List.take_of_length_le (by rw [CounterInit.code_length])] at base
    rw [base]
    exact CounterInit.counters_zero physical state address had
  · rw [actual]
    exact CounterInit.builder_head_pc physical state left.length hpc
  · rw [actual, executeOps_halted]
    exact ha

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.CounterEntry
