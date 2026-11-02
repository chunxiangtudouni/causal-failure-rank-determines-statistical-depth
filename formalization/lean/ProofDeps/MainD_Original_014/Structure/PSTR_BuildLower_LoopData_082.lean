module

public import Structure.PSTR_BuildLower_LexicalRange_079
public import Structure.PSTR_BuildLower_WordLoop_015

/-! The actual fetched countdown head and tail preserve the logical source
state and real producer data. The tail changes only the real lexical counter;
its subtraction keeps the original direct Word truncation semantics. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.LoopData
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem tail_range {q : Nat} {full : List (Finset (Fin q))} (physical : PhysicalROM) (counter entry : Nat) :
    BankRangeFrame (bits := bits q full) physical (relativeLoopTail counter entry) counter (counter + 1) := by
  refine ⟨?_, ?_⟩
  · intro state count
    by_cases hc : count ≤ 9
    · interval_cases count <;>
        simp [relativeLoopTail, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction]
    · rw [List.take_of_length_le (by rw [relativeLoopTail_length]; omega)]
      exact relativeLoopTail_word_base physical counter entry state
  · intro state point outside count
    have hn := outside counter le_rfl (by omega)
    by_cases hc : count ≤ 9
    · interval_cases count <;>
        simp [relativeLoopTail, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_of_ne hn]
    · rw [List.take_of_length_le (by rw [relativeLoopTail_length]; omega), relativeLoopTail_word_heap, Function.update_of_ne hn]

theorem head_data (q : Nat) (full : List (Finset (Fin q))) (physical : PhysicalROM)
    (counter : Nat) (left body right : List PackingOp) (logical : State) (state : WordState (bits q full))
    (hrep : SourceRep.Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ relativeLoopBlock counter left.length body ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ relativeLoopBlock counter left.length body ++ right).length)) :
    let after := packingRun physical (left ++ relativeLoopBlock counter left.length body ++ right) 5 state
    SourceRep.Prepared q full logical after ∧ RuntimeData.Data q full after.heap ∧ after.heap = state.heap ∧
      after.register .address = state.register .address ∧ after.halted = false ∧
      after.pc = if (state.heap (state.register .address + BitVec.ofNat _ counter)).toNat = 0 then
        BitVec.ofNat _ (5 * (left.length + body.length + 14)) else BitVec.ofNat _ (5 * (left.length + 5)) := by
  have hr := WordLoop.head_run physical left body right counter hcode hpcfit state hpc ha
  dsimp only
  rw [hr]
  refine ⟨⟨(relativeLoopHead_word_base physical _ _ state).trans hrep.address, hrep.registers, hrep.heap⟩,
    data, relativeLoopHead_word_heap physical _ _ state, relativeLoopHead_word_base physical _ _ state,
    (executeOps_halted physical _ state).trans ha, ?_⟩
  rw [relativeLoopHead_word_pc]
  split
  · rfl
  · rw [hpc, BitVec.ofNat_add_ofNat]
    congr 1

theorem tail_data (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (physical : PhysicalROM)
    (counter : Nat) (hc : counter < 21) (left body right : List PackingOp) (logical : State)
    (state : WordState (bits q full)) (hrep : SourceRep.Prepared q full logical state)
    (data : RuntimeData.Data q full state.heap)
    (hpc : state.pc = BitVec.ofNat _ (5 * (left.length + 5 + body.length))) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ relativeLoopBlock (64 + counter) left.length body ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ relativeLoopBlock (64 + counter) left.length body ++ right).length)) :
    let after := packingRun physical (left ++ relativeLoopBlock (64 + counter) left.length body ++ right) 9 state
    SourceRep.Prepared q full logical after ∧ RuntimeData.Data q full after.heap ∧
      after.pc = BitVec.ofNat _ (5 * left.length) ∧ after.halted = false ∧
      after.register .address = state.register .address ∧
      after.heap = Function.update state.heap (state.register .address + BitVec.ofNat _ (64 + counter))
        (BitVec.ofNat _ ((state.heap (state.register .address + BitVec.ofNat _ (64 + counter))).toNat -
          (BitVec.ofNat (bits q full) 1).toNat)) := by
  have hr := WordLoop.tail_run physical left body right (64 + counter) hcode hpcfit state hpc ha
  have hf := tail_range (q := q) (full := full) physical (64 + counter) (5 * left.length)
  have result := SourceRep.lexical_range_data q full hq physical (relativeLoopTail (64 + counter) (5 * left.length))
    (64 + counter) (64 + counter + 1) (by omega) (by omega) (by omega) hf logical state hrep data 9
  rw [List.take_of_length_le (by rw [relativeLoopTail_length])] at result
  dsimp only
  rw [hr]
  exact ⟨result.1, result.2, relativeLoopTail_word_pc physical _ _ state,
    (executeOps_halted physical _ state).trans ha, relativeLoopTail_word_base physical _ _ state,
    relativeLoopTail_word_heap physical _ _ state⟩

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.LoopData
