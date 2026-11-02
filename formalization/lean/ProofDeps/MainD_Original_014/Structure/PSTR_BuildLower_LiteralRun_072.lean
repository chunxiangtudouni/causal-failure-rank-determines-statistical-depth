module

public import Structure.PSTR_BuildLower_StoreData_071
public import Structure.PSTR_BuildLower_ALUData_068
public import Structure.PSTR_BuildLower_SourceContext_052

/-! Every ORIGINAL source literal is simulated by its real concrete lowering.
Source qualifications follow the exact original-program prefix context and
its already proved numeric/capacity invariants. No caller safety, source-store
value, returned-ROM answer or instruction-performance oracle is introduced. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

def LiteralRuns (q : Nat) (full : List (Finset (Fin q))) (physical : PhysicalROM) (op : Op)
    (logical : State) (state : WordState (bits q full)) (left right : List PackingOp) : Prop :=
  ∃ count ≤ 99,
    let block := lowerLiteral ConcreteAST.ports left.length op
    let after := packingRun physical (left ++ block ++ right) count state
    Prepared q full (op.execute (givenTreeROM q full).semantic logical) after ∧ RuntimeData.Data q full after.heap ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + block.length)) ∧ after.halted = false ∧
      ∀ offset < 128, (offset < 32 ∨ 39 ≤ offset) →
        after.heap (BitVec.ofNat _ (controlBase q full + offset)) = state.heap (BitVec.ofNat _ (controlBase q full + offset))

theorem lowerLiteral_value (ports : BuilderPorts) (start : Nat) (op : ValueOp) :
    lowerLiteral ports start op.original = op.relativeLower := by cases op <;> rfl

theorem literal_value_run (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (physical : PhysicalROM)
    (op : ValueOp) (logical : State) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (hf : ∀ reg, Fits (bits q full) (logical.register reg))
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ lowerLiteral ConcreteAST.ports left.length op.original ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ lowerLiteral ConcreteAST.ports left.length op.original ++ right).length)) :
    LiteralRuns q full physical op.original logical state left right := by
  have actual := alu_data q full hq physical op logical state hrep data hf left right hpc ha
    (by simpa only [lowerLiteral_value] using hcode) (by simpa only [lowerLiteral_value] using hpcfit)
  dsimp only [LiteralRuns]
  simp only [lowerLiteral_value]
  refine ⟨op.relativeLower.length, actual.1.trans (by decide), actual.2.1, actual.2.2.1, actual.2.2.2.1, actual.2.2.2.2.1, ?_⟩
  intro offset ho hout
  have hlo := (registerSlot_bounds op.target).1
  have hhi := (registerSlot_bounds op.target).2
  change 32 ≤ registerOffset op.target at hlo
  change registerOffset op.target < 39 at hhi
  exact actual.2.2.2.2.2 offset (by omega) (by rcases hout with h | h <;> omega)

theorem literal_load_run (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (physical : PhysicalROM)
    (op : Op) (target : Register) (value limit : Nat) (logical : State) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (left block right : List PackingOp)
    (hcompile : lowerLiteral ConcreteAST.ports left.length op = block ++ relativeWrite (registerOffset target))
    (hsemantic : op.execute (givenTreeROM q full).semantic logical = loaded logical target value)
    (port : ReadExit physical left block (relativeWrite (registerOffset target) ++ right) state value limit)
    (hlimit : limit + 3 ≤ 99)
    (hcode : WordsFit (bits q full) (packingCode (left ++ lowerLiteral ConcreteAST.ports left.length op ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ lowerLiteral ConcreteAST.ports left.length op ++ right).length)) :
    LiteralRuns q full physical op logical state left right := by
  have actual := read_then_write_data q full hq physical target value limit logical state hrep data left block right port
    (by simpa only [hcompile, List.append_assoc] using hcode) (by simpa only [hcompile, List.append_assoc] using hpcfit)
  dsimp only [LiteralRuns]
  rw [hcompile, hsemantic]
  simp only [List.append_assoc, List.length_append, relativeWrite_length, Nat.add_assoc] at actual ⊢
  refine ⟨port.steps + 3, actual.1.trans hlimit, actual.2.1, actual.2.2.1, actual.2.2.2.1, actual.2.2.2.2.1, ?_⟩
  intro offset ho hout
  have hlo := (registerSlot_bounds target).1
  have hhi := (registerSlot_bounds target).2
  change 32 ≤ registerOffset target at hlo
  change registerOffset target < 39 at hhi
  exact actual.2.2.2.2.2 offset (by omega) (by rcases hout with h | h <;> omega)

theorem literal_run (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (op : Op) (later : List Op) (logical : State)
    (context : SourceContext.Context q full (op :: later) logical) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ lowerLiteral ConcreteAST.ports left.length op ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ lowerLiteral ConcreteAST.ports left.length op ++ right).length)) :
    LiteralRuns q full (CompactControllerClaims.controllerInput q full used) op logical state left right := by
  let runtime := CompactControllerClaims.controllerInput q full used
  have hf (reg : Register) : Fits (bits q full) (logical.register reg) := by
    simpa only [List.take_zero, IndexedClosureRAM.execute] using
      SourceContext.register_fits context hq hlaminar 0 (by simp) reg
  have haccess : AccessFits (givenTreeROM q full) (PA17QueryLayout014.heapWords full.length q (t q full)) logical op := by
    have hh := SourceContext.access context hq hlaminar 0 (by simp)
    have he : (op :: later)[0]'(by simp) = op := rfl
    simpa only [List.take_zero, he, IndexedClosureRAM.execute] using hh
  have hm : op ∈ SourceFacts.program q full := by rw [context.program_eq]; simp
  have hchildren := original_buildProgram_no_children full.length q (t q full) op hm
  cases op with
  | subtract target leftReg rightReg =>
    exact literal_value_run q full hq runtime (.subtract target leftReg rightReg) logical state hrep data hf left right hpc ha hcode hpcfit
  | base instruction =>
    cases instruction with
    | constant target value =>
      exact literal_value_run q full hq runtime (.constant target value) logical state hrep data hf left right hpc ha hcode hpcfit
    | add target leftReg rightReg =>
      exact literal_value_run q full hq runtime (.add target leftReg rightReg) logical state hrep data hf left right hpc ha hcode hpcfit
    | minimum target leftReg rightReg =>
      exact literal_value_run q full hq runtime (.minimum target leftReg rightReg) logical state hrep data hf left right hpc ha hcode hpcfit
    | select target condition whenTrue whenFalse =>
      exact literal_value_run q full hq runtime (.select target condition whenTrue whenFalse) logical state hrep data hf left right hpc ha hcode hpcfit
    | loadROM region target pointer =>
      cases region with
      | input =>
        have lower : 3 ≤ logical.register pointer := by
          simpa only [List.take_zero, IndexedClosureRAM.execute] using
            SourceContext.input_lower context 0 (by simp) target pointer rfl
        have upper : logical.register pointer < (givenTreeROM q full).input.length := by
          simpa only [AccessFits, PhysicalROM.words] using haccess
        have hcompile : lowerLiteral ConcreteAST.ports left.length (.base (.loadROM .input target pointer)) =
            ConcreteAST.inputCode left.length pointer ++ relativeWrite (registerOffset target) := rfl
        obtain ⟨port⟩ := input_read_exit q full used hq pointer logical state hrep data (hf pointer) lower upper left
          (relativeWrite (registerOffset target) ++ right) hpc ha
          (by simpa only [hcompile, List.append_assoc] using hcode) (by simpa only [hcompile, List.append_assoc] using hpcfit)
        exact literal_load_run q full hq runtime _ target _ 67 logical state hrep data left _ right hcompile rfl port (by decide) hcode hpcfit
      | internal =>
        have upper : logical.register pointer < 2 * t q full := by
          change logical.register pointer < (givenTreeROM q full).internal.length at haccess
          rw [RawTreeSerialization.givenTreeROM_internal_length] at haccess
          exact haccess
        have hcompile : lowerLiteral ConcreteAST.ports left.length (.base (.loadROM .internal target pointer)) =
            InternalInput.code pointer ++ relativeWrite (registerOffset target) := rfl
        let port := internal_read_exit q full runtime pointer logical state hrep data (hf pointer) upper left
          (relativeWrite (registerOffset target) ++ right) hpc ha
          (by simpa only [hcompile, List.append_assoc] using hcode) (by simpa only [hcompile, List.append_assoc] using hpcfit)
        exact literal_load_run q full hq runtime _ target _ 25 logical state hrep data left _ right hcompile rfl port (by decide) hcode hpcfit
      | children =>
        simp only [plainReadsChildren] at hchildren
        cases hchildren
    | loadHeap target pointer =>
      have had : logical.register pointer < oldCapacity q full + indexWords q full :=
        lt_of_lt_of_le haccess (source_domain q full)
      have hcompile : lowerLiteral ConcreteAST.ports left.length (.base (.loadHeap target pointer)) =
          ConcreteHeap.read left.length pointer ++ relativeWrite (registerOffset target) := rfl
      let port := heap_read_exit q full hq runtime pointer logical state hrep data (hf pointer) had left
        (relativeWrite (registerOffset target) ++ right) hpc ha
        (by simpa only [hcompile, List.append_assoc] using hcode) (by simpa only [hcompile, List.append_assoc] using hpcfit)
      exact literal_load_run q full hq runtime _ target _ 45 logical state hrep data left _ right hcompile rfl port (by decide) hcode hpcfit
    | storeHeap pointer sourceReg =>
      have had : logical.register pointer < oldCapacity q full + indexWords q full :=
        lt_of_lt_of_le haccess (source_domain q full)
      have goodValue (hp : logical.register pointer < oldCapacity q full) : logical.register sourceReg ≤ q := by
        have hh := SourceContext.capacity (SourceContext.advance context) hq hlaminar 0 (by simp)
          (logical.register pointer) hp
        simpa only [List.take_zero, IndexedClosureRAM.execute, Op.execute, Instruction.execute, Function.update_self] using hh
      obtain ⟨count, hc, result⟩ := heap_store_data q full hq runtime pointer sourceReg logical state hrep data hf had goodValue left right hpc ha
        (by simpa only [lowerLiteral, ConcreteAST.ports, List.append_assoc] using hcode)
        (by simpa only [lowerLiteral, ConcreteAST.ports, List.append_assoc] using hpcfit)
      refine ⟨count, hc, ?_⟩
      dsimp only
      simp only [lowerLiteral, ConcreteAST.ports, List.append_assoc, List.length_append, relativeRead_length,
        ConcreteHeap.write_length] at result ⊢
      refine ⟨result.1, result.2.1, result.2.2.1, result.2.2.2.1, ?_⟩
      intro offset ho _
      exact result.2.2.2.2 offset (by omega)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
