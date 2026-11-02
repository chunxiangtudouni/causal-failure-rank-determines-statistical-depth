module

public import Structure.PSTR_BuildLower_InputPrefixes_134

/-! The actual stage-input branch's three-step jump really skips the node
getter. It preserves every heap word and is charged/fetched in the same
87-op containing program, including its last jump instruction. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.InputPrefixes
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

private theorem jump_heap {bits : Nat} (physical : PhysicalROM) (target : Nat)
    (state : WordState bits) (clock : Nat) (hc : clock ≤ 3) :
    (executeOps physical ((forwardJump target).take clock) state).heap = state.heap := by
  interval_cases clock <;> rfl

theorem jump_resources (q : Nat) (full : List (Finset (Fin q)))
    (physical : PhysicalROM) (left right : List PackingOp) (pointer : Register)
    (state : WordState (bits q full)) (bounded : GlobalCapacity.Bounded q full state.heap)
    (hpc : state.pc = BitVec.ofNat _ (5 * (left.length + 21))) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ ConcreteAST.inputCode left.length pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ ConcreteAST.inputCode left.length pointer ++ right).length)) :
    ResourceTrace.Keeps q full physical (left ++ ConcreteAST.inputCode left.length pointer ++ right) state 3 ∧
      TraceAccess.Safe (allocated q full) physical (left ++ ConcreteAST.inputCode left.length pointer ++ right) state 3 := by
  constructor
  · intro clock hc
    rw [jump physical left right pointer state hpc ha hcode hpcfit clock hc, jump_heap physical _ state clock hc]
    exact ⟨bounded, ResourceTrace.CacheFrame.refl q full state.heap⟩
  · let target := 5 * (left.length + 87)
    let lead := (forwardJump target).take 2
    have shape : lead ++ [.jumpIfZero .flag .fresh] = forwardJump target := rfl
    have leadLength : lead.length + 1 = 3 := rfl
    have straight : StraightProgram lead := by simp [lead, forwardJump, StraightProgram, StraightOp]
    have result := AccessBridge.last_safe physical
      (left ++ ConcreteAST.inputHead (5 * (left.length + 24)) pointer ++ StageInput.code pointer) lead
      (NodeInput.nodeBitCode (left.length + 24) pointer ++ right) (.jumpIfZero .flag .fresh) (allocated q full) state straight
      (by rw [shape]; exact ControlAccess.jump_safe physical target (allocated q full) state)
      (by simpa only [List.length_append, ConcreteAST.inputHead_length, StageInput.code_length, Nat.add_assoc] using hpc) ha
      (by rw [shape]; simpa only [ConcreteAST.inputCode, target, List.append_assoc] using hcode)
      (by rw [shape]; simpa only [ConcreteAST.inputCode, target, List.append_assoc] using hpcfit)
    rw [shape, leadLength] at result
    simpa only [ConcreteAST.inputCode, target, List.append_assoc] using result

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.InputPrefixes
