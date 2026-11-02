module

public import Structure.PSTR_BuildLower_ControlAccess_124
public import Structure.PSTR_BuildLower_StageResources_133

/-! Real input-dispatch head15, stage6 and forward-jump3 prefixes in the
ONE87-op containing program. Branch choice/value remain the existing real
040/041 facts; no phase is reset or allowed to skip its charged final jump. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.InputPrefixes
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

section Generic
variable {bits : Nat}

theorem head (physical : PhysicalROM) (left right : List PackingOp) (pointer : Register)
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ ConcreteAST.inputCode left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ ConcreteAST.inputCode left.length pointer ++ right).length))
    (clock : Nat) (hc : clock ≤ 15) :
    packingRun physical (left ++ ConcreteAST.inputCode left.length pointer ++ right) clock state =
      executeOps physical ((ConcreteAST.inputHead (5 * (left.length + 24)) pointer).take clock) state := by
  let target := 5 * (left.length + 24)
  let lead := (ConcreteAST.inputHead target pointer).take 14
  have shape : lead ++ [.jumpIfZero .flag .index] = ConcreteAST.inputHead target pointer := rfl
  have result := AccessBridge.last_prefix physical left lead
    (StageInput.code pointer ++ forwardJump (5 * (left.length + 87)) ++ NodeInput.nodeBitCode (left.length + 24) pointer ++ right)
    (.jumpIfZero .flag .index) state
    (by simp [lead, ConcreteAST.inputHead, relativeRead, StraightProgram, StraightOp]) hpc ha
    (by rw [shape]; simpa only [ConcreteAST.inputCode, target, List.append_assoc] using hcode)
    (by rw [shape]; simpa only [ConcreteAST.inputCode, target, List.append_assoc] using hpcfit)
    clock (by change clock ≤ 15; exact hc)
  rw [shape] at result
  simpa only [ConcreteAST.inputCode, target, List.append_assoc] using result

theorem stage (physical : PhysicalROM) (left right : List PackingOp) (pointer : Register)
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * (left.length + 15))) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ ConcreteAST.inputCode left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ ConcreteAST.inputCode left.length pointer ++ right).length))
    (clock : Nat) (hc : clock ≤ 6) :
    packingRun physical (left ++ ConcreteAST.inputCode left.length pointer ++ right) clock state =
      executeOps physical ((StageInput.code pointer).take clock) state := by
  have result := SourceRep.straight_prefix physical (left ++ ConcreteAST.inputHead (5 * (left.length + 24)) pointer)
    (StageInput.code pointer) (forwardJump (5 * (left.length + 87)) ++ NodeInput.nodeBitCode (left.length + 24) pointer ++ right)
    state (StageInput.code_straight pointer)
    (by simpa only [ConcreteAST.inputCode, List.append_assoc] using hcode)
    (by simpa only [ConcreteAST.inputCode, List.append_assoc] using hpcfit)
    (by simpa only [List.length_append, ConcreteAST.inputHead_length] using hpc) ha clock
    (by simpa only [StageInput.code_length] using hc)
  simpa only [ConcreteAST.inputCode, List.append_assoc] using result

theorem jump (physical : PhysicalROM) (left right : List PackingOp) (pointer : Register)
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * (left.length + 21))) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ ConcreteAST.inputCode left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ ConcreteAST.inputCode left.length pointer ++ right).length))
    (clock : Nat) (hc : clock ≤ 3) :
    packingRun physical (left ++ ConcreteAST.inputCode left.length pointer ++ right) clock state =
      executeOps physical ((forwardJump (5 * (left.length + 87))).take clock) state := by
  let target := 5 * (left.length + 87)
  let lead := (forwardJump target).take 2
  have shape : lead ++ [.jumpIfZero .flag .fresh] = forwardJump target := rfl
  have result := AccessBridge.last_prefix physical
    (left ++ ConcreteAST.inputHead (5 * (left.length + 24)) pointer ++ StageInput.code pointer) lead
    (NodeInput.nodeBitCode (left.length + 24) pointer ++ right) (.jumpIfZero .flag .fresh) state
    (by simp [lead, forwardJump, StraightProgram, StraightOp])
    (by simpa only [List.length_append, ConcreteAST.inputHead_length, StageInput.code_length, Nat.add_assoc] using hpc) ha
    (by rw [shape]; simpa only [ConcreteAST.inputCode, target, List.append_assoc] using hcode)
    (by rw [shape]; simpa only [ConcreteAST.inputCode, target, List.append_assoc] using hpcfit)
    clock (by change clock ≤ 3; exact hc)
  rw [shape] at result
  simpa only [ConcreteAST.inputCode, target, List.append_assoc] using result

end Generic

theorem head_resources (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (left right : List PackingOp) (pointer : Register) (state : WordState (bits q full))
    (base : state.register .address = BitVec.ofNat _ (controlBase q full))
    (bounded : GlobalCapacity.Bounded q full state.heap)
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ ConcreteAST.inputCode left.length pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ ConcreteAST.inputCode left.length pointer ++ right).length)) :
    ResourceTrace.Keeps q full physical (left ++ ConcreteAST.inputCode left.length pointer ++ right) state 15 ∧
      TraceAccess.Safe (allocated q full) physical (left ++ ConcreteAST.inputCode left.length pointer ++ right) state 15 := by
  constructor
  · intro clock hc
    rw [head physical left right pointer state hpc ha hcode hpcfit clock hc,
      (ConcreteAST.inputHead_prefix_frame physical _ pointer state clock).1]
    exact ⟨bounded, ResourceTrace.CacheFrame.refl q full state.heap⟩
  · let target := 5 * (left.length + 24)
    let lead := (ConcreteAST.inputHead target pointer).take 14
    have shape : lead ++ [.jumpIfZero .flag .index] = ConcreteAST.inputHead target pointer := rfl
    have leadLength : lead.length + 1 = 15 := rfl
    have straight : StraightProgram lead := by
      simp [lead, ConcreteAST.inputHead, relativeRead, StraightProgram, StraightOp]
    have primitive := ControlAccess.input_head_safe physical pointer target (allocated q full) state
      (BankAccess.point_room q full hq state base (registerOffset pointer)
        (by have hh := registerSlot_bounds pointer; change 32 ≤ registerOffset pointer ∧ registerOffset pointer < 39 at hh; omega))
      (BankAccess.point_room q full hq state base 0 (by decide))
      (BankAccess.point_room q full hq state base 1 (by decide))
    have result := AccessBridge.last_safe physical left lead
      (StageInput.code pointer ++ forwardJump (5 * (left.length + 87)) ++ NodeInput.nodeBitCode (left.length + 24) pointer ++ right)
      (.jumpIfZero .flag .index) (allocated q full) state straight (by rw [shape]; exact primitive) hpc ha
      (by rw [shape]; simpa only [ConcreteAST.inputCode, target, List.append_assoc] using hcode)
      (by rw [shape]; simpa only [ConcreteAST.inputCode, target, List.append_assoc] using hpcfit)
    rw [shape, leadLength] at result
    simpa only [ConcreteAST.inputCode, target, List.append_assoc] using result

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.InputPrefixes
