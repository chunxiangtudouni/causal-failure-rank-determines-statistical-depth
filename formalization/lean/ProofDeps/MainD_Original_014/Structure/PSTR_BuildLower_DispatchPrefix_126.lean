module

public import Structure.PSTR_BuildLower_JumpAccess_122
public import Structure.PSTR_BuildLower_DispatchRun_019

/-! EVERY real prefix in each actual double-cutoff dispatch phase. The
classification and forward jump include their final executed jump. The
packed and ordinary phases remain the SAME containing program and state. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.DispatchPrefix
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
variable {bits : Nat}

theorem classify (physical : PhysicalROM) (left packed ordinary right : List PackingOp) (pointer : Register)
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ DispatchRun.code packed ordinary left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ DispatchRun.code packed ordinary left.length pointer ++ right).length))
    (clock : Nat) (hc : clock ≤ 9) :
    packingRun physical (left ++ DispatchRun.code packed ordinary left.length pointer ++ right) clock state =
      executeOps physical ((memoryClassify pointer (5 * (left.length + 9 + packed.length + 3))).take clock) state := by
  let target := 5 * (left.length + 9 + packed.length + 3)
  let lead := (memoryClassify pointer target).take 8
  have shape : lead ++ [.jumpIfZero .flag .fresh] = memoryClassify pointer target := rfl
  have result := AccessBridge.last_prefix physical left lead
    (packed ++ forwardJump (5 * (left.length + 9 + packed.length + 3 + ordinary.length)) ++ ordinary ++ right)
    (.jumpIfZero .flag .fresh) state
    (by simp [lead, memoryClassify, relativeRead, StraightProgram, StraightOp]) hpc ha
    (by rw [shape]; simpa only [DispatchRun.code, target, List.append_assoc] using hcode)
    (by rw [shape]; simpa only [DispatchRun.code, target, List.append_assoc] using hpcfit)
    clock (by change clock ≤ 9; exact hc)
  rw [shape] at result
  simpa only [DispatchRun.code, target, List.append_assoc] using result

theorem packed (physical : PhysicalROM) (left block ordinary right : List PackingOp) (pointer : Register)
    (straight : StraightProgram block) (state : WordState bits)
    (hpc : state.pc = BitVec.ofNat bits (5 * (left.length + 9))) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ DispatchRun.code block ordinary left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ DispatchRun.code block ordinary left.length pointer ++ right).length))
    (clock : Nat) (hc : clock ≤ block.length) :
    packingRun physical (left ++ DispatchRun.code block ordinary left.length pointer ++ right) clock state =
      executeOps physical (block.take clock) state := by
  have result := SourceRep.straight_prefix physical
    (left ++ memoryClassify pointer (5 * (left.length + 9 + block.length + 3))) block
    (forwardJump (5 * (left.length + 9 + block.length + 3 + ordinary.length)) ++ ordinary ++ right)
    state straight
    (by simpa only [DispatchRun.code, List.append_assoc] using hcode)
    (by simpa only [DispatchRun.code, List.append_assoc] using hpcfit)
    (by simpa only [List.length_append, memoryClassify_length] using hpc) ha clock hc
  simpa only [DispatchRun.code, List.append_assoc] using result

theorem ordinary (physical : PhysicalROM) (left packed block right : List PackingOp) (pointer : Register)
    (straight : StraightProgram block) (state : WordState bits)
    (hpc : state.pc = BitVec.ofNat bits (5 * (left.length + 9 + packed.length + 3))) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ DispatchRun.code packed block left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ DispatchRun.code packed block left.length pointer ++ right).length))
    (clock : Nat) (hc : clock ≤ block.length) :
    packingRun physical (left ++ DispatchRun.code packed block left.length pointer ++ right) clock state =
      executeOps physical (block.take clock) state := by
  have result := SourceRep.straight_prefix physical
    (left ++ memoryClassify pointer (5 * (left.length + 9 + packed.length + 3)) ++ packed ++
      forwardJump (5 * (left.length + 9 + packed.length + 3 + block.length))) block right state straight
    (by simpa only [DispatchRun.code, List.append_assoc] using hcode)
    (by simpa only [DispatchRun.code, List.append_assoc] using hpcfit)
    (by simpa only [List.length_append, memoryClassify_length, forwardJump_length] using hpc) ha clock hc
  simpa only [DispatchRun.code, List.append_assoc] using result

theorem jump (physical : PhysicalROM) (left packed ordinary right : List PackingOp) (pointer : Register)
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * (left.length + 9 + packed.length)))
    (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ DispatchRun.code packed ordinary left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ DispatchRun.code packed ordinary left.length pointer ++ right).length))
    (clock : Nat) (hc : clock ≤ 3) :
    packingRun physical (left ++ DispatchRun.code packed ordinary left.length pointer ++ right) clock state =
      executeOps physical ((forwardJump (5 * (left.length + 9 + packed.length + 3 + ordinary.length))).take clock) state := by
  let target := 5 * (left.length + 9 + packed.length + 3 + ordinary.length)
  let lead := (forwardJump target).take 2
  have shape : lead ++ [.jumpIfZero .flag .fresh] = forwardJump target := rfl
  have result := AccessBridge.last_prefix physical
    (left ++ memoryClassify pointer (5 * (left.length + 9 + packed.length + 3)) ++ packed) lead (ordinary ++ right)
    (.jumpIfZero .flag .fresh) state (by simp [lead, forwardJump, StraightProgram, StraightOp])
    (by simpa only [List.length_append, memoryClassify_length] using hpc) ha
    (by rw [shape]; simpa only [DispatchRun.code, target, List.append_assoc] using hcode)
    (by rw [shape]; simpa only [DispatchRun.code, target, List.append_assoc] using hpcfit)
    clock (by change clock ≤ 3; exact hc)
  rw [shape] at result
  simpa only [DispatchRun.code, target, List.append_assoc] using result

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.DispatchPrefix
