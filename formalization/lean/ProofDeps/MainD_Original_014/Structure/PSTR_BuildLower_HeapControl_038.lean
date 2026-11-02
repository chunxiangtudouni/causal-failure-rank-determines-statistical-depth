module

public import Structure.PSTR_BuildLower_ConcreteWrite_033

/-! Concrete heap ports return at their actual static endpoint with the
same bank base. Packed Word truncation is unrestricted; the real selected
backend lemmas discharge each code-only frame argument internally. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteHeap
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
variable {bits : Nat}

private theorem tested_base (rom : PhysicalROM) (pointer : Register) (pc : Nat) (state : WordState bits) :
    (executeOps rom (memoryClassify pointer pc) state).register .address = state.register .address := by
  have hh := (memoryClassify_prefix_frame rom pointer pc state (memoryClassify pointer pc).length).2
  simpa only [List.take_length] using hh

private theorem result_pc (rom : PhysicalROM) (left packed ordinary : List PackingOp) (pointer : Register)
    (ho : StraightProgram ordinary) (state : WordState bits) :
    (DispatchRun.result rom left packed ordinary pointer state).pc =
      BitVec.ofNat bits (5 * (left.length + packed.length + ordinary.length + 12)) := by
  by_cases hg : DispatchRun.ordinaryCase pointer state
  · have raw : (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat ≤
        (Ordinary.pointerValue state pointer).toNat := hg
    simp only [DispatchRun.result, hg, ite_true]
    rw [executeOps_pc rom ordinary _ ho, memoryClassify_pc, ite_eq_left raw, BitVec.ofNat_add_ofNat]
    congr 1
    omega
  · simp only [DispatchRun.result, hg, ite_false, forwardJump_pc]
    congr 1
    omega

private theorem result_base (rom : PhysicalROM) (left packed ordinary : List PackingOp) (pointer : Register)
    (hp : ∀ state : WordState bits, (executeOps rom packed state).register .address = state.register .address)
    (ho : ∀ state : WordState bits, (executeOps rom ordinary state).register .address = state.register .address)
    (state : WordState bits) :
    (DispatchRun.result rom left packed ordinary pointer state).register .address = state.register .address := by
  by_cases hg : DispatchRun.ordinaryCase pointer state
  · simp only [DispatchRun.result, hg, ite_true, ho, tested_base]
  · simp only [DispatchRun.result, hg, ite_false]
    change (executeOps rom packed _).register .address = _
    rw [hp, tested_base]

private theorem result_active (rom : PhysicalROM) (left packed ordinary : List PackingOp) (pointer : Register)
    (state : WordState bits) :
    (DispatchRun.result rom left packed ordinary pointer state).halted = state.halted := by
  unfold DispatchRun.result
  split <;> simp only [executeOps_halted]

theorem read_call_control (rom : PhysicalROM) (left right : List PackingOp) (pointer : Register)
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ read left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ read left.length pointer ++ right).length)) :
    let count := DispatchRun.steps PA06A19PrepareBankPacked021.read (Ordinary.read pointer) pointer state
    let after := packingRun rom (left ++ read left.length pointer ++ right) count state
    after.pc = BitVec.ofNat bits (5 * (left.length + 45)) ∧ after.halted = false ∧
      after.register .address = state.register .address := by
  have hc : DispatchRun.code PA06A19PrepareBankPacked021.read (Ordinary.read pointer) left.length pointer =
      read left.length pointer := DispatchRun.code_read _ _ _
  have hrun := DispatchRun.run rom left PA06A19PrepareBankPacked021.read (Ordinary.read pointer) right pointer
    PA06A19PrepareBankPacked021.read_straight (Ordinary.read_straight pointer)
    (by rwa [hc]) (by rwa [hc]) state hpc ha
  dsimp only
  rw [hc] at hrun
  rw [hrun]
  refine ⟨?_, (result_active rom left _ _ pointer state).trans ha, ?_⟩
  · simpa only [PA06A19PrepareBankPacked021.read_length, Ordinary.read_length] using
      result_pc rom left PA06A19PrepareBankPacked021.read (Ordinary.read pointer) pointer (Ordinary.read_straight pointer) state
  · apply result_base
    · exact PA06A19PrepareBankPacked021.read_address rom
    · intro current
      have hh := Ordinary.read_prefix_base rom pointer current (Ordinary.read pointer).length
      simpa only [List.take_length] using hh

theorem write_call_control (rom : PhysicalROM) (left right : List PackingOp) (pointer : Register)
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ write left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ write left.length pointer ++ right).length)) :
    let packed := PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer)
    let count := DispatchRun.steps packed (Ordinary.write pointer) pointer state
    let after := packingRun rom (left ++ write left.length pointer ++ right) count state
    after.pc = BitVec.ofNat bits (5 * (left.length + 96)) ∧ after.halted = false ∧
      after.register .address = state.register .address := by
  have hrun := write_call rom left right pointer state hcode hpcfit hpc ha
  dsimp only at hrun ⊢
  rw [hrun.2]
  refine ⟨?_, (result_active rom left _ _ pointer state).trans ha, ?_⟩
  · simpa only [PA06A19PrepareBankPacked021.safeWrite_length, Ordinary.write_length] using
      result_pc rom left (PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer)) (Ordinary.write pointer) pointer (Ordinary.write_straight pointer) state
  · apply result_base
    · exact PA06A19PrepareBankPacked021.safeWrite_address _ rom
    · intro current
      have hh := Ordinary.write_prefix_base rom pointer current (Ordinary.write pointer).length
      simpa only [List.take_length] using hh

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteHeap
