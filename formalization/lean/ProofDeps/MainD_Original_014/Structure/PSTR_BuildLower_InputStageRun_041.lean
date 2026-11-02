module

public import Structure.PSTR_BuildLower_InputNodeRun_040

/-! Actual input-dispatch stage branch, including the real header-size
adjustment and final jump. The24 clocks are executed, not a supplied bill. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteAST
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

private theorem input_scale_fits (N q : Nat) : Fits (indexWidth 32 N q) (N * q + 3) := by
  apply fits_indexWidth_of_lt_power
  let B := N + q + 2
  have hb : 1 ≤ B := by dsimp only [B]; omega
  have hh : N * q + 3 < B ^ 2 := by
    dsimp only [B]
    simp only [pow_two]
    nlinarith [Nat.zero_le (N * N), Nat.zero_le (q * q), Nat.zero_le (N * q)]
  exact hh.trans_le (Nat.pow_le_pow_right hb (by decide : 2 ≤ 32))

private theorem inputJump_run {bits : Nat} (rom : PhysicalROM) (left right : List PackingOp) (pointer : Register)
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (left.length + 21))) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ inputCode left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ inputCode left.length pointer ++ right).length)) :
    packingRun rom (left ++ inputCode left.length pointer ++ right) 3 state =
      executeOps rom (forwardJump (5 * (left.length + 87))) state := by
  let jump := forwardJump (5 * (left.length + 87))
  let lead := jump.take 2
  have hlen : lead.length = 2 := rfl
  let startCode := left ++ inputHead (5 * (left.length + 24)) pointer ++ StageInput.code pointer
  have hs : startCode.length = left.length + 21 := by
    simp only [startCode, List.length_append, inputHead_length, StageInput.code_length]
  apply PSTRWordSegments.segment_last rom _ lead (.jumpIfZero .flag .fresh) (left.length + 21)
    (by simp only [List.length_append, inputCode_length, hlen]; omega) ?_ ?_ ?_ hcode hpcfit state hp ha
  · intro index hi
    have hh := PA17UniformGenerator035a.segment_index startCode jump
      (NodeInput.nodeBitCode (left.length + 24) pointer ++ right) index (by rw [hlen] at hi; change index < 3; omega)
    simp only [hs] at hh
    simpa only [startCode, jump, inputCode, List.append_assoc, lead, List.getElem_take] using hh
  · have hh := PA17UniformGenerator035a.segment_index startCode jump
      (NodeInput.nodeBitCode (left.length + 24) pointer ++ right) 2 (by change 2 < 3; decide)
    have he : jump[2]'(by change 2 < 3; decide) = PackingOp.jumpIfZero .flag .fresh := rfl
    simp only [hs, he] at hh
    simpa only [startCode, jump, inputCode, List.append_assoc, hlen] using hh
  · simp [lead, jump, forwardJump, StraightProgram, StraightOp]

private theorem jump_data {bits : Nat} (rom : PhysicalROM) (pc : Nat) (state : WordState bits) :
    (executeOps rom (forwardJump pc) state).register .value = state.register .value ∧
      (executeOps rom (forwardJump pc) state).register .address = state.register .address ∧
      (executeOps rom (forwardJump pc) state).heap = state.heap := ⟨rfl, rfl, rfl⟩

theorem input_stage_call (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (row : Fin full.length) (tool : Fin q) (left right : List PackingOp) (pointer : Register)
    (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc = BitVec.ofNat _ (5 * left.length)) (ha : before.halted = false)
    (hN : (before.heap (before.register .address)).toNat = full.length)
    (hq : (before.heap (before.register .address + BitVec.ofNat _ 1)).toNat = q)
    (hptr : (Ordinary.pointerValue before pointer).toNat = 3 + row.val * q + tool.val)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ inputCode left.length pointer ++ right)))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * (left ++ inputCode left.length pointer ++ right).length)) :
    let after := packingRun (CompactControllerClaims.controllerInput q full used)
      (left ++ inputCode left.length pointer ++ right) 24 before
    after.register .value = BitVec.ofNat _ (bit (decide (tool ∈ full[row.val]))) ∧
      after.register .address = before.register .address ∧ after.heap = before.heap ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + 87)) ∧ after.halted = false := by
  let runtime := CompactControllerClaims.controllerInput q full used
  let containing := left ++ inputCode left.length pointer ++ right
  let mid := executeOps runtime (inputHead (5 * (left.length + 24)) pointer) before
  let stageLeft := left ++ inputHead (5 * (left.length + 24)) pointer
  let stageRight := forwardJump (5 * (left.length + 87)) ++ NodeInput.nodeBitCode (left.length + 24) pointer ++ right
  let done := executeOps runtime (StageInput.code pointer) mid
  have stageLength : stageLeft.length = left.length + 15 := by simp only [stageLeft, List.length_append, inputHead_length]
  have shape : stageLeft ++ StageInput.code pointer ++ stageRight = containing := by
    simp only [stageLeft, stageRight, containing, inputCode, List.append_assoc]
  have front : packingRun runtime containing 15 before = mid := inputHead_run runtime left right pointer before hpc ha hcode hpcfit
  have framed := inputHead_prefix_frame runtime (5 * (left.length + 24)) pointer before
    (inputHead (5 * (left.length + 24)) pointer).length
  rw [List.take_length] at framed
  have midHeap : mid.heap = before.heap := framed.1
  have midBase : mid.register .address = before.register .address := framed.2
  have midActive : mid.halted = false := (executeOps_halted runtime _ before).trans ha
  have hrow : (row.val + 1) * q ≤ full.length * q := Nat.mul_le_mul_right q row.isLt
  rw [Nat.add_mul, Nat.one_mul] at hrow
  have notChosen : ¬full.length * q + 3 ≤ (Ordinary.pointerValue before pointer).toNat := by rw [hptr]; have ht := tool.isLt; omega
  have midPC : mid.pc = BitVec.ofNat _ (5 * stageLeft.length) := by
    have he : 5 * left.length + 75 = 5 * (left.length + 15) := by omega
    change (executeOps runtime (inputHead (5 * (left.length + 24)) pointer) before).pc = _
    rw [inputHead_pc runtime _ pointer full.length q before hN hq (input_scale_fits full.length q),
      ite_eq_right notChosen, hpc, BitVec.ofNat_add_ofNat, he, stageLength]
  have midPointer : (Ordinary.pointerValue mid pointer).toNat = 3 + row.val * q + tool.val := by
    simp only [Ordinary.pointerValue, midHeap, midBase]
    exact hptr
  have hstage := StageInput.run runtime pointer stageLeft stageRight mid midPC midActive
    (by rwa [shape]) (by rwa [shape])
  rw [shape] at hstage
  have doneValue := StageInput.original_stage_value q full used row tool pointer mid midPointer
  have sf := StageInput.prefix_frame runtime pointer mid (StageInput.code pointer).length
  rw [List.take_length] at sf
  have doneHeap : done.heap = before.heap := sf.1.trans midHeap
  have doneBase : done.register .address = before.register .address := sf.2.trans midBase
  have doneActive : done.halted = false := (executeOps_halted runtime _ mid).trans midActive
  have donePC : done.pc = BitVec.ofNat _ (5 * (left.length + 21)) := by
    have he : 5 * (left.length + 15) + 5 * 6 = 5 * (left.length + 21) := by omega
    rw [executeOps_pc runtime _ mid (StageInput.code_straight pointer), StageInput.code_length,
      midPC, stageLength, BitVec.ofNat_add_ofNat, he]
  have hjump := inputJump_run runtime left right pointer done donePC doneActive hcode hpcfit
  change ((packingRun runtime containing 24 before).register .value) = _ ∧ _
  have hcount : 24 = 15 + 6 + 3 := rfl
  rw [hcount, PSTRWordSegments.run_add, PSTRWordSegments.run_add, front, hstage, hjump]
  have jf := jump_data runtime (5 * (left.length + 87)) done
  exact ⟨jf.1.trans doneValue, jf.2.1.trans doneBase, jf.2.2.trans doneHeap,
    forwardJump_pc runtime _ done, (executeOps_halted runtime _ done).trans doneActive⟩

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteAST
