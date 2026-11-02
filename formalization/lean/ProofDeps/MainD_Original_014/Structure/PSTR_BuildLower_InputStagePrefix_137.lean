module

public import Structure.PSTR_BuildLower_InputJumpResources_136
public import Structure.PSTR_BuildLower_RuntimeFields_065
public import Structure.PSTR_BuildLower_InputStageRun_041

/-! Existing041 source/value endpoint is EXACT24. Its actual head15, real
stage6 and realjump3 supply readonly/access at those SAME clocks. No
independently selected existential count or source history is identified. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteAST
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem input_stage_prefix_call (q : Nat) (full : List (Finset (Fin q))) (hqpos : 0 < q) (used : Finset (Fin q))
    (row : Fin full.length) (tool : Fin q) (left right : List PackingOp) (pointer : Register)
    (before : WordState (bits q full)) (base : before.register .address = BitVec.ofNat _ (controlBase q full))
    (data : RuntimeData.Data q full before.heap) (bounded : GlobalCapacity.Bounded q full before.heap)
    (hpc : before.pc = BitVec.ofNat _ (5 * left.length)) (ha : before.halted = false)
    (hptr : (Ordinary.pointerValue before pointer).toNat = 3 + row.val * q + tool.val)
    (hcode : WordsFit (bits q full) (packingCode (left ++ inputCode left.length pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ inputCode left.length pointer ++ right).length)) :
    let runtime := CompactControllerClaims.controllerInput q full used
    let whole := left ++ inputCode left.length pointer ++ right
    let after := packingRun runtime whole 24 before
    after.register .value = BitVec.ofNat _ (bit (decide (tool ∈ full[row.val]))) ∧
      after.register .address = before.register .address ∧ after.heap = before.heap ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + 87)) ∧ after.halted = false ∧
      (∀ clock ≤ 24, (packingRun runtime whole clock before).heap = before.heap) ∧
      TraceAccess.Safe (allocated q full) runtime whole before 24 := by
  let runtime := CompactControllerClaims.controllerInput q full used
  let whole := left ++ inputCode left.length pointer ++ right
  let mid := executeOps runtime (inputHead (5 * (left.length + 24)) pointer) before
  let stageLeft := left ++ inputHead (5 * (left.length + 24)) pointer
  let stageRight := forwardJump (5 * (left.length + 87)) ++ NodeInput.nodeBitCode (left.length + 24) pointer ++ right
  let done := executeOps runtime (StageInput.code pointer) mid
  have hN := RuntimeData.Data.stages_nat q full before data base
  have hq := RuntimeData.Data.tools_nat q full before data base
  have endpoint := input_stage_call q full used row tool left right pointer before hpc ha hN hq hptr hcode hpcfit
  have stageLength : stageLeft.length = left.length + 15 := by simp only [stageLeft, List.length_append, inputHead_length]
  have shape : stageLeft ++ StageInput.code pointer ++ stageRight = whole := by
    simp only [stageLeft, stageRight, whole, inputCode, List.append_assoc]
  have front : packingRun runtime whole 15 before = mid := inputHead_run runtime left right pointer before hpc ha hcode hpcfit
  have frame := inputHead_prefix_frame runtime (5 * (left.length + 24)) pointer before
    (inputHead (5 * (left.length + 24)) pointer).length
  rw [List.take_length] at frame
  have midHeap : mid.heap = before.heap := frame.1
  have midBase : mid.register .address = before.register .address := frame.2
  have midActive : mid.halted = false := (executeOps_halted runtime _ before).trans ha
  have hm : (row.val + 1) * q ≤ full.length * q := Nat.mul_le_mul_right q row.isLt
  rw [Nat.add_mul, Nat.one_mul] at hm
  have notChosen : ¬full.length * q + 3 ≤ (Ordinary.pointerValue before pointer).toNat := by
    rw [hptr]
    have ht := tool.isLt
    omega
  have small : Fits (bits q full) (full.length * q + 3) := by
    apply fits_indexWidth_of_lt_power
    let B := full.length + q + 2
    have hB : 1 ≤ B := by dsimp only [B]; omega
    have hh : full.length * q + 3 < B ^ 2 := by
      dsimp only [B]
      simp only [pow_two]
      nlinarith [Nat.zero_le (full.length * full.length), Nat.zero_le (q * q), Nat.zero_le (full.length * q)]
    exact hh.trans_le (Nat.pow_le_pow_right hB (by decide : 2 ≤ 32))
  have midPC : mid.pc = BitVec.ofNat _ (5 * stageLeft.length) := by
    have scalar : 5 * left.length + 75 = 5 * (left.length + 15) := by omega
    rw [inputHead_pc runtime _ pointer full.length q before hN hq small,
      ite_eq_right notChosen, hpc, BitVec.ofNat_add_ofNat, scalar, stageLength]
  have midPointer : (Ordinary.pointerValue mid pointer).toNat = 3 + row.val * q + tool.val := by
    simp only [Ordinary.pointerValue, midHeap, midBase]
    exact hptr
  have stageRun := StageInput.run runtime pointer stageLeft stageRight mid midPC midActive
    (by rwa [shape]) (by rwa [shape])
  rw [shape] at stageRun
  have stageFrame := StageInput.prefix_frame runtime pointer mid (StageInput.code pointer).length
  rw [List.take_length] at stageFrame
  have doneHeap : done.heap = before.heap := stageFrame.1.trans midHeap
  have doneActive : done.halted = false := (executeOps_halted runtime _ mid).trans midActive
  have donePC : done.pc = BitVec.ofNat _ (5 * (left.length + 21)) := by
    have scalar : 5 * (left.length + 15) + 5 * 6 = 5 * (left.length + 21) := by omega
    rw [executeOps_pc runtime _ mid (StageInput.code_straight pointer), StageInput.code_length,
      midPC, stageLength, BitVec.ofNat_add_ofNat, scalar]
  have actual21 : packingRun runtime whole 21 before = done := by
    have scalar : 21 = 15 + 6 := rfl
    rw [scalar, PSTRWordSegments.run_add, front, stageRun]
  have headResources := InputPrefixes.head_resources q full hqpos runtime left right pointer before base bounded hpc ha hcode hpcfit
  have stageResources := StageResources.actual_resources q full hqpos used row tool pointer mid (midBase.trans base)
    (by rw [midHeap]; exact bounded) midPointer stageLeft stageRight midPC midActive
    (by rwa [shape]) (by rwa [shape])
  rw [shape] at stageResources
  have jumpResources := InputPrefixes.jump_resources q full runtime left right pointer done
    (by rw [doneHeap]; exact bounded) donePC doneActive hcode hpcfit
  refine ⟨endpoint.1, endpoint.2.1, endpoint.2.2.1, endpoint.2.2.2.1, endpoint.2.2.2.2, ?_, ?_⟩
  · intro clock hc
    by_cases first : clock ≤ 15
    · rw [InputPrefixes.head runtime left right pointer before hpc ha hcode hpcfit clock first]
      exact (inputHead_prefix_frame runtime _ pointer before clock).1
    · by_cases second : clock ≤ 21
      · have split : clock = 15 + (clock - 15) := by omega
        rw [split, PSTRWordSegments.run_add, front]
        rw [InputPrefixes.stage runtime left right pointer mid
          (by simpa only [stageLength] using midPC) midActive hcode hpcfit (clock - 15) (by omega)]
        exact ((StageInput.prefix_frame runtime pointer mid (clock - 15)).1).trans midHeap
      · have split : clock = 21 + (clock - 21) := by omega
        rw [split, PSTRWordSegments.run_add, actual21,
          InputPrefixes.jump runtime left right pointer done donePC doneActive hcode hpcfit (clock - 21) (by omega)]
        have frameJump (c : Nat) (hc : c ≤ 3) :
            (executeOps runtime ((forwardJump (5 * (left.length + 87))).take c) done).heap = done.heap := by
          interval_cases c <;> rfl
        exact (frameJump (clock - 21) (by omega)).trans doneHeap
  · have first21 := TraceAccess.add (allocated q full) runtime whole before 15 6 headResources.2
      (by rw [front]; exact stageResources.2)
    exact TraceAccess.add (allocated q full) runtime whole before 21 3 first21 (by rw [actual21]; exact jumpResources.2)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteAST
