module

public import Structure.PSTR_BuildLower_ConcreteAST_031

/-! Actual input-dispatch node branch: the real15-op classification jumps
past stage code, then the decoded pointer/raw-cache getter runs at its real
containing-code position. No supplied bit/run equality is a premise. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteAST
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

theorem input_node_call (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (left right : List PackingOp) (pointer : Register) (base heapWords : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc = BitVec.ofNat _ (5 * left.length)) (ha : before.halted = false)
    (hN : (before.heap (before.register .address)).toNat = full.length)
    (hq : (before.heap (before.register .address + BitVec.ofNat _ 1)).toNat = q)
    (hptr : (Ordinary.pointerValue before pointer).toNat = 3 + full.length * q + (node.val * q + tool.val))
    (hbase : (before.register .address).toNat = base)
    (cached : PA06A19PrepareBankNodeBit022.CachedWordNode full base node before.heap)
    (hroom : PA06A19PrepareBankNodeBit022.ordAddress full.length q base node.val < heapWords)
    (hheap : Fits (indexWidth 32 full.length q) heapWords)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ inputCode left.length pointer ++ right)))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * (left ++ inputCode left.length pointer ++ right).length)) :
    ∃ count ≤ 67,
      let after := packingRun (CompactControllerClaims.controllerInput q full used)
        (left ++ inputCode left.length pointer ++ right) count before
      (after.register .value).toNat = bit (decide (tool ∈ (prepareNormalization q full).indexed.decode node)) ∧
        (after.register .fresh).toNat = tool.val ∧ after.register .address = before.register .address ∧
        after.heap = before.heap ∧ after.pc.toNat = 5 * (left.length + 87) ∧ after.halted = false := by
  let runtime := CompactControllerClaims.controllerInput q full used
  let containing := left ++ inputCode left.length pointer ++ right
  let mid := executeOps runtime (inputHead (5 * (left.length + 24)) pointer) before
  let nodeLeft := left ++ inputHead (5 * (left.length + 24)) pointer ++ StageInput.code pointer ++
    forwardJump (5 * (left.length + 87))
  have nodeLength : nodeLeft.length = left.length + 24 := by
    simp only [nodeLeft, List.length_append, inputHead_length, StageInput.code_length, forwardJump_length]
  have shape : nodeLeft ++ NodeInput.nodeBitCode nodeLeft.length pointer ++ right = containing := by
    rw [nodeLength]
    simp only [nodeLeft, containing, inputCode, List.append_assoc]
  have front : packingRun runtime containing 15 before = mid :=
    inputHead_run runtime left right pointer before hpc ha hcode hpcfit
  have framed := inputHead_prefix_frame runtime (5 * (left.length + 24)) pointer before
    (inputHead (5 * (left.length + 24)) pointer).length
  rw [List.take_length] at framed
  have midHeap : mid.heap = before.heap := framed.1
  have midBase : mid.register .address = before.register .address := framed.2
  have midActive : mid.halted = false := (executeOps_halted runtime _ before).trans ha
  have small : Fits (indexWidth 32 full.length q) (full.length * q + 3) := by
    have hh := (Ordinary.pointerValue before pointer).isLt
    rw [hptr] at hh
    exact lt_of_le_of_lt (by omega) hh
  have chosen : full.length * q + 3 ≤ (Ordinary.pointerValue before pointer).toNat := by rw [hptr]; omega
  have midPC : mid.pc = BitVec.ofNat _ (5 * nodeLeft.length) := by
    change (executeOps runtime (inputHead (5 * (left.length + 24)) pointer) before).pc = _
    rw [inputHead_pc runtime _ pointer full.length q before hN hq small, ite_eq_left chosen, nodeLength]
  have midN : (mid.heap (mid.register .address)).toNat = full.length := by rw [midHeap, midBase]; exact hN
  have midQ : (mid.heap (mid.register .address + BitVec.ofNat _ 1)).toNat = q := by rw [midHeap, midBase]; exact hq
  have midPointer : (Ordinary.pointerValue mid pointer).toNat = 3 + full.length * q + (node.val * q + tool.val) := by
    simp only [Ordinary.pointerValue, midHeap, midBase]
    exact hptr
  obtain ⟨count, hcount, result⟩ := NodeInput.nodeBit_call_framed 32 q full (by decide) used nodeLeft right pointer
    base heapWords node tool mid midPC midActive midN midQ midPointer (by rwa [midBase])
    (by rwa [midHeap]) hroom hheap (by rwa [shape]) (by rwa [shape])
  dsimp only at result
  rw [shape] at result
  rcases result with ⟨hv, hf, hb, hh, hp, hx, _frames, _access⟩
  refine ⟨15 + count, by omega, ?_⟩
  change ((packingRun runtime containing (15 + count) before).register .value).toNat = _ ∧ _
  rw [PSTRWordSegments.run_add, front]
  refine ⟨hv, hf, hb.trans midBase, hh.trans midHeap, ?_, hx⟩
  simpa only [nodeLength, Nat.add_assoc] using hp

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteAST
