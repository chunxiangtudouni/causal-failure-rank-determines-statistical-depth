module

public import Structure.PSTR_BuildLower_NodePrep_021
public import Structure.PA06_A19Prepare_BankNodeBit022

/-! The real old node-input pointer is decoded by17 actual instructions, then
the frozen A06 getter really executes. CachedWordNode is an internal producer
representation, never an extra input answer or a full-prepare caller oracle. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.NodeInput

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

def nodeBitCode (start : Nat) (pointer : Register) : List PackingOp :=
  prep pointer ++ PA06A19PrepareBankNodeBit022.programAt (start + 17)

theorem nodeBitCode_length (start : Nat) (pointer : Register) : (nodeBitCode start pointer).length = 63 := rfl

theorem nodeBitCode_getter_slice (left right : List PackingOp) (pointer : Register) :
    PA06A19PrepareBankNodeBit022.CodeAt (left ++ nodeBitCode left.length pointer ++ right) (left.length + 17) := by
  have hh := PA06A19PrepareBankNodeBit022.append_code (left ++ prep pointer) right
  simpa only [nodeBitCode, List.length_append, prep_length, List.append_assoc] using hh

theorem nodeBit_call (factor q : Nat) (full : List (Finset (Fin q))) (hf : 16 ≤ factor)
    (initialUsed : Finset (Fin q)) (left right : List PackingOp) (pointer : Register)
    (base heapWords : Nat) (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (before : WordState (indexWidth factor full.length q))
    (hpc : before.pc = BitVec.ofNat _ (5 * left.length)) (ha : before.halted = false)
    (hN : (before.heap (before.register .address)).toNat = full.length)
    (hq : (before.heap (before.register .address + BitVec.ofNat _ 1)).toNat = q)
    (hptr : (Ordinary.pointerValue before pointer).toNat =
      3 + full.length * q + (node.val * q + tool.val))
    (hbase : (before.register .address).toNat = base)
    (cached : PA06A19PrepareBankNodeBit022.CachedWordNode full base node before.heap)
    (hroom : PA06A19PrepareBankNodeBit022.ordAddress full.length q base node.val < heapWords)
    (hheap : Fits (indexWidth factor full.length q) heapWords)
    (hcode : WordsFit (indexWidth factor full.length q)
      (packingCode (left ++ nodeBitCode left.length pointer ++ right)))
    (hpcfit : Fits (indexWidth factor full.length q)
      (5 * (left ++ nodeBitCode left.length pointer ++ right).length)) :
    ∃ count ≤ 52,
      let after := packingRun (CompactControllerClaims.controllerInput q full initialUsed)
        (left ++ nodeBitCode left.length pointer ++ right) count before
      (after.register .value).toNat = bit (decide (tool ∈ (prepareNormalization q full).indexed.decode node)) ∧
        (after.register .fresh).toNat = tool.val ∧ after.register .address = before.register .address ∧
        after.heap = before.heap ∧ after.pc.toNat = 5 * (left.length + 63) ∧ after.halted = false := by
  let runtime := CompactControllerClaims.controllerInput q full initialUsed
  let containing := left ++ nodeBitCode left.length pointer ++ right
  let mid := executeOps runtime (prep pointer) before
  have hfront' :=
    prep_run runtime left (PA06A19PrepareBankNodeBit022.programAt (left.length + 17) ++ right)
      pointer (by simpa only [nodeBitCode, List.append_assoc] using hcode)
      (by simpa only [nodeBitCode, List.append_assoc] using hpcfit) before hpc ha
  have hfront : packingRun runtime containing 17 before = mid := by
    simpa only [containing, nodeBitCode, List.append_assoc] using hfront'
  have hm := prep_prefix_frame runtime pointer before (prep pointer).length
  rw [List.take_length] at hm
  have hmheap : mid.heap = before.heap := hm.1
  have hmbase : mid.register .address = before.register .address := hm.2
  have hmactive : mid.halted = false := (executeOps_halted runtime _ before).trans ha
  have hmvalue := prep_node_tool runtime pointer before full.length q node.val tool hN hq hptr
  have hmPCWord : mid.pc = BitVec.ofNat _ (5 * (left.length + 17)) := by
    have he : 5 * left.length + 85 = 5 * (left.length + 17) := by omega
    rw [prep_pc, hpc, BitVec.ofNat_add_ofNat, he]
  have hend : Fits (indexWidth factor full.length q) (5 * (left.length + 17 + 46)) := by
    apply lt_of_le_of_lt (Nat.mul_le_mul_left 5 ?_) hpcfit
    simp only [List.length_append, nodeBitCode_length]
    omega
  have hmidFit : Fits (indexWidth factor full.length q) (5 * (left.length + 17)) :=
    lt_of_le_of_lt (by omega) hend
  have hmPC : mid.pc.toNat = 5 * (left.length + 17) := by
    rw [hmPCWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmidFit]
  have hmBaseNat : (mid.register .address).toNat = base := by rw [hmbase, hbase]
  have hmCached : PA06A19PrepareBankNodeBit022.CachedWordNode full base node mid.heap := by
    rw [hmheap]
    exact cached
  obtain ⟨count, hcount, returned⟩ := PA06A19PrepareBankNodeBit022.word_query factor q full hf initialUsed
    containing (left.length + 17) (nodeBitCode_getter_slice left right pointer) base heapWords node tool
    mid hmPC hmactive hmvalue.1 hmvalue.2 hmBaseNat hmCached hroom hheap hend hcode
  dsimp only at returned
  rcases returned with ⟨hvalue, hfresh, haddr, hdata, hlastPC, hactive, _⟩
  refine ⟨17 + count, by omega, ?_⟩
  have hrun : packingRun runtime containing (17 + count) before = packingRun runtime containing count mid := by
    rw [PSTRWordSegments.run_add, hfront]
  change ((packingRun runtime containing (17 + count) before).register .value).toNat = _ ∧ _
  rw [hrun]
  refine ⟨hvalue, ?_, haddr.trans hmbase, hdata.trans hmheap, ?_, hactive⟩
  · rw [hfresh]
    exact hmvalue.2
  · simpa only [Nat.add_assoc] using hlastPC

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.NodeInput
