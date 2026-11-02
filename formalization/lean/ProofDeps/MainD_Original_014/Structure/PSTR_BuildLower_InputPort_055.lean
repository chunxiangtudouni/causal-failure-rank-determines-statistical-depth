module

public import Structure.PSTR_BuildLower_InputStageRun_041
public import Structure.PSTR_BuildLower_SourceFacts_046

/-! The fixed input port consumes EVERY original in-range pointer>=3.
The stage/node split and finite row/tool indices are derived from that pointer;
the actual returned bit equals the original givenTreeROM input word. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteAST
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

theorem input_call (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) (hqpos : 0 < q)
    (left right : List PackingOp) (pointer : Register) (base heapWords a : Nat)
    (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hN : (state.heap (state.register .address)).toNat = full.length)
    (hq : (state.heap (state.register .address + BitVec.ofNat _ 1)).toNat = q)
    (hptr : (Ordinary.pointerValue state pointer).toNat = a)
    (hlower : 3 ≤ a) (hupper : a < (givenTreeROM q full).input.length)
    (hbase : (state.register .address).toNat = base)
    (cached : ∀ node : (prepareNormalization q full).indexed.NodeId,
      PA06A19PrepareBankNodeBit022.CachedWordNode full base node state.heap)
    (hroom : ∀ node : (prepareNormalization q full).indexed.NodeId,
      PA06A19PrepareBankNodeBit022.ordAddress full.length q base node.val < heapWords)
    (hheap : Fits (indexWidth 32 full.length q) heapWords)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ inputCode left.length pointer ++ right)))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * (left ++ inputCode left.length pointer ++ right).length)) :
    ∃ count ≤ 67,
      let after := packingRun (CompactControllerClaims.controllerInput q full used)
        (left ++ inputCode left.length pointer ++ right) count state
      after.register .value = BitVec.ofNat _ ((givenTreeROM q full).semantic.read .input a) ∧
        after.register .address = state.register .address ∧ after.heap = state.heap ∧
        after.pc = BitVec.ofNat _ (5 * (left.length + 87)) ∧ after.halted = false := by
  by_cases hs : a < 3 + full.length * q
  · let payload := a - 3
    have hpl : payload < full.length * q := by dsimp only [payload]; omega
    let row : Fin full.length := ⟨payload / q, (Nat.div_lt_iff_lt_mul hqpos).mpr hpl⟩
    let tool : Fin q := ⟨payload % q, Nat.mod_lt payload hqpos⟩
    have he : a = 3 + row.val * q + tool.val := by
      have hd := Nat.div_add_mod' payload q
      change payload / q * q + payload % q = payload at hd
      dsimp only [row, tool, payload] at hd ⊢
      omega
    have result := input_stage_call q full used row tool left right pointer state hpc ha hN hq
      (hptr.trans he) hcode hpcfit
    refine ⟨24, by decide, ?_⟩
    dsimp only at result ⊢
    rw [he, PA17StageMap001.givenTreeROM_stage_bit]
    exact result
  · let payload := a - (3 + full.length * q)
    have hlen := PA17QueryCounts008.givenTreeROM_input_length q full
    have hpl : payload < (prepareNormalization q full).indexed.nodes.size * q := by
      rw [hlen] at hupper
      dsimp only [payload]
      omega
    let node : (prepareNormalization q full).indexed.NodeId := ⟨payload / q, (Nat.div_lt_iff_lt_mul hqpos).mpr hpl⟩
    let tool : Fin q := ⟨payload % q, Nat.mod_lt payload hqpos⟩
    have he : a = 3 + full.length * q + (node.val * q + tool.val) := by
      have hd := Nat.div_add_mod' payload q
      change payload / q * q + payload % q = payload at hd
      dsimp only [node, tool, payload] at hd ⊢
      omega
    obtain ⟨count, hcount, result⟩ := input_node_call q full used left right pointer base heapWords node tool state
      hpc ha hN hq (hptr.trans he) hbase (cached node) (hroom node) hheap hcode hpcfit
    refine ⟨count, hcount, ?_⟩
    dsimp only at result ⊢
    refine ⟨?_, result.2.2.1, result.2.2.2.1, ?_, result.2.2.2.2.2⟩
    · have hv : (givenTreeROM q full).semantic.read .input a =
          bit (decide (tool ∈ (prepareNormalization q full).indexed.decode node)) := by
        rw [he, ← Nat.add_assoc, UniformTreeMetadataRAM.givenTreeROM_node_bit]
      rw [hv, ← result.1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [← result.2.2.2.2.1, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteAST
