module

public import Structure.PSTR_BuildLower_InputPrefixes_134
public import Structure.PSTR_BuildLower_RuntimeFields_065

/-! Strengthen the EXISTING040 node branch at its genuine witness: real
head15 then actual027 node getter, retaining its already proved prefix
frames/access rather than discarding them. Same whole/run, no clock reset. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteAST
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem input_node_prefix_call (q : Nat) (full : List (Finset (Fin q))) (hqpos : 0 < q) (used : Finset (Fin q))
    (left right : List PackingOp) (pointer : Register)
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (before : WordState (bits q full)) (base : before.register .address = BitVec.ofNat _ (controlBase q full))
    (data : RuntimeData.Data q full before.heap) (bounded : GlobalCapacity.Bounded q full before.heap)
    (hpc : before.pc = BitVec.ofNat _ (5 * left.length)) (ha : before.halted = false)
    (hptr : (Ordinary.pointerValue before pointer).toNat = 3 + full.length * q + (node.val * q + tool.val))
    (hcode : WordsFit (bits q full) (packingCode (left ++ inputCode left.length pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ inputCode left.length pointer ++ right).length)) :
    ∃ count ≤ 67,
      let runtime := CompactControllerClaims.controllerInput q full used
      let whole := left ++ inputCode left.length pointer ++ right
      let after := packingRun runtime whole count before
      (after.register .value).toNat = bit (decide (tool ∈ (prepareNormalization q full).indexed.decode node)) ∧
        (after.register .fresh).toNat = tool.val ∧ after.register .address = before.register .address ∧
        after.heap = before.heap ∧ after.pc.toNat = 5 * (left.length + 87) ∧ after.halted = false ∧
        (∀ clock ≤ count, (packingRun runtime whole clock before).heap = before.heap) ∧
        TraceAccess.Safe (allocated q full) runtime whole before count := by
  let runtime := CompactControllerClaims.controllerInput q full used
  let whole := left ++ inputCode left.length pointer ++ right
  let mid := executeOps runtime (inputHead (5 * (left.length + 24)) pointer) before
  let nodeLeft := left ++ inputHead (5 * (left.length + 24)) pointer ++ StageInput.code pointer ++
    forwardJump (5 * (left.length + 87))
  have nodeLength : nodeLeft.length = left.length + 24 := by
    simp only [nodeLeft, List.length_append, inputHead_length, StageInput.code_length, forwardJump_length]
  have shape : nodeLeft ++ NodeInput.nodeBitCode nodeLeft.length pointer ++ right = whole := by
    rw [nodeLength]
    simp only [nodeLeft, whole, inputCode, List.append_assoc]
  have front : packingRun runtime whole 15 before = mid := inputHead_run runtime left right pointer before hpc ha hcode hpcfit
  have frame := inputHead_prefix_frame runtime (5 * (left.length + 24)) pointer before
    (inputHead (5 * (left.length + 24)) pointer).length
  rw [List.take_length] at frame
  have midHeap : mid.heap = before.heap := frame.1
  have midBase : mid.register .address = before.register .address := frame.2
  have midActive : mid.halted = false := (executeOps_halted runtime _ before).trans ha
  have hN := RuntimeData.Data.stages_nat q full before data base
  have hq := RuntimeData.Data.tools_nat q full before data base
  have small : Fits (bits q full) (full.length * q + 3) := by
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
  have baseNat : (before.register .address).toNat = controlBase q full := by
    have hf : Fits (bits q full) (controlBase q full) := by
      simpa only [Nat.add_zero] using bank_offset_fits q full hqpos 0 (by decide)
    rw [base, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf]
  obtain ⟨count, hcount, result⟩ := NodeInput.nodeBit_call_framed 32 q full (by decide) used nodeLeft right pointer
    (controlBase q full) (allocated q full) node tool mid midPC midActive midN midQ midPointer
    (by rwa [midBase]) (by rw [midHeap]; exact data.cached node) (ord_room q full node)
    (allocation_fits q full hqpos) (by rwa [shape]) (by rwa [shape])
  dsimp only at result
  rw [shape] at result
  rcases result with ⟨hv, hfresh, hb, hh, hp, hx, frames, accesses⟩
  have frontSafe : TraceAccess.Safe (allocated q full) runtime whole before 15 :=
    (InputPrefixes.head_resources q full hqpos runtime left right pointer before base bounded hpc ha hcode hpcfit).2
  have backSafe : TraceAccess.Safe (allocated q full) runtime whole mid count := by
    intro clock hc
    have here := accesses clock hc
    exact ⟨here.1, here.2.2.1, here.2.2.2⟩
  have same : packingRun runtime whole (15 + count) before = packingRun runtime whole count mid := by
    rw [PSTRWordSegments.run_add, front]
  refine ⟨15 + count, by omega, ?_⟩
  dsimp only
  rw [same]
  refine ⟨hv, hfresh, hb.trans midBase, hh.trans midHeap, ?_, hx, ?_, ?_⟩
  · simpa only [nodeLength, Nat.add_assoc] using hp
  · intro clock hc
    by_cases first : clock ≤ 15
    · rw [InputPrefixes.head runtime left right pointer before hpc ha hcode hpcfit clock first]
      exact (inputHead_prefix_frame runtime _ pointer before clock).1
    · have split : clock = 15 + (clock - 15) := by omega
      rw [split, PSTRWordSegments.run_add, front]
      exact ((frames (clock - 15) (by omega)).1).trans midHeap
  · exact TraceAccess.add (allocated q full) runtime whole before 15 count frontSafe (by rw [front]; exact backSafe)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteAST
