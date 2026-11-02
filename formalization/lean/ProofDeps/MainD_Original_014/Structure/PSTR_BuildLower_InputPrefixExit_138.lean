module

public import Structure.PSTR_BuildLower_InputNodePrefix_135
public import Structure.PSTR_BuildLower_InputStagePrefix_137
public import Structure.PSTR_BuildLower_ReadPrefixExit_130
public import Structure.PSTR_BuildLower_ConcreteReadExits_067

/-! Every ORIGINAL in-range input pointer>=3 constructs ONE actual prefix
read witness. Stage24 and head15+node paths retain their own SAME clock,
original givenTreeROM value and real readonly/fetch/access certificates. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem input_read_prefix_exit (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) (hq : 0 < q)
    (pointer : Register) (logical : State) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (bounded : GlobalCapacity.Bounded q full state.heap)
    (hptr : Fits (bits q full) (logical.register pointer))
    (hlower : 3 ≤ logical.register pointer) (hupper : logical.register pointer < (givenTreeROM q full).input.length)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ ConcreteAST.inputCode left.length pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ ConcreteAST.inputCode left.length pointer ++ right).length)) :
    Nonempty (ReadPrefixExit (allocated q full) (CompactControllerClaims.controllerInput q full used) left
      (ConcreteAST.inputCode left.length pointer) right state
      ((givenTreeROM q full).semantic.read .input (logical.register pointer)) 67) := by
  let a := logical.register pointer
  have hp : (Ordinary.pointerValue state pointer).toNat = a := pointer_nat q full logical state hrep pointer hptr
  by_cases hs : a < 3 + full.length * q
  · let payload := a - 3
    have hpl : payload < full.length * q := by dsimp only [payload, a] at *; omega
    let row : Fin full.length := ⟨payload / q, (Nat.div_lt_iff_lt_mul hq).mpr hpl⟩
    let tool : Fin q := ⟨payload % q, Nat.mod_lt payload hq⟩
    have he : a = 3 + row.val * q + tool.val := by
      have hd := Nat.div_add_mod' payload q
      change payload / q * q + payload % q = payload at hd
      dsimp only [row, tool, payload, a] at hd ⊢
      omega
    have result := ConcreteAST.input_stage_prefix_call q full hq used row tool left right pointer state
      hrep.address data bounded hpc ha (hp.trans he) hcode hpcfit
    refine ⟨{
      toReadExit := {
        steps := 24
        bounded := by decide
        value := ?_
        heap := result.2.2.1
        address := result.2.1
        pc := ?_
        active := result.2.2.2.2.1 }
      readonly := result.2.2.2.2.2.1
      safe := result.2.2.2.2.2.2 }⟩
    · have valueEq : (givenTreeROM q full).semantic.read .input (logical.register pointer) =
          bit (decide (tool ∈ full[row.val])) := by
        change (givenTreeROM q full).semantic.read .input a = _
        rw [he, PA17StageMap001.givenTreeROM_stage_bit]
      rw [valueEq]
      exact result.1
    · simpa only [ConcreteAST.inputCode_length] using result.2.2.2.1
  · let payload := a - (3 + full.length * q)
    have hlen := PA17QueryCounts008.givenTreeROM_input_length q full
    have hpl : payload < (prepareNormalization q full).indexed.nodes.size * q := by
      rw [hlen] at hupper
      dsimp only [payload, a] at *
      omega
    let node : (prepareNormalization q full).indexed.NodeId := ⟨payload / q, (Nat.div_lt_iff_lt_mul hq).mpr hpl⟩
    let tool : Fin q := ⟨payload % q, Nat.mod_lt payload hq⟩
    have he : a = 3 + full.length * q + (node.val * q + tool.val) := by
      have hd := Nat.div_add_mod' payload q
      change payload / q * q + payload % q = payload at hd
      dsimp only [node, tool, payload, a] at hd ⊢
      omega
    obtain ⟨count, hcount, result⟩ := ConcreteAST.input_node_prefix_call q full hq used left right pointer node tool state
      hrep.address data bounded hpc ha (hp.trans he) hcode hpcfit
    refine ⟨{
      toReadExit := {
        steps := count
        bounded := hcount
        value := ?_
        heap := result.2.2.2.1
        address := result.2.2.1
        pc := ?_
        active := result.2.2.2.2.2.1 }
      readonly := result.2.2.2.2.2.2.1
      safe := result.2.2.2.2.2.2.2 }⟩
    · have valueEq : (givenTreeROM q full).semantic.read .input (logical.register pointer) =
          bit (decide (tool ∈ (prepareNormalization q full).indexed.decode node)) := by
        change (givenTreeROM q full).semantic.read .input a = _
        rw [he, ← Nat.add_assoc, UniformTreeMetadataRAM.givenTreeROM_node_bit]
      rw [valueEq, ← result.1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [ConcreteAST.inputCode_length, ← result.2.2.2.2.1, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
