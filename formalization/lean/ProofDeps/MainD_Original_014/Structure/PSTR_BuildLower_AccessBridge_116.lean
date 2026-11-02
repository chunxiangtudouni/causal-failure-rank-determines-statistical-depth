module

public import Structure.PSTR_BuildLower_SourceRep_048
public import Structure.PSTR_BuildLower_CounterAccess_037

/-! Real fetch/decode/access for a concrete straight segment. Local primitive
room is proved on its actual Word instruction prefixes and transported to
the SAME containing packingRun. No separate machine/run equality or supplied
whole-builder performance premise is used. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.AccessBridge
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawTreePreprocessingClaims PA17PackedTranslator034
variable {bits : Nat}

theorem straight_safe (physical : PhysicalROM) (left block right : List PackingOp) (heapWords : Nat)
    (state : WordState bits) (straight : StraightProgram block)
    (localSafe : PackedAccessSafe heapWords physical block state)
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ block ++ right)))
    (hpcfit : Fits bits (5 * (left ++ block ++ right).length)) :
    ∀ count < block.length,
      let current := packingRun physical (left ++ block ++ right) count state
      current.halted = false ∧ current.pc.toNat + 4 < (packingCode (left ++ block ++ right)).length ∧
        ∃ op, PackingOp.decode (fetch (left ++ block ++ right) current) = some op ∧
          packingAccessFits physical heapWords current op := by
  intro count hc
  rw [SourceRep.straight_prefix physical left block right state straight hcode hpcfit hpc ha count hc.le]
  have hlen : (block.take count).length = count := List.length_take_of_le hc.le
  have prefixStraight : StraightProgram (block.take count) := fun op hm => straight op (List.mem_of_mem_take hm)
  have pc : (executeOps physical (block.take count) state).pc.toNat = 5 * (left.length + count) := by
    rw [executeOps_pc _ _ _ prefixStraight, hlen, hpc, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    have arithmetic : 5 * left.length + 5 * count = 5 * (left.length + count) := by omega
    rw [arithmetic, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mul_le_mul_left 5 ?_) hpcfit)]
    simp only [List.length_append]
    omega
  have indexBound : left.length + count < (left ++ block ++ right).length := by
    simp only [List.length_append]
    omega
  refine ⟨(executeOps_halted physical _ state).trans ha, ?_, block[count], ?_, localSafe count hc⟩
  · rw [pc, packingCode_length]
    omega
  · change PackingOp.decode (physicalFetch _ (packingCode (left ++ block ++ right))
      (executeOps physical (block.take count) state).pc.toNat) = _
    rw [physicalFetch_eq _ _ _ hcode, pc]
    change PackingOp.decode (natFetch (left ++ block ++ right) (5 * (left.length + count))) = _
    rw [natFetch_body _ _ indexBound, PA17UniformGenerator035a.segment_index left block right count hc, decode_encode]

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.AccessBridge
