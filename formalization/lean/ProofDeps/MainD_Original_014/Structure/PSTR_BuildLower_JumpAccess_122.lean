module

public import Structure.PSTR_BuildLower_TraceAccess_119

/-! A real last jump is executed and charged. All proper prefixes before
that last instruction are straight, enabling actual fetch/decode/access
without asserting that the jump itself is a straight instruction. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.AccessBridge
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawTreePreprocessingClaims
open PA17UniformGenerator035a PA17PackedTranslator034
variable {bits : Nat}

theorem last_prefix (physical : PhysicalROM) (left lead right : List PackingOp) (last : PackingOp)
    (state : WordState bits) (straight : StraightProgram lead)
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ (lead ++ [last]) ++ right)))
    (hpcfit : Fits bits (5 * (left ++ (lead ++ [last]) ++ right).length))
    (count : Nat) (hc : count ≤ lead.length + 1) :
    packingRun physical (left ++ (lead ++ [last]) ++ right) count state =
      executeOps physical ((lead ++ [last]).take count) state := by
  apply PSTRWordSegments.segment_prefix physical _ lead last left.length
    (by simp only [List.length_append, List.length_singleton]; omega) ?_ ?_ straight hcode hpcfit state hpc ha count hc
  · intro index hi
    have hh := segment_index left (lead ++ [last]) right index
      (by simp only [List.length_append, List.length_singleton]; omega)
    simpa only [List.getElem_append_left hi] using hh
  · have hh := segment_index left (lead ++ [last]) right lead.length
      (by simp only [List.length_append, List.length_singleton]; omega)
    simpa only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero] using hh

theorem last_safe (physical : PhysicalROM) (left lead right : List PackingOp) (last : PackingOp)
    (heapWords : Nat) (state : WordState bits) (straight : StraightProgram lead)
    (localSafe : PackedAccessSafe heapWords physical (lead ++ [last]) state)
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ (lead ++ [last]) ++ right)))
    (hpcfit : Fits bits (5 * (left ++ (lead ++ [last]) ++ right).length)) :
    TraceAccess.Safe heapWords physical (left ++ (lead ++ [last]) ++ right) state (lead.length + 1) := by
  intro count hc
  rw [last_prefix physical left lead right last state straight hpc ha hcode hpcfit count hc.le]
  have hcLead : count ≤ lead.length := by omega
  have taken : (lead ++ [last]).take count = lead.take count := by
    rw [List.take_append, Nat.sub_eq_zero_of_le hcLead, List.take_zero, List.append_nil]
  have prefixStraight : StraightProgram ((lead ++ [last]).take count) := by
    rw [taken]
    intro op hm
    exact straight op (List.mem_of_mem_take hm)
  have hlen : ((lead ++ [last]).take count).length = count :=
    List.length_take_of_le (by simp only [List.length_append, List.length_singleton]; omega)
  have pc : (executeOps physical ((lead ++ [last]).take count) state).pc.toNat = 5 * (left.length + count) := by
    rw [executeOps_pc _ _ _ prefixStraight, hlen, hpc, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    have arithmetic : 5 * left.length + 5 * count = 5 * (left.length + count) := by omega
    rw [arithmetic, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mul_le_mul_left 5 ?_) hpcfit)]
    simp only [List.length_append, List.length_singleton]
    omega
  have indexBound : left.length + count < (left ++ (lead ++ [last]) ++ right).length := by
    simp only [List.length_append, List.length_singleton]
    omega
  have hcBlock : count < (lead ++ [last]).length := by
    simpa only [List.length_append, List.length_singleton] using hc
  refine ⟨(executeOps_halted physical _ state).trans ha, ?_, (lead ++ [last])[count], ?_, localSafe count hcBlock⟩
  · rw [pc, packingCode_length]
    simp only [List.length_append, List.length_singleton]
    omega
  · change PackingOp.decode (physicalFetch _ (packingCode (left ++ (lead ++ [last]) ++ right))
      (executeOps physical ((lead ++ [last]).take count) state).pc.toNat) = _
    rw [physicalFetch_eq _ _ _ hcode, pc]
    change PackingOp.decode (natFetch (left ++ (lead ++ [last]) ++ right) (5 * (left.length + count))) = _
    rw [natFetch_body _ _ indexBound, segment_index left (lead ++ [last]) right count hcBlock, decode_encode]

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.AccessBridge
