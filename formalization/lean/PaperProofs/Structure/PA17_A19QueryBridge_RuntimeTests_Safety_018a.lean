module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_010f

/-! Fetch and access certificates for literal phases of the one fixed Tests
program. These transport proved local instruction accesses into the original
containing run; no execution is restarted and no terminal step is inserted. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSafety018

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open PA17A19RuntimeTests010

def StepSafe {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp)
    (heapWords : Nat) (state : WordState bits) : Prop :=
  state.halted = false ∧ Fits bits (state.pc.toNat + 4) ∧
    state.pc.toNat + 4 < (packingCode containing).length ∧
    ∃ op, PackingOp.decode (physicalFetch bits (packingCode containing) state.pc.toNat) = some op ∧
      packingAccessFits rom heapWords state op

theorem literal_prefix_safe {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (heapWords : Nat)
    (before block after : List PackingOp) (heq : programAt origin = before ++ block ++ after)
    (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + before.length)))
    (ha : state.halted = false) (count : Nat) (hc : count < block.length)
    (hs : StraightProgram (block.take count))
    (hrun : packingRun rom containing count state = executeOps rom (block.take count) state)
    (haccess : packingAccessFits rom heapWords (executeOps rom (block.take count) state) block[count]) :
    StepSafe rom containing heapWords (packingRun rom containing count state) := by
  have hl := congrArg List.length heq
  simp only [List.length_append] at hl
  have hindex : origin + before.length + count < containing.length := by
    have hb := em.bound
    omega
  have hpc : (packingRun rom containing count state).pc.toNat =
      5 * (origin + before.length + count) := by
    rw [hrun, executeOps_pc _ _ state hs, hp, List.length_take_of_le hc.le,
      BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    have he : 5 * (origin + before.length) + 5 * count =
        5 * (origin + before.length + count) := by omega
    rw [he]
    exact Nat.mod_eq_of_lt ((Nat.mul_le_mul_left 5 hindex.le).trans_lt em.pcfit)
  have hfetch : physicalFetch bits (packingCode containing)
      (packingRun rom containing count state).pc.toNat = block[count].encode := by
    rw [hpc, physicalFetch_eq bits _ _ em.words]
    change natFetch containing (5 * (origin + before.length + count)) = _
    rw [natFetch_body containing _ hindex, phase_code em before block after heq count hc]
  have hsmall : (packingRun rom containing count state).pc.toNat + 4 <
      5 * containing.length := by rw [hpc]; omega
  refine ⟨?_, hsmall.trans em.pcfit, ?_, block[count], ?_, ?_⟩
  · rw [hrun, executeOps_halted, ha]
  · rw [packingCode_length]
    exact hsmall.trans_le (Nat.le_add_right _ _)
  · rw [hfetch, decode_encode]
  · rw [hrun]
    exact haccess

theorem straight_phase_safe {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (heapWords : Nat)
    (before block after : List PackingOp) (heq : programAt origin = before ++ block ++ after)
    (hs : StraightProgram block) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + before.length)))
    (ha : state.halted = false)
    (haccess : ∀ count (hc : count < block.length), packingAccessFits rom heapWords
      (executeOps rom (block.take count) state) block[count])
    (count : Nat) (hc : count < block.length) :
    StepSafe rom containing heapWords (packingRun rom containing count state) := by
  exact literal_prefix_safe em rom heapWords before block after heq state hp ha count hc
    (fun op ho => hs op (List.mem_of_mem_take ho))
    (actual_straight_phase_prefix em rom before block after heq hs state hp ha count hc.le)
    (haccess count hc)

theorem branch_phase_safe {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (heapWords : Nat)
    (before lead after : List PackingOp) (last : PackingOp)
    (heq : programAt origin = before ++ (lead ++ [last]) ++ after)
    (hs : StraightProgram lead) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + before.length)))
    (ha : state.halted = false)
    (haccess : ∀ count (hc : count < (lead ++ [last]).length), packingAccessFits rom heapWords
      (executeOps rom ((lead ++ [last]).take count) state) (lead ++ [last])[count])
    (count : Nat) (hc : count < (lead ++ [last]).length) :
    StepSafe rom containing heapWords (packingRun rom containing count state) := by
  have hle : count ≤ lead.length := by
    simp only [List.length_append, List.length_singleton] at hc
    omega
  have ht : (lead ++ [last]).take count = lead.take count := List.take_append_of_le_length hle
  apply literal_prefix_safe em rom heapWords before (lead ++ [last]) after heq state hp ha count hc
  · rw [ht]
    exact fun op ho => hs op (List.mem_of_mem_take ho)
  · exact actual_branch_phase_prefix em rom before lead after last heq hs state hp ha count (by omega)
  · exact haccess count hc

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTestsSafety018
