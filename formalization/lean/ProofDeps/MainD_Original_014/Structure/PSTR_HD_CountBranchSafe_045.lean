module

public import Structure.PSTR_HD_CountPhaseSafe_044

/-! The final conditional jump of each fixed loop block is fetched from the
same literal code. It has no data-memory access and no heap update. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open RawTreePreprocessingClaims

def AtSafe {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (heapWords : Nat)
    (state : WordState bits) : Prop :=
  state.halted = false ∧ state.pc.toNat + 4 < (packingCode containing).length ∧
    ∃ op, PackingOp.decode (fetch containing state) = some op ∧ packingAccessFits rom heapWords state op

theorem straight_prefix_safe {bits : Nat} (rom : PhysicalROM) (containing lead : List PackingOp)
    (heapWords start : Nat) (region : Nat → Prop)
    (hbound : start + lead.length ≤ containing.length)
    (hcode : ∀ i (hi : i < lead.length), containing[start + i]'(by omega) = lead[i])
    (hs : StraightProgram lead) (hw : WordsFit bits (packingCode containing))
    (hpcfit : Fits bits (5 * containing.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (safe : PrefixOK rom heapWords region lead state) (count : Nat) (hc : count < lead.length) :
    AtSafe rom containing heapWords (packingRun rom containing count state) ∧
      HeapFrame region state.heap (packingRun rom containing count state).heap := by
  have h := fetched_prefix_safe rom containing lead heapWords start region hbound hcode hs hw hpcfit state hp ha safe count hc
  exact ⟨⟨h.1, h.2.1, lead[count], h.2.2.1, h.2.2.2.1⟩, h.2.2.2.2⟩

theorem branch_prefix_safe {bits : Nat} (rom : PhysicalROM) (containing lead : List PackingOp)
    (heapWords start : Nat) (region : Nat → Prop)
    (hbound : start + lead.length + 1 ≤ containing.length)
    (hcode : ∀ i (hi : i < lead.length), containing[start + i]'(by omega) = lead[i])
    (hlast : containing[start + lead.length]'(by omega) = .jumpIfZero .flag .total)
    (hs : StraightProgram lead) (hw : WordsFit bits (packingCode containing))
    (hpcfit : Fits bits (5 * containing.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (safe : PrefixOK rom heapWords region lead state) (count : Nat) (hc : count ≤ lead.length) :
    AtSafe rom containing heapWords (packingRun rom containing count state) ∧
      HeapFrame region state.heap (packingRun rom containing count state).heap := by
  by_cases he : count < lead.length
  · exact straight_prefix_safe rom containing lead heapWords start region (by omega) hcode hs hw hpcfit state hp ha safe count he
  · have heq : count = lead.length := by omega
    subst count
    have hr := fetched_prefix rom containing lead start (by omega) hcode hs hw hpcfit state hp ha lead.length le_rfl
    have hpc := fetched_prefix_pc rom containing lead start (by omega) hcode hs hw hpcfit state hp ha lead.length le_rfl
    have hi : start + lead.length < containing.length := by omega
    have hf : fetch containing (packingRun rom containing lead.length state) = natFetch containing (5 * (start + lead.length)) := by
      change physicalFetch bits (packingCode containing) _ = _
      rw [physicalFetch_eq bits _ _ hw, hpc]
      rfl
    refine ⟨⟨?_, ?_, .jumpIfZero .flag .total, ?_, trivial⟩, ?_⟩
    · rw [hr, List.take_length, executeOps_halted, ha]
    · rw [hpc, packingCode_length]
      omega
    · rw [hf, natFetch_body containing (start + lead.length) hi, hlast, decode_encode]
    · rw [hr]
      exact safe.frame lead.length le_rfl

theorem phase_partition (degree clock : Nat) (hc : clock < activeSteps degree) :
    clock < 121 ∨
      (∃ count rest, count < degree ∧ rest < 114 ∧ clock = 121 + 114 * count + rest) ∨
      (∃ rest, rest < 63 ∧ clock = 121 + 114 * degree + rest) := by
  unfold activeSteps at hc
  by_cases hstart : clock < 121
  · exact Or.inl hstart
  · by_cases hloop : clock < 121 + 114 * degree
    · right; left
      refine ⟨(clock - 121) / 114, (clock - 121) % 114, ?_, ?_, ?_⟩ <;> omega
    · right; right
      exact ⟨clock - (121 + 114 * degree), by omega, by omega⟩

end PaperProofs.Structure.LaminarTree.PSTRCountKernel
