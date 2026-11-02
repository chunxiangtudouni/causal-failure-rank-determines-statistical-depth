module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009n

/-! HD owns every physical word at or beyond the exclusive endpoint
E=childBase+t+3. The selector's local clear, preparation and push components
preserve that entire suffix at every actual prefix, even above allocation.
The necessary Fits p premise excludes Word-truncation aliasing. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

def endpoint (header q size : Nat) : Nat := childBase header q + size + 3

theorem actual_clear_suffix_frame {bits origin : Nat} {containing : List PackingOp}
    (em : ClearEmbedded bits origin containing) (rom : PhysicalROM) (q size header heapWords : Nat) (state : WordState bits)
    (hroom : Fits bits (childBase header q + size + 1)) (halloc : childBase header q + size + 1 ≤ heapWords)
    (hinput : 1 < rom.input.length) (hsize : (state.heap (BitVec.ofNat bits 0)).toNat = size)
    (hq : (rom.words .input).getD 1 0 = q) (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (clock : Nat) (hc : clock ≤ clearSteps size) (physical : Nat) (hphysical : Fits bits physical)
    (hsuffix : endpoint header q size ≤ physical) :
    (packingRun rom containing clock state).heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  apply actual_clear_prefix_frame em rom q size header heapWords state hroom halloc hinput hsize hq hh hp ha clock hc
  intro i hi
  apply (ofNat_injective_of_fit _ _ hphysical
    ((show childBase header q + i ≤ childBase header q + size + 1 by omega).trans_lt hroom)).not.mpr
  unfold endpoint at hsuffix
  omega

theorem preparePush_actual_suffix_frame {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp)
    (origin header q size heapWords : Nat) (state : WordState bits)
    (hbound : origin + preparePush.length ≤ containing.length)
    (hcode : ∀ i (hi : i < preparePush.length), containing[origin + i]'(by omega) = preparePush[i])
    (hw : WordsFit bits (packingCode containing)) (hpc : Fits bits (5 * containing.length))
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (h1 : Fits bits 1) (hh : state.register .address = BitVec.ofNat bits header)
    (hinput : 1 < rom.input.length) (halloc : header + 12 < heapWords)
    (hroom : Fits bits (endpoint header q size))
    (clock : Nat) (hc : clock ≤ 38) (physical : Nat) (hphysical : Fits bits physical)
    (hsuffix : endpoint header q size ≤ physical) :
    (packingRun rom containing clock state).heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  have hprotect : ClearProtected (header + 8) 5 (BitVec.ofNat bits physical) := by
    intro i hi
    have hb : header + 8 + i < endpoint header q size := by unfold endpoint childBase; omega
    apply (ofNat_injective_of_fit _ _ hphysical (hb.le.trans_lt hroom)).not.mpr
    omega
  induction clock with
  | zero => rfl
  | succ clock ih =>
    have hcl : clock < preparePush.length := by rw [preparePush_length]; omega
    have point := preparePush_actual_point rom containing origin header heapWords state hbound hcode hw hpc hp ha
      h1 hh hinput halloc clock hcl
    rcases point with ⟨hactive, index, hi, hpcNat, _, _, hframe⟩
    rw [packingRun_succ, packingStep_of_index rom containing _ index hi hw hpcNat hactive]
    exact (hframe _ hprotect).trans (ih (by omega))

theorem pushProgram_actual_suffix_frame {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp)
    (origin header q size counts parents node parent : Nat) (state : WordState bits)
    (hbound : origin + pushProgram.length ≤ containing.length)
    (hcode : ∀ i (hi : i < pushProgram.length), containing[origin + i]'(by omega) = pushProgram[i])
    (hw : WordsFit bits (packingCode containing)) (hpc : Fits bits (5 * containing.length))
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (hroom : Fits bits (endpoint header q size)) (hparentBound : parent ≤ size)
    (h1 : Fits bits 1) (hn : Fits bits (node + 1)) (hparent : Fits bits parent)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hnode : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits (node + 1))
    (hcandidates : state.heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits (childBase header q))
    (hcounts : state.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits counts)
    (hparents : state.heap (BitVec.ofNat bits (header + 12)) = BitVec.ofNat bits parents)
    (hreadParent : state.heap (BitVec.ofNat bits (parents + (node + 1))) = BitVec.ofNat bits parent)
    (clock : Nat) (hc : clock ≤ 24) (physical : Nat) (hphysical : Fits bits physical)
    (hsuffix : endpoint header q size ≤ physical) :
    (packingRun rom containing clock state).heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  have hcl : clock ≤ pushProgram.length := by rwa [pushProgram_length]
  rw [PA17A19RuntimeRanks008.straight_prefix rom containing pushProgram origin hbound hcode pushProgram_straight hw hpc state hp ha clock hcl]
  have hv : state.register .value = BitVec.ofNat bits (state.register .value).toNat := by
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hcount : state.heap (BitVec.ofNat bits (counts + node)) =
      BitVec.ofNat bits (state.heap (BitVec.ofNat bits (counts + node))).toNat := by
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  apply pushProgram_prefix_frame rom header (childBase header q) counts parents node parent
    (state.register .value).toNat (state.heap (BitVec.ofNat bits (counts + node))).toNat state
    h1 hn hparent (BitVec.isLt _) (BitVec.isLt _) hh hv hnode hcandidates hcounts hparents hcount hreadParent clock hc
  have hb : childBase header q + parent < endpoint header q size := by unfold endpoint; omega
  apply (ofNat_injective_of_fit _ _ hphysical (hb.le.trans_lt hroom)).not.mpr
  omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
