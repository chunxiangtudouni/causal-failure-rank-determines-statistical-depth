module

public import PaperProofs.Structure.PSTR_HD_HeadsZeroHeap_089

/-! ORIGINAL q=0 persistent configuration after the SAME real8op stage
update on QUERY ROM. The actual BitVec store is at physical4, headers/failed
remain, and no tree/bitmap/capacity input is manufactured. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

theorem zero_bump_rep {bits : Nat} (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (heap : BitVec bits → BitVec bits) (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 configuration heap)
    (hnext : Fits bits (configuration.stage + 1)) :
    HeapRepresents 0 full 0 (nextConfiguration 0 full configuration .correct) (PSTRRuntimeAdvance.bumpHeap 0 heap) := by
  have hpow : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have hsmall (value : Nat) (hv : value ≤ 5) : Fits bits value := by unfold Fits; omega
  have h1 : (BitVec.ofNat bits 1).toNat = 1 := Nat.mod_eq_of_lt (hsmall 1 (by decide))
  have hframe (physical : Nat) (hp : physical < 6) (hne : physical ≠ 4) :
      (PSTRRuntimeAdvance.bumpHeap 0 heap) (BitVec.ofNat bits physical) = heap (BitVec.ofNat bits physical) := by
    apply PSTRRuntimeAdvance.heap_frame
    exact (ofNat_injective_of_fit _ _ (hsmall physical (by omega)) (hsmall 4 (by decide))).not.mpr hne
  have hphysical := zero_physical_stage_failed full configuration heap hb rep
  have hstage := PSTRRuntimeAdvance.stage_word 0 configuration.stage heap hphysical.1 hnext
  have hfailed : ((PSTRRuntimeAdvance.bumpHeap 0 heap) (BitVec.ofNat bits 5)).toNat = bit configuration.failed :=
    (congrArg BitVec.toNat (hframe 5 (by decide) (by decide))).trans hphysical.2
  change HeapRepresents 0 full 0 {configuration with stage := configuration.stage + 1} (PSTRRuntimeAdvance.bumpHeap 0 heap)
  rcases rep with ⟨h0, hcap, hp, hbits, _hstage, _hfailed, _hmetadata, _hused, _htable⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hframe 0 (by decide) (by decide)]
    exact h0
  · rw [hframe 1 (by decide) (by decide)]
    exact hcap
  · rw [hframe 2 (by decide) (by decide)]
    exact hp
  · rw [hframe 3 (by decide) (by decide)]
    exact hbits
  · simpa only [logicalHeap, ↓reduceIte, dataHeap, physicalHeaderWords, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] using hstage
  · simpa only [logicalHeap, ↓reduceIte, dataHeap, physicalHeaderWords, h1] using hfailed
  · intro position hposition
    simp [staticMetadata] at hposition
  · intro tool
    exact Fin.elim0 tool
  · intro hq
    omega

theorem zero_correct_rep {bits : Nat} (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (state : WordState bits) (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 configuration state.heap)
    (hnext : Fits bits (configuration.stage + 1)) :
    HeapRepresents 0 full 0 (nextConfiguration 0 full configuration .correct)
      (executeOps (callInput 0 full .query) headsCorrect state).heap := by
  rw [headsCorrect_heap full configuration 0 state rep, zero_packed_words bits (by omega)]
  exact zero_bump_rep full configuration state.heap hb rep hnext

theorem zero_correct_prefix_rep {bits : Nat} (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (state : WordState bits) (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 configuration state.heap)
    (hnext : Fits bits (configuration.stage + 1)) (count : Nat) (hc : count ≤ 8) :
    HeapRepresents 0 full 0 (if count < 8 then configuration else nextConfiguration 0 full configuration .correct)
      (executeOps (callInput 0 full .query) (headsCorrect.take count) state).heap := by
  have hheader : (state.heap (BitVec.ofNat bits 2)).toNat = 0 := rep.2.2.1.trans (zero_packed_words bits (by omega))
  change HeapRepresents 0 full 0 _ (executeOps (callInput 0 full .query) (PSTRRuntimeAdvance.program.take count) state).heap
  rw [PSTRRuntimeAdvance.prefix_heap (callInput 0 full .query) state 0 hheader count hc]
  by_cases hlt : count < 8
  · simpa only [hlt, ↓reduceIte] using rep
  · simpa only [hlt, ↓reduceIte] using zero_bump_rep full configuration state.heap hb rep hnext

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
