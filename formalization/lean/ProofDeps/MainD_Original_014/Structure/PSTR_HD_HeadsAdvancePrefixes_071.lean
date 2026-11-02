module

public import Structure.PSTR_HD_HeadsAdvanceRun_070

/-! Every physical prefix of the real8+3 advance/backedge. The first stage
write occurs at step8; all earlier prefixes represent the old configuration,
and all later prefixes represent the actual correct successor. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM

def advanceLead : List PackingOp := headsCorrect ++ jumpLead 0

theorem advanceLead_length : advanceLead.length = 10 := rfl

theorem advanceLead_straight : StraightProgram advanceLead := by
  simp [advanceLead, headsCorrect, PSTRRuntimeAdvance.program, jumpLead, StraightProgram, StraightOp]

theorem advanceAndRepeat_split : advanceAndRepeat = advanceLead ++ [.jumpIfZero .flag .total] := by
  simp only [advanceAndRepeat, advanceLead, jumpBack_split, List.append_assoc]

theorem advance_prefix_heap {bits : Nat} (rom : PhysicalROM) (packed : Nat) (state : WordState bits)
    (hh : (state.heap (BitVec.ofNat bits 2)).toNat = packed) (count : Nat) (hc : count ≤ 11) :
    (executeOps rom (advanceAndRepeat.take count) state).heap =
      if count < 8 then state.heap else PSTRRuntimeAdvance.bumpHeap packed state.heap := by
  have hp := PSTRRuntimeAdvance.header_word state packed hh
  have hcomm : packed + 4 = 4 + packed := by omega
  interval_cases count <;>
    simp +decide [advanceAndRepeat, headsCorrect, PSTRRuntimeAdvance.program, jumpBack,
      executeOps, packingExecuteOp, wordOp, wordInstruction, hp, BitVec.ofNat_add_ofNat,
      hcomm, PSTRRuntimeAdvance.bumpHeap]

theorem containing_advance_prefix {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (origin : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (origin + 56))) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 11) :
    packingRun rom whole count state = executeOps rom (advanceAndRepeat.take count) state := by
  have hs := tail_slice whole advanceLead origin 56 hbound hcode (by change 56 + 10 ≤ 111; decide) rfl
  have h := segment_prefix rom whole advanceLead (.jumpIfZero .flag .total) (origin + 56)
    (by have hl := tailAt_length origin; rw [advanceLead_length]; omega) hs
    (hcode 66 (by change 66 < 111; decide)) advanceLead_straight hwords hpcfit state hp ha count
    (by rw [advanceLead_length]; exact hc)
  simpa only [advanceAndRepeat_split] using h

theorem advance_prefix_frame {bits : Nat} (rom : PhysicalROM) (packed endpoint : Nat) (state : WordState bits)
    (hh : (state.heap (BitVec.ofNat bits 2)).toNat = packed)
    (hbefore : 4 + packed < endpoint) (he : Fits bits endpoint)
    (physical : Nat) (hf : Fits bits physical) (hp : endpoint ≤ physical) (count : Nat) (hc : count ≤ 11) :
    (executeOps rom (advanceAndRepeat.take count) state).heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  rw [advance_prefix_heap rom packed state hh count hc]
  split
  · rfl
  · apply PSTRRuntimeAdvance.heap_frame
    exact (ofNat_injective_of_fit _ _ hf (hbefore.trans he)).not.mpr (by omega)

theorem advance_actual_prefix_rep {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords origin : Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 56))) (ha : state.halted = false)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hi : ∀ offset < 2 + (staticMetadata q full).length,
      Fits bits (4 + packedCapacityWords q capWords bits + offset))
    (hnext : Fits bits (configuration.stage + 1)) (count : Nat) (hc : count ≤ 11) :
    HeapRepresents q full capWords (if count < 8 then configuration else nextConfiguration q full configuration .correct)
      (packingRun (callInput q full .query) whole count state).heap := by
  rw [containing_advance_prefix (callInput q full .query) whole origin hbound hcode hwords hpcfit state hp ha count hc,
    advance_prefix_heap (callInput q full .query) _ state rep.2.2.1 count hc]
  by_cases hlt : count < 8
  · simpa only [hlt, ↓reduceIte] using rep
  · have h := headsCorrect_rep full configuration capWords state hb hq rep bitmap hr hi hnext
    rw [headsCorrect_heap full configuration capWords state rep] at h
    simpa only [hlt, ↓reduceIte] using h

theorem advance_actual_prefix_recorded {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords origin rank : Nat) (entries : List Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (recorded : RecordedHeads (endpoint full capWords bits) q rank entries state.heap)
    (he : Fits bits (endpoint full capWords bits + 10 + entries.length))
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 56))) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 11) :
    RecordedHeads (endpoint full capWords bits) q rank entries (packingRun (callInput q full .query) whole count state).heap := by
  rw [containing_advance_prefix (callInput q full .query) whole origin hbound hcode hwords hpcfit state hp ha count hc]
  apply recorded_of_query_frame _ q rank entries state.heap _ recorded he
  intro physical hf hphysical
  have hbefore : 4 + packedCapacityWords q capWords bits < endpoint full capWords bits := by
    have h := endpoint_metadata_after full capWords hq (bits := bits)
    omega
  exact advance_prefix_frame (callInput q full .query) _ _ state rep.2.2.1 hbefore
    ((show endpoint full capWords bits ≤ endpoint full capWords bits + 10 + entries.length by omega).trans_lt he)
    physical hf hphysical count hc

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
