module

public import Structure.PSTR_HD_ZeroHeadsSafety_005
public import PaperProofs.Structure.RawIncidenceOuterSafety

/-! Physical fixed-word realization of the single-run q=0 head extractor.
All local numeric bounds are later discharged in the original index width.
No ranks, indices or trace are supplied in the input ROM. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRZeroHeads

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine RawIncidenceLaminarRAM RawTreePreprocessingClaims
open PaperProofs.Common.Native.CompactPrice

variable {bits : Nat}

def decodeHeap (heap : BitVec bits → BitVec bits) (address : Nat) : Nat :=
  (heap (BitVec.ofNat bits address)).toNat

theorem initial_toWord (heap : BitVec bits → BitVec bits) :
    (initialNat (decodeHeap heap)).toWord bits = packingInitial heap := by
  apply wordState_ext
  · rfl
  · funext address
    simp [initialNat, NatState.toWord, decodeHeap]
    rfl
  · rfl
  · rfl

theorem point_registersFit (N : Nat) (state : NatState) (hfit : Fits bits (N + 128))
    (hreg : RegistersBound N state) : RegistersFit bits state :=
  fun reg => (hreg reg).trans_lt hfit

theorem point_pcFit (rom : PhysicalROM) (heapWords N : Nat) (state : NatState)
    (hfit : Fits bits (N + 128)) (hs : Point rom heapWords N state) : Fits bits state.pc := by
  obtain ⟨index, hi, hp, _⟩ := hs.2
  rw [hp]
  rw [program_length] at hi
  exact lt_of_le_of_lt (by omega) hfit

theorem finalWord_low (heap : BitVec bits → BitVec bits) (N address : Nat)
    (ha : address < 6) (hne : address ≠ 4) (haddr : Fits bits address) :
    (((finalState (decodeHeap heap) N).toWord bits).heap (BitVec.ofNat bits address)).toNat =
      (heap (BitVec.ofNat bits address)).toNat := by
  simp only [NatState.toWord, finalState, BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddr,
    Function.update_of_ne hne, outputHeap_low _ N N address ha, decodeHeap]
  exact Nat.mod_eq_of_lt (BitVec.isLt _)

theorem finalWord_stage (heap : BitVec bits → BitVec bits) (N : Nat)
    (haddr : Fits bits 4) (hN : Fits bits N) :
    (((finalState (decodeHeap heap) N).toWord bits).heap (BitVec.ofNat bits 4)).toNat = N := by
  simp only [NatState.toWord, finalState, BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddr,
    Function.update_self, Nat.mod_eq_of_lt hN]

theorem finalWord_depth (heap : BitVec bits → BitVec bits) (N : Nat)
    (haddr : Fits bits 6) (hv : Fits bits (depthWord N)) :
    (((finalState (decodeHeap heap) N).toWord bits).heap (BitVec.ofNat bits 6)).toNat = depthWord N := by
  simp only [NatState.toWord, finalState, BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddr,
    Function.update_of_ne (by decide : (6 : Nat) ≠ 4), outputHeap_depth,
    Nat.mod_eq_of_lt hv]

theorem finalWord_count (heap : BitVec bits → BitVec bits) (N : Nat)
    (haddr : Fits bits 7) (hN : Fits bits N) :
    (((finalState (decodeHeap heap) N).toWord bits).heap (BitVec.ofNat bits 7)).toNat = N := by
  simp only [NatState.toWord, finalState, BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddr,
    Function.update_of_ne (by decide : (7 : Nat) ≠ 4), outputHeap_count,
    Nat.mod_eq_of_lt hN]

theorem finalWord_index (heap : BitVec bits → BitVec bits) (N index : Nat) (hi : index < N)
    (haddr : Fits bits (8 + index)) (hv : Fits bits index) :
    (((finalState (decodeHeap heap) N).toWord bits).heap (BitVec.ofNat bits (8 + index))).toNat = index := by
  have hne : 8 + index ≠ 4 := by omega
  simp only [NatState.toWord, finalState, BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddr,
    Function.update_of_ne hne, outputHeap_index _ N N index hi, Nat.mod_eq_of_lt hv]

theorem finalWord_serialized (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (heap : BitVec bits → BitVec bits) (hfit : Fits bits (full.length + 128)) :
    heapWordsAt ((finalState (decodeHeap heap) full.length).toWord bits).heap 6
      (headWords 0 full used).length = headWords 0 full used := by
  have hsmall (n : Nat) (hn : n ≤ full.length + 128) : Fits bits n := hn.trans_lt hfit
  have hd : Fits bits (depthWord full.length) := by unfold depthWord; split <;> apply hsmall <;> omega
  rw [headWords_zero]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_range]
  rw [Nat.add_comm 2 full.length]
  change (List.range (full.length + 2)).map _ = _
  rw [List.range_succ_eq_map, List.map_cons, List.map_map,
    List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Function.comp_def, Nat.add_zero]
  rw [finalWord_depth heap full.length (hsmall 6 (by omega)) hd,
    finalWord_count heap full.length (hsmall 7 (by omega)) (hsmall full.length (by omega))]
  change depthWord full.length :: full.length :: _ = depthWord full.length :: full.length :: List.range full.length
  congr 2
  conv_rhs => rw [← List.map_id (List.range full.length)]
  apply List.map_congr_left
  intro index hi
  have hi' := List.mem_range.mp hi
  have ha : 6 + (index + 1 + 1) = 8 + index := by omega
  rw [ha]
  exact finalWord_index heap full.length index hi' (hsmall _ (by omega)) (hsmall _ (by omega))

theorem finalWord_represents (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (heap : BitVec bits → BitVec bits) (hfit : Fits bits (full.length + 128))
    (hr : HeapRepresents 0 full 0 ⟨0, used, false⟩ heap) :
    HeapRepresents 0 full 0 ⟨full.length, used, false⟩
      ((finalState (decodeHeap heap) full.length).toWord bits).heap := by
  have hsmall (n : Nat) (hn : n ≤ full.length + 128) : Fits bits n := hn.trans_lt hfit
  rcases hr with ⟨h0, h1, h2, h3, _hstage, hfailed, _hmeta, _hused, _hcap⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [finalWord_low heap full.length 0 (by decide) (by decide) (hsmall 0 (by omega))]
    exact h0
  · rw [finalWord_low heap full.length 1 (by decide) (by decide) (hsmall 1 (by omega))]
    exact h1
  · rw [finalWord_low heap full.length 2 (by decide) (by decide) (hsmall 2 (by omega))]
    exact h2
  · rw [finalWord_low heap full.length 3 (by decide) (by decide) (hsmall 3 (by omega))]
    exact h3
  · change (((finalState (decodeHeap heap) full.length).toWord bits).heap (BitVec.ofNat bits 4)).toNat = full.length
    exact finalWord_stage heap full.length (hsmall 4 (by omega)) (hsmall full.length (by omega))
  · have hfailed' : (heap (BitVec.ofNat bits 5)).toNat = bit false := by
      simpa only [logicalHeap, ↓reduceIte, dataHeap, physicalHeaderWords, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (hsmall 1 (by omega))] using hfailed
    have hfinal : (((finalState (decodeHeap heap) full.length).toWord bits).heap (BitVec.ofNat bits 5)).toNat = bit false :=
      (finalWord_low heap full.length 5 (by decide) (by decide) (hsmall 5 (by omega))).trans hfailed'
    simpa only [logicalHeap, ↓reduceIte, dataHeap, physicalHeaderWords, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hsmall 1 (by omega))] using hfinal
  · intro position hp
    simp [staticMetadata] at hp
  · intro tool
    exact Fin.elim0 tool
  · intro hq
    omega

theorem zero_query_rom (full : List (Finset (Fin 0))) :
    callInput 0 full .query = ⟨[full.length, 0, 0], [], []⟩ := by
  have hi : incidence full = [] := List.eq_nil_of_length_eq_zero (by rw [incidence_length]; simp)
  simp [callInput, rawIncidenceROM, hi, Command.word]

/-- Physical q=0 post-preprocessor branch of the original HeadExtractionClaims.
All heap state is the same persistent heap, with no new rank/head input. -/
theorem physical_zero_heads (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (heapWords : Nat) (heap : BitVec bits → BitVec bits) (hb : 8 ≤ bits)
    (hfit : Fits bits (full.length + 128)) (hheap : full.length + 8 ≤ heapWords)
    (hfoot : Fits bits ((callInput 0 full .query).size + heapWords + (packingCode program).length))
    (hr : HeapRepresents 0 full 0 ⟨0, used, false⟩ heap) :
    ∃ steps : Nat, steps ≤ 9 * full.length + 18 ∧
      DynamicRunCorrect heapWords (callInput 0 full .query) program steps heap ∧
      callCost 0 full program .query steps heap ≤ 512 * headWork 0 full ∧
      let result := packingRun (callInput 0 full .query) program steps (packingInitial heap)
      HeapRepresents 0 full 0 ⟨full.length, used, false⟩ result.heap ∧
      (result.register .index).toNat = 6 ∧
      6 + (headWords 0 full used).length ≤ heapWords ∧
      heapWordsAt result.heap 6 (headWords 0 full used).length = headWords 0 full used := by
  let rom := callInput 0 full .query
  let source := initialNat (decodeHeap heap)
  have hN : rom.semantic.read .input 0 = full.length := rfl
  have hinput : 0 < rom.input.length := by dsimp only [rom]; rw [zero_query_rom]; simp
  have hcode := program_code_fit hb
  have hs (count : Nat) (hc : count ≤ 9 * full.length + 18) :
      Point rom heapWords full.length (natRun rom program count source) :=
    every_prefix rom (decodeHeap heap) full.length heapWords count hN hinput hheap hc
  have hword (count : Nat) (hc : count ≤ 9 * full.length + 18) :
      packingRun rom program count (packingInitial heap) = (natRun rom program count source).toWord bits := by
    rw [← initial_toWord heap]
    apply natRun_toWord rom program source count hcode
    intro k hk
    have hp := hs k (hk.le.trans hc)
    exact ⟨point_registersFit full.length _ hfit hp.1, point_pcFit rom heapWords full.length _ hfit hp⟩
  have hcomplete := run_complete rom (decodeHeap heap) full.length hN
  obtain ⟨steps, hsteps, hsame, hhalt, hbefore⟩ := exists_first_halt rom program source
    (9 * full.length + 18) (by rw [hcomplete]; rfl)
  have hresult : packingRun rom program steps (packingInitial heap) =
      (finalState (decodeHeap heap) full.length).toWord bits := by
    rw [hword steps hsteps, hsame, hcomplete]
  refine ⟨steps, hsteps, ?_, callCost_bound full heap steps hsteps, ?_⟩
  · refine ⟨hcode, ?_, hfoot, ?_, ?_⟩
    · intro region value hv
      rw [zero_query_rom] at hv
      cases region with
      | input =>
        simp only [PhysicalROM.words, List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl
        · exact (show full.length ≤ full.length + 128 by omega).trans_lt hfit
        · exact (show 0 ≤ full.length + 128 by omega).trans_lt hfit
        · exact (show 0 ≤ full.length + 128 by omega).trans_lt hfit
      | internal => cases hv
      | children => cases hv
    · rw [hword steps hsteps]
      exact hhalt
    · intro count hc
      have hp := hs count (hc.le.trans hsteps)
      have hreg := point_registersFit full.length _ hfit hp.1
      have hpc := point_pcFit rom heapWords full.length _ hfit hp
      dsimp only
      rw [hword count (hc.le.trans hsteps)]
      refine ⟨hbefore count hc, ?_, ?_⟩
      · change (BitVec.ofNat bits (natRun rom program count source).pc).toNat + 4 < (packingCode program).length
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpc, program_code_length]
        obtain ⟨index, hi, he, _⟩ := hp.2
        rw [program_length] at hi
        omega
      · have hf : fetch program ((natRun rom program count source).toWord bits) =
            natFetch program (natRun rom program count source).pc := by
          change physicalFetch bits (packingCode program) (BitVec.ofNat bits _).toNat = _
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpc, physicalFetch_eq bits _ _ hcode]
          rfl
        rw [hf]
        obtain ⟨_index, _hi, _he, ha⟩ := hp.2
        have ha' := ha (hbefore count hc)
        cases hd : PackingOp.decode (natFetch program (natRun rom program count source).pc) with
        | none => simpa only [hd] using ha'
        | some op =>
          apply physical_access_of_nat rom heapWords _ op hreg
          simpa only [hd] using ha'
  · dsimp only
    rw [hresult]
    refine ⟨finalWord_represents full used heap hfit hr, ?_, ?_, finalWord_serialized full used heap hfit⟩
    · change (BitVec.ofNat bits 6).toNat = 6
      exact Nat.mod_eq_of_lt ((show 6 ≤ full.length + 128 by omega).trans_lt hfit)
    · have hl := PaperProofs.Common.Native.CompactPrice.PSTRHeads.headWords_length_le 0 full used
      omega

end PaperProofs.Structure.LaminarTree.PSTRZeroHeads






