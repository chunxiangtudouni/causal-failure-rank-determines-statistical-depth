module

public import Structure.PA06_A19Prepare_PreBuild044_Frames

set_option autoImplicit false
set_option warningAsError true

/-! Uncompiled raw-to-prebuild candidate. Only original q>0/Laminar and
whole-program word/code eligibility occur at the external entry. All
intermediate data premises are discharged by actual executed producers.
No ST counter initialization is claimed here. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PreparePreBuild044

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM
open PA06A19PrepareRawHeader039Body (wordRun_add)

/-- Internal data after the real144-op children builder. The original
parent/degree/child ROM semantics and copied ordinals are both retained. -/
structure CachedData (q : Nat) (full : List (Finset (Fin q)))
    (state : WordState (bits q full)) : Prop where
  header : PA06A19PrepareRuntimePacked016.Header q state.heap
  scalars : ScalarData q full state
  copiedOrd : PA06A19PrepareBankData042.CopiedOrdData q full (controlBase q full) state
  cache : PA06A19PrepareChildrenCache023.OutputData q full (controlBase q full)
    (PA06A19PrepareChildrenCache023.wordView state)

/-- Data-only ABI for the subsequent builder. It includes CB0..6 through
the existing032/037 records plus cells3/6, the actual high cache, finite
oldC0+I zero view, and exactly VM slots32..38. ST owns its64..84 clear. -/
structure Data (q : Nat) (full : List (Finset (Fin q)))
    (state : WordState (bits q full)) : Prop where
  cached : CachedData q full state
  zeroView : ∀ a < PA06A19PreparePackedView013.oldCapacity full.length q (treeSize q full) +
      PA06A19PrepareFiniteClear031Setup.ordinaryWords full.length q (treeSize q full),
    PA06A19PreparePackedView013.view q
      (PA06A19PreparePackedView013.oldCapacity full.length q (treeSize q full))
      (capacity q full) (4 + packedWords q full) state.heap a = 0
  capacityBounded : CapacityPrefixBounded q (capacity q full)
    (unpackHeap q (capacity q full) (bits q full) (dataHeap state.heap))
  vm : ∀ slot, 32 ≤ slot → slot < 39 →
    state.heap (BitVec.ofNat _ (controlBase q full + slot)) = 0

theorem cache_stage (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full) (tail : List PackingOp)
    (before : WordState (bits q full))
    (hpc : before.pc.toNat = 5 * 1444) (ha : before.halted = false)
    (hheader : PA06A19PrepareRuntimePacked016.Header q before.heap)
    (hscalars : ScalarData q full before)
    (hord : PA06A19PrepareBankData042.CopiedOrdData q full (controlBase q full) before)
    (hinput : PA06A19PrepareChildrenCache023.InputData q full (controlBase q full)
      (PA06A19PrepareRuntimeHeader019.natView before))
    (hcode : WordsFit (bits q full) (packingCode (program tail)))
    (hend : Fits (bits q full) (5 * (program tail).length)) :
    let after := packingRun (controllerInput q full used) (program tail)
      (PA06A19PrepareChildrenCache023.totalSteps q full) before
    CachedData q full after ∧ after.pc.toNat = 5 * 1588 ∧ after.halted = false ∧
      ∀ count < PA06A19PrepareChildrenCache023.totalSteps q full,
        let current := packingRun (controllerInput q full used) (program tail) count before
        current.halted = false ∧ current.pc.toNat + 4 < (packingCode (program tail)).length ∧
          ∃ op, PackingOp.decode (fetch (program tail) current) = some op ∧
            packingAccessFits (controllerInput q full used) (allocation q full) current op := by
  have hi : PA06A19PrepareChildrenCache023.InputData q full
      (PA06A19PrepareChildrenCache023.actualControlBase q full)
      (PA06A19PrepareChildrenCache023.wordView before) := by
    rw [children_controlBase q full hq]
    exact hinput
  have built := PA06A19PrepareChildrenCache023.word_build q full hq hl
    (controllerInput q full used) (program tail) 1444 (cache_code tail)
    before hi hpc ha hcode hend
  dsimp only at built
  rcases built with ⟨output, address, pc, active, frame, safe, _stepsBound⟩
  rw [children_controlBase q full hq] at output frame
  have frames := cache_retained_frames q full hq before _ frame
  refine ⟨⟨header_of_frame hheader frames.2.2,
    hscalars.of_frame address frames.1, copiedOrd_of_frame hord frames.2.1, output⟩,
    pc, active, ?_⟩
  intro count hc
  have hs := safe count hc
  rw [children_allocation q full hq] at hs
  exact ⟨hs.2.1, hs.2.2.1, hs.2.2.2⟩

theorem clear_stage (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full) (tail : List PackingOp)
    (before : WordState (bits q full))
    (hpc : before.pc.toNat = 5 * 1588) (ha : before.halted = false)
    (data : CachedData q full before)
    (hcode : WordsFit (bits q full) (packingCode (program tail)))
    (hend : Fits (bits q full) (5 * (program tail).length)) :
    let after := packingRun (controllerInput q full used) (program tail)
      (PA06A19PrepareClearVM045.clock full.length q (treeSize q full)) before
    Data q full after ∧ after.pc.toNat = 5 * 1639 ∧ after.halted = false ∧
      ∀ count < PA06A19PrepareClearVM045.clock full.length q (treeSize q full),
        let current := packingRun (controllerInput q full used) (program tail) count before
        current.halted = false ∧ current.pc.toNat + 4 < (packingCode (program tail)).length ∧
          ∃ op, PackingOp.decode (fetch (program tail) current) = some op ∧
            packingAccessFits (controllerInput q full used) (allocation q full) current op := by
  have hp : before.pc.toNat = 5 * (clearFront tail).length := by
    rw [clearFront_length]; exact hpc
  have hc : WordsFit (bits q full)
      (packingCode (clearFront tail ++ PA06A19PrepareClearVM045.programAt (clearFront tail).length ++ tail)) := by
    rw [clear_layout]; exact hcode
  have he : Fits (bits q full)
      (5 * (clearFront tail ++ PA06A19PrepareClearVM045.programAt (clearFront tail).length ++ tail).length) := by
    rw [clear_layout]; exact hend
  have result := PA06A19PrepareClearVM045.actual_data q full used hq (clearFront tail)
    tail before hp ha data.scalars.bank032 hc he data.header
  rw [clear_layout] at result
  dsimp only at result
  rcases result with ⟨zeroView, bounded, header, address, pc, active, vm, _lower, _outer⟩
  let after := packingRun (controllerInput q full used) (program tail)
    (PA06A19PrepareClearVM045.clock full.length q (treeSize q full)) before
  have permanent (point : BitVec (bits q full))
      (hpoint : (controlBase q full ≤ point.toNat ∧ point.toNat < controlBase q full + 32) ∨
        controlBase q full + 39 ≤ point.toNat) : after.heap point = before.heap point := by
    have hh := PA06A19PrepareClearVM045.actual_permanent_frame q full used hq (clearFront tail)
      tail before hp ha data.scalars.bank032 hc he data.header point hpoint
    rw [clear_layout] at hh
    exact hh
  have scalarFrame (offset : Nat) (ho : offset < 7) :
      after.heap (BitVec.ofNat _ (controlBase q full + offset)) =
        before.heap (BitVec.ofNat _ (controlBase q full + offset)) := by
    apply permanent
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (control_cell_fits q full hq offset (by omega))]
    exact Or.inl ⟨by omega, by omega⟩
  have highFrame (a : Nat) (ha0 : controlBase q full + 512 ≤ a)
      (ha1 : a ≤ PA06A19PrepareChildrenCache023.highCacheEnd
        (controlBase q full) (PA06A19PrepareChildrenCache023.mass q full)) :
      after.heap (BitVec.ofNat _ a) = before.heap (BitVec.ofNat _ a) := by
    apply permanent
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (high_cell_fits q full hq a ha1)]
    exact Or.inr (by omega)
  have ord : PA06A19PrepareBankData042.CopiedOrdData q full (controlBase q full) after := by
    apply copiedOrd_of_frame data.copiedOrd
    intro node
    apply highFrame _ (ordinal_bounds q full node).1
    have hn := (ordinal_bounds q full node).2
    unfold PA06A19PrepareChildrenCache023.degreeBase at hn
    unfold PA06A19PrepareChildrenCache023.highCacheEnd
    omega
  have cache := outputData_of_high_frame q full hq hl before after data.cache address highFrame
  have hbaseWord : before.register .address = BitVec.ofNat (bits q full) (controlBase q full) := by
    have hbaseFit : Fits (bits q full) (controlBase q full) := by
      simpa only [Nat.add_zero] using control_cell_fits q full hq 0 (by decide)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbaseFit]
    exact data.scalars.bank032.base
  have vmActual : ∀ slot, 32 ≤ slot → slot < 39 →
      after.heap (BitVec.ofNat _ (controlBase q full + slot)) = 0 := by
    intro slot hlo hhi
    have hh := vm slot hlo hhi
    rw [hbaseWord, BitVec.ofNat_add_ofNat] at hh
    exact hh
  have safe := PA06A19PrepareClearVM045.actual_prefix_access q full used hq (clearFront tail)
    tail before hp ha data.scalars.bank032 hc he
  rw [clearFront_length] at pc
  refine ⟨⟨⟨header, data.scalars.of_frame address scalarFrame, ord, cache⟩,
    zeroView, bounded, vmActual⟩, pc, active, ?_⟩
  intro count hcount
  have hs := safe count hcount
  rw [clear_layout] at hs
  exact hs

/-- Original input to the actual same-program prebuild boundary. This
theorem does not accept any intermediate InputData, zero/cache predicate,
all-prefix safety assertion, replacement ROM, or query-result hypothesis. -/
theorem raw_prebuild_entry (q : Nat) (full : List (Finset (Fin q)))
    (tail : List PackingOp) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (hend : Fits (bits q full) (5 * (program tail).length))
    (hcode : WordsFit (bits q full) (packingCode (program tail))) :
    ∃ clock ≤ clockBound q full,
      let rom := controllerInput q full used
      let after := packingRun rom (program tail) clock (natInitial.toWord (bits q full))
      Data q full after ∧ after.pc.toNat = 5 * 1639 ∧ after.halted = false ∧
        ∀ count < clock,
          let current := packingRun rom (program tail) count (natInitial.toWord (bits q full))
          current.halted = false ∧ current.pc.toNat + 4 < (packingCode (program tail)).length ∧
            ∃ op, PackingOp.decode (fetch (program tail) current) = some op ∧
              packingAccessFits rom (allocation q full) current op := by
  let rom := controllerInput q full used
  let initial := natInitial.toWord (bits q full)
  let cacheClock := PA06A19PrepareChildrenCache023.totalSteps q full
  let clearClock := PA06A19PrepareClearVM045.clock full.length q (treeSize q full)
  obtain ⟨rawClock, rawBound, rawData⟩ :=
    PA06A19PrepareRawSequence043.raw_sequence_entry q full (suffix tail) used hq hl hend hcode
  dsimp only at rawData
  rcases rawData with ⟨rawHeader, bank032, bank037, cell3, cell6, cacheInput,
    copiedOrd, rawPC, rawActive, rawSafe⟩
  let raw := packingRun rom (program tail) rawClock initial
  let cached := packingRun rom (program tail) (rawClock + cacheClock) initial
  have cacheRun : cached = packingRun rom (program tail) cacheClock raw := by
    exact wordRun_add rom (program tail) rawClock cacheClock initial
  have cacheResult := cache_stage q full used hq hl tail raw rawPC rawActive rawHeader
    ⟨bank032, bank037, cell3, cell6⟩ copiedOrd cacheInput hcode hend
  dsimp only at cacheResult
  have cachedData : CachedData q full cached := by rw [cacheRun]; exact cacheResult.1
  have cachedPC : cached.pc.toNat = 5 * 1588 := by rw [cacheRun]; exact cacheResult.2.1
  have cachedActive : cached.halted = false := by rw [cacheRun]; exact cacheResult.2.2.1
  have clearResult := clear_stage q full used hq hl tail cached cachedPC cachedActive cachedData hcode hend
  dsimp only at clearResult
  have finalRun : packingRun rom (program tail) (rawClock + cacheClock + clearClock) initial =
      packingRun rom (program tail) clearClock cached :=
    wordRun_add rom (program tail) (rawClock + cacheClock) clearClock initial
  rw [← finalRun] at clearResult
  refine ⟨rawClock + cacheClock + clearClock, ?_, ?_⟩
  · dsimp only [clockBound, cacheClock, clearClock]
    omega
  dsimp only
  refine ⟨clearResult.1, clearResult.2.1, clearResult.2.2.1, ?_⟩
  intro count hcount
  by_cases early : count < rawClock
  · exact rawSafe count early
  · by_cases middle : count < rawClock + cacheClock
    · have ht : count = rawClock + (count - rawClock) := by omega
      have hs := cacheResult.2.2.2 (count - rawClock) (by omega)
      have hr : packingRun rom (program tail) count initial =
          packingRun rom (program tail) (count - rawClock) raw := by
        calc
          _ = packingRun rom (program tail) (rawClock + (count - rawClock)) initial :=
            congrArg (fun k => packingRun rom (program tail) k initial) ht
          _ = _ := wordRun_add rom (program tail) rawClock (count - rawClock) initial
      rw [← hr] at hs
      exact hs
    · have ht : count = rawClock + cacheClock + (count - (rawClock + cacheClock)) := by omega
      have hs := clearResult.2.2.2 (count - (rawClock + cacheClock)) (by omega)
      have hr : packingRun rom (program tail) count initial =
          packingRun rom (program tail) (count - (rawClock + cacheClock)) cached := by
        calc
          _ = packingRun rom (program tail)
              (rawClock + cacheClock + (count - (rawClock + cacheClock))) initial :=
            congrArg (fun k => packingRun rom (program tail) k initial) ht
          _ = _ := wordRun_add rom (program tail) (rawClock + cacheClock)
            (count - (rawClock + cacheClock)) initial
      rw [← hr] at hs
      exact hs

/-- Dynamic trace accounting uses the same real clock sum. -/
theorem raw_prebuild_trace_bound (q : Nat) (full : List (Finset (Fin q)))
    (tail : List PackingOp) (used : Finset (Fin q)) (clock : Nat)
    (hc : clock ≤ clockBound q full) :
    (packingDynamicTrace (controllerInput q full used) (program tail) clock
      (natInitial.toWord (bits q full))).length ≤ 12 * clockBound q full := by
  exact (packingDynamicTrace_length_le _ _ _ _).trans (Nat.mul_le_mul_left 12 hc)

end PaperProofs.Structure.LaminarTree.PA06A19PreparePreBuild044
