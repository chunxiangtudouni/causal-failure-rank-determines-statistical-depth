module

public import Structure.PA06_A19Prepare_PreBuild044
public import Structure.PSTR_BuildLower_LoadData_064
public import Structure.PSTR_BuildLower_GlobalCapacity_085

set_option autoImplicit false
set_option warningAsError true

/-! Data-only entry from one real prebuild endpoint to the frozen ST ABI.
No counter environment, builder run, future frame, or successful-output
premise is added. The actual raw producer must establish044.Data first.
Source candidate only until the parent's strict/public/private checks. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareSTInput050

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

private theorem word_of_toNat {bits value : Nat} (word : BitVec bits)
    (h : word.toNat = value) : word = BitVec.ofNat bits value := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem treeSize_eq (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    CompactControllerClaims.treeSize q full = PSTRBuildLower.PreparedLayout.t q full := by
  unfold CompactControllerClaims.treeSize
  rw [ite_eq_right (Nat.ne_of_gt hq)]

private theorem capacity_eq (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    PA06A19PreparePreBuild044.capacity q full = PSTRBuildLower.PreparedLayout.capacity q full := by
  change CompactControllerClaims.capacityWords 8192 full.length q
      (CompactControllerClaims.treeSize q full) =
    CompactControllerClaims.capacityWords 8192 full.length q (PSTRBuildLower.PreparedLayout.t q full)
  rw [treeSize_eq q full hq]

private theorem packed_eq (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    PA06A19PreparePreBuild044.packedWords q full = PSTRBuildLower.PreparedLayout.packed q full := by
  change packedCapacityWords q (PA06A19PreparePreBuild044.capacity q full)
      (indexWidth 32 full.length q) =
    packedCapacityWords q (PSTRBuildLower.PreparedLayout.capacity q full)
      (indexWidth 32 full.length q)
  rw [capacity_eq q full hq]

private theorem controlBase_eq (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    PA06A19PreparePreBuild044.controlBase q full = PSTRBuildLower.PreparedLayout.controlBase q full := by
  change 4 + PA06A19PreparePreBuild044.packedWords q full +
      4096 * (full.length + q + 1 + CompactControllerClaims.treeSize q full) =
    4 + PSTRBuildLower.PreparedLayout.packed q full +
      4096 * (full.length + q + 1 + PSTRBuildLower.PreparedLayout.t q full)
  rw [packed_eq q full hq, treeSize_eq q full hq]

private theorem oldCapacity_eq (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    PA06A19PreparePackedView013.oldCapacity full.length q (CompactControllerClaims.treeSize q full) =
      PSTRBuildLower.PreparedLayout.oldCapacity q full := by
  change PA06A19PreparePackedView013.oldCapacity full.length q (CompactControllerClaims.treeSize q full) =
    PA17CellLayout003.capacityWords full.length q (PSTRBuildLower.PreparedLayout.t q full)
  rw [treeSize_eq q full hq, PA06A19PreparePackedView013.oldCapacity_eq_A17]

private theorem ordinaryWords_eq (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    PA06A19PrepareFiniteClear031Setup.ordinaryWords full.length q (CompactControllerClaims.treeSize q full) =
      PSTRBuildLower.PreparedLayout.indexWords q full := by
  change 6 * CompactControllerClaims.treeSize q full + full.length + 2 * q + 31 =
    6 * PSTRBuildLower.PreparedLayout.t q full + full.length + 2 * q + 31
  rw [treeSize_eq q full hq]

/-- All permanent bank/header/cache inputs of ST062 are read from the SAME
044 endpoint. Candidate support alone is never used to infer a heap word. -/
theorem runtimeData_of_data (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (state : WordState (PA06A19PreparePreBuild044.bits q full))
    (data : PA06A19PreparePreBuild044.Data q full state) :
    PSTRBuildLower.RuntimeData.Data q full state.heap := by
  have ht := treeSize_eq q full hq
  have hcb := controlBase_eq q full hq
  have hc := capacity_eq q full hq
  have hp := packed_eq q full hq
  have hold := oldCapacity_eq q full hq
  refine
    { toData := { mass := ?_, size := ?_, parent := ?_, degree := ?_ }
      stages := ?_
      tools := ?_
      cutoff := ?_
      capacity := ?_
      packed := ?_
      index := ?_
      cached := ?_
      header := data.cached.header }
  · have hh := data.cached.cache.1.mass_cell
    change (state.heap (BitVec.ofNat _ (PA06A19PreparePreBuild044.controlBase q full + 528))).toNat =
      full.length + q + 1 at hh
    rw [hcb] at hh
    exact word_of_toNat _ hh
  · have hh := data.cached.scalars.bank032.T
    change (state.heap (BitVec.ofNat _ (PA06A19PreparePreBuild044.controlBase q full + 2))).toNat =
      CompactControllerClaims.treeSize q full at hh
    rw [hcb, ht] at hh
    exact word_of_toNat _ hh
  · intro node
    have hh := data.cached.cache.1.parents node.val node.isLt
    change (state.heap (BitVec.ofNat _
      (PA06A19PreparePreBuild044.controlBase q full + 533 + 4 * (full.length + q + 1) + node.val))).toNat =
      (givenTreeROM q full).internal.getD node.val 0 at hh
    rw [hcb] at hh
    exact word_of_toNat _ hh
  · intro node
    have hh := data.cached.cache.2.1 node
    change (state.heap (BitVec.ofNat _
      (PA06A19PreparePreBuild044.controlBase q full + 533 + 5 * (full.length + q + 1) + node.val))).toNat =
      (givenTreeROM q full).internal.getD (PSTRBuildLower.SourceFacts.size q full + node.val) 0 at hh
    rw [hcb] at hh
    exact word_of_toNat _ hh
  · have hh := data.cached.scalars.bank032.N
    change (state.heap (BitVec.ofNat _ (PA06A19PreparePreBuild044.controlBase q full))).toNat = full.length at hh
    rw [hcb] at hh
    exact word_of_toNat _ hh
  · have hh := data.cached.scalars.bank032.Q
    change (state.heap (BitVec.ofNat _ (PA06A19PreparePreBuild044.controlBase q full + 1))).toNat = q at hh
    rw [hcb] at hh
    exact word_of_toNat _ hh
  · have hh := data.cached.scalars.oldCapacity
    rw [hcb, hold] at hh
    exact word_of_toNat _ hh
  · have hh := data.cached.scalars.bank037.C
    change (state.heap (BitVec.ofNat _ (PA06A19PreparePreBuild044.controlBase q full + 4))).toNat =
      PA06A19PreparePreBuild044.capacity q full at hh
    rw [hcb, hc] at hh
    exact word_of_toNat _ hh
  · have hh := data.cached.scalars.bank032.P
    change (state.heap (BitVec.ofNat _ (PA06A19PreparePreBuild044.controlBase q full + 5))).toNat =
      PA06A19PreparePreBuild044.packedWords q full at hh
    rw [hcb, hp] at hh
    exact word_of_toNat _ hh
  · have hh := data.cached.scalars.ordinaryBase
    rw [hcb, hp] at hh
    exact word_of_toNat _ hh
  · intro node
    have hord := data.cached.copiedOrd node
    dsimp only at hord
    let candidate : Nat := (state.heap (BitVec.ofNat _
      (PA06A19PreparePreBuild044.controlBase q full + 512 +
        PA06A19PrepareCompactParents035Ord.ordSlot full.length q node.val))).toNat
    have hcand : candidate < full.length + q + 1 := hord.2.1
    refine ⟨⟨candidate, hcand⟩, ?_, hord.2.2⟩
    have haddress : PA06A19PrepareBankNodeBit022.ordAddress full.length q
        (PSTRBuildLower.PreparedLayout.controlBase q full) node.val =
      PA06A19PreparePreBuild044.controlBase q full + 512 +
        PA06A19PrepareCompactParents035Ord.ordSlot full.length q node.val := by
      rw [← hcb]
      dsimp only [PA06A19PrepareBankNodeBit022.ordAddress,
        PA06A19PrepareCompactParents035Ord.ordSlot, RawCandidateOrderingRAM.arraySlot]
      omega
    rw [haddress]

/-- The finite clear and seven real VM zero words provide initial source
representation. This does not assert that the infinite heap is zero. -/
theorem prepared_of_data (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (state : WordState (PA06A19PreparePreBuild044.bits q full))
    (data : PA06A19PreparePreBuild044.Data q full state) :
    PSTRBuildLower.SourceRep.Prepared q full (initial (fun _ => 0)) state := by
  have hcb := controlBase_eq q full hq
  have hold := oldCapacity_eq q full hq
  have hi := ordinaryWords_eq q full hq
  have hc := capacity_eq q full hq
  have hp := packed_eq q full hq
  constructor
  · have hb := data.cached.scalars.bank032.base
    change (state.register .address).toNat = PA06A19PreparePreBuild044.controlBase q full at hb
    rw [hcb] at hb
    exact word_of_toNat _ hb
  · funext reg
    change state.heap (BitVec.ofNat _ (PSTRBuildLower.PreparedLayout.controlBase q full) +
      BitVec.ofNat _ (PSTRBuildLower.registerOffset reg)) = BitVec.ofNat _ 0
    rw [BitVec.ofNat_add_ofNat, ← hcb]
    change state.heap (BitVec.ofNat (indexWidth 32 full.length q)
      (PA06A19PreparePreBuild044.controlBase q full + PSTRBuildLower.registerSlot reg)) = 0
    have hv := data.vm (PSTRBuildLower.registerSlot reg)
      (PSTRBuildLower.registerSlot_bounds reg).1 (PSTRBuildLower.registerSlot_bounds reg).2
    exact hv
  · intro a ha
    change PA06A19PreparePackedView013.view q (PSTRBuildLower.PreparedLayout.oldCapacity q full)
      (PSTRBuildLower.PreparedLayout.capacity q full) (PSTRBuildLower.PreparedLayout.indexBase q full)
      state.heap a = 0
    have hbound : a < PA06A19PreparePackedView013.oldCapacity full.length q
        (CompactControllerClaims.treeSize q full) +
      PA06A19PrepareFiniteClear031Setup.ordinaryWords full.length q (CompactControllerClaims.treeSize q full) := by
      simpa only [hold, hi] using ha
    have hz := data.zeroView a hbound
    simpa only [hold, hc, hp, PSTRBuildLower.PreparedLayout.indexBase] using hz

/-- The whole Cnew capacity comes from044's actual clear/VM invariant,
not from the smaller C0 source simulation or runtime cache predicates. -/
theorem bounded_of_data (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (state : WordState (PA06A19PreparePreBuild044.bits q full))
    (data : PA06A19PreparePreBuild044.Data q full state) :
    PSTRBuildLower.GlobalCapacity.Bounded q full state.heap := by
  unfold PSTRBuildLower.GlobalCapacity.Bounded
  simp only [CompactControllerClaims.logicalHeap, Nat.ne_of_gt hq, ite_false]
  simpa only [capacity_eq q full hq] using data.capacityBounded

/-- One abstract endpoint supplies all three ST input predicates together.
The actual raw-to044 theorem supplies Data internally; no future execution,
zero lexical environment, or additional original caller premise occurs. -/
theorem st_input_of_data (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (state : WordState (PA06A19PreparePreBuild044.bits q full))
    (data : PA06A19PreparePreBuild044.Data q full state) :
    PSTRBuildLower.RuntimeData.Data q full state.heap ∧
      PSTRBuildLower.SourceRep.Prepared q full (initial (fun _ => 0)) state ∧
      PSTRBuildLower.GlobalCapacity.Bounded q full state.heap :=
  ⟨runtimeData_of_data q full hq state data,
    prepared_of_data q full hq state data, bounded_of_data q full hq state data⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareSTInput050
