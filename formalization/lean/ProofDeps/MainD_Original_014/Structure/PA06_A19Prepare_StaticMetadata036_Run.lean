module

public import Structure.PA06_A19Prepare_StaticMetadata036

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Private uncompiled actual Nat run of the fixed55-op adjacency prefix.
This consumes the genuine023 output, the permanent t/base cells and the
original CB formula; it takes no free metadata list or all-run safety oracle.
The entire nine-segment metadata producer and Word lift remain open. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass parentAddress degreeBase childrenBase OutputData)

theorem straight_run (rom : PhysicalROM) (left block right : List PackingOp)
    (hstraight : ∀ op ∈ block, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    natRun rom (left ++ block ++ right) block.length state = runOps rom block state := by
  exact natRun_of_straight_segment rom (left ++ block ++ right) block left.length
    (by simp only [List.length_append]; omega)
    (PA17UniformGenerator035a.segment_index left block right) hstraight state hpc ha

theorem initializeAdjacency_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    natRun rom (left ++ adjacencyProgramAt left.length ++ right) 22 state =
      runOps rom initializeAdjacency state := by
  have h := straight_run rom left initializeAdjacency
    (copyProgramAt (left.length + 22) ++ setupDegreeChildren ++ copyProgramAt (left.length + 46) ++ right)
    initializeAdjacency_noJump state hpc ha
  simpa only [adjacencyProgramAt, List.append_assoc, initializeAdjacency_length] using h

theorem setupDegreeChildren_run (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * (left.length + 31)) (ha : state.halted = false) :
    natRun rom (left ++ adjacencyProgramAt left.length ++ right) 15 state =
      runOps rom setupDegreeChildren state := by
  let lead := left ++ initializeAdjacency ++ copyProgramAt (left.length + 22)
  have hp : lead.length = left.length + 31 := by
    simp only [lead, List.length_append, initializeAdjacency_length, copyProgramAt_length]
  have h := straight_run rom lead setupDegreeChildren (copyProgramAt (left.length + 46) ++ right)
    setupDegreeChildren_noJump state (by rw [hp]; exact hpc) ha
  simpa only [lead, adjacencyProgramAt, List.append_assoc, setupDegreeChildren_length] using h

def adjacencyTotalSteps (t : Nat) : Nat := 22 + (9 * t + 2) + 15 + (9 * (2 * t - 1) + 2)

theorem adjacencyTotalSteps_eq (t : Nat) (ht : 0 < t) : adjacencyTotalSteps t = 27 * t + 32 := by
  unfold adjacencyTotalSteps
  omega

/-- A true run writes the first four original metadata segments and nothing
outside their ordinary output interval. The returned old pointer is exactly
the start of the original cardinality segment. This is a partial producer,
not the complete staticMetadata obligation. -/
theorem adjacency_build (rom : PhysicalROM) (left right : List PackingOp)
    (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (CB P : Nat) (before : NatState) (input : OutputData q full CB before)
    (hpermanentT : before.heap (CB + 2) = preparedSize q full)
    (hpermanentBase : before.heap (CB + 6) = 4 + P)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (hpc : before.pc = 5 * left.length) (ha : before.halted = false) :
    let after := natRun rom (left ++ adjacencyProgramAt left.length ++ right)
      (adjacencyTotalSteps (preparedSize q full)) before
    AdjacencyWritten q full P after ∧
      (∀ address, address < 6 + P ∨ 6 + P + 3 * preparedSize q full ≤ address →
        after.heap address = before.heap address) ∧
      after.register .address = CB ∧ after.register .old = 6 + P + 3 * preparedSize q full ∧
      after.register .fresh = 1 ∧ after.register .flag = 0 ∧
      after.pc = 5 * (left.length + 55) ∧ after.halted = false := by
  let t := preparedSize q full
  let M := mass q full
  have ht : 0 < t := by
    have h := PA06A19PrepareControlBank017.treeSize_pos full hq
    simpa only [treeSize, Nat.ne_of_gt hq, ite_false] using h
  have htM : t ≤ M := prepared_indexed_size_le q full
  have hbelow : 6 + P + 3 * t ≤ CB := adjacency_below_control M t P ht |>.trans_eq hlayout.symm
  have hdisjoint := adjacency_sources_disjoint CB M t P ht hlayout
  let seed := runOps rom initializeAdjacency before
  have hs := initializeAdjacency_effect rom CB M t P before input.1.address input.1.mass_cell
    hpermanentT hpermanentBase (by omega)
  change seed.register .address = CB ∧ seed.register .index = parentAddress CB M 0 ∧
    seed.register .old = 7 + P ∧ seed.register .total = t ∧ seed.register .fresh = 1 ∧
    seed.register .flag = 0 ∧ seed.heap = Function.update before.heap (6 + P) (t - 1) at hs
  rcases hs with ⟨hsCB, hsindex, hsold, hstotal, hsfresh, hsflag, hsheap⟩
  have hspc : seed.pc = 5 * (left.length + 22) := by
    rw [runOps_pc rom _ before initializeAdjacency_noJump, hpc, initializeAdjacency_length]
    omega
  have hsa : seed.halted = false := (runOps_halted rom _ before).trans ha
  let code := left ++ adjacencyProgramAt left.length ++ right
  let first := natRun rom code (9 * t + 2) seed
  have hfirst := copy_run rom (left ++ initializeAdjacency)
    (setupDegreeChildren ++ copyProgramAt (left.length + 46) ++ right)
    CB (parentAddress CB M 0) (7 + P) t seed
    (by simpa only [List.length_append, initializeAdjacency_length] using hspc) hsa
    hsCB hsindex hsold hstotal hsfresh hsflag hdisjoint.1
  have hfirst' : (∀ index < t, first.heap (7 + P + index) = seed.heap (parentAddress CB M 0 + index)) ∧
    (∀ address, address < 7 + P ∨ 7 + P + t ≤ address → first.heap address = seed.heap address) ∧
    first.register .address = CB ∧ first.register .old = 7 + P + t ∧
    first.register .fresh = 1 ∧ first.register .flag = 0 ∧
    first.pc = 5 * (left.length + 31) ∧ first.halted = false := by
    simpa only [first, code, adjacencyProgramAt, List.length_append, initializeAdjacency_length,
      copyProgramAt_length, List.append_assoc, Nat.add_assoc] using hfirst
  rcases hfirst' with ⟨hfirstData, hfirstFrame, hfirstCB, hfirstOld, hfirstFresh,
    hfirstFlag, hfirstPC, hfirstActive⟩
  have hfirstM : first.heap (CB + 528) = M := by
    rw [hfirstFrame _ (Or.inr (by omega)), hsheap, Function.update_of_ne (by omega)]
    exact input.1.mass_cell
  have hfirstT : first.heap (CB + 2) = t := by
    rw [hfirstFrame _ (Or.inr (by omega)), hsheap, Function.update_of_ne (by omega)]
    exact hpermanentT
  let setup := runOps rom setupDegreeChildren first
  have hp := setupDegreeChildren_effect rom CB M t first hfirstCB hfirstM hfirstT
  change setup.register .address = CB ∧ setup.register .index = degreeBase CB M ∧
    setup.register .old = first.register .old ∧ setup.register .total = 2 * t - 1 ∧
    setup.register .fresh = 1 ∧ setup.register .flag = first.register .flag ∧ setup.heap = first.heap at hp
  rcases hp with ⟨hpCB, hpindex, hpold, hptotal, hpfresh, hpflag, hpheap⟩
  have hppc : setup.pc = 5 * (left.length + 46) := by
    rw [runOps_pc rom _ first setupDegreeChildren_noJump, hfirstPC, setupDegreeChildren_length]
    omega
  have hpa : setup.halted = false := (runOps_halted rom _ first).trans hfirstActive
  let after := natRun rom code (9 * (2 * t - 1) + 2) setup
  have hlast := copy_run rom
    (left ++ initializeAdjacency ++ copyProgramAt (left.length + 22) ++ setupDegreeChildren)
    right CB (degreeBase CB M) (7 + P + t) (2 * t - 1) setup
    (by simpa only [List.length_append, initializeAdjacency_length, copyProgramAt_length,
      setupDegreeChildren_length, Nat.add_assoc] using hppc) hpa hpCB hpindex (hpold.trans hfirstOld)
    hptotal hpfresh (hpflag.trans hfirstFlag) hdisjoint.2
  have hlast' : (∀ index < 2 * t - 1, after.heap (7 + P + t + index) = setup.heap (degreeBase CB M + index)) ∧
    (∀ address, address < 7 + P + t ∨ 7 + P + t + (2 * t - 1) ≤ address →
      after.heap address = setup.heap address) ∧
    after.register .address = CB ∧ after.register .old = 7 + P + t + (2 * t - 1) ∧
    after.register .fresh = 1 ∧ after.register .flag = 0 ∧
    after.pc = 5 * (left.length + 55) ∧ after.halted = false := by
    simpa only [after, code, adjacencyProgramAt, List.length_append, initializeAdjacency_length,
      copyProgramAt_length, setupDegreeChildren_length, List.append_assoc, Nat.add_assoc] using hlast
  rcases hlast' with ⟨hlastData, hlastFrame, hlastCB, hlastOld, hlastFresh,
    hlastFlag, hlastPC, hlastActive⟩
  have hwhole : natRun rom code (adjacencyTotalSteps t) before = after := by
    dsimp only [adjacencyTotalSteps]
    rw [natRun_add rom code (22 + (9 * t + 2) + 15) (9 * (2 * t - 1) + 2) before,
      natRun_add rom code (22 + (9 * t + 2)) 15 before,
      natRun_add rom code 22 (9 * t + 2) before,
      initializeAdjacency_run rom left right before hpc ha,
      setupDegreeChildren_run rom left right first hfirstPC hfirstActive]
  dsimp only
  rw [hwhole]
  refine ⟨?_, ?_, hlastCB, ?_, hlastFresh, hlastFlag, hlastPC, hlastActive⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hlastFrame _ (Or.inl (by omega)), hpheap,
        hfirstFrame _ (Or.inl (by omega)), hsheap, Function.update_self]
      exact (PSTRStaticLayout.edgeCount_eq q full hq hl).symm
    · intro node hn
      have hn' : node < t := hn
      rw [hlastFrame _ (Or.inl (by omega)), hpheap, hfirstData node hn', hsheap]
      have he : parentAddress CB M 0 + node = parentAddress CB M node := by unfold parentAddress; omega
      rw [he, Function.update_of_ne (by unfold parentAddress; omega)]
      exact input.1.parents node hn
    · intro node hn
      have hn' : node < t := hn
      rw [hlastData node (by omega), hpheap,
        hfirstFrame _ (Or.inr (by unfold degreeBase; omega)), hsheap,
        Function.update_of_ne (by unfold degreeBase; omega)]
      exact input.2.1 ⟨node, hn⟩
    · intro index hi
      have hi' : index < t - 1 := by
        simpa only [RawTreeSerialization.givenTreeROM_children_length q full hq hl] using hi
      have he : 7 + P + 2 * preparedSize q full + index = 7 + P + t + (t + index) := by
        dsimp only [t]
        omega
      rw [he, hlastData (t + index) (by omega), hpheap,
        hfirstFrame _ (Or.inr (by unfold degreeBase; omega)), hsheap,
        Function.update_of_ne (by unfold degreeBase; omega)]
      have had : degreeBase CB M + (t + index) = childrenBase CB M t + index := by
        unfold childrenBase
        omega
      rw [had]
      exact input.2.2 index hi
  · intro address hout
    rw [hlastFrame _ (by rcases hout with h | h; exact Or.inl (by omega); exact Or.inr (by omega)),
      hpheap, hfirstFrame _ (by rcases hout with h | h; exact Or.inl (by omega); exact Or.inr (by omega)),
      hsheap, Function.update_of_ne (by rcases hout with h | h <;> omega)]
  · rw [hlastOld]
    omega

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
