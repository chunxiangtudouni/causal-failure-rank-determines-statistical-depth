module

public import Structure.PA06_A19Prepare_StaticMetadata036_Copy

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Private candidate for the first four original staticMetadata segments:
edge count, parents, degrees, flat children. The real fixed program reads
permanent CB+2=t, CB+6=4+P and the copied CB+528=M. It uses no producer
control slot. The remaining five segments are NOT claimed produced here. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass parentAddress degreeBase childrenBase OutputData)

def initializeAdjacency : List PackingOp :=
  [.base (.base (.constant .index 6)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .old .index)), .base (.base (.constant .fresh 2)),
   .base (.base (.add .old .old .fresh)), .base (.base (.constant .index 2)),
   .base (.base (.add .index .address .index)), .base (.base (.loadHeap .total .index)),
   .base (.base (.constant .fresh 1)), .base (.subtract .value .total .fresh),
   .base (.base (.storeHeap .old .value)), .base (.base (.add .old .old .fresh)),
   .base (.base (.constant .index 528)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .value .index)), .base (.base (.constant .fresh 4)),
   .arithmetic .multiply .value .value .fresh, .base (.base (.constant .index 533)),
   .base (.base (.add .index .address .index)), .base (.base (.add .index .index .value)),
   .base (.base (.constant .fresh 1)), .base (.base (.constant .flag 0))]

def setupDegreeChildren : List PackingOp :=
  [.base (.base (.constant .index 528)), .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .total .index)), .base (.base (.constant .fresh 5)),
   .arithmetic .multiply .total .total .fresh, .base (.base (.constant .index 533)),
   .base (.base (.add .index .address .index)), .base (.base (.add .index .index .total)),
   .base (.base (.constant .total 2)), .base (.base (.add .total .address .total)),
   .base (.base (.loadHeap .total .total)), .base (.base (.constant .fresh 2)),
   .arithmetic .multiply .total .total .fresh, .base (.base (.constant .fresh 1)),
   .base (.subtract .total .total .fresh)]

def adjacencyProgramAt (start : Nat) : List PackingOp :=
  initializeAdjacency ++ copyProgramAt (start + 22) ++ setupDegreeChildren ++ copyProgramAt (start + 46)

theorem initializeAdjacency_length : initializeAdjacency.length = 22 := rfl
theorem setupDegreeChildren_length : setupDegreeChildren.length = 15 := rfl
theorem adjacencyProgramAt_length (start : Nat) : (adjacencyProgramAt start).length = 55 := rfl

theorem initializeAdjacency_noJump : ∀ op ∈ initializeAdjacency, NoJump op := by
  simp [initializeAdjacency, NoJump]

theorem setupDegreeChildren_noJump : ∀ op ∈ setupDegreeChildren, NoJump op := by
  simp [setupDegreeChildren, NoJump]

theorem initializeAdjacency_effect (rom : PhysicalROM) (CB M t P : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hM : state.heap (CB + 528) = M)
    (ht : state.heap (CB + 2) = t) (hbase : state.heap (CB + 6) = 4 + P)
    (hbelow : 6 + P < CB) :
    let after := runOps rom initializeAdjacency state
    after.register .address = CB ∧ after.register .index = parentAddress CB M 0 ∧
      after.register .old = 7 + P ∧ after.register .total = t ∧
      after.register .fresh = 1 ∧ after.register .flag = 0 ∧
      after.heap = Function.update state.heap (6 + P) (t - 1) := by
  simp (disch := omega) [initializeAdjacency, runOps, natExecuteOp, natArithmetic,
    Op.execute, Instruction.execute, hCB, hM, ht, hbase, Function.update_apply,
    parentAddress, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]

theorem setupDegreeChildren_effect (rom : PhysicalROM) (CB M t : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hM : state.heap (CB + 528) = M)
    (ht : state.heap (CB + 2) = t) :
    let after := runOps rom setupDegreeChildren state
    after.register .address = CB ∧ after.register .index = degreeBase CB M ∧
      after.register .old = state.register .old ∧ after.register .total = 2 * t - 1 ∧
      after.register .fresh = 1 ∧ after.register .flag = state.register .flag ∧ after.heap = state.heap := by
  simp [setupDegreeChildren, runOps, natExecuteOp, natArithmetic, Op.execute,
    Instruction.execute, hCB, hM, ht, degreeBase, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]

/-- Original allocation arithmetic discharges output/bank disjointness;
no separate larger allocation or caller-supplied safety property is needed. -/
theorem adjacency_below_control (M t P : Nat) (ht : 0 < t) :
    6 + P + 3 * t ≤ 4 + P + 4096 * (M + t) := by omega

theorem adjacency_sources_disjoint (CB M t P : Nat) (ht : 0 < t)
    (hlayout : CB = 4 + P + 4096 * (M + t)) :
    7 + P + t ≤ parentAddress CB M 0 ∧
      7 + P + t + (2 * t - 1) ≤ degreeBase CB M := by
  unfold parentAddress degreeBase
  omega

/-- Semantic output of the real first55 instructions and their loops.
These words are the ORIGINAL four leading metadata segments. -/
def AdjacencyWritten (q : Nat) (full : List (Finset (Fin q))) (P : Nat) (state : NatState) : Prop :=
  state.heap (6 + P) = PSTRStaticLayout.edgeCount q full ∧
  (∀ node < preparedSize q full,
    state.heap (7 + P + node) = (givenTreeROM q full).internal.getD node 0) ∧
  (∀ node < preparedSize q full,
    state.heap (7 + P + preparedSize q full + node) =
      (givenTreeROM q full).internal.getD (preparedSize q full + node) 0) ∧
  (∀ position < (givenTreeROM q full).children.length,
    state.heap (7 + P + 2 * preparedSize q full + position) = (givenTreeROM q full).children.getD position 0)

/-- Exact original-paper list correspondence, independent of compilation.
No supplied staticMetadata list is used by the actual producer. -/
theorem adjacencyWritten_static (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) (P : Nat) (state : NatState)
    (written : AdjacencyWritten q full P state) :
    ∀ position < 3 * preparedSize q full,
      state.heap (6 + P + position) = (staticMetadata q full).getD position 0 := by
  intro position hp
  have htpos : 0 < preparedSize q full := by
    have h := PA06A19PrepareControlBank017.treeSize_pos full hq
    simpa only [treeSize, Nat.ne_of_gt hq, ite_false] using h
  have offsetParent : PSTRStaticLayout.offset q full 1 = 1 := rfl
  have offsetDegree : PSTRStaticLayout.offset q full 2 = 1 + preparedSize q full := rfl
  have offsetChildren : PSTRStaticLayout.offset q full 3 = 1 + 2 * preparedSize q full := rfl
  have childWordsEq : PSTRStaticLayout.childWords q full = (givenTreeROM q full).children := rfl
  by_cases hzero : position = 0
  · subst position
    have h := PSTRStaticLayout.metadata_chunk_getD q full hq 0 0 (by decide)
      (by simp [PSTRStaticLayout.chunks])
    simpa only [PSTRStaticLayout.offset, PSTRStaticLayout.chunks, List.getElem_cons_zero,
      Nat.add_zero] using written.1.trans h.symm
  · by_cases hparent : position < 1 + preparedSize q full
    · let node : (prepareNormalization q full).indexed.NodeId := ⟨position - 1, by
        change position - 1 < preparedSize q full
        omega⟩
      have hword := written.2.1 node.val node.isLt
      have hrom := UniformNormalizationRAM.givenTreeROM_parent q full node
      have h := PSTRStaticLayout.metadata_chunk_getD q full hq 1 node.val (by decide)
        (by simp only [PSTRStaticLayout.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
          List.length_map, List.length_finRange]; exact node.isLt)
      have hget := PSTRStaticLayout.mapped_finRange_get
        (fun id : (prepareNormalization q full).indexed.NodeId =>
          encodedNode (prepareNormalization q full).indexed ((prepareNormalization q full).indexed.parents.get id)) node
      simp only [PSTRStaticLayout.chunks, List.getElem_cons_succ, List.getElem_cons_zero] at h
      rw [hget] at h
      change (givenTreeROM q full).internal.getD node.val 0 = _ at hrom
      have hoff : PSTRStaticLayout.offset q full 1 + node.val = position := by
        rw [offsetParent]
        dsimp only [node]
        omega
      rw [hoff] at h
      have haddress : 7 + P + node.val = 6 + P + position := by dsimp only [node]; omega
      rw [haddress] at hword
      exact hword.trans (hrom.trans h.symm)
    · by_cases hdegree : position < 1 + 2 * preparedSize q full
      · let node : (prepareNormalization q full).indexed.NodeId := ⟨position - (1 + preparedSize q full), by
          change position - (1 + preparedSize q full) < preparedSize q full
          omega⟩
        have hword := written.2.2.1 node.val node.isLt
        have hrom := UniformNormalizationRAM.givenTreeROM_degree q full node
        have h := PSTRStaticLayout.metadata_chunk_getD q full hq 2 node.val (by decide)
          (by simp only [PSTRStaticLayout.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
            List.length_map, List.length_finRange]; exact node.isLt)
        have hget := PSTRStaticLayout.mapped_finRange_get
          (fun id : (prepareNormalization q full).indexed.NodeId =>
            ((prepareNormalization q full).indexed.children.get id).size) node
        simp only [PSTRStaticLayout.chunks, List.getElem_cons_succ, List.getElem_cons_zero] at h
        rw [hget] at h
        change (givenTreeROM q full).internal.getD (preparedSize q full + node.val) 0 = _ at hrom
        have hoff : PSTRStaticLayout.offset q full 2 + node.val = position := by
          rw [offsetDegree]
          dsimp only [node]
          omega
        rw [hoff] at h
        have haddress : 7 + P + preparedSize q full + node.val = 6 + P + position := by
          dsimp only [node]
          omega
        rw [haddress] at hword
        exact hword.trans (hrom.trans h.symm)
      · let index := position - (1 + 2 * preparedSize q full)
        have hi : index < (givenTreeROM q full).children.length := by
          rw [RawTreeSerialization.givenTreeROM_children_length q full hq hl]
          change index < preparedSize q full - 1
          dsimp only [index]
          omega
        have hword := written.2.2.2 index hi
        have h := PSTRStaticLayout.metadata_chunk_getD q full hq 3 index (by decide)
          (by simpa only [PSTRStaticLayout.chunks, List.getElem_cons_succ, List.getElem_cons_zero,
            childWordsEq] using hi)
        change (staticMetadata q full).getD (PSTRStaticLayout.offset q full 3 + index) 0 =
          (givenTreeROM q full).children[index] at h
        rw [← List.getD_eq_getElem _ 0 hi] at h
        have hoff : PSTRStaticLayout.offset q full 3 + index = position := by
          rw [offsetChildren]
          dsimp only [index]
          omega
        rw [hoff] at h
        have haddress : 7 + P + 2 * preparedSize q full + index = 6 + P + position := by
          dsimp only [index]
          omega
        rw [haddress] at hword
        exact hword.trans h.symm

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
