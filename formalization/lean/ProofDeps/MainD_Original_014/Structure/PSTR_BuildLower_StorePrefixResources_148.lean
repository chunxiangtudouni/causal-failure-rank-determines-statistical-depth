module

public import Structure.PSTR_BuildLower_CanonicalStoreEnd_145
public import Structure.PSTR_BuildLower_HeapWriteResources_147
public import Structure.PSTR_BuildLower_LoadResources_101
public import Structure.PSTR_BuildLower_FixedExprAccess_115

/-! The actual source-value read3 followed by the chosen real heap writer.
Source endpoint and full prefix resources use the SAME exposed canonical
clock, rather than identifying independently bounded existential witnesses. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem heap_store_prefix_resources (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (physical : PhysicalROM)
    (pointer sourceReg : Register) (logical : State) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (bounded : GlobalCapacity.Bounded q full state.heap)
    (hf : ∀ reg, Fits (bits q full) (logical.register reg))
    (had : logical.register pointer < oldCapacity q full + indexWords q full)
    (hvalue : logical.register pointer < oldCapacity q full → logical.register sourceReg ≤ q)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ relativeRead (registerOffset sourceReg) .value ++
      ConcreteHeap.write (left.length + 3) pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ relativeRead (registerOffset sourceReg) .value ++
      ConcreteHeap.write (left.length + 3) pointer ++ right).length)) :
    let whole := left ++ relativeRead (registerOffset sourceReg) .value ++ ConcreteHeap.write (left.length + 3) pointer ++ right
    let count := DispatchRun.steps (PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer)) (Ordinary.write pointer) pointer
      (executeOps physical (relativeRead (registerOffset sourceReg) .value) state)
    let after := packingRun physical whole (3 + count) state
    (3 + count ≤ 99 ∧ Prepared q full ((Op.base (.storeHeap pointer sourceReg)).execute (givenTreeROM q full).semantic logical) after ∧
      RuntimeData.Data q full after.heap ∧ after.pc = BitVec.ofNat _ (5 * (left.length + 99)) ∧ after.halted = false ∧
      (∀ offset ≤ 512, after.heap (BitVec.ofNat _ (controlBase q full + offset)) =
        state.heap (BitVec.ofNat _ (controlBase q full + offset))) ∧
      GlobalCapacity.Bounded q full after.heap ∧ ResourceTrace.CacheFrame q full state.heap after.heap) ∧
      ResourceTrace.Keeps q full physical whole state (3 + count) ∧
      TraceAccess.Safe (allocated q full) physical whole state (3 + count) := by
  let first := relativeRead (registerOffset sourceReg) .value
  let code := left ++ first ++ ConcreteHeap.write (left.length + 3) pointer ++ right
  let middle := executeOps physical first state
  let writeLeft := left ++ first
  let count := DispatchRun.steps (PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer)) (Ordinary.write pointer) pointer middle
  have firstLength : first.length = 3 := relativeRead_length _ _
  have leftLength : writeLeft.length = left.length + 3 := by simp only [writeLeft, List.length_append, firstLength]
  have shape : writeLeft ++ ConcreteHeap.write writeLeft.length pointer ++ right = code := by rw [leftLength]
  have localCode : WordsFit (bits q full) (packingCode (left ++ first ++ (ConcreteHeap.write (left.length + 3) pointer ++ right))) := by
    simpa only [first, List.append_assoc] using hcode
  have localFit : Fits (bits q full) (5 * (left ++ first ++ (ConcreteHeap.write (left.length + 3) pointer ++ right)).length) := by
    simpa only [first, List.append_assoc] using hpcfit
  have front : packingRun physical code 3 state = middle := by
    have hr := straight_prefix physical left first (ConcreteHeap.write (left.length + 3) pointer ++ right) state
      (relativeRead_straight _ _) localCode localFit hpc ha 3 (by rw [firstLength])
    rw [List.take_of_length_le (by rw [firstLength])] at hr
    simpa only [code, middle, List.append_assoc] using hr
  have frontReadonly : ∀ clock ≤ 3, (packingRun physical code clock state).heap = state.heap := by
    intro clock hc
    rw [show code = left ++ first ++ (ConcreteHeap.write (left.length + 3) pointer ++ right) by simp only [code, List.append_assoc],
      straight_prefix physical left first _ state (relativeRead_straight _ _) localCode localFit hpc ha clock
        (by simpa only [firstLength] using hc)]
    funext point
    exact relativeRead_prefix_heap physical (registerOffset sourceReg) .value point state clock
  have frontKeeps := ResourceTrace.of_readonly q full physical code state 3 bounded frontReadonly
  have slots := registerSlot_bounds sourceReg
  change 32 ≤ registerOffset sourceReg ∧ registerOffset sourceReg < 39 at slots
  have primitive := BankAccess.read_safe physical (registerOffset sourceReg) (allocated q full) .value state
    (BankAccess.point_room q full hq state hrep.address _ (by omega))
  have frontSafe := TraceAccess.straight physical left first (ConcreteHeap.write (left.length + 3) pointer ++ right)
    (allocated q full) state (relativeRead_straight _ _) primitive hpc ha localCode localFit
  have frontSafeWhole : TraceAccess.Safe (allocated q full) physical code state 3 := by
    simpa only [code, List.append_assoc, firstLength] using frontSafe
  have middleHeap : middle.heap = state.heap := rfl
  have middleBase : middle.register .address = state.register .address := rfl
  have middleRep : Prepared q full logical middle := by
    refine ⟨middleBase.trans hrep.address, ?_, ?_⟩
    · rw [middleHeap]
      exact hrep.registers
    · rw [middleHeap]
      exact hrep.heap
  have middleData : RuntimeData.Data q full middle.heap := by rw [middleHeap]; exact data
  have middleBounded : GlobalCapacity.Bounded q full middle.heap := by rw [middleHeap]; exact bounded
  have middlePC : middle.pc = BitVec.ofNat _ (5 * writeLeft.length) := by
    rw [executeOps_pc physical first state (relativeRead_straight _ _), hpc, firstLength, leftLength, BitVec.ofNat_add_ofNat]
    congr 1
  have middleActive : middle.halted = false := (executeOps_halted physical first state).trans ha
  have valueWord : middle.register .value = BitVec.ofNat _ (logical.register sourceReg) := by
    rw [relativeRead_value]
    simpa only [hrep.address, portRegisters] using congrFun hrep.registers sourceReg
  have valueNat : (middle.register .value).toNat = logical.register sourceReg := by
    rw [valueWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hf sourceReg)]
  have tail := ConcreteHeap.write_prefix_resources q full hq physical pointer logical middle middleRep middleData middleBounded
    (hf pointer) had (by intro hp; rw [valueNat]; exact hvalue hp) writeLeft right middlePC middleActive
    (by rwa [shape]) (by rwa [shape])
  rw [shape] at tail
  have endpoint := heap_store_canonical_end_resources q full hq physical pointer sourceReg logical state hrep data bounded hf had hvalue
    left right hpc ha hcode hpcfit
  refine ⟨endpoint, ?_, ?_⟩
  · exact ResourceTrace.keeps_add q full physical code state 3 count frontKeeps (by rw [front]; exact tail.1)
  · exact TraceAccess.add (allocated q full) physical code state 3 count frontSafeWhole (by rw [front]; exact tail.2)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
