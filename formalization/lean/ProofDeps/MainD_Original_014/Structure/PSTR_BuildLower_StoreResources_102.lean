module

public import Structure.PSTR_BuildLower_WriteData_070
public import Structure.PSTR_BuildLower_HeapControl_038
public import Structure.PSTR_BuildLower_StoreCapacity_095

/-! Real source store, full NEW-C capacity and high-cache frame share ONE
canonical actual witness. This is an endpoint contract; actual writer-prefix
resource preservation is not inferred from it. Existing public concrete port
and replacement proofs are reused, with no additional original caller field. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem heap_store_end_resources (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (physical : PhysicalROM)
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
    ∃ count ≤ 99,
      let after := packingRun physical (left ++ relativeRead (registerOffset sourceReg) .value ++
        ConcreteHeap.write (left.length + 3) pointer ++ right) count state
      Prepared q full ((Op.base (.storeHeap pointer sourceReg)).execute (givenTreeROM q full).semantic logical) after ∧
        RuntimeData.Data q full after.heap ∧ after.pc = BitVec.ofNat _ (5 * (left.length + 99)) ∧ after.halted = false ∧
        (∀ offset ≤ 512, after.heap (BitVec.ofNat _ (controlBase q full + offset)) =
          state.heap (BitVec.ofNat _ (controlBase q full + offset))) ∧
        GlobalCapacity.Bounded q full after.heap ∧ ResourceTrace.CacheFrame q full state.heap after.heap := by
  let first := relativeRead (registerOffset sourceReg) .value
  let code := left ++ first ++ ConcreteHeap.write (left.length + 3) pointer ++ right
  let middle := executeOps physical first state
  let writeLeft := left ++ first
  have firstLength : first.length = 3 := relativeRead_length _ _
  have leftLength : writeLeft.length = left.length + 3 := by simp only [writeLeft, List.length_append, firstLength]
  have shape : writeLeft ++ ConcreteHeap.write writeLeft.length pointer ++ right = code := by rw [leftLength]
  have front : packingRun physical code 3 state = middle := by
    have hr := straight_prefix physical left first (ConcreteHeap.write (left.length + 3) pointer ++ right) state
      (relativeRead_straight _ _) (by simpa only [List.append_assoc] using hcode)
      (by simpa only [List.append_assoc] using hpcfit) hpc ha 3 (by rw [firstLength])
    rw [List.take_of_length_le (by rw [firstLength])] at hr
    simpa only [code, middle, List.append_assoc] using hr
  have middleHeap : middle.heap = state.heap := rfl
  have middleBase : middle.register .address = state.register .address := rfl
  have middleActive : middle.halted = false := (executeOps_halted physical first state).trans ha
  have middlePC : middle.pc = BitVec.ofNat _ (5 * writeLeft.length) := by
    rw [executeOps_pc physical first state (relativeRead_straight _ _), hpc, firstLength, leftLength, BitVec.ofNat_add_ofNat]
    congr 1
  have middleRep : Prepared q full logical middle := by
    refine ⟨middleBase.trans hrep.address, ?_, ?_⟩
    · rw [middleHeap]
      exact hrep.registers
    · rw [middleHeap]
      exact hrep.heap
  have middleData : RuntimeData.Data q full middle.heap := by rw [middleHeap]; exact data
  have pointerNat := pointer_nat q full logical middle middleRep pointer (hf pointer)
  have middleC := RuntimeData.Data.cutoff_nat q full hq middle middleData middleRep.address
  have middleI := RuntimeData.Data.index_nat q full hq middle middleData middleRep.address
  have valueWord : middle.register .value = BitVec.ofNat _ (logical.register sourceReg) := by
    rw [relativeRead_value]
    simpa only [hrep.address, portRegisters] using congrFun hrep.registers sourceReg
  have valueNat : (middle.register .value).toNat = logical.register sourceReg := by
    rw [valueWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hf sourceReg)]
  have middleBaseNat : (middle.register .address).toNat = controlBase q full := by
    have hh : Fits (bits q full) (controlBase q full) := by
      simpa only [Nat.add_zero] using bank_offset_fits q full hq 0 (by decide)
    change controlBase q full < 2 ^ bits q full at hh
    rw [middleRep.address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hh]
  have hlo := (registerSlot_bounds pointer).1
  have hhi := (registerSlot_bounds pointer).2
  change 32 ≤ registerOffset pointer at hlo
  change registerOffset pointer < 39 at hhi
  have bankLower : 4 + packedCapacityWords q (capacity q full) (bits q full) + 1 ≤
      (middle.register .address).toNat + registerOffset pointer := by
    rw [middleBaseNat]
    have hh : 4 + packedCapacityWords q (capacity q full) (bits q full) + 1 ≤ indexBase q full + indexWords q full :=
      packed_lookahead_before_end q full
    have hd := ordinary_before_control q full
    omega
  have bankFit : Fits (bits q full) ((middle.register .address).toNat + registerOffset pointer) := by
    rw [middleBaseNat]
    exact bank_offset_fits q full hq _ (by omega)
  have writer := ConcreteHeap.write_call_heap q (capacity q full) physical writeLeft right pointer middle middleData.header hq
    (by have hh := bits_room q full; omega) (width_room q full)
    (by rw [middleC]; exact oldCapacity_le q full hq)
    (by simpa only [pointerNat, middleC] using packed_scale q full hq (logical.register pointer))
    (by simpa only [pointerNat, middleC] using packed_next q full hq (logical.register pointer)) bankLower bankFit
    (by rwa [shape]) (by rwa [shape]) middlePC middleActive
  have control := ConcreteHeap.write_call_control physical writeLeft right pointer middle middlePC middleActive
    (by rwa [shape]) (by rwa [shape])
  let count := DispatchRun.steps (PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer)) (Ordinary.write pointer) pointer middle
  let after := packingRun physical code count middle
  have actualHeap : after.heap = ConcreteHeap.writeViewHeap q middle pointer := by
    simpa only [after, count, shape] using writer.2
  have actualBase : after.register .address = middle.register .address := by
    simpa only [after, count, shape] using control.2.2
  have actualRep := store_replacement q (oldCapacity q full) (capacity q full) (indexBase q full) (indexWords q full)
    (controlBase q full) (givenTreeROM q full) logical middle after pointer sourceReg middleRep pointerNat middleC middleI valueNat
    actualHeap actualBase hq (by have hh := bits_room q full; omega) (width_room q full) (oldCapacity_le q full hq)
    (capacity_product_fits q full hq) le_rfl (ordinary_end_fits q full hq) had
    (by intro hp; exact lt_of_le_of_lt (by omega) (packed_next q full hq (logical.register pointer) hp)) hvalue
    (packed_lookahead_before_end q full) (by have hh := ordinary_before_control q full; omega)
    (bank_offset_fits q full hq 39 (by decide))
  have actualData : RuntimeData.Data q full after.heap := by
    rw [actualHeap]
    exact RuntimeData.Data.write_replacement q full hq logical middle middleRep middleData pointer (hf pointer) had
  have actualBounded : GlobalCapacity.Bounded q full after.heap := by
    rw [actualHeap]
    exact GlobalCapacity.write_replacement q full hq logical middle middleRep middleData pointer (hf pointer) had
      (by intro hp; rw [valueNat]; exact hvalue hp) (by rw [middleHeap]; exact bounded)
  have actualCache : ResourceTrace.CacheFrame q full state.heap after.heap := by
    intro point hpoint hfit
    rw [actualHeap]
    have hh := GlobalCapacity.write_replacement_cache q full hq logical middle middleRep middleData pointer (hf pointer) had
    exact (hh point hpoint hfit).trans (congrFun middleHeap _)
  have whole : packingRun physical code (3 + count) state = after := by rw [PSTRWordSegments.run_add, front]
  refine ⟨3 + count, by have hc : count ≤ 96 := writer.1; omega, ?_⟩
  dsimp only
  rw [whole]
  refine ⟨actualRep, actualData, ?_, ?_, ?_, actualBounded, actualCache⟩
  · have he := control.1
    rw [shape] at he
    simpa only [after, leftLength, Nat.add_assoc] using he
  · simpa only [after, count, shape] using control.2.1
  · intro offset ho
    rw [actualHeap]
    exact (RuntimeData.write_replacement_offset q full hq logical middle middleRep middleData pointer (hf pointer) had offset ho).trans
      (congrFun middleHeap _)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
