module

public import Structure.PSTR_BuildLower_ReadExit_066
public import Structure.PSTR_BuildLower_RuntimeFields_065
public import Structure.PSTR_BuildLower_HeapControl_038
public import Structure.PSTR_BuildLower_InputPort_055

/-! Concrete constructors for the compositional read proof object. Each field
comes from the SAME actual fixed-port run. All dimension/packing/cache room is
discharged from original F8192/w32 geometry and true materialized producer data. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem pointer_nat (q : Nat) (full : List (Finset (Fin q))) (logical : State) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (pointer : Register) (hf : Fits (bits q full) (logical.register pointer)) :
    (Ordinary.pointerValue state pointer).toNat = logical.register pointer := by
  have hw : Ordinary.pointerValue state pointer = BitVec.ofNat _ (logical.register pointer) := by
    simpa only [Ordinary.pointerValue, hrep.address, portRegisters] using congrFun hrep.registers pointer
  rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf]

theorem heap_read_result_frame {bits : Nat} (rom : PhysicalROM) (left : List PackingOp)
    (pointer : Register) (state : WordState bits) :
    (DispatchRun.result rom left PA06A19PrepareBankPacked021.read (Ordinary.read pointer) pointer state).heap = state.heap := by
  unfold DispatchRun.result
  split <;> rfl

def heap_read_exit (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (physical : PhysicalROM)
    (pointer : Register) (logical : State) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (hptr : Fits (bits q full) (logical.register pointer))
    (had : logical.register pointer < oldCapacity q full + indexWords q full)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ ConcreteHeap.read left.length pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ ConcreteHeap.read left.length pointer ++ right).length)) :
    ReadExit physical left (ConcreteHeap.read left.length pointer) right state (logical.heap (logical.register pointer)) 45 := by
  have hp := pointer_nat q full logical state hrep pointer hptr
  have hc := RuntimeData.Data.cutoff_nat q full hq state data hrep.address
  have hi := RuntimeData.Data.index_nat q full hq state data hrep.address
  have value := ViewStep.read_call_view q (oldCapacity q full) (capacity q full) (indexBase q full) (logical.register pointer)
    physical left right pointer state hp hc hi data.header
    (by have hh := bits_room q full; omega) (width_room q full) (oldCapacity_le q full hq)
    (packed_scale q full hq (logical.register pointer)) hcode hpcfit hpc ha
  have control := ConcreteHeap.read_call_control physical left right pointer state hpc ha hcode hpcfit
  let count := DispatchRun.steps PA06A19PrepareBankPacked021.read (Ordinary.read pointer) pointer state
  have hv : ((packingRun physical (left ++ ConcreteHeap.read left.length pointer ++ right) count state).register .value).toNat =
      logical.heap (logical.register pointer) := value.2.trans (hrep.heap _ had)
  have he : DispatchRun.code PA06A19PrepareBankPacked021.read (Ordinary.read pointer) left.length pointer =
      ConcreteHeap.read left.length pointer := DispatchRun.code_read _ _ _
  have hr := DispatchRun.run physical left PA06A19PrepareBankPacked021.read (Ordinary.read pointer) right pointer
    PA06A19PrepareBankPacked021.read_straight (Ordinary.read_straight pointer)
    (by rwa [he]) (by rwa [he]) state hpc ha
  rw [he] at hr
  refine
    { steps := count
      bounded := value.1
      value := ?_
      heap := ?_
      address := control.2.2
      pc := ?_
      active := control.2.1 }
  · rw [← hv, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hr, heap_read_result_frame]
  · simpa only [ConcreteHeap.read_length] using control.1

theorem input_read_exit (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) (hq : 0 < q)
    (pointer : Register) (logical : State) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (hptr : Fits (bits q full) (logical.register pointer))
    (hlower : 3 ≤ logical.register pointer) (hupper : logical.register pointer < (givenTreeROM q full).input.length)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ ConcreteAST.inputCode left.length pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ ConcreteAST.inputCode left.length pointer ++ right).length)) :
    Nonempty (ReadExit (CompactControllerClaims.controllerInput q full used) left (ConcreteAST.inputCode left.length pointer) right state
      ((givenTreeROM q full).semantic.read .input (logical.register pointer)) 67) := by
  have hb : (state.register .address).toNat = controlBase q full := by
    have hf : Fits (bits q full) (controlBase q full) := by
      simpa only [Nat.add_zero] using bank_offset_fits q full hq 0 (by decide)
    change controlBase q full < 2 ^ bits q full at hf
    rw [hrep.address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf]
  obtain ⟨count, hc, result⟩ := ConcreteAST.input_call q full used hq left right pointer (controlBase q full)
    (allocated q full) (logical.register pointer) state hpc ha
    (RuntimeData.Data.stages_nat q full state data hrep.address) (RuntimeData.Data.tools_nat q full state data hrep.address)
    (pointer_nat q full logical state hrep pointer hptr) hlower hupper hb data.cached
    (ord_room q full) (allocation_fits q full hq) hcode hpcfit
  refine ⟨{ steps := count, bounded := hc, value := result.1, heap := result.2.2.1, address := result.2.1, pc := ?_, active := result.2.2.2.2 }⟩
  simpa only [ConcreteAST.inputCode_length] using result.2.2.2.1

def internal_read_exit (q : Nat) (full : List (Finset (Fin q))) (physical : PhysicalROM)
    (pointer : Register) (logical : State) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (hptr : Fits (bits q full) (logical.register pointer)) (hupper : logical.register pointer < 2 * t q full)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ InternalInput.code pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ InternalInput.code pointer ++ right).length)) :
    ReadExit physical left (InternalInput.code pointer) right state
      ((givenTreeROM q full).semantic.read .internal (logical.register pointer)) 25 := by
  have hr := InternalInput.run physical pointer left right state hpc ha hcode hpcfit
  have frame := InternalInput.prefix_frame physical pointer state (InternalInput.code pointer).length
  rw [List.take_length] at frame
  refine { steps := 25, bounded := le_rfl, value := ?_, heap := ?_, address := ?_, pc := ?_, active := ?_ }
  · rw [hr]
    exact InternalInput.original_value q full (controlBase q full) (logical.register pointer) physical pointer state data.toData
      hrep.address (pointer_nat q full logical state hrep pointer hptr) hupper (mass_fits q full) (size_fits q full)
      (by have hh := bits_room q full; omega)
  · rw [hr]
    exact frame.1
  · rw [hr]
    exact frame.2
  · rw [hr, executeOps_pc physical _ state (InternalInput.code_straight pointer), hpc, BitVec.ofNat_add_ofNat]
    congr 1
  · rw [hr, executeOps_halted, ha]

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
