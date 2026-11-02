module

public import Structure.PSTR_BuildLower_DispatchReadTrace_143
public import Structure.PSTR_BuildLower_OrdinaryReadResources_139
public import Structure.PSTR_BuildLower_PackedReadResources_142
public import Structure.PSTR_BuildLower_ReadPrefixExit_130
public import Structure.PSTR_BuildLower_ConcreteReadExits_067

/-! The original concrete heap reader, extended at its SAME computational
steps field with every-prefix readonly and real fetched/access certificates.
Old C0 selects the branch; NEW C supplies physical packing room. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open PA17PackedTranslator034

def heap_read_prefix_exit (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (physical : PhysicalROM)
    (pointer : Register) (logical : State) (state : WordState (bits q full))
    (hrep : Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (bounded : GlobalCapacity.Bounded q full state.heap)
    (hptr : Fits (bits q full) (logical.register pointer))
    (had : logical.register pointer < oldCapacity q full + indexWords q full)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ ConcreteHeap.read left.length pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ ConcreteHeap.read left.length pointer ++ right).length)) :
    ReadPrefixExit (allocated q full) physical left (ConcreteHeap.read left.length pointer) right state
      (logical.heap (logical.register pointer)) 45 := by
  let packed := PA06A19PrepareBankPacked021.read
  let ordinary := Ordinary.read pointer
  let target := 5 * (left.length + 9 + packed.length + 3)
  let tested := executeOps physical (memoryClassify pointer target) state
  have shape : DispatchRun.code packed ordinary left.length pointer = ConcreteHeap.read left.length pointer :=
    DispatchRun.code_read _ _ _
  have codeFit : WordsFit (bits q full) (packingCode (left ++ DispatchRun.code packed ordinary left.length pointer ++ right)) := by
    rwa [shape]
  have pcFit : Fits (bits q full) (5 * (left ++ DispatchRun.code packed ordinary left.length pointer ++ right).length) := by
    rwa [shape]
  have testedFrame := memoryClassify_prefix_frame physical pointer target state (memoryClassify pointer target).length
  rw [List.take_length] at testedFrame
  have testedHeap : tested.heap = state.heap := testedFrame.1
  have testedBase : tested.register .address = BitVec.ofNat _ (controlBase q full) := testedFrame.2.trans hrep.address
  have testedRep : Prepared q full logical tested := by
    refine ⟨testedBase, ?_, ?_⟩
    · rw [testedHeap]
      exact hrep.registers
    · rw [testedHeap]
      exact hrep.heap
  have testedData : RuntimeData.Data q full tested.heap := by rw [testedHeap]; exact data
  have testedBounded : GlobalCapacity.Bounded q full tested.heap := by rw [testedHeap]; exact bounded
  have testedActive : tested.halted = false := (executeOps_halted physical _ state).trans ha
  have hp := pointer_nat q full logical state hrep pointer hptr
  have hc := RuntimeData.Data.cutoff_nat q full hq state data hrep.address
  have packedSafe (hg : ¬ DispatchRun.ordinaryCase pointer state) :
      PackedAccessSafe (allocated q full) physical packed tested := by
    have small : logical.register pointer < oldCapacity q full := by
      change ¬ (state.heap (state.register .address + BitVec.ofNat _ 3)).toNat ≤
        (Ordinary.pointerValue state pointer).toNat at hg
      rw [hp, hc] at hg
      omega
    have testedOld : (tested.register .old).toNat = logical.register pointer := by
      rw [memoryClassify_old]
      exact hp
    have raw : ¬ (state.heap (state.register .address + BitVec.ofNat _ 3)).toNat ≤
        (Ordinary.pointerValue state pointer).toNat := hg
    have testedPC : tested.pc = BitVec.ofNat _ (5 * (left.length + 9)) := by
      have he : 5 * left.length + 45 = 5 * (left.length + 9) := by omega
      rw [memoryClassify_pc, ite_eq_right raw, hpc, BitVec.ofNat_add_ofNat, he]
    exact (PackedReadResources.read_keeps_safe q full hq physical tested testedData testedBounded
      (logical.register pointer) testedOld small
      (left ++ memoryClassify pointer target)
      (forwardJump (5 * (left.length + 9 + packed.length + 3 + ordinary.length)) ++ ordinary ++ right)
      (by simpa only [List.length_append, memoryClassify_length] using testedPC) testedActive
      (by simpa only [DispatchRun.code, target, List.append_assoc] using codeFit)
      (by simpa only [DispatchRun.code, target, List.append_assoc] using pcFit)).2
  have ordinarySafe (hg : DispatchRun.ordinaryCase pointer state) :
      PackedAccessSafe (allocated q full) physical ordinary tested := by
    have raw : (state.heap (state.register .address + BitVec.ofNat _ 3)).toNat ≤
        (Ordinary.pointerValue state pointer).toNat := hg
    have testedPC : tested.pc = BitVec.ofNat _ target := by rw [memoryClassify_pc, ite_eq_left raw]
    exact (OrdinaryResources.read_keeps_safe q full hq physical pointer logical tested testedRep testedData testedBounded hptr had
      (left ++ memoryClassify pointer target ++ packed ++
        forwardJump (5 * (left.length + 9 + packed.length + 3 + ordinary.length))) right
      (by simpa only [List.length_append, memoryClassify_length, forwardJump_length] using testedPC) testedActive
      (by simpa only [DispatchRun.code, target, List.append_assoc] using codeFit)
      (by simpa only [DispatchRun.code, target, List.append_assoc] using pcFit)).2
  have result := DispatchReadTrace.resources q full hq physical left packed ordinary right pointer
    PA06A19PrepareBankPacked021.read_straight (Ordinary.read_straight pointer) state hrep.address bounded hpc ha codeFit pcFit
    (by
      intro current clock hclock
      rw [PA06A19PrepareBankPacked021.read_prefix_simulation physical current clock
        (by simpa only [packed, PA06A19PrepareBankPacked021.read_length] using hclock)]
      exact PA06A19PrepareRuntimePacked016.read_prefix_heap physical
        (PA06A19PrepareBankPacked021.withAddress (current.register .old) current) clock)
    (by intro current clock _; exact Ordinary.read_prefix_heap physical pointer current clock)
    packedSafe ordinarySafe
  rw [shape] at result
  exact {
    toReadExit := heap_read_exit q full hq physical pointer logical state hrep data hptr had left right hpc ha hcode hpcfit
    readonly := result.1
    safe := result.2 }

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceRep
