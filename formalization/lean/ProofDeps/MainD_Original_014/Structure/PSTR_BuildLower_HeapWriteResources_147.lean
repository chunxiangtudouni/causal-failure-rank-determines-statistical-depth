module

public import Structure.PSTR_BuildLower_DispatchResources_146
public import Structure.PSTR_BuildLower_PackedResources_118
public import Structure.PSTR_BuildLower_OrdinaryResources_123

/-! Every actual old-C0-dispatched heap-write clock preserves full Cnew and
fitted high-cache words, and has a genuine fetch/access certificate. Both
local branch certificates are proved from original geometry and materialized
data; the packed safe writer really reloads its pointer in both phases. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteHeap
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem write_prefix_resources (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (physical : PhysicalROM)
    (pointer : Register) (logical : State) (state : WordState (bits q full))
    (hrep : SourceRep.Prepared q full logical state) (data : RuntimeData.Data q full state.heap)
    (bounded : GlobalCapacity.Bounded q full state.heap)
    (hptr : Fits (bits q full) (logical.register pointer))
    (had : logical.register pointer < oldCapacity q full + indexWords q full)
    (hvalue : logical.register pointer < oldCapacity q full → (state.register .value).toNat ≤ q)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ write left.length pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ write left.length pointer ++ right).length)) :
    let count := DispatchRun.steps (PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer)) (Ordinary.write pointer) pointer state
    ResourceTrace.Keeps q full physical (left ++ write left.length pointer ++ right) state count ∧
      TraceAccess.Safe (allocated q full) physical (left ++ write left.length pointer ++ right) state count := by
  let packed := PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer)
  let ordinary := Ordinary.write pointer
  let target := 5 * (left.length + 9 + packed.length + 3)
  let tested := executeOps physical (memoryClassify pointer target) state
  have shape : DispatchRun.code packed ordinary left.length pointer = write left.length pointer :=
    DispatchRun.code_write _ _ _
  have codeFit : WordsFit (bits q full) (packingCode (left ++ DispatchRun.code packed ordinary left.length pointer ++ right)) := by
    rwa [shape]
  have pcFit : Fits (bits q full) (5 * (left ++ DispatchRun.code packed ordinary left.length pointer ++ right).length) := by
    rwa [shape]
  have testedFrame := memoryClassify_prefix_frame physical pointer target state (memoryClassify pointer target).length
  rw [List.take_length] at testedFrame
  have testedHeap : tested.heap = state.heap := testedFrame.1
  have testedBase : tested.register .address = BitVec.ofNat _ (controlBase q full) := testedFrame.2.trans hrep.address
  have testedRep : SourceRep.Prepared q full logical tested := by
    refine ⟨testedBase, ?_, ?_⟩
    · rw [testedHeap]
      exact hrep.registers
    · rw [testedHeap]
      exact hrep.heap
  have testedData : RuntimeData.Data q full tested.heap := by rw [testedHeap]; exact data
  have testedBounded : GlobalCapacity.Bounded q full tested.heap := by rw [testedHeap]; exact bounded
  have testedActive : tested.halted = false := (executeOps_halted physical _ state).trans ha
  have hp := SourceRep.pointer_nat q full logical state hrep pointer hptr
  have hc := RuntimeData.Data.cutoff_nat q full hq state data hrep.address
  have packedBranch (hg : ¬ DispatchRun.ordinaryCase pointer state) :
      ResourceTrace.Keeps q full physical (left ++ DispatchRun.code packed ordinary left.length pointer ++ right) tested packed.length ∧
        TraceAccess.Safe (allocated q full) physical (left ++ DispatchRun.code packed ordinary left.length pointer ++ right) tested packed.length := by
    have small : logical.register pointer < oldCapacity q full := by
      change ¬ (state.heap (state.register .address + BitVec.ofNat _ 3)).toNat ≤
        (Ordinary.pointerValue state pointer).toNat at hg
      rw [hp, hc] at hg
      omega
    have testedValue : (tested.register .value).toNat ≤ q := by rw [memoryClassify_value]; exact hvalue small
    have raw : ¬ (state.heap (state.register .address + BitVec.ofNat _ 3)).toNat ≤
        (Ordinary.pointerValue state pointer).toNat := hg
    have testedPC : tested.pc = BitVec.ofNat _ (5 * (left.length + 9)) := by
      have he : 5 * left.length + 45 = 5 * (left.length + 9) := by omega
      rw [memoryClassify_pc, ite_eq_right raw, hpc, BitVec.ofNat_add_ofNat, he]
    let branchLeft := left ++ memoryClassify pointer target
    let branchRight := forwardJump (5 * (left.length + 9 + packed.length + 3 + ordinary.length)) ++ ordinary ++ right
    have localPC : tested.pc = BitVec.ofNat _ (5 * branchLeft.length) := by
      simpa only [branchLeft, List.length_append, memoryClassify_length] using testedPC
    have localCode : WordsFit (bits q full) (packingCode (branchLeft ++ packed ++ branchRight)) := by
      simpa only [branchLeft, branchRight, DispatchRun.code, target, List.append_assoc] using codeFit
    have localFit : Fits (bits q full) (5 * (branchLeft ++ packed ++ branchRight).length) := by
      simpa only [branchLeft, branchRight, DispatchRun.code, target, List.append_assoc] using pcFit
    have actual := PackedResources.write_keeps_safe q full hq physical pointer logical tested testedRep testedData testedBounded
      hptr small testedValue branchLeft branchRight localPC testedActive localCode localFit
    have safe := TraceAccess.straight physical branchLeft packed branchRight (allocated q full) tested
      (PA06A19PrepareBankPacked021.safeWrite_straight _) actual.2 localPC testedActive localCode localFit
    constructor
    · simpa only [branchLeft, branchRight, DispatchRun.code, target, List.append_assoc,
        packed, PA06A19PrepareBankPacked021.safeWrite_length] using actual.1
    · simpa only [branchLeft, branchRight, DispatchRun.code, target, List.append_assoc] using safe
  have ordinaryBranch (hg : DispatchRun.ordinaryCase pointer state) :
      ResourceTrace.Keeps q full physical (left ++ DispatchRun.code packed ordinary left.length pointer ++ right) tested ordinary.length ∧
        TraceAccess.Safe (allocated q full) physical (left ++ DispatchRun.code packed ordinary left.length pointer ++ right) tested ordinary.length := by
    have raw : (state.heap (state.register .address + BitVec.ofNat _ 3)).toNat ≤
        (Ordinary.pointerValue state pointer).toNat := hg
    have testedPC : tested.pc = BitVec.ofNat _ target := by rw [memoryClassify_pc, ite_eq_left raw]
    let branchLeft := left ++ memoryClassify pointer target ++ packed ++
      forwardJump (5 * (left.length + 9 + packed.length + 3 + ordinary.length))
    have localPC : tested.pc = BitVec.ofNat _ (5 * branchLeft.length) := by
      simpa only [branchLeft, target, List.length_append, memoryClassify_length, forwardJump_length] using testedPC
    have localCode : WordsFit (bits q full) (packingCode (branchLeft ++ ordinary ++ right)) := by
      simpa only [branchLeft, DispatchRun.code, target, List.append_assoc] using codeFit
    have localFit : Fits (bits q full) (5 * (branchLeft ++ ordinary ++ right).length) := by
      simpa only [branchLeft, DispatchRun.code, target, List.append_assoc] using pcFit
    have actual := OrdinaryResources.write_keeps_safe q full hq physical pointer logical tested testedRep testedData testedBounded
      hptr had branchLeft right localPC testedActive localCode localFit
    have safe := TraceAccess.straight physical branchLeft ordinary right (allocated q full) tested
      (Ordinary.write_straight pointer) actual.2 localPC testedActive localCode localFit
    constructor
    · simpa only [branchLeft, DispatchRun.code, target, List.append_assoc, ordinary, Ordinary.write_length] using actual.1
    · simpa only [branchLeft, DispatchRun.code, target, List.append_assoc] using safe
  have actual := DispatchResources.resources q full hq physical left packed ordinary right pointer
    (PA06A19PrepareBankPacked021.safeWrite_straight _) state hrep.address bounded hpc ha codeFit pcFit packedBranch ordinaryBranch
  rwa [shape] at actual

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteHeap
