module

public import Structure.PSTR_BuildLower_DispatchControls_129
public import Structure.PSTR_BuildLower_LoadResources_101

/-! Local composition of the real read dispatcher at its canonical steps.
The two selected-branch obligations concern the actual tested state. Concrete
ports discharge them; this helper is not a raw caller or whole-AST oracle. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.DispatchReadTrace
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open PA17PackedTranslator034

section Generic
variable {bits : Nat}

theorem readonly_add (physical : PhysicalROM) (whole : List PackingOp) (state : WordState bits)
    (first second : Nat)
    (front : ∀ clock ≤ first, (packingRun physical whole clock state).heap = state.heap)
    (back : ∀ clock ≤ second,
      (packingRun physical whole clock (packingRun physical whole first state)).heap =
        (packingRun physical whole first state).heap) :
    ∀ clock ≤ first + second, (packingRun physical whole clock state).heap = state.heap := by
  intro clock hc
  by_cases he : clock ≤ first
  · exact front clock he
  · have split : clock = first + (clock - first) := by omega
    rw [split, PSTRWordSegments.run_add, back (clock - first) (by omega), front first le_rfl]

theorem jump_readonly (physical : PhysicalROM) (target : Nat) (state : WordState bits)
    (clock : Nat) (hc : clock ≤ 3) :
    (executeOps physical ((forwardJump target).take clock) state).heap = state.heap := by
  interval_cases clock <;> rfl

end Generic

theorem resources (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (left packed ordinary right : List PackingOp) (pointer : Register)
    (packedStraight : StraightProgram packed) (ordinaryStraight : StraightProgram ordinary)
    (state : WordState (bits q full)) (base : state.register .address = BitVec.ofNat _ (controlBase q full))
    (bounded : GlobalCapacity.Bounded q full state.heap)
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ DispatchRun.code packed ordinary left.length pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ DispatchRun.code packed ordinary left.length pointer ++ right).length))
    (packedReadonly : ∀ current : WordState (bits q full), ∀ clock ≤ packed.length,
      (executeOps physical (packed.take clock) current).heap = current.heap)
    (ordinaryReadonly : ∀ current : WordState (bits q full), ∀ clock ≤ ordinary.length,
      (executeOps physical (ordinary.take clock) current).heap = current.heap)
    (packedSafe : ¬ DispatchRun.ordinaryCase pointer state →
      PackedAccessSafe (allocated q full) physical packed
        (executeOps physical (memoryClassify pointer (5 * (left.length + 9 + packed.length + 3))) state))
    (ordinarySafe : DispatchRun.ordinaryCase pointer state →
      PackedAccessSafe (allocated q full) physical ordinary
        (executeOps physical (memoryClassify pointer (5 * (left.length + 9 + packed.length + 3))) state)) :
    (∀ clock ≤ DispatchRun.steps packed ordinary pointer state,
      (packingRun physical (left ++ DispatchRun.code packed ordinary left.length pointer ++ right) clock state).heap = state.heap) ∧
      TraceAccess.Safe (allocated q full) physical
        (left ++ DispatchRun.code packed ordinary left.length pointer ++ right) state
        (DispatchRun.steps packed ordinary pointer state) := by
  let whole := left ++ DispatchRun.code packed ordinary left.length pointer ++ right
  let tested := executeOps physical (memoryClassify pointer (5 * (left.length + 9 + packed.length + 3))) state
  have front : packingRun physical whole 9 state = tested :=
    DispatchRun.classify_run physical left packed ordinary right pointer hcode hpcfit state hpc ha
  have frontReadonly : ∀ clock ≤ 9, (packingRun physical whole clock state).heap = state.heap := by
    intro clock hc
    rw [DispatchPrefix.classify physical left packed ordinary right pointer state hpc ha hcode hpcfit clock hc]
    exact (memoryClassify_prefix_frame physical pointer _ state clock).1
  have frontSafe := (DispatchControls.classify q full hq physical left packed ordinary right pointer state base bounded
    hpc ha hcode hpcfit).2
  have testedHeap : tested.heap = state.heap := by
    simpa only [tested, List.take_length] using
      (memoryClassify_prefix_frame physical pointer (5 * (left.length + 9 + packed.length + 3)) state
        (memoryClassify pointer (5 * (left.length + 9 + packed.length + 3))).length).1
  have testedActive : tested.halted = false := (executeOps_halted physical _ state).trans ha
  by_cases hg : DispatchRun.ordinaryCase pointer state
  · have raw : (state.heap (state.register .address + BitVec.ofNat _ 3)).toNat ≤
        (Ordinary.pointerValue state pointer).toNat := hg
    have testedPC : tested.pc = BitVec.ofNat _ (5 * (left.length + 9 + packed.length + 3)) := by
      rw [memoryClassify_pc, ite_eq_left raw]
    have tailReadonly : ∀ clock ≤ ordinary.length, (packingRun physical whole clock tested).heap = tested.heap := by
      intro clock hc
      rw [DispatchPrefix.ordinary physical left packed ordinary right pointer ordinaryStraight tested
        testedPC testedActive hcode hpcfit clock hc]
      exact ordinaryReadonly tested clock hc
    have tailSafe := TraceAccess.straight physical
      (left ++ memoryClassify pointer (5 * (left.length + 9 + packed.length + 3)) ++ packed ++
        forwardJump (5 * (left.length + 9 + packed.length + 3 + ordinary.length))) ordinary right
      (allocated q full) tested ordinaryStraight (ordinarySafe hg)
      (by simpa only [List.length_append, memoryClassify_length, forwardJump_length] using testedPC) testedActive
      (by simpa only [DispatchRun.code, List.append_assoc] using hcode)
      (by simpa only [DispatchRun.code, List.append_assoc] using hpcfit)
    have backSafe : TraceAccess.Safe (allocated q full) physical whole tested ordinary.length := by
      simpa only [whole, DispatchRun.code, List.append_assoc] using tailSafe
    simp only [DispatchRun.steps, hg, ite_true]
    constructor
    · exact readonly_add physical whole state 9 ordinary.length frontReadonly (by rw [front]; exact tailReadonly)
    · exact TraceAccess.add (allocated q full) physical whole state 9 ordinary.length frontSafe
        (by rw [front]; exact backSafe)
  · have raw : ¬ (state.heap (state.register .address + BitVec.ofNat _ 3)).toNat ≤
        (Ordinary.pointerValue state pointer).toNat := hg
    have testedPC : tested.pc = BitVec.ofNat _ (5 * (left.length + 9)) := by
      have he : 5 * left.length + 45 = 5 * (left.length + 9) := by omega
      rw [memoryClassify_pc, ite_eq_right raw, hpc, BitVec.ofNat_add_ofNat, he]
    have packedReadonlyActual : ∀ clock ≤ packed.length,
        (packingRun physical whole clock tested).heap = tested.heap := by
      intro clock hc
      rw [DispatchPrefix.packed physical left packed ordinary right pointer packedStraight tested
        testedPC testedActive hcode hpcfit clock hc]
      exact packedReadonly tested clock hc
    have packedSafeActual := TraceAccess.straight physical
      (left ++ memoryClassify pointer (5 * (left.length + 9 + packed.length + 3))) packed
      (forwardJump (5 * (left.length + 9 + packed.length + 3 + ordinary.length)) ++ ordinary ++ right)
      (allocated q full) tested packedStraight (packedSafe hg)
      (by simpa only [List.length_append, memoryClassify_length] using testedPC) testedActive
      (by simpa only [DispatchRun.code, List.append_assoc] using hcode)
      (by simpa only [DispatchRun.code, List.append_assoc] using hpcfit)
    have packedSafeWhole : TraceAccess.Safe (allocated q full) physical whole tested packed.length := by
      simpa only [whole, DispatchRun.code, List.append_assoc] using packedSafeActual
    let afterPacked := packingRun physical whole packed.length tested
    have afterEq : afterPacked = executeOps physical packed tested :=
      DispatchRun.packed_run physical left packed ordinary right pointer packedStraight hcode hpcfit tested testedPC testedActive
    have afterPC : afterPacked.pc = BitVec.ofNat _ (5 * (left.length + 9 + packed.length)) := by
      rw [afterEq, executeOps_pc physical packed tested packedStraight, testedPC, BitVec.ofNat_add_ofNat]
      congr 1
      omega
    have afterActive : afterPacked.halted = false := by rw [afterEq, executeOps_halted, testedActive]
    have afterBounded : GlobalCapacity.Bounded q full afterPacked.heap := by
      rw [packedReadonlyActual packed.length le_rfl, testedHeap]
      exact bounded
    have jumpSafe := (DispatchControls.jump q full physical left packed ordinary right pointer afterPacked afterBounded
      afterPC afterActive hcode hpcfit).2
    have jumpReadonly : ∀ clock ≤ 3, (packingRun physical whole clock afterPacked).heap = afterPacked.heap := by
      intro clock hc
      rw [DispatchPrefix.jump physical left packed ordinary right pointer afterPacked afterPC afterActive hcode hpcfit clock hc]
      exact jump_readonly physical _ afterPacked clock hc
    have secondReadonly := readonly_add physical whole tested packed.length 3 packedReadonlyActual jumpReadonly
    have secondSafe := TraceAccess.add (allocated q full) physical whole tested packed.length 3 packedSafeWhole jumpSafe
    simp only [DispatchRun.steps, hg, ite_false]
    have regroup : 9 + packed.length + 3 = 9 + (packed.length + 3) := by omega
    rw [regroup]
    constructor
    · exact readonly_add physical whole state 9 (packed.length + 3) frontReadonly (by rw [front]; exact secondReadonly)
    · exact TraceAccess.add (allocated q full) physical whole state 9 (packed.length + 3) frontSafe
        (by rw [front]; exact secondSafe)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.DispatchReadTrace
