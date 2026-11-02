module

public import Structure.PSTR_BuildLower_DispatchControls_129

/-! Resource composition for the actual chosen dispatcher branch. The
branch obligations are internal local proofs on the real tested state and
same containing program. Concrete read/write ports discharge them below. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.DispatchResources
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem resources (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (left packed ordinary right : List PackingOp) (pointer : Register)
    (packedStraight : StraightProgram packed)
    (state : WordState (bits q full)) (base : state.register .address = BitVec.ofNat _ (controlBase q full))
    (bounded : GlobalCapacity.Bounded q full state.heap)
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ DispatchRun.code packed ordinary left.length pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ DispatchRun.code packed ordinary left.length pointer ++ right).length))
    (packedResources : ¬ DispatchRun.ordinaryCase pointer state →
      let tested := executeOps physical (memoryClassify pointer (5 * (left.length + 9 + packed.length + 3))) state
      ResourceTrace.Keeps q full physical (left ++ DispatchRun.code packed ordinary left.length pointer ++ right) tested packed.length ∧
        TraceAccess.Safe (allocated q full) physical (left ++ DispatchRun.code packed ordinary left.length pointer ++ right) tested packed.length)
    (ordinaryResources : DispatchRun.ordinaryCase pointer state →
      let tested := executeOps physical (memoryClassify pointer (5 * (left.length + 9 + packed.length + 3))) state
      ResourceTrace.Keeps q full physical (left ++ DispatchRun.code packed ordinary left.length pointer ++ right) tested ordinary.length ∧
        TraceAccess.Safe (allocated q full) physical (left ++ DispatchRun.code packed ordinary left.length pointer ++ right) tested ordinary.length) :
    ResourceTrace.Keeps q full physical (left ++ DispatchRun.code packed ordinary left.length pointer ++ right) state
      (DispatchRun.steps packed ordinary pointer state) ∧
      TraceAccess.Safe (allocated q full) physical (left ++ DispatchRun.code packed ordinary left.length pointer ++ right) state
        (DispatchRun.steps packed ordinary pointer state) := by
  let whole := left ++ DispatchRun.code packed ordinary left.length pointer ++ right
  let tested := executeOps physical (memoryClassify pointer (5 * (left.length + 9 + packed.length + 3))) state
  have front : packingRun physical whole 9 state = tested :=
    DispatchRun.classify_run physical left packed ordinary right pointer hcode hpcfit state hpc ha
  have first := DispatchControls.classify q full hq physical left packed ordinary right pointer state base bounded hpc ha hcode hpcfit
  have testedActive : tested.halted = false := (executeOps_halted physical _ state).trans ha
  by_cases hg : DispatchRun.ordinaryCase pointer state
  · have second := ordinaryResources hg
    simp only [DispatchRun.steps, hg, ite_true]
    constructor
    · exact ResourceTrace.keeps_add q full physical whole state 9 ordinary.length first.1 (by rw [front]; exact second.1)
    · exact TraceAccess.add (allocated q full) physical whole state 9 ordinary.length first.2 (by rw [front]; exact second.2)
  · have raw : ¬ (state.heap (state.register .address + BitVec.ofNat _ 3)).toNat ≤
        (Ordinary.pointerValue state pointer).toNat := hg
    have testedPC : tested.pc = BitVec.ofNat _ (5 * (left.length + 9)) := by
      have he : 5 * left.length + 45 = 5 * (left.length + 9) := by omega
      rw [memoryClassify_pc, ite_eq_right raw, hpc, BitVec.ofNat_add_ofNat, he]
    have second := packedResources hg
    let afterPacked := packingRun physical whole packed.length tested
    have afterEq : afterPacked = executeOps physical packed tested :=
      DispatchRun.packed_run physical left packed ordinary right pointer packedStraight hcode hpcfit tested testedPC testedActive
    have afterPC : afterPacked.pc = BitVec.ofNat _ (5 * (left.length + 9 + packed.length)) := by
      rw [afterEq, executeOps_pc physical packed tested packedStraight, testedPC, BitVec.ofNat_add_ofNat]
      congr 1
      omega
    have afterActive : afterPacked.halted = false := by rw [afterEq, executeOps_halted, testedActive]
    have afterBounded : GlobalCapacity.Bounded q full afterPacked.heap := (second.1 packed.length le_rfl).1
    have last := DispatchControls.jump q full physical left packed ordinary right pointer afterPacked afterBounded
      afterPC afterActive hcode hpcfit
    have tailKeeps := ResourceTrace.keeps_add q full physical whole tested packed.length 3 second.1 last.1
    have tailSafe := TraceAccess.add (allocated q full) physical whole tested packed.length 3 second.2 last.2
    simp only [DispatchRun.steps, hg, ite_false]
    have regroup : 9 + packed.length + 3 = 9 + (packed.length + 3) := by omega
    rw [regroup]
    constructor
    · exact ResourceTrace.keeps_add q full physical whole state 9 (packed.length + 3) first.1 (by rw [front]; exact tailKeeps)
    · exact TraceAccess.add (allocated q full) physical whole state 9 (packed.length + 3) first.2 (by rw [front]; exact tailSafe)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.DispatchResources
