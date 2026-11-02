module

public import Structure.PSTR_BuildLower_DispatchPrefix_126
public import Structure.PSTR_BuildLower_ControlAccess_124
public import Structure.PSTR_BuildLower_ResourceTrace_094

/-! The two REAL last-jump dispatcher control phases carry every-clock
capacity/cache and proper-clock fetch/access. Both results use the SAME
actual whole program, ready for its selected concrete branch composition. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.DispatchControls
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

theorem classify (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (left packed ordinary right : List PackingOp) (pointer : Register)
    (state : WordState (bits q full)) (base : state.register .address = BitVec.ofNat _ (controlBase q full))
    (bounded : GlobalCapacity.Bounded q full state.heap)
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ DispatchRun.code packed ordinary left.length pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ DispatchRun.code packed ordinary left.length pointer ++ right).length)) :
    ResourceTrace.Keeps q full physical (left ++ DispatchRun.code packed ordinary left.length pointer ++ right) state 9 ∧
      TraceAccess.Safe (allocated q full) physical
        (left ++ DispatchRun.code packed ordinary left.length pointer ++ right) state 9 := by
  constructor
  · intro clock hc
    rw [DispatchPrefix.classify physical left packed ordinary right pointer state hpc ha hcode hpcfit clock hc,
      (memoryClassify_prefix_frame physical pointer _ state clock).1]
    exact ⟨bounded, ResourceTrace.CacheFrame.refl q full state.heap⟩
  · have result := ControlAccess.classify_actual_safe q full hq physical pointer
      (5 * (left.length + 9 + packed.length + 3)) left
      (packed ++ forwardJump (5 * (left.length + 9 + packed.length + 3 + ordinary.length)) ++ ordinary ++ right)
      state base hpc ha
      (by simpa only [DispatchRun.code, List.append_assoc] using hcode)
      (by simpa only [DispatchRun.code, List.append_assoc] using hpcfit)
    simpa only [DispatchRun.code, List.append_assoc] using result

private theorem jump_heap {bits : Nat} (physical : PhysicalROM) (target : Nat)
    (state : WordState bits) (clock : Nat) (hc : clock ≤ 3) :
    (executeOps physical ((forwardJump target).take clock) state).heap = state.heap := by
  interval_cases clock <;> rfl

theorem jump (q : Nat) (full : List (Finset (Fin q)))
    (physical : PhysicalROM) (left packed ordinary right : List PackingOp) (pointer : Register)
    (state : WordState (bits q full)) (bounded : GlobalCapacity.Bounded q full state.heap)
    (hpc : state.pc = BitVec.ofNat _ (5 * (left.length + 9 + packed.length))) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ DispatchRun.code packed ordinary left.length pointer ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ DispatchRun.code packed ordinary left.length pointer ++ right).length)) :
    ResourceTrace.Keeps q full physical (left ++ DispatchRun.code packed ordinary left.length pointer ++ right) state 3 ∧
      TraceAccess.Safe (allocated q full) physical
        (left ++ DispatchRun.code packed ordinary left.length pointer ++ right) state 3 := by
  constructor
  · intro clock hc
    rw [DispatchPrefix.jump physical left packed ordinary right pointer state hpc ha hcode hpcfit clock hc,
      jump_heap physical _ state clock hc]
    exact ⟨bounded, ResourceTrace.CacheFrame.refl q full state.heap⟩
  · let target := 5 * (left.length + 9 + packed.length + 3 + ordinary.length)
    let lead := (forwardJump target).take 2
    have leadLength : lead.length + 1 = 3 := rfl
    have shape : lead ++ [.jumpIfZero .flag .fresh] = forwardJump target := rfl
    have straight : StraightProgram lead := by
      simp [lead, forwardJump, StraightProgram, StraightOp]
    have result := AccessBridge.last_safe physical
      (left ++ memoryClassify pointer (5 * (left.length + 9 + packed.length + 3)) ++ packed)
      lead (ordinary ++ right) (.jumpIfZero .flag .fresh) (allocated q full) state straight
      (by rw [shape]; exact ControlAccess.jump_safe physical target (allocated q full) state)
      (by simpa only [List.length_append, memoryClassify_length] using hpc) ha
      (by rw [shape]; simpa only [DispatchRun.code, target, List.append_assoc] using hcode)
      (by rw [shape]; simpa only [DispatchRun.code, target, List.append_assoc] using hpcfit)
    rw [shape, leadLength] at result
    simpa only [DispatchRun.code, target, List.append_assoc] using result

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.DispatchControls
