module

public import PaperProofs.Structure.RawIncidenceCheckerBoundary

/-! Two actual fetched instructions replace the old checker HALT: zero
flags jump to the new final HALT, while one flags fall through to the
constructor's first address. The constructor is arbitrary fixed code.
No constructor execution, safety, termination, or tree-output theorem is
assumed or asserted here; global physical-word construction is separate. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.RawIncidenceLaminarRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine

def dispatcherGate (constructorLength : Nat) : List PackingOp :=
  [.base (.base (.constant .index (5 * (checker.length + 2 + constructorLength)))),
    .jumpIfZero .value .index]

def dispatcherProgram (constructor : List PackingOp) : List PackingOp :=
  checker ++ dispatcherGate constructor.length ++ constructor

theorem dispatcherGate_length (length : Nat) : (dispatcherGate length).length = 2 := rfl

theorem dispatcherProgram_length (constructor : List PackingOp) :
    (dispatcherProgram constructor).length = checker.length + 2 + constructor.length := by
  simp only [dispatcherProgram, List.length_append, dispatcherGate_length]

theorem dispatcherProgram_first (constructor : List PackingOp) :
    (dispatcherProgram constructor)[checker.length]'(by rw [dispatcherProgram_length]; omega) =
      .base (.base (.constant .index (5 * (checker.length + 2 + constructor.length)))) := rfl

theorem dispatcherProgram_second (constructor : List PackingOp) :
    (dispatcherProgram constructor)[checker.length + 1]'(by rw [dispatcherProgram_length]; omega) =
      .jumpIfZero .value .index := rfl

/-- The gate is executed by the original encoded fetch/decode semantics.
The entry is active; it is the old HALT address before HALT was consumed. -/
theorem dispatcher_gate_run (constructor : List PackingOp) (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 5 * checker.length) (hactive : state.halted = false) :
    natRun rom (dispatcherProgram constructor) 2 state =
      { state with
        register := Function.update state.register .index (5 * (checker.length + 2 + constructor.length))
        pc := if state.register .value = 0 then 5 * (checker.length + 2 + constructor.length)
          else 5 * (checker.length + 2) } := by
  change natStep rom (dispatcherProgram constructor) (natStep rom (dispatcherProgram constructor) state) = _
  rw [natStep_of_index rom (dispatcherProgram constructor) state checker.length
    (by rw [dispatcherProgram_length]; omega) hpc hactive, dispatcherProgram_first]
  let one := natExecuteOp rom
    (.base (.base (.constant .index (5 * (checker.length + 2 + constructor.length))))) state
  have hp : one.pc = 5 * (checker.length + 1) := by
    change state.pc + 5 = _
    rw [hpc]
    omega
  have ha : one.halted = false := by rw [natExecuteOp_halted, hactive]
  rw [natStep_of_index rom (dispatcherProgram constructor) one (checker.length + 1)
    (by rw [dispatcherProgram_length]; omega) hp ha, dispatcherProgram_second]
  simp [one, natExecuteOp, Op.execute, Instruction.execute, hpc, Nat.mul_add, Nat.add_assoc]

/-- Uniformly for arbitrary fixed constructor code, the real checker
prefix enters the real two-op gate. Rejection consumes the new final HALT;
acceptance only reaches the constructor address and promises nothing about
that code. An empty constructor therefore also reaches a genuine HALT. -/
theorem checker_dispatcher_boundary (constructor : List PackingOp)
    (q : Nat) (full : List (Finset (Fin q))) :
    ∃ count : Nat, count + 3 ≤ checkerSteps full.length q + 2 ∧
      (∀ clock ≤ count,
        natRun (rawIncidenceROM q full) (dispatcherProgram constructor) clock natInitial =
          natRun (rawIncidenceROM q full) checker clock natInitial) ∧
      (natRun (rawIncidenceROM q full) (dispatcherProgram constructor) (count + 2) natInitial).halted = false ∧
      (natRun (rawIncidenceROM q full) (dispatcherProgram constructor) (count + 2) natInitial).heap =
        (natRun (rawIncidenceROM q full) checker count natInitial).heap ∧
      (natRun (rawIncidenceROM q full) (dispatcherProgram constructor) (count + 2) natInitial).register .value =
        (natRun (rawIncidenceROM q full) checker count natInitial).register .value ∧
      (¬ LaminarSchedule full →
        (natRun (rawIncidenceROM q full) (dispatcherProgram constructor) (count + 2) natInitial).pc =
          5 * (dispatcherProgram constructor).length ∧
        (natRun (rawIncidenceROM q full) (dispatcherProgram constructor) (count + 2) natInitial).register .value = 0 ∧
        (natRun (rawIncidenceROM q full) (dispatcherProgram constructor) (count + 3) natInitial).halted = true ∧
        (natRun (rawIncidenceROM q full) (dispatcherProgram constructor) (count + 3) natInitial).register .value = 0 ∧
        (natRun (rawIncidenceROM q full) (dispatcherProgram constructor) (count + 3) natInitial).heap =
          (natRun (rawIncidenceROM q full) checker count natInitial).heap) ∧
      (LaminarSchedule full →
        (natRun (rawIncidenceROM q full) (dispatcherProgram constructor) (count + 2) natInitial).pc =
          5 * (checker.length + 2) ∧
        (natRun (rawIncidenceROM q full) (dispatcherProgram constructor) (count + 2) natInitial).register .value = 1) ∧
      (constructor = [] →
        (natRun (rawIncidenceROM q full) (dispatcherProgram constructor) (count + 3) natInitial).halted = true) := by
  let rom := rawIncidenceROM q full
  let program := dispatcherProgram constructor
  obtain ⟨count, hcount, hactive, hpc, hflag, hcorrect, _hterminal, _hbody, hprefix⟩ :=
    checker_before_first_halt q full
  let before := natRun rom checker count natInitial
  have beforeFlag : before.register .value ≤ 1 := hflag
  have hprefixRun : ∀ clock ≤ count, natRun rom program clock natInitial = natRun rom checker clock natInitial := by
    intro clock hc
    simpa only [program, dispatcherProgram, List.append_assoc] using
      hprefix (dispatcherGate constructor.length ++ constructor) clock hc
  have gate : natRun rom program (count + 2) natInitial =
      { before with
        register := Function.update before.register .index (5 * (checker.length + 2 + constructor.length))
        pc := if before.register .value = 0 then 5 * (checker.length + 2 + constructor.length)
          else 5 * (checker.length + 2) } := by
    rw [natRun_add, hprefixRun count le_rfl]
    exact dispatcher_gate_run constructor rom before hpc hactive
  let after := natRun rom program (count + 2) natInitial
  have afterActive : after.halted = false := by dsimp only [after]; rw [gate]; exact hactive
  have afterHeap : after.heap = before.heap := by dsimp only [after]; rw [gate]
  have afterValue : after.register .value = before.register .value := by dsimp only [after]; rw [gate]; simp
  have haltNext (hp : after.pc = 5 * program.length) :
      natRun rom program (count + 3) natInitial = { after with halted := true } := by
    rw [show count + 3 = (count + 2) + 1 from by omega, natRun_succ]
    exact natStep_halt rom program after hp afterActive
  refine ⟨count, by omega, hprefixRun, afterActive, afterHeap, afterValue, ?_, ?_, ?_⟩
  · intro hnot
    have hz : before.register .value = 0 := by
      have hn : before.register .value ≠ 1 := fun hone => hnot (hcorrect.mp hone)
      omega
    have hp : after.pc = 5 * program.length := by
      dsimp only [after]
      rw [gate]
      simp only [hz, ite_true, program, dispatcherProgram_length]
    have hh := haltNext hp
    refine ⟨hp, afterValue.trans hz, ?_, ?_, ?_⟩
    · rw [hh]
    · rw [hh]
      exact afterValue.trans hz
    · rw [hh]
      exact afterHeap
  · intro hyes
    have hone : before.register .value = 1 := hcorrect.mpr hyes
    constructor
    · rw [gate]
      simp only [hone, Nat.one_ne_zero, ite_false]
    · exact afterValue.trans hone
  · intro hempty
    have hp : after.pc = 5 * program.length := by
      dsimp only [after]
      rw [gate]
      simp only [program, dispatcherProgram_length, hempty, List.length_nil, Nat.add_zero, ite_self]
    rw [haltNext hp]

end PaperProofs.Structure.LaminarTree.RawIncidenceLaminarRAM
