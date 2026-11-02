module

public import Structure.PA06_A19Prepare_EarlyGate079_NatEntry

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED positive-tool prefix of the real early gate. At step17
the ENTIRE NatState equals the old checker prefix from natInitial. The
comparison stops there; no equality of later different-code runs is claimed.
Every prefix through17 also has an actual fixed short runOps formula. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareEarlyGate079

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims RawIncidenceLaminarRAM RawIncidenceScanSafety CompactControllerClaims

def positiveMiddle : List PackingOp := restore ++ (testCell 0 2 126).take 6

def outerBranch : PackingOp := .jumpIfZero .flag .index

def oldInitialLead : List PackingOp := checker.take 16

theorem positiveMiddle_length : positiveMiddle.length = 8 := rfl

theorem oldInitialLead_length : oldInitialLead.length = 16 := rfl

theorem positiveMiddle_noJump : ∀ op ∈ positiveMiddle, NoJump op := by
  simp [positiveMiddle, restore, testCell, loadCell, NoJump]

theorem oldInitialLead_noJump : ∀ op ∈ oldInitialLead, NoJump op := by
  simp [oldInitialLead, checker, setCell, storeCell, testCell, loadCell, NoJump]

private theorem positive_room (handlerPC : Nat) (rest : List PackingOp) :
    17 ≤ (program handlerPC (checker ++ rest)).length := by
  rw [program_length handlerPC (checker ++ rest)
    (by simp only [List.length_append, checker_length]; omega)]
  simp only [List.length_append, checker_length]
  omega

theorem positive_middle_slice (handlerPC : Nat) (rest : List PackingOp) :
    8 + positiveMiddle.length + 1 ≤ (program handlerPC (checker ++ rest)).length ∧
      (∀ position (hp : position < positiveMiddle.length),
        (program handlerPC (checker ++ rest))[8 + position]'(by
          have room := positive_room handlerPC rest
          rw [positiveMiddle_length] at hp
          omega) = positiveMiddle[position]) ∧
      (program handlerPC (checker ++ rest))[8 + positiveMiddle.length]'(by
        have room := positive_room handlerPC rest
        rw [positiveMiddle_length]
        omega) = outerBranch := by
  refine ⟨?_, ?_, ?_⟩
  · rw [positiveMiddle_length]
    exact positive_room handlerPC rest
  · intro position hp
    rw [positiveMiddle_length] at hp
    interval_cases position <;> rfl
  · rfl

theorem positive_eight_state (rom : PhysicalROM) (q handlerPC : Nat)
    (headerQ : rom.semantic.read .input 1 = q) (hq : 0 < q) :
    natExecuteOp rom branch (runOps rom (lead handlerPC) natInitial) =
      { runOps rom (lead handlerPC) natInitial with pc := 40 } := by
  have nonzero : q ≠ 0 := Nat.ne_of_gt hq
  simp [lead, branch, runOps, natInitial, natExecuteOp, Op.execute, Instruction.execute, headerQ, nonzero]

theorem positive_eight_control (rom : PhysicalROM) (q handlerPC : Nat)
    (headerQ : rom.semantic.read .input 1 = q) (hq : 0 < q) :
    let after := natExecuteOp rom branch (runOps rom (lead handlerPC) natInitial)
    after.pc = 40 ∧ after.halted = false := by
  dsimp only
  rw [positive_eight_state rom q handlerPC headerQ hq]
  exact ⟨rfl, rfl⟩

theorem positive_tail_prefix (rom : PhysicalROM) (q handlerPC : Nat) (rest : List PackingOp)
    (headerQ : rom.semantic.read .input 1 = q) (hq : 0 < q)
    (count : Nat) (bound : count ≤ 9) :
    natRun rom (program handlerPC (checker ++ rest)) (8 + count) natInitial =
      runOps rom ((positiveMiddle ++ [outerBranch]).take count)
        (natExecuteOp rom branch (runOps rom (lead handlerPC) natInitial)) := by
  have slice := positive_middle_slice handlerPC rest
  have entry := positive_eight_control rom q handlerPC headerQ hq
  rw [natRun_add, first_eight_run]
  exact natRun_segment_prefix rom (program handlerPC (checker ++ rest)) positiveMiddle outerBranch 8
    slice.1 slice.2.1 slice.2.2 positiveMiddle_noJump _ entry.1 entry.2 count
    (by simpa only [positiveMiddle_length] using bound)

theorem positive_prefix_formula (rom : PhysicalROM) (q handlerPC : Nat) (rest : List PackingOp)
    (headerQ : rom.semantic.read .input 1 = q) (hq : 0 < q)
    (count : Nat) (bound : count ≤ 17) :
    natRun rom (program handlerPC (checker ++ rest)) count natInitial =
      if count ≤ 8 then runOps rom (((lead handlerPC) ++ [branch]).take count) natInitial
      else runOps rom ((positiveMiddle ++ [outerBranch]).take (count - 8))
        (natExecuteOp rom branch (runOps rom (lead handlerPC) natInitial)) := by
  by_cases first : count ≤ 8
  · rw [ite_eq_left first]
    exact first_eight_prefix rom handlerPC (checker ++ rest) count first
  · rw [ite_eq_right first]
    have actual := positive_tail_prefix rom q handlerPC rest headerQ hq (count - 8) (by omega)
    have sameCount : 8 + (count - 8) = count := by omega
    simpa only [sameCount] using actual

theorem positive_seventeen_run (rom : PhysicalROM) (q handlerPC : Nat) (rest : List PackingOp)
    (headerQ : rom.semantic.read .input 1 = q) (hq : 0 < q) :
    natRun rom (program handlerPC (checker ++ rest)) 17 natInitial =
      natExecuteOp rom outerBranch (runOps rom positiveMiddle
        (natExecuteOp rom branch (runOps rom (lead handlerPC) natInitial))) := by
  have slice := positive_middle_slice handlerPC rest
  have entry := positive_eight_control rom q handlerPC headerQ hq
  rw [show 17 = 8 + 9 by decide, natRun_add, first_eight_run]
  simpa only [positiveMiddle_length] using
    natRun_of_segment_last rom (program handlerPC (checker ++ rest)) positiveMiddle outerBranch 8
      slice.1 slice.2.1 slice.2.2 positiveMiddle_noJump _ entry.1 entry.2

theorem old_seventeen_run (rom : PhysicalROM) (rest : List PackingOp) :
    natRun rom (checker ++ rest) 17 natInitial =
      natExecuteOp rom outerBranch (runOps rom oldInitialLead natInitial) := by
  have code : ∀ position (hp : position < oldInitialLead.length),
      (checker ++ rest)[0 + position]'(by
        simp only [List.length_append, checker_length]
        rw [oldInitialLead_length] at hp
        omega) = oldInitialLead[position] := by
    intro position hp
    rw [oldInitialLead_length] at hp
    interval_cases position <;> rfl
  simpa only [oldInitialLead_length] using
    natRun_of_segment_last rom (checker ++ rest) oldInitialLead outerBranch 0
      (by simp only [List.length_append, checker_length, oldInitialLead_length]; omega)
      code (by rfl) oldInitialLead_noJump natInitial rfl rfl

private theorem state_ext (first second : NatState)
    (register : ∀ reg, first.register reg = second.register reg)
    (heap : ∀ address, first.heap address = second.heap address)
    (pc : first.pc = second.pc) (active : first.halted = second.halted) : first = second := by
  cases first with
  | mk fr fh fp fa =>
    cases second with
    | mk sr sh sp sa =>
      have registers : fr = sr := funext register
      have heaps : fh = sh := funext heap
      cases registers
      cases heaps
      cases pc
      cases active
      rfl

theorem positive_sixteen_state (rom : PhysicalROM) (q handlerPC : Nat)
    (headerQ : rom.semantic.read .input 1 = q) (hq : 0 < q) :
    runOps rom positiveMiddle (natExecuteOp rom branch (runOps rom (lead handlerPC) natInitial)) =
      runOps rom oldInitialLead natInitial := by
  rw [positive_eight_state rom q handlerPC headerQ hq]
  apply state_ext
  case' register => intro point; cases point
  case' heap => intro point; cases point
  all_goals simp [positiveMiddle, oldInitialLead, restore, lead, checker, setCell, storeCell,
    testCell, loadCell, runOps, natInitial, natExecuteOp, Op.execute, Instruction.execute, Function.update_apply]
  all_goals omega

/-- Full-state equality only at the real common step17. The N header is
read identically on both sides, so this equality needs only its genuine
positive-q header condition, not a supplied N/heap/tree value. -/
theorem positive_seventeen_eq (rom : PhysicalROM) (q handlerPC : Nat) (rest : List PackingOp)
    (headerQ : rom.semantic.read .input 1 = q) (hq : 0 < q) :
    natRun rom (program handlerPC (checker ++ rest)) 17 natInitial =
      natRun rom (checker ++ rest) 17 natInitial := by
  rw [positive_seventeen_run rom q handlerPC rest headerQ hq, old_seventeen_run]
  exact congrArg (natExecuteOp rom outerBranch) (positive_sixteen_state rom q handlerPC headerQ hq)

theorem positive_seventeen_control (rom : PhysicalROM) (N q handlerPC : Nat) (rest : List PackingOp)
    (headerN : rom.semantic.read .input 0 = N) (headerQ : rom.semantic.read .input 1 = q) (hq : 0 < q) :
    let after := natRun rom (program handlerPC (checker ++ rest)) 17 natInitial
    after.pc = (if N = 0 then 630 else 85) ∧ after.halted = false := by
  dsimp only
  rw [positive_seventeen_eq rom q handlerPC rest headerQ hq, old_seventeen_run]
  simp [oldInitialLead, outerBranch, checker, setCell, storeCell, testCell, loadCell,
    runOps, natInitial, natExecuteOp, Op.execute, Instruction.execute, headerN]

theorem original_positive_seventeen_eq (q : Nat) (full : List (Finset (Fin q)))
    (used : Finset (Fin q)) (hq : 0 < q) (handlerPC : Nat) (rest : List PackingOp) :
    natRun (controllerInput q full used) (program handlerPC (checker ++ rest)) 17 natInitial =
      natRun (controllerInput q full used) (checker ++ rest) 17 natInitial :=
  positive_seventeen_eq (controllerInput q full used) q handlerPC rest rfl hq

theorem original_positive_seventeen_control (q : Nat) (full : List (Finset (Fin q)))
    (used : Finset (Fin q)) (hq : 0 < q) (handlerPC : Nat) (rest : List PackingOp) :
    let after := natRun (controllerInput q full used) (program handlerPC (checker ++ rest)) 17 natInitial
    after.pc = (if full.length = 0 then 630 else 85) ∧ after.halted = false :=
  positive_seventeen_control (controllerInput q full used) full.length q handlerPC rest rfl rfl hq

end PaperProofs.Structure.LaminarTree.PA06A19PrepareEarlyGate079
