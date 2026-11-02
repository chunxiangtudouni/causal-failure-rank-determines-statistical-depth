module

public import Common.PSTR_SYM_RestoreCount_026

/-! Static finite control for the real N-tag test. Both callees are fixed
before the input. Its two HALT ports really WRITE the current symbol and
transfer to the corresponding fixed callee; there is no head reset. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicFront

open Turing PSTRTMSeq005

variable {z p : Nat}

def testLabel (label : Fin 11) : Fin ((z + p + 12) + 1) := ⟨label.val, by omega⟩
def zeroLabel (label : Fin (z + 1)) : Fin ((z + p + 12) + 1) := ⟨11 + label.val, by omega⟩
def positiveLabel (label : Fin (p + 1)) : Fin ((z + p + 12) + 1) := ⟨z + 12 + label.val, by omega⟩

def testCfg (cfg : MachineState 10) : MachineState (z + p + 12) := ⟨testLabel cfg.q, cfg.Tape⟩
def zeroCfg (cfg : MachineState z) : MachineState (z + p + 12) := ⟨zeroLabel cfg.q, cfg.Tape⟩
def positiveCfg (cfg : MachineState p) : MachineState (z + p + 12) := ⟨positiveLabel cfg.q, cfg.Tape⟩

def firstNatBranchMachine (zero : Machine z) (positive : Machine p) : Machine (z + p + 12) :=
  fun label symbol =>
    if htest : label.val < 11 then
      match firstNatTestMachine ⟨label.val, htest⟩ symbol with
      | some (next, op) => some (testLabel next, op)
      | none => if label.val = 10 then some (zeroLabel (0 : Fin (z + 1)), .write symbol)
        else some (positiveLabel (0 : Fin (p + 1)), .write symbol)
    else if hzero : label.val < z + 12 then
      (zero ⟨label.val - 11, by omega⟩ symbol).map (fun (next, op) => (zeroLabel next, op))
    else
      (positive ⟨label.val - (z + 12), by omega⟩ symbol).map
        (fun (next, op) => (positiveLabel next, op))

theorem branch_step_test (zero : Machine z) (positive : Machine p) (cfg : MachineState 10) :
    TM0.step (firstNatBranchMachine zero positive) (testCfg cfg) =
      match TM0.step firstNatTestMachine cfg with
      | some next => some (testCfg next)
      | none => if cfg.q.val = 10 then some (zeroCfg ⟨0, cfg.Tape⟩)
        else some (positiveCfg ⟨0, cfg.Tape⟩) := by
  cases cfg with
  | mk label tape =>
    unfold TM0.step firstNatBranchMachine testCfg testLabel
    simp only [dite_eq_left label.isLt, Fin.eta]
    cases h : firstNatTestMachine label tape.head with
    | none =>
      by_cases port : label.val = 10 <;> simp [port, zeroCfg, positiveCfg, Tape.write_self]
    | some value =>
      obtain ⟨next, op⟩ := value
      cases op <;> simp

theorem branch_step_zero (zero : Machine z) (positive : Machine p) (cfg : MachineState z) :
    TM0.step (firstNatBranchMachine zero positive) (zeroCfg cfg) =
      (TM0.step zero cfg).map (zeroCfg (p := p)) := by
  cases cfg with
  | mk label tape =>
    unfold TM0.step firstNatBranchMachine zeroCfg zeroLabel
    simp only [show ¬11 + label.val < 11 by omega, ↓reduceDIte,
      show 11 + label.val < z + 12 by omega, Nat.add_sub_cancel_left, Fin.eta]
    cases h : zero label tape.head with
    | none => simp
    | some value =>
      obtain ⟨next, op⟩ := value
      cases op <;> simp

theorem branch_step_positive (zero : Machine z) (positive : Machine p) (cfg : MachineState p) :
    TM0.step (firstNatBranchMachine zero positive) (positiveCfg cfg) =
      (TM0.step positive cfg).map (positiveCfg (z := z)) := by
  cases cfg with
  | mk label tape =>
    unfold TM0.step firstNatBranchMachine positiveCfg positiveLabel
    simp only [show ¬z + 12 + label.val < 11 by omega, ↓reduceDIte,
      show ¬z + 12 + label.val < z + 12 by omega, Nat.add_sub_cancel_left, Fin.eta]
    cases h : positive label tape.head with
    | none => simp
    | some value =>
      obtain ⟨next, op⟩ := value
      cases op <;> simp

theorem branch_runs_zero (zero : Machine z) (positive : Machine p)
    (initial testFinal : MachineState 10) (final : MachineState z)
    (testTrace : List (MachineState 10)) (trace : List (MachineState z))
    (testRun : RunsFrom firstNatTestMachine initial testTrace testFinal)
    (port : testFinal.q.val = 10)
    (run : RunsFrom zero ⟨0, testFinal.Tape⟩ trace final) :
    RunsFrom (firstNatBranchMachine zero positive) (testCfg initial)
      (testTrace.map (testCfg (z := z) (p := p)) ++ trace.map (zeroCfg (p := p)))
      (zeroCfg final) := by
  obtain ⟨thead, tchain, tlast, thalt⟩ := testRun
  obtain ⟨head, chain, last, halt⟩ := run
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [List.head?_append, List.head?_map, thead]
  · apply List.IsChain.append
    · apply (List.isChain_map _).mpr
      exact tchain.imp (fun before after step => by simp [branch_step_test, step])
    · apply (List.isChain_map _).mpr
      exact chain.imp (fun before after step => by simp [branch_step_zero, step])
    · intro x hx y hy
      simp only [List.getLast?_map, tlast, Option.map_some, Option.mem_some_iff] at hx
      simp only [List.head?_map, head, Option.map_some, Option.mem_some_iff] at hy
      subst x
      subst y
      simp [branch_step_test, thalt, port]
  · simp [List.getLast?_append, List.getLast?_map, last]
  · simp [branch_step_zero, halt]

theorem branch_runs_positive (zero : Machine z) (positive : Machine p)
    (initial testFinal : MachineState 10) (final : MachineState p)
    (testTrace : List (MachineState 10)) (trace : List (MachineState p))
    (testRun : RunsFrom firstNatTestMachine initial testTrace testFinal)
    (port : testFinal.q.val ≠ 10)
    (run : RunsFrom positive ⟨0, testFinal.Tape⟩ trace final) :
    RunsFrom (firstNatBranchMachine zero positive) (testCfg initial)
      (testTrace.map (testCfg (z := z) (p := p)) ++ trace.map (positiveCfg (z := z)))
      (positiveCfg final) := by
  obtain ⟨thead, tchain, tlast, thalt⟩ := testRun
  obtain ⟨head, chain, last, halt⟩ := run
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [List.head?_append, List.head?_map, thead]
  · apply List.IsChain.append
    · apply (List.isChain_map _).mpr
      exact tchain.imp (fun before after step => by simp [branch_step_test, step])
    · apply (List.isChain_map _).mpr
      exact chain.imp (fun before after step => by simp [branch_step_positive, step])
    · intro x hx y hy
      simp only [List.getLast?_map, tlast, Option.map_some, Option.mem_some_iff] at hx
      simp only [List.head?_map, head, Option.map_some, Option.mem_some_iff] at hy
      subst x
      subst y
      simp [branch_step_test, thalt, port]
  · simp [List.getLast?_append, List.getLast?_map, last]
  · simp [branch_step_positive, halt]

theorem branch_trace_length_zero (testTrace : List (MachineState 10))
    (trace : List (MachineState z)) :
    (testTrace.map (testCfg (z := z) (p := p)) ++ trace.map (zeroCfg (p := p))).length =
      testTrace.length + trace.length := by simp

theorem branch_trace_length_positive (testTrace : List (MachineState 10))
    (trace : List (MachineState p)) :
    (testTrace.map (testCfg (z := z) (p := p)) ++ trace.map (positiveCfg (z := z))).length =
      testTrace.length + trace.length := by simp

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicFront
