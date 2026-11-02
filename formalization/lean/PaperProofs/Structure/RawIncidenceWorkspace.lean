module

public import PaperProofs.Structure.RawIncidenceCheckerBoundary
public import PaperProofs.Structure.RawIncidenceDispatcher

/-! The raw checker preserves every actual natural-address workspace cell
outside its eight scratch words, including the active handoff boundary.
No fresh heap is supplied when construction starts. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PackingMachine

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawIncidenceScanSafety

def GuardedNatAccess (heapWords : Nat) (rom : PhysicalROM)
    (program : List PackingOp) (state : NatState) : Prop :=
  state.halted = false →
    match PackingOp.decode (natFetch program state.pc) with
    | none => True
    | some op => NatAccessFits rom heapWords state op

theorem natExecuteOp_heap_frame (rom : PhysicalROM) (heapWords : Nat)
    (op : PackingOp) (state : NatState) (haccess : NatAccessFits rom heapWords state op)
    (address : Nat) (haddress : heapWords ≤ address) :
    (natExecuteOp rom op state).heap address = state.heap address := by
  cases op with
  | base op =>
    cases op with
    | base instruction =>
      cases instruction with
      | storeHeap pointer source =>
        have hp : state.register pointer < heapWords := haccess
        have hne : address ≠ state.register pointer := by omega
        change Function.update state.heap (state.register pointer) (state.register source) address = _
        exact Function.update_of_ne hne _ _
      | constant target value => rfl
      | add target left right => rfl
      | minimum target left right => rfl
      | select target condition whenTrue whenFalse => rfl
      | loadROM region target pointer => rfl
      | loadHeap target pointer => rfl
    | subtract target left right => rfl
  | arithmetic operation target left right => rfl
  | jumpIfZero condition target => rfl

theorem natStep_heap_frame (rom : PhysicalROM) (program : List PackingOp)
    (heapWords : Nat) (state : NatState) (haccess : GuardedNatAccess heapWords rom program state)
    (address : Nat) (haddress : heapWords ≤ address) :
    (natStep rom program state).heap address = state.heap address := by
  cases hh : state.halted
  · have hs := haccess hh
    simp only [natStep, hh, Bool.false_eq_true, ite_false]
    cases hd : PackingOp.decode (natFetch program state.pc) with
    | none => rfl
    | some op =>
      rw [hd] at hs
      exact natExecuteOp_heap_frame rom heapWords op state hs address haddress
  · simp only [natStep, hh, ite_true]

theorem natRun_heap_frame (rom : PhysicalROM) (program : List PackingOp)
    (heapWords count : Nat) (state : NatState)
    (haccess : ∀ k < count, GuardedNatAccess heapWords rom program (natRun rom program k state))
    (address : Nat) (haddress : heapWords ≤ address) :
    (natRun rom program count state).heap address = state.heap address := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [natRun_succ]
    exact (natStep_heap_frame rom program heapWords _ (haccess count (by omega)) address haddress).trans
      (ih (fun k hk => haccess k (by omega)))

theorem natRun_active_of_le (rom : PhysicalROM) (program : List PackingOp) (state : NatState)
    (before after : Nat) (hle : before ≤ after)
    (hactive : (natRun rom program after state).halted = false) :
    (natRun rom program before state).halted = false := by
  cases hh : (natRun rom program before state).halted
  · rfl
  · have hsame : natRun rom program after state = natRun rom program before state := by
      conv_lhs => rw [show after = before + (after - before) by omega]
      rw [natRun_add, RawIncidenceLaminarRAM.natRun_of_halted rom program _ hh]
    rw [hsame, hh] at hactive
    cases hactive

end PaperProofs.Structure.LaminarTree.PackingMachine

namespace PaperProofs.Structure.LaminarTree.RawIncidenceLaminarRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine
  RawIncidenceScanSafety

theorem checker_active_heap_frame (q : Nat) (full : List (Finset (Fin q))) (count : Nat)
    (hactive : (natRun (rawIncidenceROM q full) checker count natInitial).halted = false)
    (address : Nat) (haddress : 8 ≤ address) :
    (natRun (rawIncidenceROM q full) checker count natInitial).heap address = 0 := by
  let rom := rawIncidenceROM q full
  obtain ⟨steps, _hsteps, hsafe, hhalt⟩ := checker_has_safe_halt q full
  have hc : count < steps := by
    by_contra hnot
    have hle : steps ≤ count := by omega
    have hsame : natRun rom checker count natInitial = natRun rom checker steps natInitial := by
      conv_lhs => rw [show count = steps + (count - steps) by omega]
      exact natRun_after_halt rom checker natInitial steps hhalt (count - steps)
    rw [hsame, hhalt] at hactive
    cases hactive
  change (natRun rom checker count natInitial).heap address = natInitial.heap address
  apply natRun_heap_frame rom checker 8 count natInitial ?_ address haddress
  intro k hk ha
  have hp := hsafe k ((hk.trans hc).le)
  obtain ⟨index, _hi, _hpc, hguard⟩ := hp.2.2
  have hg := hguard ha
  cases hd : PackingOp.decode (natFetch checker (natRun rom checker k natInitial).pc) with
  | none => trivial
  | some op =>
    rw [hd] at hg
    exact hg

/-- Acceptance enters the actual appended constructor with its original
workspace intact. The code has not executed any constructor instruction. -/
theorem dispatcher_constructor_entry (constructor : List PackingOp) (q : Nat)
    (full : List (Finset (Fin q))) (hlaminar : LaminarSchedule full) :
    ∃ clock : Nat, clock ≤ checkerSteps full.length q + 1 ∧
      (natRun (rawIncidenceROM q full) (dispatcherProgram constructor) clock natInitial).halted = false ∧
      (natRun (rawIncidenceROM q full) (dispatcherProgram constructor) clock natInitial).pc =
        5 * (checker.length + 2) ∧
      (natRun (rawIncidenceROM q full) (dispatcherProgram constructor) clock natInitial).register .value = 1 ∧
      ∀ address : Nat, 8 ≤ address →
        (natRun (rawIncidenceROM q full) (dispatcherProgram constructor) clock natInitial).heap address = 0 := by
  obtain ⟨count, hcount, hprefix, hactive, hheap, _hvalue, _hreject, haccept, _hempty⟩ :=
    checker_dispatcher_boundary constructor q full
  have hbefore : (natRun (rawIncidenceROM q full) checker count natInitial).halted = false := by
    have hs := natRun_active_of_le (rawIncidenceROM q full) (dispatcherProgram constructor)
      natInitial count (count + 2) (by omega) hactive
    rw [hprefix count le_rfl] at hs
    exact hs
  obtain ⟨hpc, hflag⟩ := haccept hlaminar
  refine ⟨count + 2, by omega, hactive, hpc, hflag, ?_⟩
  intro address haddress
  rw [hheap]
  exact checker_active_heap_frame q full count hbefore address haddress

end PaperProofs.Structure.LaminarTree.RawIncidenceLaminarRAM
