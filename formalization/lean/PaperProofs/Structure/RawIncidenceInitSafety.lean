module

public import PaperProofs.Structure.RawIncidenceMacroRunSafety

/-! Actual initialization and the two reset segments of the fixed raw
checker. Only original heap cells and raw header words are accessed. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.RawIncidenceMacroSafety

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety

theorem setCell_prefix_registerBound (N q : Nat) (rom : PhysicalROM) (cell value : Nat)
    (state : NatState) (hr : RegistersBound N q state) (hc : cell < 8)
    (hv : value ≤ registerBound N q) (count : Nat) (hcount : count ≤ 3) :
    RegistersBound N q (runOps rom ((setCell cell value).take count) state) := by
  have ha := hr .address
  have hi := hr .index
  have hval := hr .value
  have ht := hr .total
  have ho := hr .old
  have hf := hr .fresh
  have hflag := hr .flag
  intro reg
  cases reg <;> interval_cases count <;>
    simp_all +decide [runOps, setCell, storeCell, natExecuteOp, Op.execute, Instruction.execute,
      RegistersBound, registerBound] <;> omega

theorem setCell_prefix_accessFits (rom : PhysicalROM) (cell value : Nat) (state : NatState)
    (hc : cell < 8) (count : Nat) (hcount : count < (setCell cell value).length) :
    NatAccessFits rom 8 (runOps rom ((setCell cell value).take count) state) (setCell cell value)[count] := by
  have hn : count ≤ 2 := by change count < 3 at hcount; omega
  interval_cases count <;>
    simp_all +decide [runOps, setCell, storeCell, natExecuteOp, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits]

theorem checker_setJ_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 85) (hactive : state.halted = false) (hr : RegistersBound full.length q state) :
    ∀ count ≤ 3, SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  let lead := setJCode.take 2
  let last : PackingOp := .base (.base (.storeHeap .address .total))
  have hlen : lead.length = 2 := rfl
  have hblock : lead ++ [last] = setJCode := rfl
  have hcode : ∀ position (hp : position < (lead ++ [last]).length),
      checker[17 + position]'(by rw [checker_length]; change position < 3 at hp; omega) = (lead ++ [last])[position] := by
    intro position hp
    change position < 3 at hp
    interval_cases position <;> rfl
  have hend : QuickPC (runOps (rawIncidenceROM q full) (lead ++ [last]) state).pc := by
    have hp : (runOps (rawIncidenceROM q full) (lead ++ [last]) state).pc = 100 := by
      simp [hblock, runOps, setJCode, setCell, storeCell, natExecuteOp, Op.execute, Instruction.execute, hpc]
    rw [hp]
    decide
  have h := checker_segment_prefix_safe q full lead last 17 (by decide) hcode
    (by simp [lead, setJCode, setCell, storeCell, NoJump]) state hpc hactive
    (by
      intro count hc
      rw [hblock]
      exact setCell_prefix_registerBound full.length q _ 3 0 state hr (by decide) (by omega)
        count (by simpa only [hlen] using hc))
    (by
      intro count hc
      simpa only [hblock, setJCode] using setCell_prefix_accessFits (rawIncidenceROM q full) 3 0 state
        (by decide) count (by simpa only [hblock, setJCode] using hc)) hend
  simpa only [hlen] using h

theorem scanInit_prefix_registerBound (N q : Nat) (rom : PhysicalROM) (state : NatState)
    (hr : RegistersBound N q state) (count : Nat) (hcount : count ≤ 12) :
    RegistersBound N q (runOps rom (scanInitCode.take count) state) := by
  have ha := hr .address
  have hi := hr .index
  have hval := hr .value
  have ht := hr .total
  have ho := hr .old
  have hf := hr .fresh
  have hflag := hr .flag
  intro reg
  cases reg <;> interval_cases count <;>
    simp_all +decide [runOps, scanInitCode, setCell, storeCell, natExecuteOp, Op.execute,
      Instruction.execute, RegistersBound, registerBound]

theorem scanInit_prefix_accessFits (rom : PhysicalROM) (state : NatState)
    (count : Nat) (hcount : count < scanInitCode.length) :
    NatAccessFits rom 8 (runOps rom (scanInitCode.take count) state) scanInitCode[count] := by
  have hn : count ≤ 11 := by change count < 12 at hcount; omega
  interval_cases count <;>
    simp +decide [runOps, scanInitCode, setCell, storeCell, natExecuteOp, Op.execute,
      Instruction.execute, NatAccessFits, AccessFits]

theorem checker_scanInit_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 135) (hactive : state.halted = false) (hr : RegistersBound full.length q state) :
    ∀ count ≤ 12, SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  let lead := scanInitCode.take 11
  let last : PackingOp := .base (.base (.storeHeap .address .total))
  have hlen : lead.length = 11 := rfl
  have hblock : lead ++ [last] = scanInitCode := rfl
  have hcode : ∀ position (hp : position < (lead ++ [last]).length),
      checker[27 + position]'(by rw [checker_length]; change position < 12 at hp; omega) = (lead ++ [last])[position] := by
    intro position hp
    change position < 12 at hp
    interval_cases position <;> rfl
  have hend : QuickPC (runOps (rawIncidenceROM q full) (lead ++ [last]) state).pc := by
    have hp : (runOps (rawIncidenceROM q full) (lead ++ [last]) state).pc = 195 := by
      simp [hblock, runOps, scanInitCode, setCell, storeCell, natExecuteOp, Op.execute, Instruction.execute,
        hpc]
    rw [hp]
    decide
  have h := checker_segment_prefix_safe q full lead last 27 (by decide) hcode
    (by simp [lead, scanInitCode, setCell, storeCell, NoJump]) state hpc hactive
    (by
      intro count hc
      rw [hblock]
      exact scanInit_prefix_registerBound full.length q _ state hr count (by simpa only [hlen] using hc))
    (by
      intro count hc
      simpa only [hblock] using scanInit_prefix_accessFits (rawIncidenceROM q full) state count
        (by simpa only [hblock] using hc)) hend
  simpa only [hlen] using h

theorem checker_outer_setup_safe (q : Nat) (full : List (Finset (Fin q))) (i j : Nat) (state : NatState)
    (ready : Ready full.length q i j 50 state) (hi : i < full.length) (_hj : j ≤ full.length)
    (hr : RegistersBound full.length q state) :
    ∀ count ≤ 10, SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  have ht := checker_outerTest_safe q full i j state ready hi.le hr
  let tested := natRun (rawIncidenceROM q full) checker 7 state
  have hp : tested.pc = 85 := by
    rw [show tested = runOps (rawIncidenceROM q full) (testCell 0 2 126) state from
      natRun_checker_outerTest _ state ready.pc ready.active]
    simpa only [ready.dimension, ready.left, ready.pc, Nat.sub_ne_zero_of_lt hi, ite_false] using
      (runOps_testCell (rawIncidenceROM q full) 0 2 126 state).2.2.1
  have ha : tested.halted = false := by
    rw [show tested = runOps (rawIncidenceROM q full) (testCell 0 2 126) state from
      natRun_checker_outerTest _ state ready.pc ready.active, runOps_halted, ready.active]
  exact safe_prefix_add q full state 7 3 ht (checker_setJ_safe q full tested hp ha (ht 7 le_rfl).1)

theorem checker_pair_setup_safe (q : Nat) (full : List (Finset (Fin q))) (i j : Nat) (state : NatState)
    (ready : Ready full.length q i j 100 state) (_hi : i < full.length) (hj : j < full.length)
    (hr : RegistersBound full.length q state) :
    ∀ count ≤ 19, SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  have ht := checker_pairTest_safe q full i j state ready hj.le hr
  let tested := natRun (rawIncidenceROM q full) checker 7 state
  have hp : tested.pc = 135 := by
    rw [show tested = runOps (rawIncidenceROM q full) (testCell 0 3 117) state from
      natRun_checker_pairTest _ state ready.pc ready.active]
    simpa only [ready.dimension, ready.right, ready.pc, Nat.sub_ne_zero_of_lt hj, ite_false] using
      (runOps_testCell (rawIncidenceROM q full) 0 3 117 state).2.2.1
  have ha : tested.halted = false := by
    rw [show tested = runOps (rawIncidenceROM q full) (testCell 0 3 117) state from
      natRun_checker_pairTest _ state ready.pc ready.active, runOps_halted, ready.active]
  exact safe_prefix_add q full state 7 12 ht (checker_scanInit_safe q full tested hp ha (ht 7 le_rfl).1)

theorem checkerInit_prefix_registerBound (q : Nat) (full : List (Finset (Fin q)))
    (count : Nat) (hcount : count ≤ 10) :
    RegistersBound full.length q (runOps (rawIncidenceROM q full) (checkerInitCode.take count) natInitial) := by
  intro reg
  cases reg <;> interval_cases count <;>
    simp +decide [runOps, checkerInitCode, checker, setCell, storeCell, natInitial, natExecuteOp,
      Op.execute, Instruction.execute, rawIncidenceROM, PhysicalROM.semantic, PhysicalROM.words,
      registerBound] <;> omega

theorem checkerInit_prefix_accessFits (q : Nat) (full : List (Finset (Fin q)))
    (count : Nat) (hcount : count < checkerInitCode.length) :
    NatAccessFits (rawIncidenceROM q full) 8
      (runOps (rawIncidenceROM q full) (checkerInitCode.take count) natInitial) checkerInitCode[count] := by
  have hn : count ≤ 9 := by change count < 10 at hcount; omega
  interval_cases count <;>
    simp +decide [runOps, checkerInitCode, checker, setCell, storeCell, natInitial, natExecuteOp,
      Op.execute, Instruction.execute, rawIncidenceROM, PhysicalROM.semantic, PhysicalROM.words,
      NatAccessFits, AccessFits]

theorem checker_init_safe (q : Nat) (full : List (Finset (Fin q))) :
    ∀ count ≤ 10, SafePoint q full (natRun (rawIncidenceROM q full) checker count natInitial) := by
  let lead := checkerInitCode.take 9
  let last : PackingOp := .base (.base (.storeHeap .address .total))
  have hlen : lead.length = 9 := rfl
  have hblock : lead ++ [last] = checkerInitCode := rfl
  have hcode : ∀ position (hp : position < (lead ++ [last]).length),
      checker[0 + position]'(by rw [checker_length]; change position < 10 at hp; omega) = (lead ++ [last])[position] := by
    intro position hp
    change position < 10 at hp
    interval_cases position <;> rfl
  have hend : QuickPC (runOps (rawIncidenceROM q full) (lead ++ [last]) natInitial).pc := by
    have hp : (runOps (rawIncidenceROM q full) (lead ++ [last]) natInitial).pc = 50 := by
      simp [hblock, runOps, checkerInitCode, checker, setCell, storeCell, natInitial, natExecuteOp,
        Op.execute, Instruction.execute]
    rw [hp]
    decide
  have h := checker_segment_prefix_safe q full lead last 0 (by decide) hcode
    (by simp [lead, checkerInitCode, checker, setCell, storeCell, NoJump]) natInitial rfl rfl
    (by
      intro count hc
      rw [hblock]
      exact checkerInit_prefix_registerBound q full count (by simpa only [hlen] using hc))
    (by
      intro count hc
      simpa only [hblock] using checkerInit_prefix_accessFits q full count (by simpa only [hblock] using hc)) hend
  simpa only [hlen] using h

end PaperProofs.Structure.LaminarTree.RawIncidenceMacroSafety
