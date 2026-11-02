module

public import PaperProofs.Structure.RawIncidenceMacroRunSafety

/-! Actual four-instruction counter tests and the original rejecting HALT.
These local branches retain every real prefix and use only the eight cells
already allocated by the original raw-incidence checker. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.RawIncidenceMacroSafety

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety

section Bounds

attribute [local simp] runOps natExecuteOp Op.execute Instruction.execute
  pairCounterTest loadCell rejectCode jumpTo RegistersBound registerBound

theorem counterTest_prefix_registerBound (N q : Nat) (rom : PhysicalROM) (cell : Nat)
    (state : NatState) (hr : RegistersBound N q state) (hc : cell < 8)
    (hv : state.heap cell ≤ registerBound N q) (count : Nat) (hcount : count ≤ 4) :
    RegistersBound N q (runOps rom ((pairCounterTest cell).take count) state) := by
  have ha := hr .address
  have hi := hr .index
  have hval := hr .value
  have ht := hr .total
  have ho := hr .old
  have hf := hr .fresh
  have hflag := hr .flag
  intro reg
  cases reg <;> interval_cases count <;> simp_all +decide <;> omega

theorem counterTest_prefix_accessFits (rom : PhysicalROM) (cell : Nat) (state : NatState)
    (hc : cell < 8) (count : Nat) (hcount : count < (pairCounterTest cell).length) :
    NatAccessFits rom 8 (runOps rom ((pairCounterTest cell).take count) state) (pairCounterTest cell)[count] := by
  have hn : count ≤ 3 := by change count < 4 at hcount; omega
  interval_cases count <;> try exact True.intro
  simp_all +decide [NatAccessFits, AccessFits]

theorem reject_prefix_registerBound (N q : Nat) (rom : PhysicalROM) (state : NatState)
    (hr : RegistersBound N q state) (count : Nat) (hcount : count ≤ 4) :
    RegistersBound N q (runOps rom (rejectCode.take count) state) := by
  have ha := hr .address
  have hi := hr .index
  have hval := hr .value
  have ht := hr .total
  have ho := hr .old
  have hf := hr .fresh
  have hflag := hr .flag
  intro reg
  cases reg <;> interval_cases count <;> simp_all +decide

theorem reject_prefix_accessFits (rom : PhysicalROM) (state : NatState)
    (count : Nat) (hcount : count < rejectCode.length) :
    NatAccessFits rom 8 (runOps rom (rejectCode.take count) state) rejectCode[count] := by
  have hn : count ≤ 3 := by change count < 4 at hcount; omega
  interval_cases count <;> exact True.intro

end Bounds

theorem counterTest_code (which : Fin 3) :
    ∀ position (hp : position < 4),
      checker[92 + 4 * which.val + position]'(by have := which.isLt; rw [checker_length]; omega) =
        (pairCounterTest (5 + which.val))[position] := by
  rcases which with ⟨which, hwhich⟩
  interval_cases which <;> intro position hp <;> interval_cases position <;> rfl

theorem checker_counterTest_safe (q : Nat) (full : List (Finset (Fin q))) (which : Fin 3)
    (state : NatState) (hpc : state.pc = 5 * (92 + 4 * which.val)) (hactive : state.halted = false)
    (hcounter : state.heap (5 + which.val) ≤ q) (hr : RegistersBound full.length q state) :
    ∀ count ≤ 4, SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  let lead := (pairCounterTest (5 + which.val)).take 3
  have hlen : lead.length = 3 := rfl
  have hblock : lead ++ [.jumpIfZero .total .index] = pairCounterTest (5 + which.val) := rfl
  have hcell : 5 + which.val < 8 := by have := which.isLt; omega
  have hv : state.heap (5 + which.val) ≤ registerBound full.length q := by
    dsimp [registerBound]
    omega
  have hend : QuickPC (runOps (rawIncidenceROM q full) (pairCounterTest (5 + which.val)) state).pc := by
    rw [(runOps_counterTest _ (5 + which.val) state).2.2.1, hpc]
    split_ifs
    · decide
    · simp only [QuickPC, List.mem_cons, List.not_mem_nil, or_false]
      have := which.isLt
      omega
  have h := checker_segment_prefix_safe q full lead (.jumpIfZero .total .index) (92 + 4 * which.val)
    (by have := which.isLt; rw [hlen, checker_length]; omega)
    (by
      intro position hp
      change position < 4 at hp
      exact counterTest_code which position hp)
    (by simp [lead, pairCounterTest, loadCell, NoJump]) state hpc hactive
    (by
      intro count hc
      rw [hblock]
      exact counterTest_prefix_registerBound full.length q _ _ state hr hcell hv count (by simpa only [hlen] using hc))
    (by
      intro count hc
      simpa only [hblock] using counterTest_prefix_accessFits (rawIncidenceROM q full)
        (5 + which.val) state hcell count (by simpa only [hblock] using hc))
    (by simpa only [hblock] using hend)
  simpa only [hlen] using h

theorem checker_reject_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hpc : state.pc = 520) (hactive : state.halted = false) (hr : RegistersBound full.length q state) :
    ∀ count ≤ 5, SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
  let lead := rejectCode.take 3
  have hlen : lead.length = 3 := rfl
  have hblock : lead ++ [.jumpIfZero .flag .index] = rejectCode := rfl
  have hend : QuickPC (runOps (rawIncidenceROM q full) rejectCode state).pc := by
    have hp : (runOps (rawIncidenceROM q full) rejectCode state).pc = 630 := by
      simp [runOps, rejectCode, jumpTo, natExecuteOp, Op.execute, Instruction.execute]
    rw [hp]
    decide
  have hcode : ∀ position (hp : position < rejectCode.length),
      checker[104 + position]'(by change position < 4 at hp; rw [checker_length]; omega) = rejectCode[position] := by
    intro position hp
    change position < 4 at hp
    interval_cases position <;> rfl
  have hfour := checker_segment_prefix_safe q full lead (.jumpIfZero .flag .index) 104
    (by rw [hlen, checker_length]; decide)
    (by simpa only [hblock] using hcode)
    (by simp [lead, rejectCode, jumpTo, NoJump]) state hpc hactive
    (by
      intro count hc
      rw [hblock]
      exact reject_prefix_registerBound full.length q _ state hr count (by simpa only [hlen] using hc))
    (by
      intro count hc
      simpa only [hblock] using reject_prefix_accessFits (rawIncidenceROM q full) state count
        (by simpa only [hblock] using hc))
    (by simpa only [hblock] using hend)
  have hfour' : ∀ count ≤ 4, SafePoint q full (natRun (rawIncidenceROM q full) checker count state) := by
    simpa only [hlen] using hfour
  let rejected := natRun (rawIncidenceROM q full) checker 4 state
  have hp : rejected.pc = 630 := by
    rw [show rejected = runOps (rawIncidenceROM q full) rejectCode state from
      natRun_checker_reject_runOps _ state hpc hactive]
    simp [runOps, rejectCode, jumpTo, natExecuteOp, Op.execute, Instruction.execute]
  have hh : rejected.halted = false := by
    rw [show rejected = runOps (rawIncidenceROM q full) rejectCode state from
      natRun_checker_reject_runOps _ state hpc hactive, runOps_halted, hactive]
  apply safe_prefix_add q full state 4 1 hfour'
  intro count hc
  have hrr : RegistersBound full.length q rejected := (hfour' 4 le_rfl).1
  have he : count = 0 ∨ count = 1 := by omega
  rcases he with rfl | rfl
  · exact hfour' 4 le_rfl
  · rw [natRun_checker_halt _ rejected hp hh]
    exact safePoint_of_halt q full _ hp hrr

end PaperProofs.Structure.LaminarTree.RawIncidenceMacroSafety
