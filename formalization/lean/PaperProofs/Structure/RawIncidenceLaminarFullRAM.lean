module

public import PaperProofs.Structure.RawIncidenceLaminarRAM
import Mathlib.Tactic.IntervalCases

/-! Completion of the fixed raw-incidence checker phase. Proof invariants
below describe the existing RAM state; they supply no extra machine inputs.
Tree serialization remains a separate part of A06. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.RawIncidenceLaminarRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine

structure Ready (N q i j pointer : Nat) (state : NatState) : Prop where
  dimension : state.heap 0 = N
  tools : state.heap 1 = q
  left : state.heap 2 = i
  right : state.heap 3 = j
  value : state.register .value = 1
  pc : state.pc = pointer
  active : state.halted = false

def PairOK {q : Nat} (full : List (Finset (Fin q))) (i j : Nat) : Prop :=
  Disjoint (full.getD i ∅) (full.getD j ∅) ∨
    full.getD i ∅ ⊆ full.getD j ∅ ∨ full.getD j ∅ ⊆ full.getD i ∅

def RowOKFrom {q : Nat} (full : List (Finset (Fin q))) (i first : Nat) : Prop :=
  ∀ j, first ≤ j → j < full.length → PairOK full i j

def RowsOKFrom {q : Nat} (full : List (Finset (Fin q))) (first : Nat) : Prop :=
  ∀ i, first ≤ i → i < full.length → RowOKFrom full i 0

theorem rowOKFrom_step {q : Nat} (full : List (Finset (Fin q))) (i j : Nat)
    (hj : j < full.length) :
    RowOKFrom full i j ↔ PairOK full i j ∧ RowOKFrom full i (j + 1) := by
  constructor
  · intro h
    exact ⟨h j le_rfl hj, fun other ho hn => h other (by omega) hn⟩
  · rintro ⟨hfirst, hlater⟩ other ho hn
    by_cases heq : other = j
    · simpa only [heq] using hfirst
    · exact hlater other (by omega) hn

theorem rowsOKFrom_step {q : Nat} (full : List (Finset (Fin q))) (i : Nat)
    (hi : i < full.length) :
    RowsOKFrom full i ↔ RowOKFrom full i 0 ∧ RowsOKFrom full (i + 1) := by
  constructor
  · intro h
    exact ⟨h i le_rfl hi, fun other ho hn => h other (by omega) hn⟩
  · rintro ⟨hfirst, hlater⟩ other ho hn
    by_cases heq : other = i
    · simpa only [heq] using hfirst
    · exact hlater other (by omega) hn

theorem rowsOKFrom_zero_iff {q : Nat} (full : List (Finset (Fin q))) :
    RowsOKFrom full 0 ↔ LaminarSchedule full := by
  constructor
  · intro h left hleft right hright
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hleft
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hright
    simpa only [PairOK, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using
      h i (Nat.zero_le _) hi j (Nat.zero_le _) hj
  · intro h i _hi hi j _hj hj
    exact h _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
      _ (by rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj)

theorem natRun_checker_outerTest (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 50) (hactive : state.halted = false) :
    natRun rom checker 7 state = runOps rom (testCell 0 2 126) state := by
  let lead := (testCell 0 2 126).take 6
  have hlength : lead.length = 6 := rfl
  have hcode : ∀ position (hposition : position < lead.length),
      checker[10 + position]'(by rw [checker_length]; rw [hlength] at hposition; omega) = lead[position] := by
    intro position hposition
    rw [hlength] at hposition
    interval_cases position <;> rfl
  have hstraight : ∀ op ∈ lead, NoJump op := by simp [lead, testCell, loadCell, NoJump]
  exact natRun_of_segment_last rom checker lead (.jumpIfZero .flag .index) 10
    (by decide) hcode (by rfl) hstraight state hpc hactive

theorem natRun_checker_pairTest (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 100) (hactive : state.halted = false) :
    natRun rom checker 7 state = runOps rom (testCell 0 3 117) state := by
  let lead := (testCell 0 3 117).take 6
  have hlength : lead.length = 6 := rfl
  have hcode : ∀ position (hposition : position < lead.length),
      checker[20 + position]'(by rw [checker_length]; rw [hlength] at hposition; omega) = lead[position] := by
    intro position hposition
    rw [hlength] at hposition
    interval_cases position <;> rfl
  have hstraight : ∀ op ∈ lead, NoJump op := by simp [lead, testCell, loadCell, NoJump]
  exact natRun_of_segment_last rom checker lead (.jumpIfZero .flag .index) 20
    (by decide) hcode (by rfl) hstraight state hpc hactive

def setJCode : List PackingOp := setCell 3 0
def scanInitCode : List PackingOp := setCell 4 0 ++ setCell 5 0 ++ setCell 6 0 ++ setCell 7 0
def nextPairCode : List PackingOp := incrementCell 3 ++ jumpTo 20
def nextRowCode : List PackingOp := incrementCell 2 ++ jumpTo 10

theorem natRun_checker_setJ (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 85) (hactive : state.halted = false) :
    natRun rom checker 3 state = runOps rom setJCode state := by
  have hcode : ∀ position (hposition : position < setJCode.length),
      checker[17 + position]'(by rw [checker_length]; change position < 3 at hposition; omega) = setJCode[position] := by
    intro position hposition
    change position < 3 at hposition
    interval_cases position <;> rfl
  exact natRun_of_straight_segment rom checker setJCode 17 (by decide) hcode
    (by simp [setJCode, setCell, storeCell, NoJump]) state hpc hactive

theorem natRun_checker_scanInit (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 135) (hactive : state.halted = false) :
    natRun rom checker 12 state = runOps rom scanInitCode state := by
  have hcode : ∀ position (hposition : position < scanInitCode.length),
      checker[27 + position]'(by rw [checker_length]; change position < 12 at hposition; omega) = scanInitCode[position] := by
    intro position hposition
    change position < 12 at hposition
    interval_cases position <;> rfl
  exact natRun_of_straight_segment rom checker scanInitCode 27 (by decide) hcode
    (by simp [scanInitCode, setCell, storeCell, NoJump]) state hpc hactive

theorem natRun_checker_nextPair (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 540) (hactive : state.halted = false) :
    natRun rom checker 9 state = runOps rom nextPairCode state := by
  let lead := nextPairCode.take 8
  have hlength : lead.length = 8 := rfl
  have hcode : ∀ position (hposition : position < lead.length),
      checker[108 + position]'(by rw [checker_length]; rw [hlength] at hposition; omega) = lead[position] := by
    intro position hposition
    rw [hlength] at hposition
    interval_cases position <;> rfl
  have hstraight : ∀ op ∈ lead, NoJump op := by
    simp [lead, nextPairCode, incrementCell, loadCell, storeCell, jumpTo, NoJump]
  exact natRun_of_segment_last rom checker lead (.jumpIfZero .flag .index) 108
    (by decide) hcode (by rfl) hstraight state hpc hactive

theorem natRun_checker_nextRow (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 585) (hactive : state.halted = false) :
    natRun rom checker 9 state = runOps rom nextRowCode state := by
  let lead := nextRowCode.take 8
  have hlength : lead.length = 8 := rfl
  have hcode : ∀ position (hposition : position < lead.length),
      checker[117 + position]'(by rw [checker_length]; rw [hlength] at hposition; omega) = lead[position] := by
    intro position hposition
    rw [hlength] at hposition
    interval_cases position <;> rfl
  have hstraight : ∀ op ∈ lead, NoJump op := by
    simp [lead, nextRowCode, incrementCell, loadCell, storeCell, jumpTo, NoJump]
  exact natRun_of_segment_last rom checker lead (.jumpIfZero .flag .index) 117
    (by decide) hcode (by rfl) hstraight state hpc hactive

theorem ready_test (rom : PhysicalROM) {N q i j pointer : Nat} {state : NatState}
    (ready : Ready N q i j pointer state) (bound counter exit : Nat) :
    (runOps rom (testCell bound counter exit) state).heap = state.heap ∧
      (runOps rom (testCell bound counter exit) state).register .value = 1 ∧
      (runOps rom (testCell bound counter exit) state).pc =
        (if state.heap bound - state.heap counter = 0 then 5 * exit else pointer + 35) ∧
      (runOps rom (testCell bound counter exit) state).halted = false := by
  simpa only [ready.value, ready.pc, ready.active] using runOps_testCell rom bound counter exit state

theorem ready_setJ (rom : PhysicalROM) {N q i j : Nat} {state : NatState}
    (ready : Ready N q i j 85 state) : Ready N q i 0 100 (runOps rom setJCode state) := by
  constructor <;> simp [runOps, setJCode, setCell, storeCell, natExecuteOp, Op.execute,
    Instruction.execute, ready.dimension, ready.tools, ready.left,
    ready.value, ready.pc, ready.active]

theorem ready_scanInit (rom : PhysicalROM) {N q i j : Nat} {state : NatState}
    (ready : Ready N q i j 135 state) :
    Ready N q i j 195 (runOps rom scanInitCode state) ∧
      (runOps rom scanInitCode state).heap 4 = 0 ∧ (runOps rom scanInitCode state).heap 5 = 0 ∧
      (runOps rom scanInitCode state).heap 6 = 0 ∧ (runOps rom scanInitCode state).heap 7 = 0 := by
  refine ⟨?_, ?_⟩
  · constructor <;> simp [runOps, scanInitCode, setCell, storeCell, natExecuteOp, Op.execute,
      Instruction.execute, ready.dimension, ready.tools, ready.left, ready.right,
      ready.value, ready.pc, ready.active]
  · simp [runOps, scanInitCode, setCell, storeCell, natExecuteOp, Op.execute, Instruction.execute]

theorem ready_nextPair (rom : PhysicalROM) {N q i j : Nat} {state : NatState}
    (ready : Ready N q i j 540 state) : Ready N q i (j + 1) 100 (runOps rom nextPairCode state) := by
  constructor <;> simp [runOps, nextPairCode, incrementCell, loadCell, storeCell, jumpTo,
    natExecuteOp, Op.execute, Instruction.execute, ready.dimension, ready.tools, ready.left,
    ready.right, ready.value, ready.active]

theorem ready_nextRow (rom : PhysicalROM) {N q i j : Nat} {state : NatState}
    (ready : Ready N q i j 585 state) : Ready N q (i + 1) j 50 (runOps rom nextRowCode state) := by
  constructor <;> simp [runOps, nextRowCode, incrementCell, loadCell, storeCell, jumpTo,
    natExecuteOp, Op.execute, Instruction.execute, ready.dimension, ready.tools, ready.left,
    ready.right, ready.value, ready.active]

theorem Ready.frame {N q i j before after : Nat} {state next : NatState}
    (ready : Ready N q i j before state) (heap : next.heap = state.heap)
    (value : next.register .value = 1) (pc : next.pc = after) (active : next.halted = false) :
    Ready N q i j after next := by
  exact ⟨(congrFun heap 0).trans ready.dimension, (congrFun heap 1).trans ready.tools,
    (congrFun heap 2).trans ready.left, (congrFun heap 3).trans ready.right, value, pc, active⟩

theorem checker_outer_setup (rom : PhysicalROM) {N q i j : Nat} {state : NatState}
    (ready : Ready N q i j 50 state) (hi : i < N) :
    Ready N q i 0 100 (natRun rom checker 10 state) := by
  let tested := runOps rom (testCell 0 2 126) state
  have ht := ready_test rom ready 0 2 126
  have hp : tested.pc = 85 := by
    simpa only [tested, ready.dimension, ready.left, Nat.sub_ne_zero_of_lt hi, ite_false] using ht.2.2.1
  have hr : Ready N q i j 85 tested := ready.frame ht.1 ht.2.1 hp ht.2.2.2
  rw [show 10 = 7 + 3 from rfl, natRun_add,
    natRun_checker_outerTest rom state ready.pc ready.active,
    natRun_checker_setJ rom tested hr.pc hr.active]
  exact ready_setJ rom hr

theorem checker_pair_setup (rom : PhysicalROM) {N q i j : Nat} {state : NatState}
    (ready : Ready N q i j 100 state) (hj : j < N) :
    Ready N q i j 195 (natRun rom checker 19 state) ∧
      (natRun rom checker 19 state).heap 4 = 0 ∧ (natRun rom checker 19 state).heap 5 = 0 ∧
      (natRun rom checker 19 state).heap 6 = 0 ∧ (natRun rom checker 19 state).heap 7 = 0 := by
  let tested := runOps rom (testCell 0 3 117) state
  have ht := ready_test rom ready 0 3 117
  have hp : tested.pc = 135 := by
    simpa only [tested, ready.dimension, ready.right, Nat.sub_ne_zero_of_lt hj, ite_false] using ht.2.2.1
  have hr : Ready N q i j 135 tested := ready.frame ht.1 ht.2.1 hp ht.2.2.2
  rw [show 19 = 7 + 12 from rfl, natRun_add,
    natRun_checker_pairTest rom state ready.pc ready.active,
    natRun_checker_scanInit rom tested hr.pc hr.active]
  exact ready_scanInit rom hr

theorem checker_pair_terminal (rom : PhysicalROM) {N q i : Nat} {state : NatState}
    (ready : Ready N q i N 100 state) : Ready N q i N 585 (natRun rom checker 7 state) := by
  rw [natRun_checker_pairTest rom state ready.pc ready.active]
  have ht := ready_test rom ready 0 3 117
  exact ready.frame ht.1 ht.2.1 (by simpa only [ready.dimension, ready.right, Nat.sub_self, ite_true] using ht.2.2.1) ht.2.2.2

theorem natRun_checker_halt (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 630) (hactive : state.halted = false) :
    natRun rom checker 1 state = { state with halted := true } := by
  change natStep rom checker state = _
  exact natStep_halt rom checker state (by simpa only [checker_length] using hpc) hactive

theorem checker_outer_terminal (rom : PhysicalROM) {N q j : Nat} {state : NatState}
    (ready : Ready N q N j 50 state) :
    (natRun rom checker 8 state).halted = true ∧ (natRun rom checker 8 state).register .value = 1 := by
  let tested := runOps rom (testCell 0 2 126) state
  have ht := ready_test rom ready 0 2 126
  have hp : tested.pc = 630 := by
    simpa only [tested, ready.dimension, ready.left, Nat.sub_self, ite_true] using ht.2.2.1
  rw [show 8 = 7 + 1 from rfl, natRun_add,
    natRun_checker_outerTest rom state ready.pc ready.active,
    natRun_checker_halt rom tested hp ht.2.2.2]
  exact ⟨rfl, ht.2.1⟩

theorem natRun_checker_counterTest (rom : PhysicalROM) (which : Fin 3) (state : NatState)
    (hpc : state.pc = 5 * (92 + 4 * which.val)) (hactive : state.halted = false) :
    natRun rom checker 4 state = runOps rom (pairCounterTest (5 + which.val)) state := by
  let lead := (pairCounterTest (5 + which.val)).take 3
  have hlength : lead.length = 3 := rfl
  have hcode : ∀ position (hposition : position < lead.length),
      checker[92 + 4 * which.val + position]'(by rw [checker_length]; rw [hlength] at hposition; have := which.isLt; omega) = lead[position] := by
    intro position hposition
    rw [hlength] at hposition
    rcases which with ⟨which, hwhich⟩
    interval_cases which <;> interval_cases position <;> rfl
  have hlast : checker[92 + 4 * which.val + lead.length]'(by rw [checker_length, hlength]; have := which.isLt; omega) =
      .jumpIfZero .total .index := by
    have hwhich : which.val = 0 ∨ which.val = 1 ∨ which.val = 2 := by have := which.isLt; omega
    rcases hwhich with hw | hw | hw <;> simp only [lead, hw] <;> rfl
  have hstraight : ∀ op ∈ lead, NoJump op := by simp [lead, pairCounterTest, loadCell, NoJump]
  exact natRun_of_segment_last rom checker lead (.jumpIfZero .total .index) (92 + 4 * which.val)
    (by rw [hlength, checker_length]; have := which.isLt; omega) hcode hlast hstraight state hpc hactive

theorem runOps_counterTest (rom : PhysicalROM) (cell : Nat) (state : NatState) :
    (runOps rom (pairCounterTest cell) state).heap = state.heap ∧
    (runOps rom (pairCounterTest cell) state).register .value = state.register .value ∧
    (runOps rom (pairCounterTest cell) state).pc = (if state.heap cell = 0 then 540 else state.pc + 20) ∧
    (runOps rom (pairCounterTest cell) state).halted = state.halted := by
  simp [runOps, pairCounterTest, loadCell, natExecuteOp, Op.execute, Instruction.execute, Nat.add_assoc]

theorem checker_counterTest_ready (rom : PhysicalROM) (which : Fin 3) {N q i j : Nat} {state : NatState}
    (ready : Ready N q i j (5 * (92 + 4 * which.val)) state) :
    (natRun rom checker 4 state).heap = state.heap ∧
    Ready N q i j (if state.heap (5 + which.val) = 0 then 540 else 5 * (92 + 4 * which.val) + 20)
      (natRun rom checker 4 state) := by
  rw [natRun_checker_counterTest rom which state ready.pc ready.active]
  have ht := runOps_counterTest rom (5 + which.val) state
  exact ⟨ht.1, ready.frame ht.1 (ht.2.1.trans ready.value)
    (by simpa only [ready.pc] using ht.2.2.1) (ht.2.2.2.trans ready.active)⟩

def rejectCode : List PackingOp := [.base (.base (.constant .value 0))] ++ jumpTo 126

theorem natRun_checker_reject_runOps (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 520) (hactive : state.halted = false) :
    natRun rom checker 4 state = runOps rom rejectCode state := by
  let lead := rejectCode.take 3
  have hlength : lead.length = 3 := rfl
  have hcode : ∀ position (hposition : position < lead.length),
      checker[104 + position]'(by rw [checker_length]; rw [hlength] at hposition; omega) = lead[position] := by
    intro position hposition
    rw [hlength] at hposition
    interval_cases position <;> rfl
  have hstraight : ∀ op ∈ lead, NoJump op := by simp [lead, rejectCode, jumpTo, NoJump]
  exact natRun_of_segment_last rom checker lead (.jumpIfZero .flag .index) 104 (by decide)
    hcode (by rfl) hstraight state hpc hactive

theorem checker_reject (rom : PhysicalROM) (state : NatState)
    (hpc : state.pc = 520) (hactive : state.halted = false) :
    (natRun rom checker 5 state).halted = true ∧ (natRun rom checker 5 state).register .value = 0 := by
  let rejected := runOps rom rejectCode state
  have hp : rejected.pc = 630 := by simp [rejected, runOps, rejectCode, jumpTo, natExecuteOp, Op.execute, Instruction.execute]
  have hh : rejected.halted = false := by rw [runOps_halted, hactive]
  rw [show 5 = 4 + 1 from rfl, natRun_add, natRun_checker_reject_runOps rom state hpc hactive,
    natRun_checker_halt rom rejected hp hh]
  constructor
  · rfl
  · simp [rejected, runOps, rejectCode, jumpTo, natExecuteOp, Op.execute, Instruction.execute]

theorem checker_pair_decision (rom : PhysicalROM) {N q i j : Nat} {state : NatState}
    (ready : Ready N q i j 460 state) :
    ∃ steps : Nat, steps ≤ 17 ∧
      ((steps ≤ 12 ∧ Ready N q i j 540 (natRun rom checker steps state) ∧
        (state.heap 5 = 0 ∨ state.heap 6 = 0 ∨ state.heap 7 = 0)) ∨
      ((natRun rom checker steps state).halted = true ∧
        (natRun rom checker steps state).register .value = 0 ∧
        state.heap 5 ≠ 0 ∧ state.heap 6 ≠ 0 ∧ state.heap 7 ≠ 0)) := by
  have first := checker_counterTest_ready rom ⟨0, by decide⟩ ready
  by_cases h5 : state.heap 5 = 0
  · exact ⟨4, by decide, Or.inl ⟨by decide, by simpa only [h5, ite_true] using first.2, Or.inl h5⟩⟩
  · let one := natRun rom checker 4 state
    have rone : Ready N q i j 480 one := by simpa only [h5, ite_false] using first.2
    have second := checker_counterTest_ready rom ⟨1, by decide⟩ rone
    have one6 : one.heap 6 = state.heap 6 := congrFun first.1 6
    by_cases h6 : state.heap 6 = 0
    · refine ⟨8, by decide, Or.inl ⟨by decide, ?_, Or.inr (Or.inl h6)⟩⟩
      rw [show 8 = 4 + 4 from rfl, natRun_add]
      simpa only [one6, h6, ite_true] using second.2
    · let two := natRun rom checker 4 one
      have rtwo : Ready N q i j 500 two := by simpa only [one6, h6, ite_false] using second.2
      have third := checker_counterTest_ready rom ⟨2, by decide⟩ rtwo
      have two7 : two.heap 7 = state.heap 7 := (congrFun second.1 7).trans (congrFun first.1 7)
      have hrun12 : natRun rom checker 12 state = natRun rom checker 4 two := by
        rw [show 12 = (4 + 4) + 4 from rfl, natRun_add, natRun_add]
      by_cases h7 : state.heap 7 = 0
      · refine ⟨12, by decide, Or.inl ⟨by decide, ?_, Or.inr (Or.inr h7)⟩⟩
        rw [hrun12]
        simpa only [two7, h7, ite_true] using third.2
      · let three := natRun rom checker 4 two
        have rthree : Ready N q i j 520 three := by simpa only [two7, h7, ite_false] using third.2
        have hreject := checker_reject rom three rthree.pc rthree.active
        refine ⟨17, by decide, Or.inr ?_⟩
        rw [show 17 = 12 + 5 from rfl, natRun_add, hrun12]
        exact ⟨hreject.1, hreject.2, h5, h6, h7⟩

theorem checker_pair_scan {q : Nat} (full : List (Finset (Fin q))) (i j : Nat)
    (hi : i < full.length) (hj : j < full.length) (state : NatState)
    (ready : Ready full.length q i j 100 state) :
    let result := natRun (rawIncidenceROM q full) checker (53 * q + 26) state
    Ready full.length q i j 460 result ∧
      (result.heap 5 = 0 ∨ result.heap 6 = 0 ∨ result.heap 7 = 0 ↔ PairOK full i j) := by
  let rom := rawIncidenceROM q full
  have hsetup := checker_pair_setup rom ready hj
  let scanning := natRun rom checker 19 state
  have hs := natRun_checker_pairScan_raw q full ⟨i, hi⟩ ⟨j, hj⟩ scanning
    hsetup.1.pc hsetup.1.active hsetup.1.tools hsetup.1.left hsetup.1.right
    hsetup.2.1 hsetup.2.2.1 hsetup.2.2.2.1 hsetup.2.2.2.2
  dsimp only at hs
  rcases hs with ⟨_hk, h5, h6, h7, hframe, hv, hp, hh⟩
  have hrun : natRun rom checker (53 * q + 26) state = natRun rom checker (53 * q + 7) scanning := by
    rw [show 53 * q + 26 = 19 + (53 * q + 7) from by omega, natRun_add]
  dsimp only
  rw [hrun]
  refine ⟨⟨?_, ?_, ?_, ?_, hv.trans hsetup.1.value, hp, hh⟩, ?_⟩
  · exact (hframe 0 (by decide) (by decide) (by decide) (by decide)).trans hsetup.1.dimension
  · exact (hframe 1 (by decide) (by decide) (by decide) (by decide)).trans hsetup.1.tools
  · exact (hframe 2 (by decide) (by decide) (by decide) (by decide)).trans hsetup.1.left
  · exact (hframe 3 (by decide) (by decide) (by decide) (by decide)).trans hsetup.1.right
  · rw [h5, h6, h7]
    simpa only [PairOK, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using
      (pair_laminar_iff_counter_zero full[i] full[j]).symm

def RowResult {q : Nat} (full : List (Finset (Fin q))) (i first : Nat)
    (state : NatState) (steps : Nat) : Prop :=
  let result := natRun (rawIncidenceROM q full) checker steps state
  (result.halted = true ∧ result.register .value = 0 ∧ ¬ RowOKFrom full i first) ∨
    (Ready full.length q i full.length 585 result ∧ RowOKFrom full i first)

theorem checker_row {q : Nat} (full : List (Finset (Fin q))) (i : Nat)
    (hi : i < full.length) (j : Nat) (hj : j ≤ full.length) (state : NatState)
    (ready : Ready full.length q i j 100 state) :
    ∃ steps : Nat, steps ≤ (full.length - j) * (53 * q + 47) + 7 ∧ RowResult full i j state steps := by
  have solve : ∀ remaining : Nat, ∀ j : Nat, full.length - j = remaining → j ≤ full.length →
      ∀ state : NatState, Ready full.length q i j 100 state →
        ∃ steps : Nat, steps ≤ remaining * (53 * q + 47) + 7 ∧ RowResult full i j state steps := by
    intro remaining
    induction remaining using Nat.strong_induction_on with
    | h remaining ih =>
      intro j hsize hj state ready
      let rom := rawIncidenceROM q full
      by_cases hlast : j = full.length
      · subst j
        have hz : remaining = 0 := by omega
        refine ⟨7, by rw [hz]; simp, Or.inr ⟨checker_pair_terminal rom ready, ?_⟩⟩
        intro other ho hn
        omega
      · have hjlive : j < full.length := by omega
        let base := 53 * q + 26
        let scanned := natRun rom checker base state
        have hscan := checker_pair_scan full i j hi hjlive state ready
        obtain ⟨decision, hdecisionBound, hdecision⟩ := checker_pair_decision rom hscan.1
        rcases hdecision with hpass | hfail
        · rcases hpass with ⟨hpassBound, rpass, hzero⟩
          have hcurrent : PairOK full i j := hscan.2.mp hzero
          let next := natRun rom checker 9 (natRun rom checker decision scanned)
          have rnext : Ready full.length q i (j + 1) 100 next := by
            dsimp only [next]
            rw [natRun_checker_nextPair rom _ rpass.pc rpass.active]
            exact ready_nextPair rom rpass
          have hsmall : full.length - (j + 1) < remaining := by omega
          obtain ⟨rest, hrest, hresult⟩ := ih _ hsmall (j + 1) rfl (by omega) next rnext
          have hnextRun : natRun rom checker (base + decision + 9) state = next := by
            rw [natRun_add, natRun_add]
          have hremaining : remaining = (full.length - (j + 1)) + 1 := by omega
          have hprefix : base + decision + 9 ≤ 53 * q + 47 := by dsimp only [base]; omega
          refine ⟨base + decision + 9 + rest, ?_, ?_⟩
          · rw [hremaining, Nat.add_mul, Nat.one_mul]
            omega
          · unfold RowResult at hresult ⊢
            rw [natRun_add, hnextRun]
            rcases hresult with ⟨hh, hv, hnot⟩ | ⟨rfinish, hrow⟩
            · exact Or.inl ⟨hh, hv, fun hcur => hnot ((rowOKFrom_step full i j hjlive).mp hcur).2⟩
            · exact Or.inr ⟨rfinish, (rowOKFrom_step full i j hjlive).mpr ⟨hcurrent, hrow⟩⟩
        · rcases hfail with ⟨hhalt, hvalue, h5, h6, h7⟩
          have hnot : ¬ PairOK full i j := by
            intro hOK
            rcases hscan.2.mpr hOK with hz | hz | hz
            · exact h5 hz
            · exact h6 hz
            · exact h7 hz
          have hwork : 53 * q + 47 ≤ remaining * (53 * q + 47) := by
            simpa only [Nat.one_mul] using Nat.mul_le_mul_right (53 * q + 47) (by omega : 1 ≤ remaining)
          refine ⟨base + decision, ?_, ?_⟩
          · dsimp only [base]
            omega
          · unfold RowResult
            rw [natRun_add]
            exact Or.inl ⟨hhalt, hvalue, fun hrow => hnot (hrow j le_rfl hjlive)⟩
  exact solve (full.length - j) j rfl hj state ready

def CheckerResult {q : Nat} (full : List (Finset (Fin q))) (first : Nat)
    (state : NatState) (steps : Nat) : Prop :=
  let result := natRun (rawIncidenceROM q full) checker steps state
  result.halted = true ∧ result.register .value ≤ 1 ∧
    (result.register .value = 1 ↔ RowsOKFrom full first)

theorem checker_rows {q : Nat} (full : List (Finset (Fin q))) (i : Nat)
    (hi : i ≤ full.length) (j : Nat) (state : NatState)
    (ready : Ready full.length q i j 50 state) :
    ∃ steps : Nat, steps ≤ (full.length - i) * (full.length * (53 * q + 47) + 26) + 8 ∧
      CheckerResult full i state steps := by
  have solve : ∀ remaining : Nat, ∀ i : Nat, full.length - i = remaining → i ≤ full.length →
      ∀ j : Nat, ∀ state : NatState, Ready full.length q i j 50 state →
        ∃ steps : Nat, steps ≤ remaining * (full.length * (53 * q + 47) + 26) + 8 ∧
          CheckerResult full i state steps := by
    intro remaining
    induction remaining using Nat.strong_induction_on with
    | h remaining ih =>
      intro i hsize hi j state ready
      let rom := rawIncidenceROM q full
      by_cases hlast : i = full.length
      · subst i
        have hz : remaining = 0 := by omega
        have hterminal := checker_outer_terminal rom ready
        refine ⟨8, by rw [hz]; simp, hterminal.1, ?_, ?_⟩
        · rw [hterminal.2]
        · rw [hterminal.2]
          constructor
          · intro _ other ho hn
            omega
          · intro _
            rfl
      · have hilive : i < full.length := by omega
        let pairs := natRun rom checker 10 state
        have rpairs : Ready full.length q i 0 100 pairs := checker_outer_setup rom ready hilive
        obtain ⟨rowSteps, hrowBound, hrowResult⟩ := checker_row full i hilive 0 (Nat.zero_le _) pairs rpairs
        rcases hrowResult with ⟨hhalt, hvalue, hnotRow⟩ | ⟨rrow, hrow⟩
        · have hwork : full.length * (53 * q + 47) + 26 ≤ remaining * (full.length * (53 * q + 47) + 26) := by
            simpa only [Nat.one_mul] using Nat.mul_le_mul_right (full.length * (53 * q + 47) + 26)
              (by omega : 1 ≤ remaining)
          refine ⟨10 + rowSteps, ?_, ?_⟩
          · simp only [Nat.sub_zero] at hrowBound
            omega
          · unfold CheckerResult
            rw [natRun_add]
            refine ⟨hhalt, ?_, ?_⟩
            · rw [hvalue]
              decide
            · rw [hvalue]
              have hnot : ¬ RowsOKFrom full i := fun hrows => hnotRow (hrows i le_rfl hilive)
              simpa only [Nat.zero_ne_one, false_iff] using hnot
        · let next := natRun rom checker 9 (natRun rom checker rowSteps pairs)
          have rnext : Ready full.length q (i + 1) full.length 50 next := by
            dsimp only [next]
            rw [natRun_checker_nextRow rom _ rrow.pc rrow.active]
            exact ready_nextRow rom rrow
          have hsmall : full.length - (i + 1) < remaining := by omega
          obtain ⟨rest, hrest, hresult⟩ := ih _ hsmall (i + 1) rfl (by omega) full.length next rnext
          have hnextRun : natRun rom checker (10 + rowSteps + 9) state = next := by
            rw [natRun_add, natRun_add]
          have hremaining : remaining = (full.length - (i + 1)) + 1 := by omega
          have hrowBound' : rowSteps ≤ full.length * (53 * q + 47) + 7 := by
            simpa only [Nat.sub_zero] using hrowBound
          have hprefix : 10 + rowSteps + 9 ≤ full.length * (53 * q + 47) + 26 := by
            omega
          refine ⟨10 + rowSteps + 9 + rest, ?_, ?_⟩
          · rw [hremaining, Nat.add_mul, Nat.one_mul]
            omega
          · unfold CheckerResult at hresult ⊢
            rw [natRun_add, hnextRun]
            rcases hresult with ⟨hh, hv, hiff⟩
            refine ⟨hh, hv, ?_⟩
            constructor
            · intro hone
              exact (rowsOKFrom_step full i hilive).mpr ⟨hrow, hiff.mp hone⟩
            · intro hrows
              exact hiff.mpr ((rowsOKFrom_step full i hilive).mp hrows).2
  exact solve (full.length - i) i rfl hi j state ready

def natInitial : NatState := ⟨fun _ => 0, fun _ => 0, 0, false⟩
def checkerInitCode : List PackingOp := checker.take 10

theorem natRun_checker_init (q : Nat) (full : List (Finset (Fin q))) :
    Ready full.length q 0 0 50 (natRun (rawIncidenceROM q full) checker 10 natInitial) := by
  have hcode : ∀ position (hposition : position < checkerInitCode.length),
      checker[0 + position]'(by rw [checker_length]; change position < 10 at hposition; omega) = checkerInitCode[position] := by
    intro position hposition
    change position < 10 at hposition
    interval_cases position <;> rfl
  have hstraight : ∀ op ∈ checkerInitCode, NoJump op := by
    simp [checkerInitCode, checker, setCell, storeCell, NoJump]
  have hrun : natRun (rawIncidenceROM q full) checker 10 natInitial =
      runOps (rawIncidenceROM q full) checkerInitCode natInitial := by
    simpa only [show checkerInitCode.length = 10 from rfl] using
      natRun_of_straight_segment (rawIncidenceROM q full) checker checkerInitCode 0 (by decide)
        hcode hstraight natInitial rfl rfl
  rw [hrun]
  constructor <;> simp [runOps, checkerInitCode, checker, setCell, storeCell, natInitial,
    natExecuteOp, Op.execute, Instruction.execute, rawIncidenceROM, PhysicalROM.semantic, PhysicalROM.words]

/-- Whole fixed-code Nat-view execution from the genuine all-zero initial
state, with encoded HALT counted. No algorithm result is supplied to ROM. -/
theorem nat_checker_correct (q : Nat) (full : List (Finset (Fin q))) :
    ∃ steps : Nat, steps ≤ full.length * full.length * (53 * q + 47) + 26 * full.length + 18 ∧
      (natRun (rawIncidenceROM q full) checker steps natInitial).halted = true ∧
      (natRun (rawIncidenceROM q full) checker steps natInitial).register .value ≤ 1 ∧
      ((natRun (rawIncidenceROM q full) checker steps natInitial).register .value = 1 ↔ LaminarSchedule full) := by
  obtain ⟨rest, hrest, hresult⟩ := checker_rows full 0 (Nat.zero_le _) 0
    (natRun (rawIncidenceROM q full) checker 10 natInitial) (natRun_checker_init q full)
  refine ⟨10 + rest, ?_, ?_⟩
  · simp only [Nat.sub_zero] at hrest
    calc
      10 + rest ≤ 10 + (full.length * (full.length * (53 * q + 47) + 26) + 8) := Nat.add_le_add_left hrest 10
      _ = _ := by ring
  · unfold CheckerResult at hresult
    rw [natRun_add]
    exact ⟨hresult.1, hresult.2.1, hresult.2.2.trans (rowsOKFrom_zero_iff full)⟩

end PaperProofs.Structure.LaminarTree.RawIncidenceLaminarRAM
