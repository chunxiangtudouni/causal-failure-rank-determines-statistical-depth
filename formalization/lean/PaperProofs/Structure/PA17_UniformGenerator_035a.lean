module

public import PaperProofs.Structure.PA17_Generator_001

/-! A real finite countdown controller for the six-program emitter.
The body is an embedded fetched segment and may clobber every register.
Only its dedicated heap counter is preserved by that segment. These are
control components; no complete UniformCodeGenerationClaims is asserted. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035a

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety

def loopHead (counter exit : Nat) : List PackingOp :=
  [.base (.base (.constant .index counter)), .base (.base (.loadHeap .value .index)),
   .base (.base (.constant .fresh exit)), .jumpIfZero .value .fresh]

def loopTail (counter entry : Nat) : List PackingOp :=
  [.base (.base (.constant .index counter)), .base (.base (.loadHeap .value .index)),
   .base (.base (.constant .old 1)), .base (.subtract .value .value .old),
   .base (.base (.storeHeap .index .value)), .base (.base (.constant .flag 0)),
   .base (.base (.constant .fresh entry)), .jumpIfZero .flag .fresh]

def loopBlock (counter start : Nat) (body : List PackingOp) : List PackingOp :=
  loopHead counter (5 * (start + body.length + 12)) ++ body ++ loopTail counter (5 * start)

theorem loopBlock_length (counter start : Nat) (body : List PackingOp) :
    (loopBlock counter start body).length = body.length + 12 := by
  simp [loopBlock, loopHead, loopTail]

theorem segment_index (left block right : List PackingOp) (position : Nat) (hp : position < block.length) :
    (left ++ block ++ right)[left.length + position]'(by simp only [List.length_append]; omega) = block[position] := by
  rw [List.getElem_append_left (by simp only [List.length_append]; omega),
    List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem head_heap (rom : PhysicalROM) (counter exit : Nat) (state : NatState) :
    (runOps rom (loopHead counter exit) state).heap = state.heap := rfl

theorem head_pc (rom : PhysicalROM) (counter exit : Nat) (state : NatState) :
    (runOps rom (loopHead counter exit) state).pc =
      if state.heap counter = 0 then exit else state.pc + 20 := by
  simp [loopHead, runOps, natExecuteOp, Op.execute, Instruction.execute, Nat.add_assoc]

theorem tail_heap (rom : PhysicalROM) (counter entry : Nat) (state : NatState) :
    (runOps rom (loopTail counter entry) state).heap =
      Function.update state.heap counter (state.heap counter - 1) := by
  simp [loopTail, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem tail_pc (rom : PhysicalROM) (counter entry : Nat) (state : NatState) :
    (runOps rom (loopTail counter entry) state).pc = entry := by
  simp [loopTail, runOps, natExecuteOp, Op.execute, Instruction.execute]

theorem head_run (rom : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    natRun rom (left ++ loopBlock counter left.length body ++ right) 4 state =
      runOps rom (loopHead counter (5 * (left.length + body.length + 12))) state := by
  let lead := (loopHead counter (5 * (left.length + body.length + 12))).take 3
  have hlen : lead.length = 3 := rfl
  have hlb := loopBlock_length counter left.length body
  have hrun := natRun_of_segment_last rom (left ++ loopBlock counter left.length body ++ right)
    lead (.jumpIfZero .value .fresh) left.length
    (by simp only [List.length_append, hlen, hlb]; omega) ?_ ?_ ?_ state hpc ha
  · exact hrun
  · intro position hp
    rw [hlen] at hp
    have hh := segment_index left (loopHead counter (5 * (left.length + body.length + 12)))
      (body ++ loopTail counter (5 * left.length) ++ right) position (by change position < 4; omega)
    simpa only [loopBlock, List.append_assoc, lead, List.getElem_take] using hh
  · have hh := segment_index left (loopHead counter (5 * (left.length + body.length + 12)))
      (body ++ loopTail counter (5 * left.length) ++ right) 3 (by change 3 < 4; decide)
    simpa only [loopBlock, List.append_assoc, hlen, loopHead, List.getElem_cons_zero, List.getElem_cons_succ] using hh
  · simp [lead, loopHead, NoJump]

theorem tail_run (rom : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (state : NatState) (hpc : state.pc = 5 * (left.length + 4 + body.length)) (ha : state.halted = false) :
    natRun rom (left ++ loopBlock counter left.length body ++ right) 8 state =
      runOps rom (loopTail counter (5 * left.length)) state := by
  let lead := (loopTail counter (5 * left.length)).take 7
  have hlen : lead.length = 7 := rfl
  have hlb := loopBlock_length counter left.length body
  have hhead : (loopHead counter (5 * (left.length + body.length + 12))).length = 4 := rfl
  have hpref : (left ++ loopHead counter (5 * (left.length + body.length + 12)) ++ body).length = left.length + 4 + body.length := by
    simp only [List.length_append, hhead]
  have hrun := natRun_of_segment_last rom (left ++ loopBlock counter left.length body ++ right)
    lead (.jumpIfZero .flag .fresh) (left.length + 4 + body.length)
    (by simp only [List.length_append, hlen, hlb]; omega) ?_ ?_ ?_ state hpc ha
  · exact hrun
  · intro position hp
    rw [hlen] at hp
    have hh := segment_index (left ++ loopHead counter (5 * (left.length + body.length + 12)) ++ body)
      (loopTail counter (5 * left.length)) right position (by change position < 8; omega)
    simp only [hpref] at hh
    simpa only [loopBlock, List.append_assoc, lead, List.getElem_take] using hh
  · have hh := segment_index (left ++ loopHead counter (5 * (left.length + body.length + 12)) ++ body)
      (loopTail counter (5 * left.length)) right 7 (by change 7 < 8; decide)
    simp only [hpref] at hh
    simpa only [loopBlock, List.append_assoc, hlen, loopTail, List.getElem_cons_zero, List.getElem_cons_succ] using hh
  · simp [lead, loopTail, NoJump]

/-- This is an ordinary embedded-segment control contract, with the result
defined by its actual fetched execution. It introduces no output oracle. -/
def BodyExits (rom : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (bodySteps : NatState → Nat) : Prop :=
  ∀ state : NatState, state.pc = 5 * (left.length + 4) → state.halted = false →
    let done := natRun rom (left ++ loopBlock counter left.length body ++ right) (bodySteps state) state
    done.pc = 5 * (left.length + 4 + body.length) ∧ done.halted = false ∧ done.heap counter = state.heap counter

theorem straight_body_run (rom : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (hs : ∀ op ∈ body, NoJump op) (state : NatState)
    (hpc : state.pc = 5 * (left.length + 4)) (ha : state.halted = false) :
    natRun rom (left ++ loopBlock counter left.length body ++ right) body.length state = runOps rom body state := by
  have hh : (loopHead counter (5 * (left.length + body.length + 12))).length = 4 := rfl
  apply natRun_of_straight_segment rom _ body (left.length + 4)
    (by simp only [List.length_append, loopBlock_length]; omega) ?_ hs state hpc ha
  intro position hp
  have hc := segment_index (left ++ loopHead counter (5 * (left.length + body.length + 12))) body
    (loopTail counter (5 * left.length) ++ right) position hp
  simp only [List.length_append, hh] at hc
  simpa only [loopBlock, List.append_assoc] using hc

theorem straight_body_exits (rom : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (hs : ∀ op ∈ body, NoJump op)
    (hf : ∀ state : NatState, (runOps rom body state).heap counter = state.heap counter) :
    BodyExits rom left body right counter (fun _ => body.length) := by
  intro state hpc ha
  rw [straight_body_run rom left body right counter hs state hpc ha]
  refine ⟨?_, (runOps_halted rom body state).trans ha, hf state⟩
  rw [runOps_pc rom body state hs, hpc]
  omega

def cycleResult (rom : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (bodySteps : NatState → Nat) (state : NatState) : NatState :=
  let tested := runOps rom (loopHead counter (5 * (left.length + body.length + 12))) state
  runOps rom (loopTail counter (5 * left.length))
    (natRun rom (left ++ loopBlock counter left.length body ++ right) (bodySteps tested) tested)

def cycleSteps (rom : PhysicalROM) (left body : List PackingOp) (counter : Nat)
    (bodySteps : NatState → Nat) (state : NatState) : Nat :=
  4 + bodySteps (runOps rom (loopHead counter (5 * (left.length + body.length + 12))) state) + 8

theorem cycle_run (rom : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (bodySteps : NatState → Nat) (hb : BodyExits rom left body right counter bodySteps)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hc : state.heap counter ≠ 0) :
    natRun rom (left ++ loopBlock counter left.length body ++ right)
      (cycleSteps rom left body counter bodySteps state) state = cycleResult rom left body right counter bodySteps state := by
  let tested := runOps rom (loopHead counter (5 * (left.length + body.length + 12))) state
  have htpc : tested.pc = 5 * (left.length + 4) := by
    rw [head_pc, ite_eq_right hc, hpc]
    omega
  have htactive : tested.halted = false := (runOps_halted rom _ state).trans ha
  have hdone := hb tested htpc htactive
  dsimp only [cycleSteps]
  rw [natRun_add, natRun_add, head_run rom left body right counter state hpc ha,
    tail_run rom left body right counter _ hdone.1 hdone.2.1]
  rfl

theorem cycle_control (rom : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (bodySteps : NatState → Nat) (hb : BodyExits rom left body right counter bodySteps)
    (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hc : state.heap counter ≠ 0) :
    let done := cycleResult rom left body right counter bodySteps state
    done.pc = 5 * left.length ∧ done.halted = false ∧ done.heap counter = state.heap counter - 1 := by
  let tested := runOps rom (loopHead counter (5 * (left.length + body.length + 12))) state
  have htpc : tested.pc = 5 * (left.length + 4) := by
    rw [head_pc, ite_eq_right hc, hpc]
    omega
  have hd := hb tested htpc ((runOps_halted rom _ state).trans ha)
  dsimp only [cycleResult]
  refine ⟨tail_pc _ _ _ _, ?_, ?_⟩
  · exact (runOps_halted rom _ _).trans hd.2.1
  · rw [tail_heap, Function.update_self, hd.2.2, head_heap]

def loopResult (rom : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (bodySteps : NatState → Nat) : Nat → NatState → NatState
  | 0, state => runOps rom (loopHead counter (5 * (left.length + body.length + 12))) state
  | count + 1, state => loopResult rom left body right counter bodySteps count
      (cycleResult rom left body right counter bodySteps state)

def loopSteps (rom : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (bodySteps : NatState → Nat) : Nat → NatState → Nat
  | 0, _ => 4
  | count + 1, state => cycleSteps rom left body counter bodySteps state +
      loopSteps rom left body right counter bodySteps count (cycleResult rom left body right counter bodySteps state)

theorem loop_run (rom : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (bodySteps : NatState → Nat) (hb : BodyExits rom left body right counter bodySteps)
    (count : Nat) (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hc : state.heap counter = count) :
    natRun rom (left ++ loopBlock counter left.length body ++ right)
      (loopSteps rom left body right counter bodySteps count state) state =
      loopResult rom left body right counter bodySteps count state := by
  induction count generalizing state with
  | zero => exact head_run rom left body right counter state hpc ha
  | succ count ih =>
    have hn : state.heap counter ≠ 0 := by omega
    have hcontrol := cycle_control rom left body right counter bodySteps hb state hpc ha hn
    rw [loopSteps, natRun_add, cycle_run rom left body right counter bodySteps hb state hpc ha hn]
    exact ih _ hcontrol.1 hcontrol.2.1 (by rw [hcontrol.2.2, hc]; omega)

theorem loop_control (rom : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (bodySteps : NatState → Nat) (hb : BodyExits rom left body right counter bodySteps)
    (count : Nat) (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hc : state.heap counter = count) :
    let done := loopResult rom left body right counter bodySteps count state
    done.pc = 5 * (left.length + body.length + 12) ∧ done.halted = false ∧ done.heap counter = 0 := by
  induction count generalizing state with
  | zero =>
    dsimp only [loopResult]
    exact ⟨by rw [head_pc, hc, ite_eq_left rfl], (runOps_halted rom _ state).trans ha, by rw [head_heap, hc]⟩
  | succ count ih =>
    have hn : state.heap counter ≠ 0 := by omega
    have hcontrol := cycle_control rom left body right counter bodySteps hb state hpc ha hn
    exact ih _ hcontrol.1 hcontrol.2.1 (by rw [hcontrol.2.2, hc]; omega)

theorem loopSteps_le (rom : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (bodySteps : NatState → Nat) (bodyBound : Nat) (hb : ∀ state, bodySteps state ≤ bodyBound)
    (count : Nat) (state : NatState) :
    loopSteps rom left body right counter bodySteps count state ≤ count * (bodyBound + 12) + 4 := by
  induction count generalizing state with
  | zero => simp only [loopSteps, Nat.zero_mul, Nat.zero_add, le_refl]
  | succ count ih =>
    rw [loopSteps]
    have hh := hb (runOps rom (loopHead counter (5 * (left.length + body.length + 12))) state)
    have hi := ih (cycleResult rom left body right counter bodySteps state)
    dsimp only [cycleSteps]
    nlinarith

theorem loopResult_frame (rom : PhysicalROM) (left body right : List PackingOp) (counter address : Nat)
    (hne : address ≠ counter) (bodySteps : NatState → Nat)
    (hf : ∀ state : NatState,
      (natRun rom (left ++ loopBlock counter left.length body ++ right) (bodySteps state) state).heap address = state.heap address)
    (count : Nat) (state : NatState) :
    (loopResult rom left body right counter bodySteps count state).heap address = state.heap address := by
  induction count generalizing state with
  | zero => exact congrFun (head_heap rom _ _ state) address
  | succ count ih =>
    rw [loopResult, ih]
    dsimp only [cycleResult]
    rw [tail_heap, Function.update_of_ne hne, hf, head_heap]

theorem events_length_le (op : PackingOp) : op.events.length ≤ 12 := by
  cases op with
  | base op => cases op with
    | base instruction => cases instruction <;> simp [PackingOp.events, Op.trace, Instruction.trace, Instruction.operations]
    | subtract target left right => simp [PackingOp.events, Op.trace]
  | arithmetic operation target left right => simp [PackingOp.events]
  | jumpIfZero condition target => simp [PackingOp.events]

theorem dynamicTrace_length_le (rom : PhysicalROM) (program : List PackingOp) (bits count : Nat)
    (state : WordState bits) : (packingDynamicTrace rom program count state).length ≤ 12 * count := by
  induction count generalizing state with
  | zero => exact Nat.zero_le _
  | succ count ih =>
    rw [packingDynamicTrace]
    split_ifs
    · simp
    · dsimp only
      split
      · rw [List.length_map, haltTrace_length]
        omega
      · rw [List.length_append]
        rename_i op _
        have hi := ih (packingExecuteOp rom op state)
        have he := events_length_le op
        omega

/-- Physical fetched execution follows the proved controller result once
the compiler's separate prefix numeric certificate is supplied. -/
theorem loop_word_run (rom : PhysicalROM) (left body right : List PackingOp) (counter : Nat)
    (bodySteps : NatState → Nat) (hb : BodyExits rom left body right counter bodySteps)
    (count bits : Nat) (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hc : state.heap counter = count)
    (hcode : WordsFit bits (packingCode (left ++ loopBlock counter left.length body ++ right)))
    (hsafe : ∀ k < loopSteps rom left body right counter bodySteps count state,
      RegistersFit bits (natRun rom (left ++ loopBlock counter left.length body ++ right) k state) ∧
        Fits bits (natRun rom (left ++ loopBlock counter left.length body ++ right) k state).pc) :
    packingRun rom (left ++ loopBlock counter left.length body ++ right)
      (loopSteps rom left body right counter bodySteps count state) (state.toWord bits) =
      (loopResult rom left body right counter bodySteps count state).toWord bits := by
  rw [natRun_toWord _ _ _ _ hcode hsafe, loop_run rom left body right counter bodySteps hb count state hpc ha hc]

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035a
