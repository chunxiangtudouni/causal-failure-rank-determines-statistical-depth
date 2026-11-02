module

public import PaperProofs.Structure.PA17_UniformGenerator_035h
public import PaperProofs.Structure.PA17_UniformGenerator_035d

/-! Actual dimension-only logarithm prelude for the packed templates:
cell1 is capacity width, cell2 is the original 32-factor index width. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035i

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035c
  PA17UniformGenerator035d PA17UniformGenerator035h

def storeLog (target scale : Nat) : List PackingOp :=
  [.base (.base (.constant .old scale)), .arithmetic .multiply .value .old .index,
   .base (.base (.constant .address target)), .base (.base (.storeHeap .address .value))]

def computeLog (expression : Expr) (stack target scale start : Nat) : List PackingOp :=
  expression.compile stack ++ logBlock (start + (expression.compile stack).length) ++ storeLog target scale

def computeClock (expression : Expr) (rom : PhysicalROM) (heap : Nat → Nat) (stack : Nat) : Nat :=
  (expression.compile stack).length + (6 * Nat.clog 2 (expression.eval rom heap + 1) + 6) + 4

theorem computeLog_length (expression : Expr) (stack target scale start : Nat) :
    (computeLog expression stack target scale start).length = (expression.compile stack).length + 14 := by
  simp only [computeLog, List.length_append, logBlock_length, storeLog, List.length_cons, List.length_nil]

theorem storeLog_noJump (target scale : Nat) : ∀ op ∈ storeLog target scale, NoJump op := by simp [storeLog, NoJump]

theorem storeLog_heap (rom : PhysicalROM) (target scale : Nat) (state : NatState) :
    (runOps rom (storeLog target scale) state).heap = Function.update state.heap target (scale * state.register .index) := rfl

theorem computeLog_run (expression : Expr) (rom : PhysicalROM) (stack target scale : Nat)
    (he : expression.Below stack) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    let fresh := natRun rom (left ++ computeLog expression stack target scale left.length ++ right)
      (computeClock expression rom state.heap stack) state
    fresh.pc = 5 * (left.length + (expression.compile stack).length + 14) ∧ fresh.halted = false ∧
      fresh.heap = Function.update (runOps rom (expression.compile stack) state).heap target
        (scale * Nat.clog 2 (expression.eval rom state.heap + 1)) := by
  let pre := expression.compile stack
  let lead := left ++ pre
  let store := storeLog target scale
  let allCode := lead ++ logBlock lead.length ++ store ++ right
  let a := runOps rom pre state
  have hvalue : a.register .value = expression.eval rom state.heap := (expression.compile_correct rom stack he state).1
  have hapc : a.pc = 5 * lead.length := by
    rw [runOps_pc rom pre state (expression.compile_noJump stack), hpc]
    simp only [lead, List.length_append]
    omega
  have hactive : a.halted = false := (runOps_halted rom pre state).trans ha
  let b := natRun rom allCode (6 * Nat.clog 2 (expression.eval rom state.heap + 1) + 6) a
  have hb := log_run rom lead (store ++ right) a hapc hactive
  rw [hvalue] at hb
  have hb' : LogInv (Nat.clog 2 (expression.eval rom state.heap + 1)) 0 b ∧
      b.pc = 5 * (lead.length + 10) ∧ b.halted = false ∧ b.heap = a.heap := by
    simpa only [b, allCode, List.append_assoc] using hb
  have hpre : natRun rom allCode pre.length state = a := by
    have hh := expression.segment_run rom stack left (logBlock lead.length ++ store ++ right) state hpc ha
    simpa only [a, allCode, lead, pre, List.append_assoc] using hh
  have hstore : natRun rom allCode 4 b = runOps rom store b := by
    have hh := natRun_of_straight_segment rom ((lead ++ logBlock lead.length) ++ store ++ right)
      store (lead ++ logBlock lead.length).length (by simp only [List.length_append]; omega)
      (segment_index (lead ++ logBlock lead.length) store right) (storeLog_noJump target scale) b
      (by simpa only [List.length_append, logBlock_length] using hb'.2.1) hb'.2.2.1
    simpa only [allCode, store, storeLog, List.length_cons, List.length_nil] using hh
  have hcode : left ++ computeLog expression stack target scale left.length ++ right = allCode := by
    simp only [computeLog, allCode, lead, pre, store, List.length_append, List.append_assoc]
  have hrun : natRun rom allCode (computeClock expression rom state.heap stack) state = runOps rom store b := by
    rw [computeClock, natRun_add, natRun_add, hpre, hstore]
  rw [hcode, hrun]
  refine ⟨?_, (runOps_halted rom store b).trans hb'.2.2.1, ?_⟩
  · rw [runOps_pc rom store b (storeLog_noJump target scale), hb'.2.1]
    have hlen : store.length = 4 := rfl
    rw [hlen]
    simp only [lead, List.length_append, pre]
    omega
  · rw [storeLog_heap, hb'.2.2.2, hb'.1.1]

theorem computeLog_target (expression : Expr) (rom : PhysicalROM) (stack target scale : Nat)
    (he : expression.Below stack) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    (natRun rom (left ++ computeLog expression stack target scale left.length ++ right)
      (computeClock expression rom state.heap stack) state).heap target = scale * Nat.clog 2 (expression.eval rom state.heap + 1) := by
  rw [(computeLog_run expression rom stack target scale he left right state hpc ha).2.2, Function.update_self]

theorem computeLog_frame (expression : Expr) (rom : PhysicalROM) (stack target scale address : Nat)
    (he : expression.Below stack) (ht : address ≠ target)
    (hf : address < stack ∨ stack + expression.size ≤ address)
    (left right : List PackingOp) (state : NatState) (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    (natRun rom (left ++ computeLog expression stack target scale left.length ++ right)
      (computeClock expression rom state.heap stack) state).heap address = state.heap address := by
  rw [(computeLog_run expression rom stack target scale he left right state hpc ha).2.2,
    Function.update_of_ne ht]
  exact expression_frame expression rom stack address hf state

def widthExpr : Expr := .input 1
def bitsExpr : Expr := .binary .add (.binary .add (.input 0) (.input 1)) (.constant 1)

def dimensionPrelude (start : Nat) : List PackingOp :=
  let first := computeLog widthExpr 64 1 1 start
  first ++ computeLog bitsExpr 64 2 32 (start + first.length)

def dimensionClock (N q : Nat) : Nat := 6 * Nat.clog 2 (q + 1) + 6 * Nat.clog 2 (N + q + 2) + 37

theorem dimensionPrelude_length (start : Nat) : (dimensionPrelude start).length = 45 := rfl

theorem widthExpr_eval (N q t : Nat) (heap : Nat → Nat) :
    widthExpr.eval (PA17Generator.dimensionROM N q t) heap = q := rfl

theorem bitsExpr_eval (N q t : Nat) (heap : Nat → Nat) :
    bitsExpr.eval (PA17Generator.dimensionROM N q t) heap = N + q + 1 := rfl

theorem dimensionPrelude_run (N q t : Nat) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    let fresh := natRun (PA17Generator.dimensionROM N q t)
      (left ++ dimensionPrelude left.length ++ right) (dimensionClock N q) state
    fresh.pc = 5 * (left.length + 45) ∧ fresh.halted = false ∧
      fresh.heap 1 = CapacityBits.width q ∧ fresh.heap 2 = indexWidth 32 N q ∧
      (∀ address, (address < 64 ∨ 69 ≤ address) → address ≠ 1 → address ≠ 2 → fresh.heap address = state.heap address) := by
  let rom := PA17Generator.dimensionROM N q t
  let first := computeLog widthExpr 64 1 1 left.length
  let second := computeLog bitsExpr 64 2 32 (left.length + first.length)
  let allCode := left ++ first ++ second ++ right
  let a := natRun rom allCode (computeClock widthExpr rom state.heap 64) state
  let b := natRun rom allCode (computeClock bitsExpr rom a.heap 64) a
  have hw : widthExpr.Below 64 := by trivial
  have hb : bitsExpr.Below 64 := by exact ⟨⟨trivial, trivial⟩, trivial⟩
  have hwLen : (widthExpr.compile 64).length = 2 := rfl
  have hbLen : (bitsExpr.compile 64).length = 15 := rfl
  have hwHeap : (runOps rom (widthExpr.compile 64) state).heap = state.heap := rfl
  have hwEval : ∀ heap, widthExpr.eval rom heap = q := fun _ => rfl
  have hbEval : ∀ heap, bitsExpr.eval rom heap = N + q + 1 := fun _ => rfl
  have hfLen : first.length = 16 := rfl
  have hfirst := computeLog_run widthExpr rom 64 1 1 hw left (second ++ right) state hpc ha
  have hfirst' : a.pc = 5 * (left.length + 16) ∧ a.halted = false ∧
      a.heap = Function.update state.heap 1 (CapacityBits.width q) := by
    simpa only [a, allCode, first, List.append_assoc, hwLen, hwHeap, hwEval, Nat.one_mul, CapacityBits.width] using hfirst
  have hsecond := computeLog_run bitsExpr rom 64 2 32 hb (left ++ first) right a
    (by simpa only [List.length_append, hfLen] using hfirst'.1) hfirst'.2.1
  have hsecond' : b.pc = 5 * (left.length + 45) ∧ b.halted = false ∧
      b.heap = Function.update (runOps rom (bitsExpr.compile 64) a).heap 2 (indexWidth 32 N q) := by
    simpa only [b, allCode, second, List.length_append, hfLen, List.append_assoc, hbLen, hbEval,
      indexWidth, Nat.add_assoc] using hsecond
  have hf1 (address : Nat) (hf : address < 64 ∨ 69 ≤ address) (hne : address ≠ 1) : a.heap address = state.heap address := by
    have hh := computeLog_frame widthExpr rom 64 1 1 address hw hne
      (by change address < 64 ∨ 64 + 1 ≤ address; omega) left (second ++ right) state hpc ha
    simpa only [a, allCode, first, List.append_assoc] using hh
  have hf2 (address : Nat) (hf : address < 64 ∨ 69 ≤ address) (hne : address ≠ 2) : b.heap address = a.heap address := by
    have hh := computeLog_frame bitsExpr rom 64 2 32 address hb hne
      (by change address < 64 ∨ 64 + 5 ≤ address; omega) (left ++ first) right a
      (by simpa only [List.length_append, hfLen] using hfirst'.1) hfirst'.2.1
    simpa only [b, allCode, second, List.length_append, List.append_assoc] using hh
  have hclock : computeClock widthExpr rom state.heap 64 + computeClock bitsExpr rom a.heap 64 = dimensionClock N q := by
    simp only [computeClock, hwEval, hbEval, hwLen, hbLen, dimensionClock]
    rw [show N + q + 1 + 1 = N + q + 2 by omega]
    omega
  have hcode : left ++ dimensionPrelude left.length ++ right = allCode := by
    simp only [dimensionPrelude, first, second, allCode, List.append_assoc]
  rw [hcode, ← hclock, natRun_add]
  refine ⟨hsecond'.1, hsecond'.2.1, ?_, ?_, ?_⟩
  · rw [hf2 1 (Or.inl (by decide)) (by decide), hfirst'.2.2, Function.update_self]
  · rw [hsecond'.2.2, Function.update_self]
  · intro address haddr h1 h2
    exact (hf2 address haddr h2).trans (hf1 address haddr h1)

theorem dimensionClock_le (N q : Nat) : dimensionClock N q ≤ 6 * N + 12 * q + 43 := by
  have hw := clog_succ_le q
  have hb := clog_succ_le (N + q + 1)
  change Nat.clog 2 (N + q + 2) ≤ N + q + 1 at hb
  dsimp only [dimensionClock]
  omega

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035i
