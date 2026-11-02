module

public import PaperProofs.Structure.PA17_UniformGenerator_035w

/-! Whole actual dimension-log computation prefix certificate, derived
from real expression, divide/count and store executions. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035z

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035h PA17UniformGenerator035i
  PA17UniformGenerator035j PA17UniformGenerator035l PA17UniformGenerator035m PA17UniformGenerator035u PA17UniformGenerator035w

theorem computeLog_safe (expression : Expr) (rom : PhysicalROM) (B heapWords stack target scale : Nat)
    (he : expression.Below stack) (hstackB : stack + expression.size ≤ B) (hstackH : stack + expression.size ≤ heapWords)
    (htarget : target ≤ B) (htargetH : target < heapWords) (hscale : scale ≤ B) (htwo : 2 ≤ B)
    (left right : List PackingOp) (state : NatState) (hpc : state.pc = 5 * left.length)
    (ha : state.halted = false) (hr : RegistersLE B state) (hchecked : ExprChecked rom state.heap B heapWords expression)
    (hvalue : scale * Nat.clog 2 (expression.eval rom state.heap + 1) ≤ B)
    (hpcB : 5 * (left ++ computeLog expression stack target scale left.length ++ right).length ≤ B) :
    RunSafe B heapWords rom (left ++ computeLog expression stack target scale left.length ++ right)
      (computeClock expression rom state.heap stack) state := by
  let pre := expression.compile stack
  let lead := left ++ pre
  let store := storeLog target scale
  let allCode := lead ++ logBlock lead.length ++ store ++ right
  let a := runOps rom pre state
  have hcode : left ++ computeLog expression stack target scale left.length ++ right = allCode := by
    simp only [computeLog, allCode, lead, pre, store, List.length_append, List.append_assoc]
  have hAllPc : 5 * allCode.length ≤ B := by rw [← hcode]; exact hpcB
  have hsExpr := expression_numeric expression rom B heapWords stack he hstackB hstackH state hr hchecked
  have hsPre : RunSafe B heapWords rom allCode pre.length state := by
    have hh := straight_segment_safe rom B heapWords left pre (logBlock lead.length ++ store ++ right)
      (expression.compile_noJump stack) state hpc ha hsExpr
    simpa only [allCode, lead, List.append_assoc] using hh
  have hpreRun : natRun rom allCode pre.length state = a := by
    have hh := expression.segment_run rom stack left (logBlock lead.length ++ store ++ right) state hpc ha
    simpa only [a, allCode, lead, pre, List.append_assoc] using hh
  have hValue : a.register .value = expression.eval rom state.heap := (expression.compile_correct rom stack he state).1
  have hapc : a.pc = 5 * lead.length := by
    rw [runOps_pc rom pre state (expression.compile_noJump stack), hpc]
    simp only [lead, List.length_append]
    omega
  have haactive : a.halted = false := (runOps_halted rom pre state).trans ha
  have hareg : RegistersLE B a := (hsExpr.final _ _ _ _ _)
  have hsLog := log_safe rom B heapWords lead (store ++ right)
    (by simpa only [allCode, List.append_assoc] using hAllPc) htwo a hapc haactive hareg
  rw [hValue] at hsLog
  have hsLog' : RunSafe B heapWords rom allCode (6 * Nat.clog 2 (expression.eval rom state.heap + 1) + 6) a := by
    simpa only [allCode, List.append_assoc] using hsLog
  let b := natRun rom allCode (6 * Nat.clog 2 (expression.eval rom state.heap + 1) + 6) a
  have hb := log_run rom lead (store ++ right) a hapc haactive
  rw [hValue] at hb
  have hb' : LogInv (Nat.clog 2 (expression.eval rom state.heap + 1)) 0 b ∧ b.pc = 5 * (lead.length + 10) ∧
      b.halted = false ∧ b.heap = a.heap := by simpa only [b, allCode, List.append_assoc] using hb
  have hsStore := storeLog_numeric rom B heapWords target scale htarget htargetH hscale b (hsLog'.final _ _ _ _ _).1
    (by rw [hb'.1.1]; exact hvalue)
  have hsTail : RunSafe B heapWords rom allCode 4 b := by
    have hlen : store.length = 4 := rfl
    have hh := straight_segment_safe rom B heapWords (lead ++ logBlock lead.length) store right
      (storeLog_noJump target scale) b
      (by simpa only [List.length_append, logBlock_length] using hb'.2.1) hb'.2.2.1 hsStore
    simpa only [allCode, hlen] using hh
  have hfirstRun : natRun rom allCode (pre.length + (6 * Nat.clog 2 (expression.eval rom state.heap + 1) + 6)) state = b := by
    rw [natRun_add, hpreRun]
  have hsFirst := RunSafe.add _ _ _ _ _ _ state hsPre (by rw [hpreRun]; exact hsLog')
  rw [hcode, computeClock]
  exact RunSafe.add _ _ _ _ _ _ state hsFirst (by rw [hfirstRun]; exact hsTail)

theorem dimensionPrelude_safe (N q t B heapWords : Nat) (left right : List PackingOp) (state : NatState)
    (hsmall : 69 ≤ B) (hheap : 69 ≤ heapWords) (hinput : N + q + 1 ≤ B) (hbits : indexWidth 32 N q ≤ B)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state)
    (hpcB : 5 * (left ++ dimensionPrelude left.length ++ right).length ≤ B) :
    RunSafe B heapWords (PA17Generator.dimensionROM N q t) (left ++ dimensionPrelude left.length ++ right)
      (dimensionClock N q) state := by
  let rom := PA17Generator.dimensionROM N q t
  let first := computeLog widthExpr 64 1 1 left.length
  let second := computeLog bitsExpr 64 2 32 (left.length + first.length)
  let allCode := left ++ first ++ second ++ right
  have hcode : left ++ dimensionPrelude left.length ++ right = allCode := by
    simp only [dimensionPrelude, first, second, allCode, List.append_assoc]
  have hAllPc : 5 * allCode.length ≤ B := by rw [← hcode]; exact hpcB
  have hwChecked (heap : Nat → Nat) : ExprChecked rom heap B heapWords widthExpr := by
    exact ⟨by change 1 < 3; decide, by omega, by change q ≤ B; omega⟩
  have hbChecked (heap : Nat → Nat) : ExprChecked rom heap B heapWords bitsExpr := by
    refine ⟨⟨⟨by change 0 < 3; decide, by omega, by change N ≤ B; omega⟩,
      ⟨by change 1 < 3; decide, by omega, by change q ≤ B; omega⟩, ?_⟩, ?_, ?_⟩
    · change N + q ≤ B; omega
    · change 1 ≤ B; omega
    · change N + q + 1 ≤ B; exact hinput
  have hwBelow : widthExpr.Below 64 := by trivial
  have hbBelow : bitsExpr.Below 64 := by exact ⟨⟨trivial, trivial⟩, trivial⟩
  have hwValue : ∀ heap, widthExpr.eval rom heap = q := fun _ => rfl
  have hbValue : ∀ heap, bitsExpr.eval rom heap = N + q + 1 := fun _ => rfl
  have hfirst := computeLog_safe widthExpr rom B heapWords 64 1 1 hwBelow
    (by change 64 + 1 ≤ B; omega) (by change 64 + 1 ≤ heapWords; omega)
    (by omega) (by omega) (by omega) (by omega) left (second ++ right) state hpc ha hr (hwChecked state.heap)
    (by rw [hwValue, Nat.one_mul]; exact (clog_succ_le q).trans (by omega))
    (by simpa only [first, allCode, List.append_assoc] using hAllPc)
  have hfirst' : RunSafe B heapWords rom allCode (computeClock widthExpr rom state.heap 64) state := by
    simpa only [first, allCode, List.append_assoc] using hfirst
  let a := natRun rom allCode (computeClock widthExpr rom state.heap 64) state
  have hsem := computeLog_run widthExpr rom 64 1 1 hwBelow left (second ++ right) state hpc ha
  have hsem' : a.pc = 5 * (left.length + 16) ∧ a.halted = false := by
    have hlen : (widthExpr.compile 64).length = 2 := rfl
    simpa only [a, first, allCode, List.append_assoc, hlen] using (And.intro hsem.1 hsem.2.1)
  have hflen : first.length = 16 := rfl
  have hsecond := computeLog_safe bitsExpr rom B heapWords 64 2 32 hbBelow
    (by change 64 + 5 ≤ B; omega) (by change 64 + 5 ≤ heapWords; omega)
    (by omega) (by omega) (by omega) (by omega) (left ++ first) right a
    (by simpa only [List.length_append, hflen] using hsem'.1) hsem'.2 (hfirst'.final _ _ _ _ _).1 (hbChecked a.heap)
    (by rw [hbValue, show N + q + 1 + 1 = N + q + 2 by omega]; exact hbits)
    (by simpa only [second, allCode, List.length_append] using hAllPc)
  have hsecond' : RunSafe B heapWords rom allCode (computeClock bitsExpr rom a.heap 64) a := by
    simpa only [second, allCode, List.length_append] using hsecond
  have hclock : computeClock widthExpr rom state.heap 64 + computeClock bitsExpr rom a.heap 64 = dimensionClock N q := by
    have hwlen : (widthExpr.compile 64).length = 2 := rfl
    have hblen : (bitsExpr.compile 64).length = 15 := rfl
    simp only [computeClock, hwValue, hbValue, hwlen, hblen, dimensionClock]
    rw [show N + q + 1 + 1 = N + q + 2 by omega]
    omega
  rw [hcode, ← hclock]
  exact RunSafe.add _ _ _ _ _ _ state hfirst' hsecond'

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035z
