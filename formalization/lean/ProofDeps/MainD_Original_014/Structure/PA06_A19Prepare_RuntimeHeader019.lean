module

public import Structure.PA06_A19Prepare_RuntimePacked016
public import PaperProofs.Structure.PA17_UniformGenerator_035z
public import PaperProofs.Structure.PA17_UniformGenerator_035p
public import PaperProofs.Structure.PA17_UniformGenerator_035x
public import PaperProofs.Structure.PA17_PackingBounds_043
public import PaperProofs.Structure.PA17_GeneratorStatic_048d
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Uncompiled candidate: actual temporary-header producer over the real
controllerInput. The original halving/count loop runs twice on ROM[1] and
ROM[0]+ROM[1]+1; no dimensionROM substitution or third supplied dimension.
The producer runs after low raw cache has been copied into the high bank;
its only scratch is the existing expression stack at 64..68. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeHeader019

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035h
  PA17UniformGenerator035i PA17UniformGenerator035j PA17UniformGenerator035l
  PA17UniformGenerator035m PA17UniformGenerator035p PA17UniformGenerator035z

/-- Only the two original raw headers are read. Used bits remain appended
exactly as in the original controller input. -/
theorem controller_header_N (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) :
    (controllerInput q full used).semantic.read .input 0 = full.length := rfl

theorem controller_header_q (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) :
    (controllerInput q full used).semantic.read .input 1 = q := rfl

theorem controller_input_length_two (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) :
    2 ≤ (controllerInput q full used).input.length := by
  change 2 ≤ (([full.length, q] ++ incidence full) ++
    (List.finRange q).map (fun tool => bit (decide (tool ∈ used)))).length
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

theorem prelude_run (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    let fresh := natRun (controllerInput q full used)
      (left ++ dimensionPrelude left.length ++ right) (dimensionClock full.length q) state
    fresh.pc = 5 * (left.length + 45) ∧ fresh.halted = false ∧
      fresh.heap 1 = CapacityBits.width q ∧ fresh.heap 2 = indexWidth 32 full.length q ∧
      (∀ address, (address < 64 ∨ 69 ≤ address) → address ≠ 1 → address ≠ 2 → fresh.heap address = state.heap address) := by
  let rom := controllerInput q full used
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
  have hbEval : ∀ heap, bitsExpr.eval rom heap = full.length + q + 1 := fun _ => rfl
  have hfLen : first.length = 16 := rfl
  have hfirst := computeLog_run widthExpr rom 64 1 1 hw left (second ++ right) state hpc ha
  have hfirst' : a.pc = 5 * (left.length + 16) ∧ a.halted = false ∧
      a.heap = Function.update state.heap 1 (CapacityBits.width q) := by
    simpa only [a, allCode, first, List.append_assoc, hwLen, hwHeap, hwEval, Nat.one_mul, CapacityBits.width] using hfirst
  have hsecond := computeLog_run bitsExpr rom 64 2 32 hb (left ++ first) right a
    (by simpa only [List.length_append, hfLen] using hfirst'.1) hfirst'.2.1
  have hsecond' : b.pc = 5 * (left.length + 45) ∧ b.halted = false ∧
      b.heap = Function.update (runOps rom (bitsExpr.compile 64) a).heap 2 (indexWidth 32 full.length q) := by
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
  have hclock : computeClock widthExpr rom state.heap 64 + computeClock bitsExpr rom a.heap 64 = dimensionClock full.length q := by
    simp only [computeClock, hwEval, hbEval, hwLen, hbLen, dimensionClock]
    rw [show full.length + q + 1 + 1 = full.length + q + 2 by omega]
    omega
  have hcode : left ++ dimensionPrelude left.length ++ right = allCode := by
    simp only [dimensionPrelude, first, second, allCode, List.append_assoc]
  rw [hcode, ← hclock, natRun_add]
  refine ⟨hsecond'.1, hsecond'.2.1, ?_, ?_, ?_⟩
  · rw [hf2 1 (Or.inl (by decide)) (by decide), hfirst'.2.2, Function.update_self]
  · rw [hsecond'.2.2, Function.update_self]
  · intro address haddr h1 h2
    exact (hf2 address haddr h2).trans (hf1 address haddr h1)

theorem prelude_safe (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) (B heapWords : Nat) (left right : List PackingOp) (state : NatState)
    (hsmall : 69 ≤ B) (hheap : 69 ≤ heapWords) (hinput : full.length + q + 1 ≤ B) (hbits : indexWidth 32 full.length q ≤ B)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) (hr : RegistersLE B state)
    (hpcB : 5 * (left ++ dimensionPrelude left.length ++ right).length ≤ B) :
    RunSafe B heapWords (controllerInput q full used) (left ++ dimensionPrelude left.length ++ right)
      (dimensionClock full.length q) state := by
  let rom := controllerInput q full used
  let first := computeLog widthExpr 64 1 1 left.length
  let second := computeLog bitsExpr 64 2 32 (left.length + first.length)
  let allCode := left ++ first ++ second ++ right
  have hcode : left ++ dimensionPrelude left.length ++ right = allCode := by
    simp only [dimensionPrelude, first, second, allCode, List.append_assoc]
  have hAllPc : 5 * allCode.length ≤ B := by rw [← hcode]; exact hpcB
  have hinputLength : 2 ≤ rom.input.length := controller_input_length_two q full used
  have hwChecked (heap : Nat → Nat) : ExprChecked rom heap B heapWords widthExpr := by
    exact ⟨by omega, by omega, by change q ≤ B; omega⟩
  have hbChecked (heap : Nat → Nat) : ExprChecked rom heap B heapWords bitsExpr := by
    refine ⟨⟨⟨by omega, by omega, by change full.length ≤ B; omega⟩,
      ⟨by omega, by omega, by change q ≤ B; omega⟩, ?_⟩, ?_, ?_⟩
    · change full.length + q ≤ B; omega
    · change 1 ≤ B; omega
    · change full.length + q + 1 ≤ B; exact hinput
  have hwBelow : widthExpr.Below 64 := by trivial
  have hbBelow : bitsExpr.Below 64 := by exact ⟨⟨trivial, trivial⟩, trivial⟩
  have hwValue : ∀ heap, widthExpr.eval rom heap = q := fun _ => rfl
  have hbValue : ∀ heap, bitsExpr.eval rom heap = full.length + q + 1 := fun _ => rfl
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
    (by rw [hbValue, show full.length + q + 1 + 1 = full.length + q + 2 by omega]; exact hbits)
    (by simpa only [second, allCode, List.length_append] using hAllPc)
  have hsecond' : RunSafe B heapWords rom allCode (computeClock bitsExpr rom a.heap 64) a := by
    simpa only [second, allCode, List.length_append] using hsecond
  have hclock : computeClock widthExpr rom state.heap 64 + computeClock bitsExpr rom a.heap 64 = dimensionClock full.length q := by
    have hwlen : (widthExpr.compile 64).length = 2 := rfl
    have hblen : (bitsExpr.compile 64).length = 15 := rfl
    simp only [computeClock, hwValue, hbValue, hwlen, hblen, dimensionClock]
    rw [show full.length + q + 1 + 1 = full.length + q + 2 by omega]
    omega
  rw [hcode, ← hclock]
  exact RunSafe.add _ _ _ _ _ _ state hfirst' hsecond'

/-- This is the original A19 heap allocation, not a new workspace premise. -/
def heapWords (N q t : Nat) : Nat :=
  4 + packedCapacityWords q (capacityWords 8192 N q t) (indexWidth 32 N q) +
    8192 * (N + q + t + 1)

theorem heapWords_room (N q t : Nat) : 69 ≤ heapWords N q t := by
  unfold heapWords
  omega

/-- Fixed 19-op postamble: actual copies to 0/3, actual mask arithmetic,
and a split allOnes computation whose transient values fit the word. -/
def postamble : List PackingOp :=
  [.base (.base (.constant .index 1)),
   .base (.base (.loadHeap .value .index)),
   .base (.base (.constant .address 0)),
   .base (.base (.storeHeap .address .value)),
   .base (.base (.constant .index 2)),
   .base (.base (.loadHeap .total .index)),
   .base (.base (.constant .address 3)),
   .base (.base (.storeHeap .address .total)),
   .base (.base (.constant .fresh 1)),
   .arithmetic .shiftLeft .old .fresh .value,
   .base (.subtract .old .old .fresh),
   .base (.base (.constant .address 1)),
   .base (.base (.storeHeap .address .old)),
   .base (.subtract .total .total .fresh),
   .arithmetic .shiftLeft .old .fresh .total,
   .base (.subtract .value .old .fresh),
   .base (.base (.add .old .old .value)),
   .base (.base (.constant .address 2)),
   .base (.base (.storeHeap .address .old))]

def program (start : Nat) : List PackingOp := dimensionPrelude start ++ postamble

def clock (N q : Nat) : Nat := dimensionClock N q + postamble.length

theorem postamble_length : postamble.length = 19 := rfl
theorem program_length (start : Nat) : (program start).length = 64 := rfl
theorem program_code_length : (packingCode (program 0)).length = 325 := rfl

theorem postamble_noJump : ∀ op ∈ postamble, NoJump op := by
  simp [postamble, NoJump]

theorem split_ones (bits : Nat) (hb : 0 < bits) :
    2 ^ (bits - 1) + (2 ^ (bits - 1) - 1) = 2 ^ bits - 1 := by
  have hpred : bits - 1 + 1 = bits := Nat.sub_add_cancel hb
  have hpow : 2 ^ bits = 2 ^ (bits - 1) * 2 := calc
    2 ^ bits = 2 ^ (bits - 1 + 1) := congrArg (fun exponent => 2 ^ exponent) hpred.symm
    _ = 2 ^ (bits - 1) * 2 := Nat.pow_succ _ _
  have hp := Nat.two_pow_pos (bits - 1)
  omega

theorem postamble_heap (rom : PhysicalROM) (state : NatState) (width bits : Nat)
    (hw : state.heap 1 = width) (hb : state.heap 2 = bits) (hbits : 0 < bits) :
    (runOps rom postamble state).heap =
      Function.update (Function.update (Function.update (Function.update state.heap 0 width) 3 bits)
        1 (2 ^ width - 1)) 2 (2 ^ bits - 1) := by
  simp +decide only [postamble, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
    Function.update_apply, ↓reduceIte, hw, hb, Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul, split_ones bits hbits]

theorem postamble_frame (rom : PhysicalROM) (state : NatState) (address : Nat) (ha : 4 ≤ address) :
    (runOps rom postamble state).heap address = state.heap address := by
  simp +decide only [postamble, runOps, natExecuteOp, Op.execute, Instruction.execute,
    Function.update_apply, ↓reduceIte, show address ≠ 0 by omega, show address ≠ 1 by omega,
    show address ≠ 2 by omega, show address ≠ 3 by omega]

theorem postamble_numeric (rom : PhysicalROM) (B heapWords width bits : Nat)
    (hsmall : 3 ≤ B) (hheap : 4 ≤ heapWords) (hbits : 0 < bits)
    (hwB : width ≤ B) (hbB : bits ≤ B) (hmaskPow : 2 ^ width ≤ B)
    (hhalf : 2 ^ (bits - 1) ≤ B) (hones : 2 ^ bits - 1 ≤ B)
    (state : NatState) (hr : RegistersLE B state) (hw : state.heap 1 = width) (hb : state.heap 2 = bits) :
    NumericSafe B heapWords rom postamble state := by
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 19 at hc
    interval_cases count <;> cases register <;>
      simp [postamble, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
        hw, hb, Nat.shiftLeft_eq, split_ones bits hbits]
    all_goals omega
  · intro count hc
    change count < 19 at hc
    interval_cases count <;>
      simp [postamble, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals omega

theorem width_lt_bits (N q : Nat) : CapacityBits.width q < indexWidth 32 N q := by
  have hw : CapacityBits.width q ≤ Nat.clog 2 (N + q + 2) :=
    Nat.clog_mono_right 2 (by omega)
  have hp : 0 < Nat.clog 2 (N + q + 2) := Nat.clog_pos (by decide) (by omega)
  unfold indexWidth
  omega

theorem maxWord_small (N q : Nat) (hq : 0 < q) : 320 ≤ 2 ^ indexWidth 32 N q - 1 := by
  have hb := PA17GeneratorStatic048.bits_ge_64 N q hq
  have hp : 2 ^ 64 ≤ 2 ^ indexWidth 32 N q := Nat.pow_le_pow_right (by decide) hb
  have hs : 320 < 2 ^ 64 := by decide
  omega

theorem maskPow_le_maxWord (N q : Nat) :
    2 ^ CapacityBits.width q ≤ 2 ^ indexWidth 32 N q - 1 := by
  have hp := Nat.pow_lt_pow_right (by decide : 1 < 2) (width_lt_bits N q)
  omega

theorem halfPow_le_maxWord (N q : Nat) :
    2 ^ (indexWidth 32 N q - 1) ≤ 2 ^ indexWidth 32 N q - 1 := by
  have hb := PA17PackingBounds043.bits_pos N q
  have hp := Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.sub_lt hb (by decide : 0 < 1))
  omega

/-- All original-data bounds are derived at wordFactor32. No final Header
or new dimension is supplied by the caller. -/
theorem program_run (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    let fresh := natRun (controllerInput q full used)
      (left ++ program left.length ++ right) (clock full.length q) state
    fresh.pc = 5 * (left.length + 64) ∧ fresh.halted = false ∧
      fresh.heap 0 = CapacityBits.width q ∧
      fresh.heap 1 = 2 ^ CapacityBits.width q - 1 ∧
      fresh.heap 2 = 2 ^ indexWidth 32 full.length q - 1 ∧
      fresh.heap 3 = indexWidth 32 full.length q ∧
      (∀ address, 69 ≤ address → fresh.heap address = state.heap address) := by
  let rom := controllerInput q full used
  let lead := left ++ dimensionPrelude left.length
  let allCode := left ++ program left.length ++ right
  let a := natRun rom allCode (dimensionClock full.length q) state
  have hpre := prelude_run q full used left (postamble ++ right) state hpc ha
  have hp : a.pc = 5 * (left.length + 45) ∧ a.halted = false ∧
      a.heap 1 = CapacityBits.width q ∧ a.heap 2 = indexWidth 32 full.length q ∧
      (∀ address, (address < 64 ∨ 69 ≤ address) → address ≠ 1 → address ≠ 2 → a.heap address = state.heap address) := by
    simpa only [a, allCode, program, List.append_assoc] using hpre
  have hlead : lead.length = left.length + 45 := by
    simp only [lead, List.length_append, dimensionPrelude_length]
  have htail : natRun rom allCode postamble.length a = runOps rom postamble a := by
    have hsegment := natRun_of_straight_segment rom (lead ++ postamble ++ right) postamble lead.length
      (by simp only [List.length_append]; omega) (segment_index lead postamble right)
      postamble_noJump a (by rw [hlead]; exact hp.1) hp.2.1
    simpa only [allCode, program, lead, List.append_assoc] using hsegment
  have hcode : allCode = lead ++ postamble ++ right := by
    simp only [allCode, program, lead, List.append_assoc]
  have hheap := postamble_heap rom a (CapacityBits.width q) (indexWidth 32 full.length q)
    hp.2.2.1 hp.2.2.2.1 (PA17PackingBounds043.bits_pos full.length q)
  have hrun : natRun (controllerInput q full used) (left ++ program left.length ++ right)
      (clock full.length q) state = runOps rom postamble a := by
    change natRun rom allCode (dimensionClock full.length q + postamble.length) state = _
    rw [natRun_add, htail]
  simp only [hrun]
  refine ⟨?_, (runOps_halted rom postamble a).trans hp.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [runOps_pc rom postamble a postamble_noJump, hp.1, postamble_length]
    omega
  · rw [hheap]; simp
  · rw [hheap]; simp
  · rw [hheap]; simp
  · rw [hheap]; simp
  · intro address haddr
    exact (postamble_frame rom a address (by omega)).trans
      (hp.2.2.2.2 address (Or.inr haddr) (by omega) (by omega))

/-- Full real Nat-prefix safety uses the existing computeLog_safe twice,
then the postamble's independently bounded actual instructions. The local
register bound is a normal internal machine representation obligation. -/
theorem program_safe (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (t : Nat) (hq : 0 < q) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hr : RegistersLE (2 ^ indexWidth 32 full.length q - 1) state)
    (hpcB : 5 * (left ++ program left.length ++ right).length ≤ 2 ^ indexWidth 32 full.length q - 1) :
    RunSafe (2 ^ indexWidth 32 full.length q - 1) (heapWords full.length q t)
      (controllerInput q full used) (left ++ program left.length ++ right) (clock full.length q) state := by
  let B := 2 ^ indexWidth 32 full.length q - 1
  let rom := controllerInput q full used
  let allCode := left ++ program left.length ++ right
  let lead := left ++ dimensionPrelude left.length
  let a := natRun rom allCode (dimensionClock full.length q) state
  have hsmall := maxWord_small full.length q hq
  have hinput := PA17GeneratorStatic048.input_le_maxWord full.length q 0 hq (by omega)
  have hbits := PA17GeneratorStatic048.bits_le_maxWord full.length q 0 hq (by omega)
  have hpre := prelude_safe q full used B (heapWords full.length q t) left (postamble ++ right) state
    (by exact (show 69 ≤ 320 by decide).trans hsmall) (heapWords_room full.length q t)
    hinput hbits hpc ha hr (by simpa only [program, List.append_assoc] using hpcB)
  have hpre' : RunSafe B (heapWords full.length q t) rom allCode (dimensionClock full.length q) state := by
    simpa only [allCode, program, List.append_assoc] using hpre
  have hsem := prelude_run q full used left (postamble ++ right) state hpc ha
  have hsem' : a.pc = 5 * (left.length + 45) ∧ a.halted = false ∧
      a.heap 1 = CapacityBits.width q ∧ a.heap 2 = indexWidth 32 full.length q := by
    have hprefix : a.pc = 5 * (left.length + 45) ∧ a.halted = false ∧
        a.heap 1 = CapacityBits.width q ∧ a.heap 2 = indexWidth 32 full.length q ∧
        (∀ address, (address < 64 ∨ 69 ≤ address) → address ≠ 1 → address ≠ 2 → a.heap address = state.heap address) := by
      simpa only [a, allCode, program, List.append_assoc] using hsem
    exact ⟨hprefix.1, hprefix.2.1, hprefix.2.2.1, hprefix.2.2.2.1⟩
  have hnumeric := postamble_numeric rom B (heapWords full.length q t) (CapacityBits.width q)
    (indexWidth 32 full.length q) (by omega) ((show 4 ≤ 69 by decide).trans (heapWords_room full.length q t))
    (PA17PackingBounds043.bits_pos full.length q)
    ((width_lt_bits full.length q).le.trans hbits) hbits (maskPow_le_maxWord full.length q)
    (halfPow_le_maxWord full.length q) le_rfl a (hpre'.final _ _ _ _ _).1
    hsem'.2.2.1 hsem'.2.2.2
  have hlead : lead.length = left.length + 45 := by
    simp only [lead, List.length_append, dimensionPrelude_length]
  have hpost := straight_segment_safe rom B (heapWords full.length q t) lead postamble right
    postamble_noJump a (by rw [hlead]; exact hsem'.1) hsem'.2.1 hnumeric
  have hpost' : RunSafe B (heapWords full.length q t) rom allCode postamble.length a := by
    simpa only [allCode, program, lead, List.append_assoc] using hpost
  exact RunSafe.add _ _ _ _ _ _ state hpre' hpost'

theorem program0_code_fit {bits : Nat} (hb : 9 ≤ bits) : WordsFit bits (packingCode (program 0)) := by
  have hpow : 2 ^ 9 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hb
  intro value hv
  simp [packingCode, program, dimensionPrelude, computeLog, widthExpr, bitsExpr,
    Expr.compile, spill, finish, Binary.instruction, logBlock, logInit, logHead, logTail, storeLog,
    postamble, PackingOp.encode, Op.encodeWords, Instruction.encodeWords,
    PackingPrimitive.word, Register.word, Region.word, haltWords] at hv
  simp only [Fits]
  omega

theorem program0_pc_fit {bits : Nat} (hb : 9 ≤ bits) : Fits bits (5 * (program 0).length) := by
  have hpow : 2 ^ 9 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hb
  rw [program_length]
  change 320 < 2 ^ bits
  omega

/-- Canonical Nat view of an actual physical state. This carries no extra
input fields, and every incoming register already fits the actual Word. -/
def natView {bits : Nat} (state : WordState bits) : NatState :=
  ⟨fun register => (state.register register).toNat,
    fun address => (state.heap (BitVec.ofNat bits address)).toNat, state.pc.toNat, state.halted⟩

theorem natView_toWord {bits : Nat} (state : WordState bits) : (natView state).toWord bits = state := by
  apply wordState_ext
  · funext register
    simp only [natView, NatState.toWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · funext address
    simp only [natView, NatState.toWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [natView, NatState.toWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rfl

theorem natView_registers {bits : Nat} (state : WordState bits) :
    RegistersLE (2 ^ bits - 1) (natView state) := by
  intro register
  have hfit := (state.register register).toNat_lt_twoPow_of_le (Nat.le_refl bits)
  change (state.register register).toNat ≤ 2 ^ bits - 1
  omega

/-- The real fixed producer starts with arbitrary actual heap/registers.
Only the normal pc/active entry conditions are needed; temporary Header
is an output proved from original raw inputs, not an input premise. -/
theorem actual_header (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (t : Nat) (hq : 0 < q) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc = BitVec.ofNat _ 0) (ha : state.halted = false) :
    PA06A19PrepareRuntimePacked016.Header q
      (packingRun (controllerInput q full used) (program 0) (clock full.length q) state).heap := by
  let bits := indexWidth 32 full.length q
  let B := 2 ^ bits - 1
  let start := natView state
  have hb64 : 64 ≤ bits := PA17GeneratorStatic048.bits_ge_64 full.length q hq
  have hsmall := maxWord_small full.length q hq
  have hstartpc : start.pc = 5 * ([] : List PackingOp).length := by
    change state.pc.toNat = 0
    rw [hpc]
    rfl
  have hs := program_safe q full used t hq [] [] start hstartpc ha (natView_registers state)
    (by simpa only [List.nil_append, List.append_nil, program_length] using hsmall)
  have hs' : RunSafe B (heapWords full.length q t) (controllerInput q full used) (program 0)
      (clock full.length q) start := by
    simpa only [B, bits, List.nil_append, List.append_nil, List.length_nil] using hs
  have hw := actual_word_run (controllerInput q full used) B (heapWords full.length q t) bits
    (program 0) (clock full.length q) start hs' (PA17GeneratorStatic048.maxWord_fits bits)
    (program0_code_fit (by omega)) (program0_pc_fit (by omega)) (clock full.length q) le_rfl
  rw [natView_toWord] at hw
  have hn := program_run q full used [] [] start hstartpc ha
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at hn
  rw [hw]
  constructor
  · change BitVec.ofNat bits ((natRun _ _ _ start).heap (BitVec.ofNat bits 0).toNat) = _
    rw [BitVec.toNat_ofNat, Nat.zero_mod, hn.2.2.1]
  · change BitVec.ofNat bits ((natRun _ _ _ start).heap (BitVec.ofNat bits 1).toNat) = _
    have h1 : (BitVec.ofNat bits 1).toNat = 1 := Nat.mod_eq_of_lt (by
      have hp : 2 ^ 64 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb64
      omega)
    rw [h1, hn.2.2.2.1]
    rfl
  · change BitVec.ofNat bits ((natRun _ _ _ start).heap (BitVec.ofNat bits 2).toNat) = _
    have h2 : (BitVec.ofNat bits 2).toNat = 2 := Nat.mod_eq_of_lt (by
      have hp : 2 ^ 64 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb64
      omega)
    rw [h2, hn.2.2.2.2.1]
  · change BitVec.ofNat bits ((natRun _ _ _ start).heap (BitVec.ofNat bits 3).toNat) = _
    have h3 : (BitVec.ofNat bits 3).toNat = 3 := Nat.mod_eq_of_lt (by
      have hp : 2 ^ 64 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb64
      omega)
    rw [h3, hn.2.2.2.2.2.1]

end PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimeHeader019
