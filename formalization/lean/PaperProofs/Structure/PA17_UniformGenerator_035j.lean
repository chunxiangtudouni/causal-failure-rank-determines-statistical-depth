module

public import PaperProofs.Structure.PA17_UniformGenerator_035f
public import PaperProofs.Structure.PA17_UniformGenerator_035i
import Mathlib.Tactic.IntervalCases

/-! Actual compiler prefix numeric and access certificates. The expression
contract bounds every evaluated subexpression and actual source address;
it is independent of the emitted code stream or its desired answer. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035j

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety PA17UniformGenerator035a PA17UniformGenerator035b
  PA17UniformGenerator035c PA17UniformGenerator035d PA17UniformGenerator035e

def RegistersLE (B : Nat) (state : NatState) : Prop := ∀ register, state.register register ≤ B

def NumericSafe (B heapWords : Nat) (rom : PhysicalROM) (ops : List PackingOp) (state : NatState) : Prop :=
  (∀ count ≤ ops.length, RegistersLE B (runOps rom (ops.take count) state)) ∧
    ∀ count (hc : count < ops.length), NatAccessFits rom heapWords (runOps rom (ops.take count) state) ops[count]

theorem NumericSafe.final (B heapWords : Nat) (rom : PhysicalROM) (ops : List PackingOp) (state : NatState)
    (hs : NumericSafe B heapWords rom ops state) : RegistersLE B (runOps rom ops state) := by
  simpa only [List.take_length] using hs.1 ops.length le_rfl

theorem NumericSafe.nil (B heapWords : Nat) (rom : PhysicalROM) (state : NatState) (hr : RegistersLE B state) :
    NumericSafe B heapWords rom [] state := by
  constructor
  · intro count _; simpa only [List.take_nil, runOps] using hr
  · intro count hc; simp only [List.length_nil] at hc; omega

theorem NumericSafe.append (B heapWords : Nat) (rom : PhysicalROM) (left right : List PackingOp) (state : NatState)
    (hl : NumericSafe B heapWords rom left state)
    (hr : NumericSafe B heapWords rom right (runOps rom left state)) :
    NumericSafe B heapWords rom (left ++ right) state := by
  constructor
  · intro count hc
    by_cases hleft : count ≤ left.length
    · rw [List.take_append_of_le_length hleft]
      exact hl.1 count hleft
    · have hn : left.length ≤ count := by omega
      rw [List.take_append, List.take_of_length_le hn, runOps_append]
      exact hr.1 (count - left.length) (by simp only [List.length_append] at hc; omega)
  · intro count hc
    by_cases hleft : count < left.length
    · rw [List.getElem_append_left hleft, List.take_append_of_le_length hleft.le]
      exact hl.2 count hleft
    · have hn : left.length ≤ count := by omega
      rw [List.getElem_append_right hn, List.take_append, List.take_of_length_le hn, runOps_append]
      exact hr.2 (count - left.length) (by simp only [List.length_append] at hc; omega)

def ExprChecked (rom : PhysicalROM) (heap : Nat → Nat) (B heapWords : Nat) : Expr → Prop
  | .constant value => value ≤ B
  | .cell address => address < heapWords ∧ address ≤ B ∧ heap address ≤ B
  | .input address => address < rom.input.length ∧ address ≤ B ∧ rom.semantic.read .input address ≤ B
  | .binary operation left right => ExprChecked rom heap B heapWords left ∧
      ExprChecked rom heap B heapWords right ∧ operation.eval (left.eval rom heap) (right.eval rom heap) ≤ B

theorem checked_value (expression : Expr) (rom : PhysicalROM) (heap : Nat → Nat) (B heapWords : Nat)
    (hs : ExprChecked rom heap B heapWords expression) : expression.eval rom heap ≤ B := by
  cases expression with
  | constant value => exact hs
  | cell address => exact hs.2.2
  | input address => exact hs.2.2
  | binary operation left right => exact hs.2.2

theorem checked_transfer (expression : Expr) (rom : PhysicalROM) (B heapWords stack : Nat)
    (hb : expression.Below stack) (old fresh : Nat → Nat)
    (hf : ∀ address < stack, fresh address = old address)
    (hc : ExprChecked rom old B heapWords expression) : ExprChecked rom fresh B heapWords expression := by
  induction expression with
  | constant value => exact hc
  | cell address => exact ⟨hc.1, hc.2.1, by rw [hf address hb]; exact hc.2.2⟩
  | input address => exact hc
  | binary operation left right ihl ihr =>
    refine ⟨ihl hb.1 hc.1, ihr hb.2 hc.2.1, ?_⟩
    rw [Expr.eval_congr left rom stack hb.1 old fresh hf, Expr.eval_congr right rom stack hb.2 old fresh hf]
    exact hc.2.2

theorem spill_numeric (rom : PhysicalROM) (B heapWords stack : Nat) (hb : stack ≤ B) (ha : stack < heapWords)
    (state : NatState) (hr : RegistersLE B state) : NumericSafe B heapWords rom (spill stack) state := by
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 2 at hc
    interval_cases count <;> cases register <;> simp [spill, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 2 at hc
    interval_cases count <;> simp [spill, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, ha]

theorem finish_numeric (rom : PhysicalROM) (B heapWords stack : Nat) (operation : Binary)
    (hb : stack ≤ B) (ha : stack < heapWords) (state : NatState) (hr : RegistersLE B state)
    (hleft : state.heap stack ≤ B) (hvalue : operation.eval (state.heap stack) (state.register .value) ≤ B) :
    NumericSafe B heapWords rom (finish stack operation) state := by
  constructor
  · intro count hc register
    have hh := hr register
    change count ≤ 3 at hc
    interval_cases count <;> cases register <;> cases operation <;>
      simp [finish, Binary.instruction, Binary.eval, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute] at *
    all_goals omega
  · intro count hc
    change count < 3 at hc
    interval_cases count <;> cases operation <;>
      simp [finish, Binary.instruction, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, ha]

theorem expression_numeric (expression : Expr) (rom : PhysicalROM) (B heapWords stack : Nat)
    (hb : expression.Below stack) (hstackB : stack + expression.size ≤ B)
    (hstackH : stack + expression.size ≤ heapWords) (state : NatState)
    (hr : RegistersLE B state) (hc : ExprChecked rom state.heap B heapWords expression) :
    NumericSafe B heapWords rom (expression.compile stack) state := by
  induction expression generalizing stack state with
  | constant value =>
    change value ≤ B at hc
    constructor
    · intro count hcount register
      have hh := hr register
      change count ≤ 1 at hcount
      interval_cases count <;> cases register <;> simp [Expr.compile, runOps, natExecuteOp, Op.execute, Instruction.execute]
      all_goals omega
    · intro count hcount
      change count < 1 at hcount
      have hz : count = 0 := by omega
      subst count
      trivial
  | cell address =>
    constructor
    · intro count hcount register
      have hh := hr register
      change count ≤ 2 at hcount
      interval_cases count <;> cases register <;> simp [Expr.compile, runOps, natExecuteOp, Op.execute, Instruction.execute]
      all_goals exact (by first | exact hh | exact hc.2.1 | exact hc.2.2)
    · intro count hcount
      change count < 2 at hcount
      interval_cases count <;> simp [Expr.compile, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hc.1]
  | input address =>
    constructor
    · intro count hcount register
      have hh := hr register
      change count ≤ 2 at hcount
      interval_cases count <;> cases register <;> simp [Expr.compile, runOps, natExecuteOp, Op.execute, Instruction.execute]
      all_goals exact (by first | exact hh | exact hc.2.1 | exact hc.2.2)
    · intro count hcount
      change count < 2 at hcount
      interval_cases count <;> simp [Expr.compile, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, PhysicalROM.words, hc.1]
  | binary operation left right ihl ihr =>
    have hleftSize : 1 ≤ left.size := by cases left <;> simp [Expr.size]
    have hrightSize : 1 ≤ right.size := by cases right <;> simp [Expr.size]
    change stack + (left.size + right.size + 1) ≤ B at hstackB
    change stack + (left.size + right.size + 1) ≤ heapWords at hstackH
    let a := runOps rom (left.compile stack) state
    let b := runOps rom (spill stack) a
    let c := runOps rom (right.compile (stack + 1)) b
    have h1 := ihl stack hb.1 (by omega) (by omega) state hr hc.1
    have h2 := spill_numeric rom B heapWords stack (by omega) (by omega) a (h1.final _ _ _ _ _)
    have hf (address : Nat) (ha : address < stack) : b.heap address = state.heap address := by
      rw [spill_heap, Function.update_of_ne (show address ≠ stack by omega)]
      exact (left.compile_correct rom stack hb.1 state).2.1 address ha
    have h3 := ihr (stack + 1) (Expr.Below.mono right stack (stack + 1) (by omega) hb.2)
      (by omega) (by omega) b (h2.final _ _ _ _ _)
      (checked_transfer right rom B heapWords stack hb.2 state.heap b.heap hf hc.2.1)
    have hcvalue : c.register .value = right.eval rom state.heap := by
      rw [(right.compile_correct rom (stack + 1) (Expr.Below.mono right stack (stack + 1) (by omega) hb.2) b).1]
      exact Expr.eval_congr right rom stack hb.2 state.heap b.heap hf
    have hcstack : c.heap stack = left.eval rom state.heap := by
      rw [(right.compile_correct rom (stack + 1) (Expr.Below.mono right stack (stack + 1) (by omega) hb.2) b).2.1 stack (by omega),
        spill_heap, Function.update_self]
      exact (left.compile_correct rom stack hb.1 state).1
    have h4 := finish_numeric rom B heapWords stack operation (by omega) (by omega) c (h3.final _ _ _ _ _)
      (by rw [hcstack]; exact checked_value left rom state.heap B heapWords hc.1)
      (by rw [hcstack, hcvalue]; exact hc.2.2)
    dsimp only [Expr.compile]
    exact NumericSafe.append _ _ _ _ _ _ h1
      (NumericSafe.append _ _ _ _ _ _ h2 (NumericSafe.append _ _ _ _ _ _ h3 h4))

theorem expression_segment_numeric (expression : Expr) (rom : PhysicalROM) (B heapWords stack : Nat)
    (hb : expression.Below stack) (hstackB : stack + expression.size ≤ B)
    (hstackH : stack + expression.size ≤ heapWords) (state : NatState)
    (hr : RegistersLE B state) (hc : ExprChecked rom state.heap B heapWords expression)
    (left right : List PackingOp) (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    (∀ count ≤ (expression.compile stack).length, RegistersLE B
      (natRun rom (left ++ expression.compile stack ++ right) count state)) ∧
      ∀ count (hcount : count < (expression.compile stack).length), NatAccessFits rom heapWords
        (natRun rom (left ++ expression.compile stack ++ right) count state) (expression.compile stack)[count] := by
  have hn := expression_numeric expression rom B heapWords stack hb hstackB hstackH state hr hc
  have he (count : Nat) (hcount : count ≤ (expression.compile stack).length) :
      natRun rom (left ++ expression.compile stack ++ right) count state = runOps rom ((expression.compile stack).take count) state := by
    have hlen : ((expression.compile stack).take count).length = count := List.length_take_of_le hcount
    conv_lhs => rw [← hlen]
    exact natRun_of_straight_segment rom _ _ left.length
      (by simp only [List.length_append, hlen]; omega)
      (fun position hp => by
        have hh := segment_index left (expression.compile stack) right position (by rw [hlen] at hp; omega)
        simpa only [List.getElem_take] using hh)
      (fun op hm => expression.compile_noJump stack op (List.mem_of_mem_take hm)) state hpc ha
  constructor
  · intro count hcount; rw [he count hcount]; exact hn.1 count hcount
  · intro count hcount; rw [he count hcount.le]; exact hn.2 count hcount

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035j
