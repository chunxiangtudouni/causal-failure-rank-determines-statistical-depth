module

public import PaperProofs.Structure.PA17_UniformGenerator_035a

/-! A finite expression compiler used by the dimension-only six-program
emitter. Variable cells and a disjoint temporary stack are ordinary heap
words. Expressions evaluate through real ISA operations, not code ROM. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035b

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a

inductive Binary where
  | add | subtract | minimum | multiply | divide | bitAnd | bitOr | shiftLeft | shiftRight
  deriving DecidableEq

def Binary.eval : Binary → Nat → Nat → Nat
  | .add, left, right => left + right
  | .subtract, left, right => left - right
  | .minimum, left, right => min left right
  | .multiply, left, right => left * right
  | .divide, left, right => left / right
  | .bitAnd, left, right => Nat.land left right
  | .bitOr, left, right => Nat.lor left right
  | .shiftLeft, left, right => Nat.shiftLeft left right
  | .shiftRight, left, right => Nat.shiftRight left right

def Binary.instruction : Binary → PackingOp
  | .add => .base (.base (.add .value .old .value))
  | .subtract => .base (.subtract .value .old .value)
  | .minimum => .base (.base (.minimum .value .old .value))
  | .multiply => .arithmetic .multiply .value .old .value
  | .divide => .arithmetic .divide .value .old .value
  | .bitAnd => .arithmetic .bitAnd .value .old .value
  | .bitOr => .arithmetic .bitOr .value .old .value
  | .shiftLeft => .arithmetic .shiftLeft .value .old .value
  | .shiftRight => .arithmetic .shiftRight .value .old .value

inductive Expr where
  | constant (value : Nat)
  | cell (address : Nat)
  | input (address : Nat)
  | binary (operation : Binary) (left right : Expr)

def Expr.eval (rom : PhysicalROM) (heap : Nat → Nat) : Expr → Nat
  | .constant value => value
  | .cell address => heap address
  | .input address => rom.semantic.read .input address
  | .binary operation left right => operation.eval (left.eval rom heap) (right.eval rom heap)

def Expr.Below (stack : Nat) : Expr → Prop
  | .constant _ => True
  | .cell address => address < stack
  | .input _ => True
  | .binary _ left right => left.Below stack ∧ right.Below stack

theorem Expr.Below.mono (expression : Expr) (small large : Nat) (h : small ≤ large)
    (hf : expression.Below small) : expression.Below large := by
  induction expression with
  | constant value => trivial
  | cell address => exact lt_of_lt_of_le hf h
  | input address => trivial
  | binary operation left right ihl ihr => exact ⟨ihl hf.1, ihr hf.2⟩

theorem Expr.eval_congr (expression : Expr) (rom : PhysicalROM) (stack : Nat)
    (hf : expression.Below stack) (heap heap' : Nat → Nat)
    (hh : ∀ address < stack, heap' address = heap address) :
    expression.eval rom heap' = expression.eval rom heap := by
  induction expression with
  | constant value => rfl
  | cell address => exact hh address hf
  | input address => rfl
  | binary operation left right ihl ihr =>
    simp only [Expr.eval, ihl hf.1, ihr hf.2]

def spill (stack : Nat) : List PackingOp :=
  [.base (.base (.constant .index stack)), .base (.base (.storeHeap .index .value))]

def finish (stack : Nat) (operation : Binary) : List PackingOp :=
  [.base (.base (.constant .index stack)), .base (.base (.loadHeap .old .index)), operation.instruction]

def Expr.compile (stack : Nat) : Expr → List PackingOp
  | .constant value => [.base (.base (.constant .value value))]
  | .cell address => [.base (.base (.constant .index address)), .base (.base (.loadHeap .value .index))]
  | .input address => [.base (.base (.constant .index address)), .base (.base (.loadROM .input .value .index))]
  | .binary operation left right => left.compile stack ++
      (spill stack ++ (right.compile (stack + 1) ++ finish stack operation))

theorem spill_heap (rom : PhysicalROM) (stack : Nat) (state : NatState) :
    (runOps rom (spill stack) state).heap = Function.update state.heap stack (state.register .value) := rfl

theorem spill_address (rom : PhysicalROM) (stack : Nat) (state : NatState) :
    (runOps rom (spill stack) state).register .address = state.register .address := rfl

theorem finish_value (rom : PhysicalROM) (stack : Nat) (operation : Binary) (state : NatState) :
    (runOps rom (finish stack operation) state).register .value =
      operation.eval (state.heap stack) (state.register .value) := by
  cases operation <;> rfl

theorem finish_heap (rom : PhysicalROM) (stack : Nat) (operation : Binary) (state : NatState) :
    (runOps rom (finish stack operation) state).heap = state.heap := by
  cases operation <;> rfl

theorem finish_address (rom : PhysicalROM) (stack : Nat) (operation : Binary) (state : NatState) :
    (runOps rom (finish stack operation) state).register .address = state.register .address := by
  cases operation <;> rfl

theorem Expr.compile_correct (expression : Expr) (rom : PhysicalROM) (stack : Nat)
    (hf : expression.Below stack) (state : NatState) :
    let result := runOps rom (expression.compile stack) state
    result.register .value = expression.eval rom state.heap ∧
      (∀ address < stack, result.heap address = state.heap address) ∧
      result.register .address = state.register .address := by
  induction expression generalizing stack state with
  | constant value => exact ⟨rfl, fun _ _ => rfl, rfl⟩
  | cell address => exact ⟨rfl, fun _ _ => rfl, rfl⟩
  | input address => exact ⟨rfl, fun _ _ => rfl, rfl⟩
  | binary operation left right ihl ihr =>
    let a := runOps rom (left.compile stack) state
    let b := runOps rom (spill stack) a
    let c := runOps rom (right.compile (stack + 1)) b
    have hl := ihl stack hf.1 state
    have hr := ihr (stack + 1) (Expr.Below.mono right stack (stack + 1) (by omega) hf.2) b
    have hbframe (address : Nat) (ha : address < stack) : b.heap address = state.heap address := by
      rw [spill_heap, Function.update_of_ne (show address ≠ stack by omega)]
      exact hl.2.1 address ha
    have heval := Expr.eval_congr right rom stack hf.2 state.heap b.heap hbframe
    have hstack : c.heap stack = left.eval rom state.heap := by
      rw [hr.2.1 stack (by omega), spill_heap, Function.update_self]
      exact hl.1
    dsimp only [Expr.compile]
    rw [runOps_append, runOps_append, runOps_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [finish_value, hstack, hr.1, heval]
      rfl
    · intro address ha
      rw [finish_heap, hr.2.1 address (by omega)]
      exact hbframe address ha
    · rw [finish_address, hr.2.2, spill_address]
      exact hl.2.2

theorem Expr.compile_noJump (expression : Expr) (stack : Nat) :
    ∀ op ∈ expression.compile stack, NoJump op := by
  induction expression generalizing stack with
  | constant value => simp [Expr.compile, NoJump]
  | cell address => simp [Expr.compile, NoJump]
  | input address => simp [Expr.compile, NoJump]
  | binary operation left right ihl ihr =>
    intro op hm
    simp only [Expr.compile, List.mem_append] at hm
    rcases hm with hm | hm | hm | hm
    · exact ihl stack op hm
    · have hs : ∀ entry ∈ spill stack, NoJump entry := by simp [spill, NoJump]
      exact hs op hm
    · exact ihr (stack + 1) op hm
    · have hs : ∀ entry ∈ finish stack operation, NoJump entry := by
        cases operation <;> simp [finish, Binary.instruction, NoJump]
      exact hs op hm

theorem Expr.segment_run (expression : Expr) (rom : PhysicalROM) (stack : Nat)
    (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    natRun rom (left ++ expression.compile stack ++ right) (expression.compile stack).length state =
      runOps rom (expression.compile stack) state := by
  exact natRun_of_straight_segment rom _ _ left.length
    (by simp only [List.length_append]; omega)
    (segment_index left (expression.compile stack) right) (expression.compile_noJump stack) state hpc ha

theorem Expr.segment_value (expression : Expr) (rom : PhysicalROM) (stack : Nat)
    (hf : expression.Below stack) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    (natRun rom (left ++ expression.compile stack ++ right) (expression.compile stack).length state).register .value =
      expression.eval rom state.heap := by
  rw [expression.segment_run rom stack left right state hpc ha]
  exact (expression.compile_correct rom stack hf state).1

def Expr.size : Expr → Nat
  | .constant _ | .cell _ | .input _ => 1
  | .binary _ left right => left.size + right.size + 1

theorem Expr.compile_length_le (expression : Expr) (stack : Nat) :
    (expression.compile stack).length ≤ 5 * expression.size := by
  induction expression generalizing stack with
  | constant value => simp [Expr.compile, Expr.size]
  | cell address => simp [Expr.compile, Expr.size]
  | input address => simp [Expr.compile, Expr.size]
  | binary operation left right ihl ihr =>
    have hl := ihl stack
    have hr := ihr (stack + 1)
    simp only [Expr.compile, Expr.size, List.length_append, spill, finish, List.length_cons, List.length_nil]
    omega

theorem Expr.segment_word_run (expression : Expr) (rom : PhysicalROM) (stack bits : Nat)
    (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ expression.compile stack ++ right)))
    (hsafe : ∀ count < (expression.compile stack).length,
      RegistersFit bits (natRun rom (left ++ expression.compile stack ++ right) count state) ∧
        Fits bits (natRun rom (left ++ expression.compile stack ++ right) count state).pc) :
    packingRun rom (left ++ expression.compile stack ++ right) (expression.compile stack).length (state.toWord bits) =
      (runOps rom (expression.compile stack) state).toWord bits := by
  rw [natRun_toWord _ _ _ _ hcode hsafe, expression.segment_run rom stack left right state hpc ha]

theorem Expr.segment_word_value (expression : Expr) (rom : PhysicalROM) (stack bits : Nat)
    (hf : expression.Below stack) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ expression.compile stack ++ right)))
    (hsafe : ∀ count < (expression.compile stack).length,
      RegistersFit bits (natRun rom (left ++ expression.compile stack ++ right) count state) ∧
        Fits bits (natRun rom (left ++ expression.compile stack ++ right) count state).pc)
    (hvalue : Fits bits (expression.eval rom state.heap)) :
    ((packingRun rom (left ++ expression.compile stack ++ right) (expression.compile stack).length
      (state.toWord bits)).register .value).toNat = expression.eval rom state.heap := by
  rw [expression.segment_word_run rom stack bits left right state hpc ha hcode hsafe]
  change (BitVec.ofNat bits ((runOps rom (expression.compile stack) state).register .value)).toNat = _
  rw [(expression.compile_correct rom stack hf state).1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvalue]

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035b
