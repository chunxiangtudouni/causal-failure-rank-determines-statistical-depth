module

public import Structure.PSTR_BuildLower_Relative_008
public import Structure.PSTR_BuildLower_Relocate_006

/-! Fixed-code expression execution with a runtime .address bank base.
Only static source offsets and stack offsets enter code literals. This is the
inline relative-address counterpart of the original Expr.compile, using its
same binary instructions and induction; no target instruction decoder exists. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035b

def bankFinish (stack : Nat) (operation : Binary) : List PackingOp :=
  [.base (.base (.constant .index stack)),
   .base (.base (.add .index .address .index)),
   .base (.base (.loadHeap .old .index)), operation.instruction]

def bankCompile (stack : Nat) : Expr → List PackingOp
  | .constant value => [.base (.base (.constant .value value))]
  | .cell address => relativeRead address .value
  | .input address =>
      [.base (.base (.constant .index address)), .base (.base (.loadROM .input .value .index))]
  | .binary operation left right => bankCompile stack left ++
      (relativeWrite stack ++ (bankCompile (stack + 1) right ++ bankFinish stack operation))

theorem bankWrite_nat_address (rom : PhysicalROM) (stack : Nat) (state : NatState) :
    (runOps rom (relativeWrite stack) state).register .address = state.register .address := rfl

theorem bankFinish_nat_value (rom : PhysicalROM) (stack : Nat) (operation : Binary)
    (state : NatState) :
    (runOps rom (bankFinish stack operation) state).register .value =
      operation.eval (state.heap (state.register .address + stack)) (state.register .value) := by
  cases operation <;> rfl

theorem bankFinish_nat_heap (rom : PhysicalROM) (stack : Nat) (operation : Binary)
    (state : NatState) : (runOps rom (bankFinish stack operation) state).heap = state.heap := by
  cases operation <;> rfl

theorem bankFinish_nat_address (rom : PhysicalROM) (stack : Nat) (operation : Binary)
    (state : NatState) :
    (runOps rom (bankFinish stack operation) state).register .address = state.register .address := by
  cases operation <;> rfl

theorem bankCompile_correct (expr : Expr) (rom : PhysicalROM) (stack : Nat)
    (hf : expr.Below stack) (state : NatState) :
    let result := runOps rom (bankCompile stack expr) state
    result.register .value = expr.eval rom (fun address => state.heap (state.register .address + address)) ∧
      (∀ address < state.register .address + stack, result.heap address = state.heap address) ∧
      result.register .address = state.register .address := by
  induction expr generalizing stack state with
  | constant value => exact ⟨rfl, fun _ _ => rfl, rfl⟩
  | cell address => exact ⟨relativeRead_nat_value rom address .value state, fun _ _ => rfl, rfl⟩
  | input address => exact ⟨rfl, fun _ _ => rfl, rfl⟩
  | binary operation left right ihl ihr =>
    let a := runOps rom (bankCompile stack left) state
    let b := runOps rom (relativeWrite stack) a
    let c := runOps rom (bankCompile (stack + 1) right) b
    have hl := ihl stack hf.1 state
    have habase : a.register .address = state.register .address := hl.2.2
    have hbbase : b.register .address = state.register .address :=
      (bankWrite_nat_address rom stack a).trans hl.2.2
    have hr := ihr (stack + 1) (Expr.Below.mono right stack (stack + 1) (by omega) hf.2) b
    have hcbase : c.register .address = state.register .address := hr.2.2.trans hbbase
    have hbframe (address : Nat) (ha : address < state.register .address + stack) :
        b.heap address = state.heap address := by
      rw [relativeWrite_nat_heap, Function.update_of_ne (show address ≠ a.register .address + stack by omega)]
      exact hl.2.1 address ha
    have heval := Expr.eval_congr right rom stack hf.2
      (fun address => state.heap (state.register .address + address))
      (fun address => b.heap (b.register .address + address)) (by
        intro address ha
        rw [hbbase]
        exact hbframe _ (by omega))
    have hstack : c.heap (state.register .address + stack) =
        left.eval rom (fun address => state.heap (state.register .address + address)) := by
      rw [hr.2.1 _ (by omega), relativeWrite_nat_heap, hl.2.2, Function.update_self]
      exact hl.1
    dsimp only [bankCompile]
    rw [runOps_append, runOps_append, runOps_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [bankFinish_nat_value, hcbase, hstack, hr.1, heval]
      rfl
    · intro address ha
      rw [bankFinish_nat_heap, hr.2.1 address (by omega)]
      exact hbframe address ha
    · rw [bankFinish_nat_address, hr.2.2, bankWrite_nat_address]
      exact hl.2.2

theorem bankCompile_length (expr : Expr) (stack : Nat) :
    (bankCompile stack expr).length ≤ 7 * expr.size := by
  induction expr generalizing stack with
  | constant value => simp [bankCompile, Expr.size]
  | cell address => simp [bankCompile, relativeRead, Expr.size]
  | input address => simp [bankCompile, Expr.size]
  | binary operation left right ihl ihr =>
    have hl := ihl stack
    have hr := ihr (stack + 1)
    simp only [bankCompile, Expr.size, List.length_append, relativeWrite_length,
      bankFinish, List.length_cons, List.length_nil]
    omega

end PaperProofs.Structure.LaminarTree.PSTRBuildLower
