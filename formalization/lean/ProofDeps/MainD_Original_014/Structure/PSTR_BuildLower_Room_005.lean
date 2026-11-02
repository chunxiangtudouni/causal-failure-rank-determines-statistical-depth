module

public import PaperProofs.Structure.PA17_ProgramTemplates_041k

/-! Kernel-checked fixed-AST bounds and ordinary allocated-room arithmetic.
The control/cache bases are the shared prepare ABI, not a new allocation. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b
  PA17ProgramTemplates041

def expressionCellLimit : Expr → Nat
  | .constant _ | .input _ => 0
  | .cell address => address + 1
  | .binary _ left right => max (expressionCellLimit left) (expressionCellLimit right)

def expressionInputLimit : Expr → Nat
  | .constant _ | .cell _ => 0
  | .input address => address + 1
  | .binary _ left right => max (expressionInputLimit left) (expressionInputLimit right)

def programExpressionSize : Program → Nat
  | .code ops => (ops.map (fun op => match op with
      | .constant _ expr => expr.size
      | .literal _ => 0)).foldl max 0
  | .append left right => max (programExpressionSize left) (programExpressionSize right)
  | .repeat _ bound body => max bound.size (programExpressionSize body)

def programRepeatDepth : Program → Nat
  | .code _ => 0
  | .append left right => max (programRepeatDepth left) (programRepeatDepth right)
  | .repeat _ _ body => programRepeatDepth body + 1

def programCellLimit : Program → Nat
  | .code ops => (ops.map (fun op => match op with
      | .constant _ expr => expressionCellLimit expr
      | .literal _ => 0)).foldl max 0
  | .append left right => max (programCellLimit left) (programCellLimit right)
  | .repeat counter bound body =>
      max (counter + 1) (max (expressionCellLimit bound) (programCellLimit body))

def programInputLimit : Program → Nat
  | .code ops => (ops.map (fun op => match op with
      | .constant _ expr => expressionInputLimit expr
      | .literal _ => 0)).foldl max 0
  | .append left right => max (programInputLimit left) (programInputLimit right)
  | .repeat _ bound body => max (expressionInputLimit bound) (programInputLimit body)

#reduce (programExpressionSize fullBuild, programRepeatDepth fullBuild,
  programCellLimit fullBuild, programInputLimit fullBuild)

theorem fullBuild_expression_room : programExpressionSize fullBuild ≤ 384 := by decide
theorem fullBuild_repeat_room : programRepeatDepth fullBuild ≤ 32 := by decide
theorem fullBuild_cell_room : programCellLimit fullBuild ≤ 22 := by decide
theorem fullBuild_input_room : programInputLimit fullBuild ≤ 3 := by decide

def prepareControlBase (packed D : Nat) : Nat := 4 + packed + 4096 * D
def prepareCacheBase (packed D : Nat) : Nat := prepareControlBase packed D + 512
def prepareHeapWords (packed D : Nat) : Nat := 4 + packed + 8192 * D

theorem prepare_cache_room (M t : Nat) (hM : 2 ≤ M) (ht : 1 ≤ t) :
    512 + 16 + 8 * M + 8192 < 4096 * (M + t) := by omega

theorem prepare_cache_allocated (packed M t : Nat) (hM : 2 ≤ M) (ht : 1 ≤ t) :
    prepareCacheBase packed (M + t) + (16 + 8 * M + 8192) <
      prepareHeapWords packed (M + t) := by
  have hr := prepare_cache_room M t hM ht
  change (4 + packed + 4096 * (M + t) + 512) + (16 + 8 * M + 8192) <
    4 + packed + 8192 * (M + t)
  calc
    _ = (4 + packed) + (4096 * (M + t) + (512 + 16 + 8 * M + 8192)) := by ac_rfl
    _ < (4 + packed) + (4096 * (M + t) + 4096 * (M + t)) :=
      Nat.add_lt_add_left (Nat.add_lt_add_left hr _) _
    _ = _ := by rw [← Nat.add_mul]

theorem prepare_control_allocated (packed M t offset : Nat) (hM : 2 ≤ M)
    (ht : 1 ≤ t) (ho : offset < 512) :
    prepareControlBase packed (M + t) + offset < prepareHeapWords packed (M + t) := by
  unfold prepareControlBase prepareHeapWords
  omega

theorem prepare_banks_disjoint (packed D offset : Nat) (ho : offset < 512) :
    prepareControlBase packed D + offset < prepareCacheBase packed D := by
  unfold prepareCacheBase
  omega

end PaperProofs.Structure.LaminarTree.PSTRBuildLower
