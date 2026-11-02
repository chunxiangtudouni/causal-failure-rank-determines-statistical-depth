module

public import Structure.PSTR_BuildLower_RelativeValue_011
public import Structure.PSTR_BuildLower_LoopControl_012

/-! Direct structured lowering of the one frozen fullBuild typed AST.
Ports below contain code only: no output/performance oracle or caller theorem.
They must be instantiated by the actual A06 backend before a complete execution
claim. PC labels/offsets depend on fixed syntax, never on N,q,t or heap values. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  PA17UniformGenerator035b PA17ProgramTemplates041

variable {bits : Nat}

def relativeCopy (source target : Nat) : List PackingOp :=
  relativeRead source .value ++ relativeWrite target

theorem relativeCopy_length (source target : Nat) : (relativeCopy source target).length = 6 := rfl

theorem relativeCopy_heap (rom : PhysicalROM) (source target : Nat) (state : WordState bits) :
    (executeOps rom (relativeCopy source target) state).heap =
      Function.update state.heap (state.register .address + BitVec.ofNat bits target)
        (state.heap (state.register .address + BitVec.ofNat bits source)) := by
  simp [relativeCopy, relativeRead, relativeWrite, executeOps, packingExecuteOp,
    wordOp, wordInstruction]

theorem relativeCopy_base_prefix (rom : PhysicalROM) (source target : Nat)
    (state : WordState bits) (count : Nat) :
    (executeOps rom ((relativeCopy source target).take count) state).register .address =
      state.register .address := by
  by_cases hc : count ≤ 6
  · interval_cases count <;>
      simp [relativeCopy, relativeRead, relativeWrite, executeOps, packingExecuteOp,
        wordOp, wordInstruction]
  · rw [List.take_of_length_le (by rw [relativeCopy_length]; omega)]
    rfl

/-- All arguments are static labels/ISA register names/ROM-region tags. The
functions contain no input dimension or arbitrary source-program answer. -/
structure BuilderPorts where
  readROM : Nat → Region → Register → List PackingOp
  readHeap : Nat → Register → List PackingOp
  writeHeap : Nat → Register → List PackingOp

def lowerLiteral (ports : BuilderPorts) (start : Nat) : Op → List PackingOp
  | .base (.constant target value) => (ValueOp.constant target value).relativeLower
  | .base (.add target left right) => (ValueOp.add target left right).relativeLower
  | .base (.minimum target left right) => (ValueOp.minimum target left right).relativeLower
  | .base (.select target condition whenTrue whenFalse) =>
      (ValueOp.select target condition whenTrue whenFalse).relativeLower
  | .base (.loadROM region target pointer) =>
      ports.readROM start region pointer ++ relativeWrite (registerOffset target)
  | .base (.loadHeap target pointer) =>
      ports.readHeap start pointer ++ relativeWrite (registerOffset target)
  | .base (.storeHeap pointer source) =>
      relativeRead (registerOffset source) .value ++ ports.writeHeap (start + 3) pointer
  | .subtract target left right => (ValueOp.subtract target left right).relativeLower

def lowerOpExpr (ports : BuilderPorts) (start : Nat) : OpExpr → List PackingOp
  | .constant target value => fixedExprCode value ++ relativeWrite (registerOffset target)
  | .literal op => lowerLiteral ports start op

def lowerOps (ports : BuilderPorts) : List OpExpr → Nat → List PackingOp
  | [], _ => []
  | op :: later, start =>
      let current := lowerOpExpr ports start op
      current ++ lowerOps ports later (start + current.length)

def relativeRepeatPrefix (counter saved : Nat) (bound : Expr) : List PackingOp :=
  relativeCopy counter saved ++ fixedExprCode bound ++ relativeWrite counter

def lowerProgram (ports : BuilderPorts) : Program → Nat → Nat → List PackingOp
  | .code ops, start, _ => lowerOps ports ops start
  | .append left right, start, depth =>
      let first := lowerProgram ports left start depth
      first ++ lowerProgram ports right (start + first.length) depth
  | .repeat counter bound body, start, depth =>
      let physicalCounter := 64 + counter
      let saved := 96 + depth
      let setupCode := relativeRepeatPrefix physicalCounter saved bound
      let loopStart := start + setupCode.length
      let compiledBody := lowerProgram ports body (loopStart + 5) (depth + 1)
      setupCode ++ relativeLoopBlock physicalCounter loopStart compiledBody ++
        relativeCopy saved physicalCounter

/-- Once its actual static A06 ports are supplied, this is ONE fixed code list
selected before every input dimension, incidence schedule, or initialUsed. -/
def fullBuildCode (ports : BuilderPorts) : List PackingOp := lowerProgram ports fullBuild 0 0

theorem lowerOpExpr_dynamic (ports : BuilderPorts) (start : Nat) (target : Register) (value : Expr) :
    lowerOpExpr ports start (.constant target value) =
      fixedExprCode value ++ relativeWrite (registerOffset target) := rfl

theorem relativeRepeatPrefix_length (counter saved : Nat) (bound : Expr) :
    (relativeRepeatPrefix counter saved bound).length = (fixedExprCode bound).length + 9 := by
  simp only [relativeRepeatPrefix, List.length_append, relativeCopy_length, relativeWrite_length]
  omega

end PaperProofs.Structure.LaminarTree.PSTRBuildLower

