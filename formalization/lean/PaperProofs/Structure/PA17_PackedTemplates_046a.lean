module
public import PaperProofs.Structure.PA17_ProgramTemplates_041e
public import PaperProofs.Structure.PA17_PackedTranslator_034b

/-! Symbolic physical instructions and the actual scalar access templates.
The mask expression never computes the unrepresentable intermediate 2^bits. -/
@[expose] public section
set_option maxRecDepth 20000
namespace PaperProofs.Structure.LaminarTree.PA17PackedTemplates046

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM
open PA17UniformGenerator035b PA17UniformGenerator035d PA17ProgramTemplates041
local instance pa17OfNat046a (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add046a : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance pa17Sub046a : HSub Expr Expr Expr := ⟨.binary .subtract⟩
local instance pa17Mul046a : HMul Expr Expr Expr := ⟨.binary .multiply⟩

inductive PhysicalExpr where
  | base (op : OpExpr)
  | literal (op : PackingOp)

def PhysicalExpr.eval (rom : PhysicalROM) (environment : Nat → Nat) : PhysicalExpr → PackingOp
  | .base op => .base (op.eval rom environment)
  | .literal op => op

def PhysicalExpr.words : PhysicalExpr → List Expr
  | .base op => op.words
  | .literal op => op.encode.toArray.toList.map Expr.constant

theorem PhysicalExpr.words_eval (op : PhysicalExpr) (rom : PhysicalROM) (environment : Nat → Nat) :
    op.words.map (Expr.eval rom environment) = (op.eval rom environment).encode.toArray.toList := by
  cases op with
  | base op => exact OpExpr.words_eval op rom environment
  | literal op =>
    simp only [PhysicalExpr.words, PhysicalExpr.eval, List.map_map]
    change List.map id _ = _
    exact List.map_id _

def evalBlock (rom : PhysicalROM) (environment : Nat → Nat) (ops : List PhysicalExpr) : List PackingOp :=
  ops.map (PhysicalExpr.eval rom environment)

def blockTemplate (ops : List PhysicalExpr) : Template := Template.words (ops.flatMap PhysicalExpr.words)

theorem blockTemplate_denote (ops : List PhysicalExpr) (rom : PhysicalROM) (environment : Nat → Nat) :
    (blockTemplate ops).denote rom environment = bodyWords (evalBlock rom environment ops) := by
  simp only [blockTemplate, Template.denote_words, List.map_flatMap, bodyWords, evalBlock, List.flatMap_map]
  apply List.flatMap_congr
  intro op _
  exact PhysicalExpr.words_eval op rom environment

def constant (target : Register) (value : Expr) : PhysicalExpr := .base (.constant target value)
def ordinary (op : Op) : PhysicalExpr := .base (.literal op)
def arithmetic (operation : PackingPrimitive) (target left right : Register) : PhysicalExpr :=
  .literal (.arithmetic operation target left right)

def safeMask (width : Expr) : Expr :=
  ((.binary .shiftLeft 1 (width - 1)) - 1) * 2 + 1

theorem safeMask_eval (width : Expr) (rom : PhysicalROM) (environment : Nat → Nat)
    (hpositive : 0 < width.eval rom environment) :
    (safeMask width).eval rom environment = 2 ^ (width.eval rom environment) - 1 := by
  let value := width.eval rom environment
  have hv : 0 < value := hpositive
  have hpred : value - 1 + 1 = value := by omega
  have hpow : 2 ^ value = 2 ^ (value - 1) * 2 := calc
    2 ^ value = 2 ^ (value - 1 + 1) := congrArg (fun exponent => 2 ^ exponent) hpred.symm
    _ = 2 ^ (value - 1) * 2 := Nat.pow_succ _ _
  have hpos := Nat.two_pow_pos (value - 1)
  change (Nat.shiftLeft 1 (value - 1) - 1) * 2 + 1 = _
  change ((1 <<< (value - 1)) - 1) * 2 + 1 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  change (2 ^ (value - 1) - 1) * 2 + 1 = 2 ^ value - 1
  omega

def read (width bits : Expr) : List PhysicalExpr :=
  [constant .total width, arithmetic .multiply .old .address .total,
    constant .total bits, arithmetic .divide .index .old .total,
    arithmetic .multiply .fresh .index .total, ordinary (.subtract .old .old .fresh),
    ordinary (.base (.loadHeap .value .index)), arithmetic .shiftRight .value .value .old,
    constant .fresh 1, ordinary (.base (.add .index .index .fresh)),
    ordinary (.base (.loadHeap .fresh .index)), ordinary (.subtract .old .total .old),
    arithmetic .shiftLeft .fresh .fresh .old, arithmetic .bitOr .value .value .fresh,
    constant .total (safeMask width), arithmetic .bitAnd .value .value .total]

theorem read_eval (width bits : Expr) (rom : PhysicalROM) (environment : Nat → Nat) (q wordBits : Nat)
    (hw : width.eval rom environment = CapacityBits.width q) (hb : bits.eval rom environment = wordBits)
    (hpositive : 0 < width.eval rom environment) :
    evalBlock rom environment (read width bits) = PackedCapacityRAM.readProgram q wordBits := by
  simp only [read, evalBlock, List.map_cons, List.map_nil, PhysicalExpr.eval, constant, ordinary,
    arithmetic, OpExpr.eval, safeMask_eval width rom environment hpositive, hw, hb]
  rfl

def clear (width bits : Expr) : List PhysicalExpr :=
  [constant .total width, arithmetic .multiply .old .address .total,
    constant .total bits, arithmetic .divide .index .old .total,
    arithmetic .multiply .fresh .index .total, ordinary (.subtract .old .old .fresh),
    constant .fresh (safeMask width), arithmetic .shiftLeft .fresh .fresh .old,
    constant .flag (safeMask bits), ordinary (.subtract .fresh .flag .fresh),
    ordinary (.base (.loadHeap .flag .index)), arithmetic .bitAnd .flag .flag .fresh,
    ordinary (.base (.storeHeap .index .flag)), ordinary (.subtract .old .total .old),
    constant .fresh (safeMask width), arithmetic .shiftRight .fresh .fresh .old,
    constant .flag (safeMask bits), ordinary (.subtract .fresh .flag .fresh),
    constant .flag 1, ordinary (.base (.add .index .index .flag)),
    ordinary (.base (.loadHeap .flag .index)), arithmetic .bitAnd .flag .flag .fresh,
    ordinary (.base (.storeHeap .index .flag))]

def directWrite (width bits : Expr) : List PhysicalExpr :=
  [constant .total width, arithmetic .multiply .old .address .total,
    constant .total bits, arithmetic .divide .index .old .total,
    arithmetic .multiply .fresh .index .total, ordinary (.subtract .old .old .fresh),
    constant .fresh (safeMask width), arithmetic .shiftLeft .fresh .fresh .old,
    constant .flag (safeMask bits), ordinary (.subtract .fresh .flag .fresh),
    ordinary (.base (.loadHeap .flag .index)), arithmetic .bitAnd .flag .flag .fresh,
    arithmetic .shiftLeft .fresh .value .old, arithmetic .bitOr .flag .flag .fresh,
    ordinary (.base (.storeHeap .index .flag)), ordinary (.subtract .old .total .old),
    constant .fresh (safeMask width), arithmetic .shiftRight .fresh .fresh .old,
    constant .flag (safeMask bits), ordinary (.subtract .fresh .flag .fresh),
    constant .flag 1, ordinary (.base (.add .index .index .flag)),
    ordinary (.base (.loadHeap .flag .index)), arithmetic .bitAnd .flag .flag .fresh,
    arithmetic .shiftRight .fresh .value .old, arithmetic .bitOr .flag .flag .fresh,
    ordinary (.base (.storeHeap .index .flag))]

theorem clear_eval (width bits : Expr) (rom : PhysicalROM) (environment : Nat → Nat) (q wordBits : Nat)
    (hw : width.eval rom environment = CapacityBits.width q) (hb : bits.eval rom environment = wordBits)
    (hwidth : 0 < width.eval rom environment) (hbits : 0 < bits.eval rom environment) :
    evalBlock rom environment (clear width bits) = PackedCapacityRAM.clearProgram q wordBits := by
  simp only [clear, evalBlock, List.map_cons, List.map_nil, PhysicalExpr.eval, constant, ordinary,
    arithmetic, OpExpr.eval, safeMask_eval width rom environment hwidth, safeMask_eval bits rom environment hbits, hw, hb]
  rfl

theorem directWrite_eval (width bits : Expr) (rom : PhysicalROM) (environment : Nat → Nat) (q wordBits : Nat)
    (hw : width.eval rom environment = CapacityBits.width q) (hb : bits.eval rom environment = wordBits)
    (hwidth : 0 < width.eval rom environment) (hbits : 0 < bits.eval rom environment) :
    evalBlock rom environment (directWrite width bits) = PackedCapacityRAM.directWriteProgram q wordBits := by
  simp only [directWrite, evalBlock, List.map_cons, List.map_nil, PhysicalExpr.eval, constant, ordinary,
    arithmetic, OpExpr.eval, safeMask_eval width rom environment hwidth, safeMask_eval bits rom environment hbits, hw, hb]
  rfl

def safeWrite (width bits : Expr) : List PhysicalExpr := clear width bits ++ directWrite width bits

theorem safeWrite_eval (width bits : Expr) (rom : PhysicalROM) (environment : Nat → Nat) (q wordBits : Nat)
    (hw : width.eval rom environment = CapacityBits.width q) (hb : bits.eval rom environment = wordBits)
    (hwidth : 0 < width.eval rom environment) (hbits : 0 < bits.eval rom environment) :
    evalBlock rom environment (safeWrite width bits) = PackedCapacityRAM.safeWriteProgram q wordBits := by
  rw [safeWrite, evalBlock, List.map_append]
  change evalBlock rom environment (clear width bits) ++ evalBlock rom environment (directWrite width bits) = _
  rw [clear_eval _ _ _ _ _ _ hw hb hwidth hbits, directWrite_eval _ _ _ _ _ _ hw hb hwidth hbits]
  rfl

end PaperProofs.Structure.LaminarTree.PA17PackedTemplates046
