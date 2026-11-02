module
public import PaperProofs.Structure.PA17_PackedTemplates_046a

/-! Exact physical macro templates and lowering of each retained logical
opcode. The heap operations lower to the real read32/write87 translation. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17PackedTemplates046

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM
open PA17UniformGenerator035b PA17UniformGenerator035d PA17ProgramTemplates041
local instance pa17OfNat046b (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add046b : HAdd Expr Expr Expr := ⟨.binary .add⟩

theorem evalBlock_append (left right : List PhysicalExpr) (rom : PhysicalROM) (environment : Nat → Nat) :
    evalBlock rom environment (left ++ right) = evalBlock rom environment left ++ evalBlock rom environment right :=
  List.map_append

def loadReg (spill : Expr) (source target : Register) : List PhysicalExpr :=
  [constant .total (spill + .constant source.word), ordinary (.base (.loadHeap target .total))]

def saveReg (spill : Expr) (target : Register) : List PhysicalExpr :=
  [constant .total (spill + .constant target.word), ordinary (.base (.storeHeap .total .value))]

theorem loadReg_eval (spill : Expr) (source target : Register) (rom : PhysicalROM) (environment : Nat → Nat) :
    evalBlock rom environment (loadReg spill source target) =
      PA17PackedTranslator034.loadReg (spill.eval rom environment) source target := by
  rfl

theorem saveReg_eval (spill : Expr) (target : Register) (rom : PhysicalROM) (environment : Nat → Nat) :
    evalBlock rom environment (saveReg spill target) =
      PA17PackedTranslator034.saveReg (spill.eval rom environment) target := by
  rfl

def capAddress (capacity spill : Expr) (pointer : Register) : List PhysicalExpr :=
  loadReg spill pointer .address ++
    [constant .total capacity, ordinary (.subtract .flag .total .address),
      constant .fresh 0, ordinary (.base (.select .address .flag .address .fresh))]

theorem capAddress_eval (capacity spill : Expr) (pointer : Register) (rom : PhysicalROM) (environment : Nat → Nat) :
    evalBlock rom environment (capAddress capacity spill pointer) =
      PA17PackedTranslator034.capAddress (capacity.eval rom environment) (spill.eval rom environment) pointer := by
  rw [capAddress, evalBlock_append, loadReg_eval]
  rfl

def indexAddress (capacity packedWords spill : Expr) (pointer : Register) : List PhysicalExpr :=
  loadReg spill pointer .address ++
    [constant .total capacity, ordinary (.subtract .fresh .address .total),
      constant .old packedWords, ordinary (.base (.add .index .old .fresh))]

theorem indexAddress_eval (capacity packedWords spill : Expr) (pointer : Register)
    (rom : PhysicalROM) (environment : Nat → Nat) (q bits : Nat)
    (hp : packedWords.eval rom environment = packedCapacityWords q (capacity.eval rom environment) bits) :
    evalBlock rom environment (indexAddress capacity packedWords spill pointer) =
      PA17PackedTranslator034.indexAddress q bits (capacity.eval rom environment) (spill.eval rom environment) pointer := by
  rw [indexAddress, evalBlock_append, loadReg_eval]
  simp only [evalBlock, List.map_cons, List.map_nil, constant, ordinary, PhysicalExpr.eval, OpExpr.eval, hp]
  rfl

def readMacro (width bits capacity packedWords spill : Expr) (target pointer : Register) : List PhysicalExpr :=
  capAddress capacity spill pointer ++ read width bits ++ indexAddress capacity packedWords spill pointer ++
    [ordinary (.base (.loadHeap .fresh .index)), ordinary (.base (.select .value .flag .value .fresh))] ++
    saveReg spill target

theorem readMacro_eval (width bits capacity packedWords spill : Expr) (target pointer : Register)
    (rom : PhysicalROM) (environment : Nat → Nat) (q wordBits : Nat)
    (hw : width.eval rom environment = CapacityBits.width q) (hb : bits.eval rom environment = wordBits)
    (hwidth : 0 < width.eval rom environment)
    (hp : packedWords.eval rom environment = packedCapacityWords q (capacity.eval rom environment) wordBits) :
    evalBlock rom environment (readMacro width bits capacity packedWords spill target pointer) =
      PA17PackedTranslator034.readMacro q wordBits (capacity.eval rom environment) (spill.eval rom environment) target pointer := by
  simp only [readMacro, evalBlock_append, capAddress_eval, read_eval _ _ _ _ _ _ hw hb hwidth,
    indexAddress_eval _ _ _ _ _ _ _ _ hp, saveReg_eval]
  rfl

def writeMacro (width bits capacity packedWords spill : Expr) (pointer source : Register) : List PhysicalExpr :=
  capAddress capacity spill pointer ++ read width bits ++
    loadReg spill source .fresh ++ [ordinary (.base (.select .value .flag .fresh .value))] ++
    safeWrite width bits ++ indexAddress capacity packedWords spill pointer ++
    [ordinary (.subtract .flag .total .address), ordinary (.base (.loadHeap .old .index))] ++
    loadReg spill source .fresh ++
    [ordinary (.base (.select .value .flag .old .fresh)), ordinary (.base (.storeHeap .index .value))]

theorem writeMacro_eval (width bits capacity packedWords spill : Expr) (pointer source : Register)
    (rom : PhysicalROM) (environment : Nat → Nat) (q wordBits : Nat)
    (hw : width.eval rom environment = CapacityBits.width q) (hb : bits.eval rom environment = wordBits)
    (hwidth : 0 < width.eval rom environment) (hbits : 0 < bits.eval rom environment)
    (hp : packedWords.eval rom environment = packedCapacityWords q (capacity.eval rom environment) wordBits) :
    evalBlock rom environment (writeMacro width bits capacity packedWords spill pointer source) =
      PA17PackedTranslator034.writeMacro q wordBits (capacity.eval rom environment) (spill.eval rom environment) pointer source := by
  simp only [writeMacro, evalBlock_append, capAddress_eval, read_eval _ _ _ _ _ _ hw hb hwidth,
    safeWrite_eval _ _ _ _ _ _ hw hb hwidth hbits, indexAddress_eval _ _ _ _ _ _ _ _ hp, loadReg_eval]
  rfl

def translateLiteral (width bits capacity packedWords spill : Expr) : Op → List PhysicalExpr
  | .base (.constant target value) => [constant .value (.constant value)] ++ saveReg spill target
  | .base (.add target left right) => loadReg spill left .old ++ loadReg spill right .fresh ++
      [ordinary (.base (.add .value .old .fresh))] ++ saveReg spill target
  | .base (.minimum target left right) => loadReg spill left .old ++ loadReg spill right .fresh ++
      [ordinary (.base (.minimum .value .old .fresh))] ++ saveReg spill target
  | .base (.select target condition whenTrue whenFalse) => loadReg spill condition .flag ++
      loadReg spill whenTrue .old ++ loadReg spill whenFalse .fresh ++
      [ordinary (.base (.select .value .flag .old .fresh))] ++ saveReg spill target
  | .base (.loadROM region target pointer) => loadReg spill pointer .index ++
      [ordinary (.base (.loadROM region .value .index))] ++ saveReg spill target
  | .base (.loadHeap target pointer) => readMacro width bits capacity packedWords spill target pointer
  | .base (.storeHeap pointer source) => writeMacro width bits capacity packedWords spill pointer source
  | .subtract target left right => loadReg spill left .old ++ loadReg spill right .fresh ++
      [ordinary (.subtract .value .old .fresh)] ++ saveReg spill target

theorem translateLiteral_eval (width bits capacity packedWords spill : Expr) (op : Op)
    (rom : PhysicalROM) (environment : Nat → Nat) (q wordBits : Nat)
    (hw : width.eval rom environment = CapacityBits.width q) (hb : bits.eval rom environment = wordBits)
    (hwidth : 0 < width.eval rom environment) (hbits : 0 < bits.eval rom environment)
    (hp : packedWords.eval rom environment = packedCapacityWords q (capacity.eval rom environment) wordBits) :
    evalBlock rom environment (translateLiteral width bits capacity packedWords spill op) =
      PA17PackedTranslator034.translateOp q wordBits (capacity.eval rom environment) (spill.eval rom environment) op := by
  cases op with
  | base instruction =>
    cases instruction <;>
      simp only [translateLiteral, evalBlock_append, loadReg_eval, saveReg_eval,
        readMacro_eval _ _ _ _ _ _ _ _ _ _ _ hw hb hwidth hp,
        writeMacro_eval _ _ _ _ _ _ _ _ _ _ _ hw hb hwidth hbits hp]
    all_goals rfl
  | subtract target left right =>
    simp only [translateLiteral, evalBlock_append, loadReg_eval, saveReg_eval]
    rfl

def translateOp (width bits capacity packedWords spill : Expr) : OpExpr → List PhysicalExpr
  | .constant target value => [constant .value value] ++ saveReg spill target
  | .literal op => translateLiteral width bits capacity packedWords spill op

theorem translateOp_eval (width bits capacity packedWords spill : Expr) (op : OpExpr)
    (rom : PhysicalROM) (environment : Nat → Nat) (q wordBits : Nat)
    (hw : width.eval rom environment = CapacityBits.width q) (hb : bits.eval rom environment = wordBits)
    (hwidth : 0 < width.eval rom environment) (hbits : 0 < bits.eval rom environment)
    (hp : packedWords.eval rom environment = packedCapacityWords q (capacity.eval rom environment) wordBits) :
    evalBlock rom environment (translateOp width bits capacity packedWords spill op) =
      PA17PackedTranslator034.translateOp q wordBits (capacity.eval rom environment) (spill.eval rom environment)
        (op.eval rom environment) := by
  cases op with
  | constant target value =>
    rw [translateOp, evalBlock_append, saveReg_eval]
    rfl
  | literal op => exact translateLiteral_eval _ _ _ _ _ _ _ _ _ _ hw hb hwidth hbits hp

end PaperProofs.Structure.LaminarTree.PA17PackedTemplates046
