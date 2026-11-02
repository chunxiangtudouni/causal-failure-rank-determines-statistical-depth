module
public import PaperProofs.Structure.PA17_PackedTemplates_046d
public import PaperProofs.Structure.PA17_ProgramTemplates_041n
public import PaperProofs.Structure.PA17_QueryTemplates_044g
public import PaperProofs.Structure.PA17_PackingBounds_043

/-! The three concrete physical code templates for the same original038
implementation. Only the real dimension prelude's width/bits cells are read. -/
@[expose] public section
set_option maxRecDepth 20000
namespace PaperProofs.Structure.LaminarTree.PA17PackedTemplates046

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM
open PA17UniformGenerator035b PA17UniformGenerator035d PA17ProgramTemplates041
local instance pa17OfNat046e (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add046e : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance pa17Mul046e : HMul Expr Expr Expr := ⟨.binary .multiply⟩

def fullIndices : Expr := 6 * tDim + nDim + 2 * qDim + 24
def rollingIndices : Expr := 4 * tDim + 2 * qDim + 7

theorem fullIndices_cells : fullIndices.cells = ∅ := by simp [fullIndices, Expr.cells, nDim, qDim, tDim]
theorem rollingIndices_cells : rollingIndices.cells = ∅ := by simp [rollingIndices, Expr.cells, qDim, tDim]

theorem fullIndices_eval (N q t : Nat) (environment : Nat → Nat) :
    fullIndices.eval (dimensionROM N q t) environment = PA17QueryLayout014.indexWords N q t := rfl

theorem rollingIndices_eval (N q t : Nat) (environment : Nat → Nat) :
    rollingIndices.eval (dimensionROM N q t) environment = PA17Rolling018B.indexWords q t := rfl

theorem rawFull_scoped : fullBuild.toTemplate.WellScoped (insert 3 {1, 2}) := full_parentScoped.2.1.2.1
theorem rawRolling_scoped : rollingProgram.toTemplate.WellScoped (insert 3 {1, 2}) := rolling_parentScoped.2.1.2.1
theorem rawQuery_scoped : PA17QueryTemplates044f.queryProgram.toTemplate.WellScoped (insert 3 {1, 2}) :=
  PA17QueryTemplates044g.query_parentScoped.2.1

def full : Template := packedTemplate fullCapacity fullIndices fullBuild
def query : Template := packedTemplate fullCapacity fullIndices PA17QueryTemplates044f.queryProgram
def rolling : Template := packedTemplate rollingCapacity rollingIndices rollingProgram

theorem width_pos (q : Nat) (hq : 0 < q) : 0 < CapacityBits.width q :=
  Nat.clog_pos (by decide) (by omega)

theorem full_denote (N q t : Nat) (hq : 0 < q) (environment : Nat → Nat)
    (hw : environment 1 = CapacityBits.width q) (hb : environment 2 = indexWidth 32 N q) :
    full.denote (dimensionROM N q t) environment =
      packingCode (PA17PackedTranslator034.packedProgram q (indexWidth 32 N q)
        (PA17QueryLayout014.capacityWords N q t) (PA17QueryLayout014.indexWords N q t)
        (PA17TableBuild005.buildProgram N q t)) := by
  have h1 := wellScoped_countersAvoid _ _ 1 rawFull_scoped (by decide)
  have h2 := wellScoped_countersAvoid _ _ 2 rawFull_scoped (by decide)
  simpa only [full, fullCapacity_eval, fullIndices_eval, fullBuild_eval, PA17QueryLayout014.capacityWords] using
    packedTemplate_denote fullBuild fullCapacity fullIndices fullCapacity_cells fullIndices_cells h1 h2
      (dimensionROM N q t) environment q (indexWidth 32 N q) hw hb (width_pos q hq) (PA17PackingBounds043.bits_pos N q)

theorem query_denote (N q t : Nat) (hq : 0 < q) (environment : Nat → Nat)
    (hw : environment 1 = CapacityBits.width q) (hb : environment 2 = indexWidth 32 N q) :
    query.denote (dimensionROM N q t) environment =
      packingCode (PA17PackedTranslator034.packedProgram q (indexWidth 32 N q)
        (PA17QueryLayout014.capacityWords N q t) (PA17QueryLayout014.indexWords N q t)
        (PA17Query019.program N q t)) := by
  have h1 := wellScoped_countersAvoid _ _ 1 rawQuery_scoped (by decide)
  have h2 := wellScoped_countersAvoid _ _ 2 rawQuery_scoped (by decide)
  simpa only [query, fullCapacity_eval, fullIndices_eval, PA17QueryTemplates044f.queryProgram_eval,
    PA17QueryLayout014.capacityWords] using
    packedTemplate_denote PA17QueryTemplates044f.queryProgram fullCapacity fullIndices fullCapacity_cells fullIndices_cells h1 h2
      (dimensionROM N q t) environment q (indexWidth 32 N q) hw hb (width_pos q hq) (PA17PackingBounds043.bits_pos N q)

theorem rolling_denote (N q t : Nat) (hq : 0 < q) (environment : Nat → Nat)
    (hw : environment 1 = CapacityBits.width q) (hb : environment 2 = indexWidth 32 N q) :
    rolling.denote (dimensionROM N q t) environment =
      packingCode (PA17PackedTranslator034.packedProgram q (indexWidth 32 N q)
        (PA17Rolling018.capacityWords q t) (PA17Rolling018B.indexWords q t)
        (PA17Rolling018B.program N q t)) := by
  have h1 := wellScoped_countersAvoid _ _ 1 rawRolling_scoped (by decide)
  have h2 := wellScoped_countersAvoid _ _ 2 rawRolling_scoped (by decide)
  have hc : rollingCapacity.eval (dimensionROM N q t) environment = PA17Rolling018.capacityWords q t := rfl
  simpa only [rolling, hc, rollingIndices_eval, rollingProgram_eval] using
    packedTemplate_denote rollingProgram rollingCapacity rollingIndices rollingCapacity_cells rollingIndices_cells h1 h2
      (dimensionROM N q t) environment q (indexWidth 32 N q) hw hb (width_pos q hq) (PA17PackingBounds043.bits_pos N q)

end PaperProofs.Structure.LaminarTree.PA17PackedTemplates046
