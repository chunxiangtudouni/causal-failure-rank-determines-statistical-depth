module
public import PaperProofs.Structure.PA17_PackedTemplates_046c

/-! The full physical code template includes real spill initialization,
the exact body translator, answer restoration, final wipe and encoded HALT. -/
@[expose] public section
set_option maxRecDepth 20000
namespace PaperProofs.Structure.LaminarTree.PA17PackedTemplates046

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM
open PA17UniformGenerator035b PA17UniformGenerator035d PA17ProgramTemplates041
local instance pa17OfNat046d (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add046d : HAdd Expr Expr Expr := ⟨.binary .add⟩

def wipe (spill : Expr) : List PhysicalExpr :=
  [constant .flag 0] ++ (List.range 7).flatMap (fun index =>
    [constant .total (spill + .constant index), ordinary (.base (.storeHeap .total .flag))]) ++
      [constant .total 0]

theorem wipe_eval (spill : Expr) (rom : PhysicalROM) (environment : Nat → Nat) :
    evalBlock rom environment (wipe spill) = PA17PackedTranslator034.physicalWipe (spill.eval rom environment) := by
  rfl

def restore (spill : Expr) : List PhysicalExpr :=
  PA17PackedTranslator034.restoredRegisters.flatMap (fun register => loadReg spill register register)

theorem restore_eval (spill : Expr) (rom : PhysicalROM) (environment : Nat → Nat) :
    evalBlock rom environment (restore spill) = PA17PackedTranslator034.restore (spill.eval rom environment) := by
  rfl

def packedTemplate (capacity indices : Expr) (body : Program) : Template :=
  .append (blockTemplate (wipe (spill capacity indices)))
    (.append (lowerBody capacity indices body)
      (.append (blockTemplate (restore (spill capacity indices)))
        (.append (blockTemplate (wipe (spill capacity indices))) (Template.literal haltWords.toArray.toList))))

theorem packedTemplate_denote (body : Program) (capacity indices : Expr)
    (hc : capacity.cells = ∅) (hi : indices.cells = ∅)
    (h1 : PA17UniformGenerator035e.CountersAvoid 1 body.toTemplate)
    (h2 : PA17UniformGenerator035e.CountersAvoid 2 body.toTemplate)
    (rom : PhysicalROM) (environment : Nat → Nat) (q bits : Nat)
    (hw : environment 1 = CapacityBits.width q) (hb : environment 2 = bits)
    (hwidth : 0 < CapacityBits.width q) (hbits : 0 < bits) :
    (packedTemplate capacity indices body).denote rom environment =
      packingCode (PA17PackedTranslator034.packedProgram q bits (capacity.eval rom environment)
        (indices.eval rom environment) (body.eval rom environment)) := by
  simp only [packedTemplate, Template.denote, Template.denote_literal,
    blockTemplate_denote, wipe_eval, restore_eval]
  rw [lowerBody_denote body capacity indices hc hi h1 h2 rom environment q bits hw hb hwidth hbits]
  have hs : (spill capacity indices).eval rom environment =
      PA17PackedTranslator034.physicalSpillBase q bits (capacity.eval rom environment) (indices.eval rom environment) := by
    change (packedWords capacity).eval rom environment + _ = _
    rw [packedWords_eval capacity rom environment q bits hw hb]
    rfl
  rw [hs]
  simp only [PA17PackedTranslator034.packedProgram, packingCode, bodyWords, List.flatMap_append,
    PA17PackedTranslator034.physicalSpillBase, List.append_assoc]

end PaperProofs.Structure.LaminarTree.PA17PackedTemplates046
