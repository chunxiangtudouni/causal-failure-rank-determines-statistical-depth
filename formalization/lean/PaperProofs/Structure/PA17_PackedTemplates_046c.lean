module
public import PaperProofs.Structure.PA17_PackedTemplates_046b
public import PaperProofs.Structure.PA17_UniformGenerator_035e

/-! Whole retained-AST physical lowering. Original lexical loops are emitted
by the fixed generator, and each original opcode uses the exact translator. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17PackedTemplates046

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PackedCapacityRAM
open PA17UniformGenerator035b PA17UniformGenerator035d PA17ProgramTemplates041
local instance pa17OfNat046c (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add046c : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance pa17Sub046c : HSub Expr Expr Expr := ⟨.binary .subtract⟩
local instance pa17Mul046c : HMul Expr Expr Expr := ⟨.binary .multiply⟩

def packedWords (capacity : Expr) : Expr :=
  .binary .divide (capacity * .cell 1 + .cell 2 - 1) (.cell 2)
def spill (capacity indices : Expr) : Expr := packedWords capacity + indices

theorem packedWords_eval (capacity : Expr) (rom : PhysicalROM) (environment : Nat → Nat) (q bits : Nat)
    (hw : environment 1 = CapacityBits.width q) (hb : environment 2 = bits) :
    (packedWords capacity).eval rom environment = packedCapacityWords q (capacity.eval rom environment) bits := by
  change (capacity.eval rom environment * environment 1 + environment 2 - 1) / environment 2 = _
  rw [hw, hb]
  rfl

def lowerBody (capacity indices : Expr) : Program → Template
  | .code ops => blockTemplate (ops.flatMap (translateOp (.cell 1) (.cell 2) capacity (packedWords capacity) (spill capacity indices)))
  | .append left right => .append (lowerBody capacity indices left) (lowerBody capacity indices right)
  | .repeat counter bound body => .repeat counter bound (lowerBody capacity indices body)

theorem wellScoped_countersAvoid (template : Template) (scope : Finset Nat) (cursor : Nat)
    (hscope : template.WellScoped scope) (hcursor : cursor ∈ scope) :
    PA17UniformGenerator035e.CountersAvoid cursor template := by
  induction template generalizing scope with
  | empty => trivial
  | word _ => trivial
  | append left right ihl ihr => exact ⟨ihl scope hscope.1 hcursor, ihr scope hscope.2 hcursor⟩
  | «repeat» counter bound body ih =>
    exact ⟨fun he => hscope.1 (he ▸ hcursor), ih _ hscope.2.2 (Finset.mem_insert_of_mem hcursor)⟩

theorem lowerBody_denote (program : Program) (capacity indices : Expr)
    (hc : capacity.cells = ∅) (hi : indices.cells = ∅)
    (h1 : PA17UniformGenerator035e.CountersAvoid 1 program.toTemplate)
    (h2 : PA17UniformGenerator035e.CountersAvoid 2 program.toTemplate)
    (rom : PhysicalROM) (environment : Nat → Nat) (q bits : Nat)
    (hw : environment 1 = CapacityBits.width q) (hb : environment 2 = bits)
    (hwidth : 0 < CapacityBits.width q) (hbits : 0 < bits) :
    (lowerBody capacity indices program).denote rom environment =
      bodyWords ((program.eval rom environment).flatMap
        (PA17PackedTranslator034.translateOp q bits (capacity.eval rom environment)
          (packedCapacityWords q (capacity.eval rom environment) bits + indices.eval rom environment))) := by
  induction program generalizing environment with
  | code ops =>
    rw [lowerBody, blockTemplate_denote]
    congr 1
    simp only [evalBlock, List.map_flatMap, Program.eval, instructions, List.flatMap_map]
    apply List.flatMap_congr
    intro op _
    change evalBlock rom environment (translateOp (.cell 1) (.cell 2) capacity (packedWords capacity) (spill capacity indices) op) = _
    rw [translateOp_eval (.cell 1) (.cell 2) capacity (packedWords capacity) (spill capacity indices)
      op rom environment q bits hw hb (by simpa only [Expr.eval, hw] using hwidth)
      (by simpa only [Expr.eval, hb] using hbits)
      (packedWords_eval capacity rom environment q bits hw hb)]
    rw [show (spill capacity indices).eval rom environment =
        packedCapacityWords q (capacity.eval rom environment) bits + indices.eval rom environment from by
      change (packedWords capacity).eval rom environment + _ = _
      rw [packedWords_eval capacity rom environment q bits hw hb]]
  | append left right ihl ihr =>
    simp only [lowerBody, Template.denote, Program.eval, List.flatMap_append, bodyWords, List.flatMap_append]
    exact congrArg₂ List.append (ihl h1.1 h2.1 environment hw hb) (ihr h1.2 h2.2 environment hw hb)
  | «repeat» counter bound body ih =>
    simp only [lowerBody, Template.denote, Program.eval, bodyWords, List.flatMap_assoc]
    apply List.flatMap_congr
    intro index _
    have hw' : (Function.update environment counter (index + 1)) 1 = CapacityBits.width q := by
      rw [Function.update_of_ne h1.1.symm]
      exact hw
    have hb' : (Function.update environment counter (index + 1)) 2 = bits := by
      rw [Function.update_of_ne h2.1.symm]
      exact hb
    have hcap := eval_update_of_not_mem capacity rom environment counter (index + 1) (by simp [hc])
    have hind := eval_update_of_not_mem indices rom environment counter (index + 1) (by simp [hi])
    simpa only [bodyWords, List.flatMap_assoc, hcap, hind] using ih h1.2 h2.2 (Function.update environment counter (index + 1)) hw' hb'

end PaperProofs.Structure.LaminarTree.PA17PackedTemplates046
