module
public import PaperProofs.Structure.PA17_ProgramTemplates_041b
import Mathlib.Data.List.Range

/-! Exact ascending/descending source-loop order under the fixed generator's
actual countdown controller. These lemmas connect finite opcode templates
to the original unrolled program families, including reverse schedules. -/
@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d

theorem reverse_range_eq_map (count : Nat) :
    (List.range count).reverse = (List.range count).map (fun index => count - 1 - index) := by
  simpa only [← List.range_eq_range', Nat.zero_add] using (List.reverse_range' (s := 0) (n := count))

theorem repeat_eval_ascending (counter : Nat) (bound : Expr) (body : Program)
    (rom : PhysicalROM) (environment : Nat → Nat) (count : Nat) (hbound : bound.eval rom environment = count)
    (block : Nat → List Op)
    (hbody : ∀ index < count, body.eval rom (Function.update environment counter (count - index)) = block index) :
    (Program.repeat counter bound body).eval rom environment = (List.range count).flatMap block := by
  simp only [Program.eval, hbound]
  rw [reverse_range_eq_map, List.flatMap_map]
  apply List.flatMap_congr
  intro index hi
  have hn := List.mem_range.mp hi
  have he : count - 1 - index + 1 = count - index := by omega
  rw [he]
  exact hbody index hn

theorem repeat_eval_descending (counter : Nat) (bound : Expr) (body : Program)
    (rom : PhysicalROM) (environment : Nat → Nat) (count : Nat) (hbound : bound.eval rom environment = count)
    (block : Nat → List Op)
    (hbody : ∀ index < count, body.eval rom (Function.update environment counter (index + 1)) = block index) :
    (Program.repeat counter bound body).eval rom environment = (List.range count).reverse.flatMap block := by
  simp only [Program.eval, hbound]
  apply List.flatMap_congr
  intro index hi
  exact hbody index (List.mem_range.mp (List.mem_reverse.mp hi))

theorem repeat_eval_replicate (counter : Nat) (bound : Expr) (op : Op)
    (rom : PhysicalROM) (environment : Nat → Nat) (count : Nat) (hbound : bound.eval rom environment = count) :
    (Program.repeat counter bound (.code [.literal op])).eval rom environment = List.replicate count op := by
  simp only [Program.eval, hbound, instructions, OpExpr.eval, List.map_cons, List.map_nil]
  rw [← List.map_eq_flatMap, List.map_const', List.length_reverse, List.length_range]

theorem haltTemplate_of_eval (program : Program) (rom : PhysicalROM) (environment : Nat → Nat)
    (code : List Op) (hprogram : program.eval rom environment = code) :
    program.haltingTemplate.denote rom environment = haltingWords code := by
  rw [Program.haltingTemplate_denote, hprogram]

end PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041
