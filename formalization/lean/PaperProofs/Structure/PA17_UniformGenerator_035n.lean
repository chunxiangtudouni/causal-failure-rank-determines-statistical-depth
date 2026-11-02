module

public import PaperProofs.Structure.PA17_UniformGenerator_035f

/-! A syntax-derived generation clock bound. Every repeated body that
actually runs emits at least one word; this charges loop control to real
output, not to a supplied execution trace. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035n

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035c
  PA17UniformGenerator035d PA17UniformGenerator035e

def factor (stack : Nat) : Template → Nat
  | .empty => 1
  | .word expression => (expression.compile stack).length + 8
  | .append left right => factor stack left + factor stack right
  | .repeat _ bound body => (bound.compile stack).length + 2 * factor stack body + 18

def Productive (rom : PhysicalROM) (environment : Nat → Nat) : Template → Prop
  | .empty | .word _ => True
  | .append left right => Productive rom environment left ∧ Productive rom environment right
  | .repeat counter bound body => ∀ index < bound.eval rom environment,
      let updated := Function.update environment counter (index + 1)
      0 < (body.denote rom updated).length ∧ Productive rom updated body

theorem sum_map_le (indexes : List Nat) (left right : Nat → Nat)
    (hs : ∀ index ∈ indexes, left index ≤ right index) :
    (indexes.map left).sum ≤ (indexes.map right).sum := by
  induction indexes with
  | nil => exact le_rfl
  | cons index later ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (hs index List.mem_cons_self) (ih (fun value hm => hs value (List.mem_cons_of_mem _ hm)))

theorem sum_map_scale (indexes : List Nat) (value : Nat → Nat) (scale : Nat) :
    (indexes.map (fun index => scale * value index)).sum = scale * (indexes.map value).sum := by
  induction indexes with
  | nil => simp
  | cons index later ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem clock_le_output (template : Template) (rom : PhysicalROM) (environment : Nat → Nat) (stack : Nat)
    (hp : Productive rom environment template) :
    clock rom environment stack template ≤ factor stack template * ((template.denote rom environment).length + 1) := by
  induction template generalizing environment with
  | empty => simp only [clock, Template.denote, factor, List.length_nil]; omega
  | word expression =>
    simp only [clock, Template.denote, factor, List.length_singleton]
    omega
  | append left right ihl ihr =>
    have hl := ihl environment hp.1
    have hr := ihr environment hp.2
    simp only [clock, Template.denote, factor, List.length_append]
    nlinarith
  | «repeat» counter bound body ih =>
    let indexes := (List.range (bound.eval rom environment)).reverse
    let output := fun index => (body.denote rom (Function.update environment counter (index + 1))).length
    have hterm (index : Nat) (hm : index ∈ indexes) :
        clock rom (Function.update environment counter (index + 1)) stack body + 12 ≤
          (2 * factor stack body + 12) * output index := by
      have hi : index < bound.eval rom environment := List.mem_range.mp (List.mem_reverse.mp hm)
      have hh := hp index hi
      have hc := ih (Function.update environment counter (index + 1)) hh.2
      have hpositive : 0 < output index := hh.1
      change clock rom (Function.update environment counter (index + 1)) stack body ≤ factor stack body * (output index + 1) at hc
      nlinarith
    have hs := sum_map_le indexes
      (fun index => clock rom (Function.update environment counter (index + 1)) stack body + 12)
      (fun index => (2 * factor stack body + 12) * output index) hterm
    rw [sum_map_scale] at hs
    have hlength : (Template.denote rom environment (Template.repeat counter bound body)).length = (indexes.map output).sum := by
      simp only [Template.denote, List.length_flatMap]
      rfl
    change (bound.compile stack).length + 2 +
        (indexes.map (fun index => clock rom (Function.update environment counter (index + 1)) stack body + 12)).sum + 4 ≤ _
    rw [hlength]
    change _ ≤ ((bound.compile stack).length + 2 * factor stack body + 18) * ((indexes.map output).sum + 1)
    nlinarith

theorem compiled_dynamicTrace_le_output (template : Template) (rom : PhysicalROM) (environment : Nat → Nat)
    (stack cursor outputBase start bits : Nat) (left right : List PackingOp) (state : WordState bits)
    (hp : Productive rom environment template) :
    (packingDynamicTrace rom (left ++ template.compile stack cursor outputBase start ++ right)
      (clock rom environment stack template) state).length ≤
      12 * factor stack template * ((template.denote rom environment).length + 1) := by
  have ht := dynamicTrace_length_le rom (left ++ template.compile stack cursor outputBase start ++ right)
    bits (clock rom environment stack template) state
  have hc := clock_le_output template rom environment stack hp
  nlinarith

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035n
