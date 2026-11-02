module
public import PaperProofs.Structure.PA17_GeneratorStatic_048a
public import PaperProofs.Structure.PA17_PackedTemplates_046k
public import PaperProofs.Structure.PA17_UniformGenerator_035ae

/-! The one actual six-program generator has fixed finite code and fixed
stream-clock factors, before any runtime N,q,t or tree data is supplied. -/
@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace PaperProofs.Structure.LaminarTree.PA17GeneratorStatic048

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open PA17UniformGenerator035b PA17UniformGenerator035d PA17UniformGenerator035n

def generator : List PackingOp := PA17UniformGenerator035ae.generator PA17PackedTemplates046.templates

theorem fixedCodeBound : codeSumBound PA17PackedTemplates046.templates ≤ 4294967296 := by decide
theorem fixedFactorBound : factorSumBound PA17PackedTemplates046.templates ≤ 4294967296 := by decide

theorem fixedStreamLength_le :
    PA17UniformGenerator035ac.streamLength 64 PA17PackedTemplates046.templates ≤ 4294967296 :=
  (streamLength_le_bound _ 64).trans fixedCodeBound

theorem streamFactor_eq_sum (templates : List Template) (stack : Nat) :
    PA17UniformGenerator035ae.streamFactor stack templates =
      (templates.map (fun template => factor stack template + 23)).sum := by
  induction templates with
  | nil => rfl
  | cons first later ih =>
    simp only [PA17UniformGenerator035ae.streamFactor, List.map_cons, List.sum_cons, ih]

theorem fixedStreamFactor_le :
    PA17UniformGenerator035ae.streamFactor 64 PA17PackedTemplates046.templates ≤ 4294967296 := by
  rw [streamFactor_eq_sum]
  exact (factorSum_le_bound _ 64).trans fixedFactorBound

theorem generator_length_le : generator.length ≤ 4294967296 + 63 := by
  rw [generator, PA17UniformGenerator035ae.generator_length]
  exact Nat.add_le_add_right fixedStreamLength_le 63

theorem generator_codeLength_le : (packingCode generator).length ≤ 5 * (4294967296 + 63) + 5 := by
  rw [packingCode_length]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 5 generator_length_le) 5

end PaperProofs.Structure.LaminarTree.PA17GeneratorStatic048
