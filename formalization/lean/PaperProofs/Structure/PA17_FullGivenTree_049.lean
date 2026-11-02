module
public import PaperProofs.Structure.PA17_UniformGenerator_035ai
public import PaperProofs.Structure.PA17_ConstantBounds_040
public import PaperProofs.Structure.PA17_WrappedNatRAM_038c
public import PaperProofs.Structure.PA17_PackedPhase_045f

/-! Original A17 assembly for the same actual spill-wrapped implementation.
Both the fixed six-code generator and all physical phases are substantive
proved inputs; no runtime, code, trace or query-scratch oracle is assumed. -/
@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA17FullGivenTree049

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def constant : Nat := PA17GenerationBounds047.generationConstant

theorem natClaims : NatRAMImplementationClaims constant 32 PA17WrappedNatRAM038a.implementation :=
  PA17ConstantBounds040.natRAMImplementationClaims_mono PA17WrappedNatRAM038a.constant constant 32
    (by decide) PA17WrappedNatRAM038a.implementation PA17WrappedNatRAM038c.implementation_claims

theorem packedClaims : PackedImplementationClaims constant 32 PA17WrappedNatRAM038a.implementation := by
  refine ⟨PA17PackedPhase045.programs, PA17UniformGenerator035ai.uniformCodeGenerationClaims, ?_⟩
  intro q full hq hlaminar
  obtain ⟨hbuild, hrolling, hquery⟩ := PA17PackedPhase045.three_phases q full hq hlaminar
  have hc : 512 ≤ constant := by decide
  refine ⟨PA17ConstantBounds040.packedPhaseRefines_mono 512 constant 32 _ _ _ _ _ hc _ _ _ _ hbuild, ?_, ?_⟩
  · intro used
    exact PA17ConstantBounds040.packedPhaseRefines_mono 512 constant 32 _ _ _ _ _ hc _ _ _ _ (hrolling used)
  · intro heap
    dsimp only
    intro htable hcapacity stage used
    exact PA17ConstantBounds040.packedPhaseRefines_mono 512 constant 32 _ _ _ _ _ hc _ _ _ _
      (hquery heap htable hcapacity stage used)

theorem fullGivenTreeClaims : AlgorithmClaims.FullGivenTreeClaims :=
  ⟨constant, 32, PA17WrappedNatRAM038a.implementation,
    PA17GenerationBounds047.generationConstant_pos, by decide, natClaims, packedClaims⟩

end PaperProofs.Structure.LaminarTree.PA17FullGivenTree049
