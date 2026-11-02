module

import Structure.PA17_FullGivenTree_049

open PaperProofs.Structure.LaminarTree

example : AlgorithmClaims.FullGivenTreeClaims :=
  PA17FullGivenTree049.fullGivenTreeClaims

example : AlgorithmClaims.UniformCodeGenerationClaims
    PA17GenerationBounds047.generationConstant 32
    PA17WrappedNatRAM038a.implementation PA17PackedPhase045.programs :=
  PA17UniformGenerator035ai.uniformCodeGenerationClaims
