module

public import PaperProofs.Structure.PA17_UniformGenerator_035ah
public import PaperProofs.Structure.PA17_GeneratorStatic_048c
public import PaperProofs.Structure.PA17_GeneratorStatic_048d
public import PaperProofs.Structure.PA17_GenerationBounds_047c
public import PaperProofs.Structure.PA17_QueryTemplates_044o

/-! The original uniform six-program generation claim. The witness is one
fixed finite ISA list, independent of the runtime dimensions. Its only ROM
is [N,q,t]; all output, branching, length measurement and copying execute.
-/

@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035ai

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  PA17UniformGenerator035d PA17UniformGenerator035e PA17UniformGenerator035ac

theorem fixed_generator_wordsFit64 :
    WordsFit 64 (packingCode PA17GeneratorStatic048.generator) := by
  have hchecked := PA17GeneratorStatic048.six_checked 0 1 1 64 0
    (by decide) (by decide) (by decide)
  have h64 : indexWidth 32 0 1 = 64 := by decide
  rw [h64] at hchecked
  apply PA17QueryTemplates044o.generator_packingCode_fits PA17PackedTemplates046.templates
    (PA17Generator.dimensionROM 0 1 1) (PA17UniformGenerator035ae.preparedEnv 0 1)
    (2 ^ 64 - 1) 64 64 (by decide) (PA17GeneratorStatic048.maxWord_fits 64)
    (fun template ht => (PA17PackedTemplates046.templates_static template ht).2.1)
    (fun template ht => (PA17PackedTemplates046.templates_static template ht).2.2.1)
    hchecked
  rw [PA17UniformGenerator035ae.generator_length]
  have hh := PA17GeneratorStatic048.fixedStreamLength_le
  have hlarge : 5 * (4294967296 + 63) ≤ 2 ^ 64 - 1 := by decide
  omega

theorem uniformCodeGenerationClaims :
    UniformCodeGenerationClaims PA17GenerationBounds047.generationConstant 32
      PA17WrappedNatRAM038a.implementation PA17PackedPhase045.programs := by
  refine ⟨PA17GeneratorStatic048.generator, ?_⟩
  intro N q t hq ht hu
  let bits := indexWidth 32 N q
  let B := 2 ^ bits - 1
  let heapWords := PA17GenerationBounds047.generatorHeapWords N q t
  let steps := PA17UniformGenerator035ae.stepsBeforeHalt PA17PackedTemplates046.templates N q t + 1
  have hbounds := PA17GenerationBounds047.generator_bounds N q t
    (streamLength 64 PA17PackedTemplates046.templates) hq ht hu
    PA17GeneratorStatic048.fixedStreamLength_le
  have hwords : streamWords (PA17Generator.dimensionROM N q t)
      (PA17UniformGenerator035ae.preparedEnv N q) 3 0 PA17PackedTemplates046.templates =
      generatedCode PA17WrappedNatRAM038a.implementation PA17PackedPhase045.programs N q t :=
    PA17GeneratorStatic048.six_output N q t 0 hq
  have hchecked := PA17GeneratorStatic048.six_checked N q t heapWords 0 hq hu hbounds.reserve
  have hcode : WordsFit bits (packingCode PA17GeneratorStatic048.generator) :=
    PA17GeneratorStatic048.wordsFit_mono64 _ N q hq fixed_generator_wordsFit64
  have hpc : 5 * (PA17UniformGenerator035ae.generator PA17PackedTemplates046.templates).length ≤ B := by
    rw [PA17UniformGenerator035ae.generator_length]
    exact hbounds.pc
  have houtB : 1024 + (streamWords (PA17Generator.dimensionROM N q t)
      (PA17UniformGenerator035ae.preparedEnv N q) 3 0 PA17PackedTemplates046.templates).length + 1 ≤ B := by
    rw [hwords]
    exact hbounds.output_end
  have houtH : 1024 + (streamWords (PA17Generator.dimensionROM N q t)
      (PA17UniformGenerator035ae.preparedEnv N q) 3 0 PA17PackedTemplates046.templates).length + 1 ≤ heapWords := by
    rw [hwords]
    dsimp only [heapWords, PA17GenerationBounds047.generatorHeapWords, PA17GenerationBounds047.targetLength]
    omega
  have hrun := PA17UniformGenerator035ah.generator_word PA17PackedTemplates046.templates N q t B heapWords bits
    (fun template hm => (PA17PackedTemplates046.templates_static template hm).1)
    (fun template hm => (PA17PackedTemplates046.templates_static template hm).2.1)
    (fun template hm => (PA17PackedTemplates046.templates_static template hm).2.2.1)
    (fun template hm => (PA17PackedTemplates046.templates_static template hm).2.2.2.2)
    hchecked (PA17GeneratorStatic048.input_le_maxWord N q t hq hu)
    (PA17GeneratorStatic048.bits_le_maxWord N q t hq hu) hpc houtB houtH
    (PA17GeneratorStatic048.maxWord_fits bits) hcode
  dsimp only at hrun
  rw [hwords] at hrun
  refine ⟨steps, heapWords, hcode, hbounds.input, ?_, hbounds.target, hrun.1, hrun.2.1, hrun.2.2, ?_⟩
  · have hh := hbounds.footprint
    simpa only [PA17GeneratorStatic048.generator, packingCode_length,
      PA17UniformGenerator035ae.generator_length, PhysicalROM.size, List.length_cons,
      List.length_nil, Nat.add_zero] using hh
  · have htrace := PA17UniformGenerator035ae.generator_trace_le PA17PackedTemplates046.templates N q t bits
      (PA17GeneratorStatic048.six_productive N q t 0 ht)
    rw [hwords] at htrace
    have htotal := PA17GenerationBounds047.generator_total_envelope_le N q t
      (streamLength 64 PA17PackedTemplates046.templates)
      (PA17UniformGenerator035ae.streamFactor 64 PA17PackedTemplates046.templates) ht
      PA17GeneratorStatic048.fixedStreamLength_le PA17GeneratorStatic048.fixedStreamFactor_le
    have hlength : (packingCode PA17GeneratorStatic048.generator).length =
        5 * (streamLength 64 PA17PackedTemplates046.templates + 63) + 5 := by
      rw [packingCode_length, PA17GeneratorStatic048.generator, PA17UniformGenerator035ae.generator_length]
    simpa only [steps, heapWords, PA17GenerationBounds047.targetLength, PA17GeneratorStatic048.generator,
      PA17Generator.dimensionROM, PhysicalROM.size, List.length_cons, List.length_nil, Nat.add_zero,
      hlength] using (Nat.add_le_add_left htrace
        (3 + (packingCode PA17GeneratorStatic048.generator).length + heapWords + 8)).trans
          (by simpa only [hlength, heapWords, PA17GenerationBounds047.targetLength] using htotal)

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035ai
