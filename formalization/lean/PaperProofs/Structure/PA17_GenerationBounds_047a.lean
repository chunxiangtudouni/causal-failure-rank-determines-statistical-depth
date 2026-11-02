module

public import PaperProofs.Structure.PA17_PackedPhase_045f

/-! Actual six-program serialization length, depending only on dimensions.
Every length prefix and every terminal HALT is included. No tree, trace,
correctness certificate, or generator output is supplied by the caller. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

namespace PaperProofs.Structure.LaminarTree.PA17GenerationBounds047

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PA17PackedTranslator034 PA17PackedPhase045

def lengthConstant : Nat := 4194304

theorem lengthConstant_pos : 0 < lengthConstant := by decide

theorem queryWork_le_work (N q size : Nat) : queryWork q size ≤ work N q size := by
  have hh := Nat.le_mul_of_pos_left ((q + 1) * size) (show 0 < N + 1 by omega)
  simpa only [queryWork, work, Nat.mul_assoc] using hh

theorem raw_build_code_length_le (N q size : Nat) (hsize : 0 < size) :
    (haltingWords (PA17TableBuild005.buildProgram N q size)).length ≤ 5855 * work N q size := by
  have ht := PA17TableBuild005.buildProgram_trace_le N q size hsize
  have hl := PA17BuildResources006.program_length_le_trace (PA17TableBuild005.buildProgram N q size)
  have hw := (PA17BuildResources006.dimension_le_work N q size hsize).2.2
  rw [List.length_append] at ht
  rw [haltingWords_length]
  omega

theorem raw_query_code_length_le (N q size : Nat) (hsize : 0 < size) :
    (haltingWords (PA17Query019.program N q size)).length ≤ 16384 * work N q size := by
  exact (PA17QueryFootprint025.query_code_length_le N q size hsize).trans
    (Nat.mul_le_mul_left _ (queryWork_le_work N q size))

theorem raw_rolling_code_length_le (N q size : Nat) (hsize : 0 < size) :
    (haltingWords (PA17Rolling018B.program N q size)).length ≤ 12255 * work N q size := by
  have ht := PA17Rolling018B.program_trace_le N q size hsize
  have hl := PA17BuildResources006.program_length_le_trace (PA17Rolling018B.program N q size)
  have hw := (PA17BuildResources006.dimension_le_work N q size hsize).2.2
  rw [haltingWords_length]
  omega

theorem packed_code_length_le_raw (q bits capWords indexWords : Nat) (body : List Op) :
    (packingCode (packedProgram q bits capWords indexWords body)).length ≤
      87 * (haltingWords body).length := by
  have hh := packedProgram_length_le q bits capWords indexWords body
  rw [packingCode_length, haltingWords_length]
  omega

theorem wrapper_packed_pair_length_le (q bits capWords indexWords : Nat) (body : List Op) :
    (haltingWords (logicalProgram (capWords + indexWords) body)).length +
      (packingCode (packedProgram q bits capWords indexWords body)).length ≤
        88 * (haltingWords body).length + 160 := by
  have hp := packed_code_length_le_raw q bits capWords indexWords body
  rw [PA17WrappedNatRAM038a.logicalProgram_code_length]
  omega

theorem generatedCode_length_eq (implementation : Implementation) (packed : PackedPrograms) (N q size : Nat) :
    (generatedCode implementation packed N q size).length =
      (haltingWords (implementation.buildProgram N q size)).length +
      (haltingWords (implementation.queryProgram N q size)).length +
      (haltingWords (implementation.rollingProgram N q size)).length +
      (packingCode (packed.build N q size)).length +
      (packingCode (packed.query N q size)).length +
      (packingCode (packed.rolling N q size)).length + 6 := by
  simp only [generatedCode, List.flatMap_cons, List.flatMap_nil, List.length_append, List.length_cons,
    List.length_nil]
  omega

theorem generatedCode_length_le (N q size : Nat) (hsize : 0 < size) :
    (generatedCode PA17WrappedNatRAM038a.implementation PA17PackedPhase045.programs N q size).length ≤
      lengthConstant * work N q size := by
  have hb := raw_build_code_length_le N q size hsize
  have hq := raw_query_code_length_le N q size hsize
  have hr := raw_rolling_code_length_le N q size hsize
  have pb := wrapper_packed_pair_length_le q (indexWidth 32 N q)
    (PA17QueryLayout014.capacityWords N q size) (PA17QueryLayout014.indexWords N q size)
    (PA17TableBuild005.buildProgram N q size)
  have pq := wrapper_packed_pair_length_le q (indexWidth 32 N q)
    (PA17QueryLayout014.capacityWords N q size) (PA17QueryLayout014.indexWords N q size)
    (PA17Query019.program N q size)
  have pr := wrapper_packed_pair_length_le q (indexWidth 32 N q)
    (PA17Rolling018.capacityWords q size) (PA17Rolling018B.indexWords q size)
    (PA17Rolling018B.program N q size)
  have hw := (PA17BuildResources006.dimension_le_work N q size hsize).2.2
  rw [generatedCode_length_eq]
  change (haltingWords (logicalProgram _ _)).length + (haltingWords (logicalProgram _ _)).length +
    (haltingWords (logicalProgram _ _)).length + (packingCode (packedProgram _ _ _ _ _)).length +
    (packingCode (packedProgram _ _ _ _ _)).length + (packingCode (packedProgram _ _ _ _ _)).length + 6 ≤ _
  unfold PA17WrappedNatRAM038a.spillBase PA17WrappedNatRAM038a.rollingSpillBase
    PA17QueryLayout014.heapWords PA17GivenWord031f.heapWords
  unfold lengthConstant
  omega

theorem generatedCode_length_le_cube (N q size : Nat) (hsize : 0 < size) (hupper : size ≤ N + q + 1) :
    (generatedCode PA17WrappedNatRAM038a.implementation PA17PackedPhase045.programs N q size).length ≤
      lengthConstant * (N + q + 2) ^ 3 :=
  (generatedCode_length_le N q size hsize).trans
    (Nat.mul_le_mul_left _ (PA17FullBuildWord036c.work_le_cube N q size hupper))

theorem generatedCode_length_fits (N q size : Nat) (hsize : 0 < size) (hupper : size ≤ N + q + 1) :
    Fits (indexWidth 32 N q)
      (generatedCode PA17WrappedNatRAM038a.implementation PA17PackedPhase045.programs N q size).length := by
  apply PA17PackingBounds043.polynomial_fits N q
  have hh := generatedCode_length_le_cube N q size hsize hupper
  have hp := PA17PackingBounds043.powers_le_six N q
  unfold lengthConstant at hh
  omega

end PaperProofs.Structure.LaminarTree.PA17GenerationBounds047
