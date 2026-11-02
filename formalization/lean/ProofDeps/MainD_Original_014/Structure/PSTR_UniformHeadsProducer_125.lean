module

public import Structure.PSTR_HD_HeadsOriginalPositive_133
public import Structure.PSTR_UniformQuery_122

/-! Discharge the actual heads query producer using the SAME frozen1371
body in the ONE whole heads program, with no rank-fit or safe-run premise. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRUniformHeads

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open RawTreePreprocessingClaims PA17A19RuntimeEntry020 PSTRHeadsRuntime

def program : List PackingOp := uniformHeadsProgram PSTRUniformQueryCode.program

theorem body_contains : PSTRUniformQueryCode.Contains program := by
  refine ⟨?_, ?_⟩
  · rw [program, uniformHeadsProgram_length]
    omega
  · intro index hi
    exact heads_body_prefix_get PSTRUniformQueryCode.program index hi

theorem body_length : PSTRUniformQueryCode.program.length ≤ 8192 := by
  rw [PSTRUniformQueryCode.program_length]
  decide

theorem body_literal : ∀ value ∈ packingCode PSTRUniformQueryCode.program, value < 65536 :=
  PSTRUniformQueryCode.code_fit (bits := 16) (by change 8192 < 2 ^ 16; decide)

theorem program_pc (N q : Nat) : Fits (indexWidth 32 N q) (5 * program.length) := by
  unfold program
  exact original_uniform_heads_pc_fit N q PSTRUniformQueryCode.program (body_length.trans (by decide : 8192 ≤ 65536))

theorem program_words (N q : Nat) : WordsFit (indexWidth 32 N q) (packingCode program) := by
  unfold program
  exact original_uniform_heads_code_fit N q PSTRUniformQueryCode.program
    (body_length.trans (by decide : 8192 ≤ 65536)) (PSTRUniformQueryEmbeddings.program_words N q)

theorem actual_positive_producer {q : Nat} (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) (used : Finset (Fin q)) :
    InternalQueryProducer full used (capacity full) (allocatedWords full)
      (PSTRUniformQuery.budget full) PSTRUniformQueryCode.program (bits := wordBits full) := by
  intro stage hs state rep hp ha
  let configuration : Configuration q := ⟨stage, used, false⟩
  have allowed : Allowed full configuration .query := ⟨rfl, hs⟩
  obtain ⟨steps, upper, result⟩ := PSTRUniformQuery.actual_query full configuration allowed hl
    program body_contains (program_words full.length q) (program_pc full.length q) state hp ha rep
  refine ⟨steps, upper, ?_, result.safe, ?_⟩
  · apply internal_query_exit_of_original_reply full used (capacity full) PSTRUniformQueryCode.program stage hs
    · rw [PSTRUniformQueryCode.program_length]
      exact result.pc
    · exact result.active
    · exact result.correct
  · intro clock hc
    refine ⟨result.represents clock hc, ?_⟩
    intro physical hf hh
    apply result.high clock hc physical hf
    change PSTRQueryLayout.endpoint
      (PSTRQueryLayout.physicalWorkspace full (capacity full) (wordBits full)) (treeSize q full) q ≤ physical
    rw [PSTRCountLogical.workspace_eq full _ _ hq]
    exact hh

end PaperProofs.Structure.LaminarTree.PSTRUniformHeads
