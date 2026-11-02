module
public import PaperProofs.Structure.PA17_PackedTemplates_046k
public import PaperProofs.Structure.PA17_PackedTemplates_046i
public import PaperProofs.Structure.PA17_PackedTemplates_046j
public import PaperProofs.Structure.PA17_ProgramTemplates_041o
public import PaperProofs.Structure.PA17_QueryTemplates_044j

/-! Complete concrete six-template value/clock inputs for the real generator.
Only the canonical proof environment is bounded; actual scratch remains
governed by lexical EnvRep and is never assumed globally small. -/
@[expose] public section
set_option maxRecDepth 30000
namespace PaperProofs.Structure.LaminarTree.PA17PackedTemplates046

open IndexedRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d PA17UniformGenerator035n
  PA17UniformGenerator035o PA17ProgramTemplates041 PA17QueryTemplates044j

theorem prepared_builder_small (width bits snapshot N q t : Nat) :
    ∀ address ∈ builderScope, preparedEnv width bits snapshot address ≤ builderScale N q t := by
  intro address ha
  simp only [builderScope, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [preparedEnv]

theorem builderBound_le_maxWord (N q t : Nat) (hq : 0 < q) (ht : t ≤ N + q + 1) :
    builderBound N q t ≤ 2 ^ indexWidth 32 N q - 1 := by
  have hf := builderBound_fits N q t hq ht
  change builderBound N q t < 2 ^ indexWidth 32 N q at hf
  omega

theorem prepared_logicalFull_checked (N q t H snapshot : Nat) (hq : 0 < q)
    (ht : t ≤ N + q + 1) (hh : 64 ≤ H) :
    TemplateChecked (dimensionROM N q t) (2 ^ indexWidth 32 N q - 1) H
      (preparedEnv (CapacityBits.width q) (indexWidth 32 N q) snapshot) wrappedFull.haltingTemplate := by
  have hc := PA17ProgramTemplates041.full_template_checked N q t H hh
    (preparedEnv (CapacityBits.width q) (indexWidth 32 N q) snapshot)
    (prepared_builder_small _ _ _ N q t)
  exact (template_checked_mono wrappedFull.codeTemplate _ _ _ H _ H
    (builderBound_le_maxWord N q t hq ht) le_rfl hc).2

theorem prepared_logicalQuery_checked (N q t H snapshot : Nat)
    (ht : t ≤ N + q + 1) (hh : 64 ≤ H) :
    TemplateChecked (dimensionROM N q t) (2 ^ indexWidth 32 N q - 1) H
      (preparedEnv (CapacityBits.width q) (indexWidth 32 N q) snapshot) PA17QueryTemplates044f.wrappedQuery.haltingTemplate :=
  (PA17QueryTemplates044j.prepared_wrapped_word_checked N q t H (CapacityBits.width q)
    (indexWidth 32 N q) snapshot ht hh).2

theorem prepared_logicalRolling_checked (N q t H snapshot : Nat) (hq : 0 < q)
    (ht : t ≤ N + q + 1) (hh : 64 ≤ H) :
    TemplateChecked (dimensionROM N q t) (2 ^ indexWidth 32 N q - 1) H
      (preparedEnv (CapacityBits.width q) (indexWidth 32 N q) snapshot) wrappedRolling.haltingTemplate := by
  have hc := PA17ProgramTemplates041.rolling_template_checked N q t H hh
    (preparedEnv (CapacityBits.width q) (indexWidth 32 N q) snapshot)
    (prepared_builder_small _ _ _ N q t)
  exact (template_checked_mono wrappedRolling.codeTemplate _ _ _ H _ H
    (builderBound_le_maxWord N q t hq ht) le_rfl hc).2

theorem bits_le_numericScale (N q t : Nat) : indexWidth 32 N q ≤ numericScale N q t := by
  have hc : Nat.clog 2 (N + q + 2) ≤ N + q + 2 :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide)))
  unfold indexWidth numericScale
  omega

theorem prepared_numeric_small (N q t snapshot : Nat) :
    ∀ address ∈ numericScope,
      preparedEnv (CapacityBits.width q) (indexWidth 32 N q) snapshot address ≤ numericScale N q t := by
  have hw : CapacityBits.width q ≤ numericScale N q t :=
    (PA17PackingBounds043.width_le_bits N q).trans (bits_le_numericScale N q t)
  have hb := bits_le_numericScale N q t
  intro address ha
  simp only [numericScope, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [preparedEnv] using hw
  · simpa [preparedEnv] using hb
  all_goals simp [preparedEnv]

theorem prepared_maskEnvironment (N q snapshot : Nat) (hq : 0 < q) :
    MaskEnvironment (indexWidth 32 N q) (preparedEnv (CapacityBits.width q) (indexWidth 32 N q) snapshot) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [preparedEnv] using width_pos q hq
  · simpa [preparedEnv] using PA17PackingBounds043.width_le_bits N q
  · simp [preparedEnv]

theorem templates_checked (template : Template) (hmem : template ∈ templates)
    (N q t H snapshot : Nat) (hq : 0 < q) (ht : t ≤ N + q + 1) (hh : 64 ≤ H) :
    TemplateChecked (dimensionROM N q t) (2 ^ indexWidth 32 N q - 1) H
      (preparedEnv (CapacityBits.width q) (indexWidth 32 N q) snapshot) template := by
  simp only [templates, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact prepared_logicalFull_checked N q t H snapshot hq ht hh
  · exact prepared_logicalQuery_checked N q t H snapshot ht hh
  · exact prepared_logicalRolling_checked N q t H snapshot hq ht hh
  · exact full_checked N q t H hq ht hh _ (prepared_numeric_small N q t snapshot) (prepared_maskEnvironment N q snapshot hq)
  · exact query_checked N q t H hq ht hh _ (prepared_numeric_small N q t snapshot) (prepared_maskEnvironment N q snapshot hq)
  · exact rolling_checked N q t H hq ht hh _ (prepared_numeric_small N q t snapshot) (prepared_maskEnvironment N q snapshot hq)

theorem templates_productive (template : Template) (hmem : template ∈ templates)
    (N q t : Nat) (ht : 0 < t) (environment : Nat → Nat) :
    Productive (dimensionROM N q t) environment template := by
  simp only [templates, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact logicalFull_productive N q t ht environment
  · exact logicalQuery_productive N q t ht environment
  · exact logicalRolling_productive N q t ht environment
  · exact physicalFull_productive N q t ht environment
  · exact physicalQuery_productive N q t ht environment
  · exact physicalRolling_productive N q t ht environment

end PaperProofs.Structure.LaminarTree.PA17PackedTemplates046
