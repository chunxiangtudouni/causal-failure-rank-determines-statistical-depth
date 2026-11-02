module
public import PaperProofs.Structure.PA17_GeneratorStatic_048b
public import PaperProofs.Structure.PA17_PackedTemplates_046l
public import PaperProofs.Structure.PA17_UniformGenerator_035ad

/-! The actual measured six-stream semantics is the original generatedCode,
independently of each runtime length snapshot. All source value/productivity
conditions are instantiated from the same fixed templates. -/
@[expose] public section
set_option maxRecDepth 20000
namespace PaperProofs.Structure.LaminarTree.PA17GeneratorStatic048

open IndexedRAM AlgorithmClaims PackingMachine PA17UniformGenerator035b PA17UniformGenerator035d
  PA17UniformGenerator035o PA17UniformGenerator035ac PA17UniformGenerator035ad
  PA17ProgramTemplates041

theorem prepared_update (N q snapshot : Nat) :
    Function.update (PA17UniformGenerator035ae.preparedEnv N q) 3 snapshot =
      PA17QueryTemplates044j.preparedEnv (CapacityBits.width q) (indexWidth 32 N q) snapshot := by
  funext address
  by_cases h3 : address = 3
  · subst address
    simp [PA17QueryTemplates044j.preparedEnv]
  · by_cases h2 : address = 2
    · subst address
      simp [PA17UniformGenerator035ae.preparedEnv, PA17QueryTemplates044j.preparedEnv]
    · by_cases h1 : address = 1
      · subst address
        simp [PA17UniformGenerator035ae.preparedEnv, PA17QueryTemplates044j.preparedEnv]
      · simp [PA17UniformGenerator035ae.preparedEnv, PA17QueryTemplates044j.preparedEnv, h1, h2, h3]

theorem streamsChecked_of_forall (list : List Template) (rom : PhysicalROM) (B H : Nat)
    (environment : Nat → Nat) (saved : Nat)
    (hc : ∀ template ∈ list, ∀ snapshot,
      TemplateChecked rom B H (Function.update environment saved snapshot) template) (count : Nat) :
    StreamsChecked rom B H environment saved count list := by
  induction list generalizing count with
  | nil => trivial
  | cons first later ih =>
    exact ⟨hc first List.mem_cons_self count,
      ih (fun template hm snapshot => hc template (List.mem_cons_of_mem _ hm) snapshot) _⟩

theorem streamsProductive_of_forall (list : List Template) (rom : PhysicalROM)
    (environment : Nat → Nat) (saved : Nat)
    (hp : ∀ template ∈ list, ∀ snapshot,
      PA17UniformGenerator035n.Productive rom (Function.update environment saved snapshot) template) (count : Nat) :
    PA17UniformGenerator035ae.StreamsProductive rom environment saved count list := by
  induction list generalizing count with
  | nil => trivial
  | cons first later ih =>
    exact ⟨hp first List.mem_cons_self count,
      ih (fun template hm snapshot => hp template (List.mem_cons_of_mem _ hm) snapshot) _⟩

theorem six_checked (N q t H count : Nat) (hq : 0 < q) (ht : t ≤ N + q + 1) (hh : 64 ≤ H) :
    StreamsChecked (dimensionROM N q t) (2 ^ indexWidth 32 N q - 1) H
      (PA17UniformGenerator035ae.preparedEnv N q) 3 count PA17PackedTemplates046.templates := by
  apply streamsChecked_of_forall
  intro template hmem snapshot
  rw [prepared_update]
  exact PA17PackedTemplates046.templates_checked template hmem N q t H snapshot hq ht hh

theorem six_productive (N q t count : Nat) (ht : 0 < t) :
    PA17UniformGenerator035ae.StreamsProductive (dimensionROM N q t)
      (PA17UniformGenerator035ae.preparedEnv N q) 3 count PA17PackedTemplates046.templates := by
  apply streamsProductive_of_forall
  intro template hmem snapshot
  exact PA17PackedTemplates046.templates_productive template hmem N q t ht _

theorem six_output (N q t count : Nat) (hq : 0 < q) :
    streamWords (dimensionROM N q t) (PA17UniformGenerator035ae.preparedEnv N q) 3 count
      PA17PackedTemplates046.templates =
      generatedCode PA17WrappedNatRAM038a.implementation PA17PackedPhase045.programs N q t := by
  let environment := PA17UniformGenerator035ae.preparedEnv N q
  have hw : environment 1 = CapacityBits.width q := by simp [environment, PA17UniformGenerator035ae.preparedEnv]
  have hb : environment 2 = indexWidth 32 N q := by simp [environment, PA17UniformGenerator035ae.preparedEnv]
  have hmap (snapshot : Nat) :
      PA17PackedTemplates046.templates.map (fun template => template.denote (dimensionROM N q t)
        (Function.update environment 3 snapshot)) =
      PA17PackedTemplates046.templates.map (fun template => template.denote (dimensionROM N q t) environment) := by
    rw [PA17PackedTemplates046.templates_denote N q t hq _
      (by simpa only [Function.update_of_ne (by decide : 1 ≠ 3)] using hw)
      (by simpa only [Function.update_of_ne (by decide : 2 ≠ 3)] using hb),
      PA17PackedTemplates046.templates_denote N q t hq environment hw hb]
  rw [streamWords_eq_flatMap _ _ _ _ _ (stable_of_map_equal _ _ _ _ hmap)]
  exact PA17PackedTemplates046.output_eq_generatedCode N q t hq environment hw hb

end PaperProofs.Structure.LaminarTree.PA17GeneratorStatic048
