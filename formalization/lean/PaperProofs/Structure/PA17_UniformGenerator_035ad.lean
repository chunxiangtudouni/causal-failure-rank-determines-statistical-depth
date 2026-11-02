module

public import PaperProofs.Structure.PA17_UniformGenerator_035ac

/-! Every actually emitted word is bounded from the finite syntax contract.
The real copy therefore needs no external generated-code-word oracle. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035ad

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035b PA17UniformGenerator035d PA17UniformGenerator035e
  PA17UniformGenerator035j PA17UniformGenerator035o PA17UniformGenerator035ac

theorem denote_words_le (template : Template) (rom : PhysicalROM) (B heapWords : Nat) (environment : Nat → Nat)
    (hc : TemplateChecked rom B heapWords environment template) :
    ∀ word ∈ template.denote rom environment, word ≤ B := by
  induction template generalizing environment with
  | empty => intro word hw; simp only [Template.denote, List.not_mem_nil] at hw
  | word expression =>
    intro word hw
    simp only [Template.denote, List.mem_singleton] at hw
    subst word
    exact checked_value expression rom environment B heapWords hc
  | append left right ihl ihr =>
    intro word hw
    simp only [Template.denote, List.mem_append] at hw
    rcases hw with hw | hw
    · exact ihl environment hc.1 word hw
    · exact ihr environment hc.2 word hw
  | «repeat» counter bound body ih =>
    intro word hw
    simp only [Template.denote, List.mem_flatMap] at hw
    obtain ⟨index, hi, hw⟩ := hw
    have hn : index < bound.eval rom environment := List.mem_range.mp (List.mem_reverse.mp hi)
    exact ih (Function.update environment counter (index + 1)) (hc.2 (index + 1) (by omega)) word hw

theorem stream_words_le (templates : List Template) (rom : PhysicalROM) (B heapWords : Nat)
    (environment : Nat → Nat) (saved count : Nat) (hc : StreamsChecked rom B heapWords environment saved count templates)
    (hbudget : count + (streamWords rom environment saved count templates).length ≤ B) :
    ∀ word ∈ streamWords rom environment saved count templates, word ≤ B := by
  induction templates generalizing count with
  | nil => intro word hw; simp only [streamWords, List.not_mem_nil] at hw
  | cons first later ih =>
    intro word hw
    simp only [streamWords, List.mem_cons, List.mem_append] at hw
    rcases hw with hw | hw | hw
    · subst word
      simp only [streamWords, List.length_cons, List.length_append] at hbudget
      omega
    · exact denote_words_le first rom B heapWords (Function.update environment saved count) hc.1 word hw
    · apply ih _ hc.2 ?_ word hw
      simp only [streamWords, List.length_cons, List.length_append] at hbudget
      omega

theorem streamWords_eq_flatMap (templates : List Template) (rom : PhysicalROM) (environment : Nat → Nat) (saved count : Nat)
    (hstable : ∀ template ∈ templates, ∀ snapshot,
      template.denote rom (Function.update environment saved snapshot) = template.denote rom environment) :
    streamWords rom environment saved count templates =
      (templates.map (fun template => template.denote rom environment)).flatMap (fun code => code.length :: code) := by
  induction templates generalizing count with
  | nil => rfl
  | cons first later ih =>
    rw [streamWords, hstable first List.mem_cons_self count]
    rw [ih _ (fun template hm snapshot => hstable template (List.mem_cons_of_mem _ hm) snapshot)]
    simp only [List.map_cons, List.flatMap_cons, List.cons_append]

theorem stable_of_map_equal (templates : List Template) (rom : PhysicalROM) (environment : Nat → Nat) (saved : Nat)
    (hmap : ∀ snapshot,
      templates.map (fun template => template.denote rom (Function.update environment saved snapshot)) =
        templates.map (fun template => template.denote rom environment)) :
    ∀ template ∈ templates, ∀ snapshot,
      template.denote rom (Function.update environment saved snapshot) = template.denote rom environment := by
  intro template ht snapshot
  exact List.map_inj_left.mp (hmap snapshot) template ht

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035ad
