module
public import PaperProofs.Structure.PA17_QueryTemplates_044i
public import PaperProofs.Structure.PA17_PackingBounds_043

/-! The query subexpression envelope fits the original factor32 word size.
Arbitrary width/bits/snapshot cell values are not assumed small or read
by the original logical query AST. -/
@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA17QueryTemplates044j
open IndexedRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035o
  PA17ProgramTemplates041 PA17QueryTemplates044i

theorem bound_polynomial (N q size : Nat) (ht : size ≤ N + q + 1) :
    bound N q size ≤ 16777216 * (N + q + 2) ^ 6 := by
  let base := N + q + 2
  have hb : 2 ≤ base := by dsimp [base]; omega
  have hcube : 8 ≤ base ^ 3 := Nat.pow_le_pow_left hb 3
  have hs : scale N q size ≤ 5 * base := by dsimp [scale, base]; omega
  calc
    bound N q size = 1048576 * scale N q size ^ 3 := rfl
    _ ≤ 1048576 * (5 * base) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs 3)
    _ = 131072000 * base ^ 3 := by ring
    _ ≤ 16777216 * base ^ 6 := by
      have he : base ^ 6 = (base ^ 3) ^ 2 := by ring
      rw [he]
      nlinarith

theorem bound_fits (N q size : Nat) (ht : size ≤ N + q + 1) :
    Fits (indexWidth 32 N q) (bound N q size) :=
  PA17PackingBounds043.polynomial_fits N q _ (bound_polynomial N q size ht)

def wordBound (N q : Nat) : Nat := 2 ^ indexWidth 32 N q - 1

theorem bound_le_wordBound (N q size : Nat) (ht : size ≤ N + q + 1) :
    bound N q size ≤ wordBound N q := by
  have hf := bound_fits N q size ht
  change bound N q size < 2 ^ indexWidth 32 N q at hf
  dsimp [wordBound]
  omega

theorem wrapped_word_checked (N q size heapWords : Nat) (ht : size ≤ N + q + 1) (hh : 64 ≤ heapWords)
    (env : Nat → Nat) (he : ∀ address ∈ queryScope, env address ≤ scale N q size) :
    TemplateChecked (dimensionROM N q size) (wordBound N q) heapWords env
      PA17QueryTemplates044f.wrappedQuery.codeTemplate :=
  template_checked_mono _ _ env _ heapWords _ heapWords (bound_le_wordBound N q size ht) le_rfl
    (wrapped_template_checked N q size heapWords hh env he)

theorem query_word_checked (N q size heapWords : Nat) (ht : size ≤ N + q + 1) (hh : 64 ≤ heapWords)
    (env : Nat → Nat) (he : ∀ address ∈ queryScope, env address ≤ scale N q size) :
    TemplateChecked (dimensionROM N q size) (wordBound N q) heapWords env
      PA17QueryTemplates044f.queryProgram.codeTemplate :=
  template_checked_mono _ _ env _ heapWords _ heapWords (bound_le_wordBound N q size ht) le_rfl
    (query_template_checked N q size heapWords hh env he)

def preparedEnv (width bits snapshot : Nat) : Nat → Nat :=
  Function.update (Function.update (Function.update (fun _ => 0) 1 width) 2 bits) 3 snapshot

theorem preparedEnv_small (width bits snapshot N q size : Nat) :
    ∀ address ∈ queryScope, preparedEnv width bits snapshot address ≤ scale N q size := by
  intro address ha
  simp only [queryScope, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl
  all_goals simp [preparedEnv]

theorem prepared_wrapped_word_checked (N q size heapWords width bits snapshot : Nat)
    (ht : size ≤ N + q + 1) (hh : 64 ≤ heapWords) :
    TemplateChecked (dimensionROM N q size) (wordBound N q) heapWords (preparedEnv width bits snapshot)
      PA17QueryTemplates044f.wrappedQuery.codeTemplate :=
  wrapped_word_checked N q size heapWords ht hh _ (preparedEnv_small width bits snapshot N q size)

end PaperProofs.Structure.LaminarTree.PA17QueryTemplates044j
