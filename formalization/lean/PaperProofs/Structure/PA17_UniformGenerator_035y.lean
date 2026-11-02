module

public import PaperProofs.Structure.PA17_UniformGenerator_035o

/-! Encoded generator-code Fits from ordinary literal bounds. In particular
the ISA tags/register fields need no execution or code-ROM oracle. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035y

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035c
  PA17UniformGenerator035d PA17UniformGenerator035e PA17UniformGenerator035j PA17UniformGenerator035o

def ConstantLE (B : Nat) : PackingOp → Prop
  | .base (.base (.constant _ value)) => value ≤ B
  | _ => True

def ConstantsLE (B : Nat) (program : List PackingOp) : Prop := ∀ op ∈ program, ConstantLE B op

theorem register_word_le (register : Register) : register.word ≤ 6 := by cases register <;> decide
theorem region_word_le (region : Region) : region.word ≤ 2 := by cases region <;> decide
theorem primitive_word_le (primitive : PackingPrimitive) : primitive.word ≤ 14 := by cases primitive <;> decide

theorem fiveWords_le (B a b c d e : Nat) (ha : a ≤ B) (hb : b ≤ B) (hc : c ≤ B) (hd : d ≤ B) (he : e ≤ B) :
    ∀ word ∈ [a,b,c,d,e], word ≤ B := by
  intro word hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem op_words_le (B : Nat) (hB : 15 ≤ B) (op : PackingOp) (hc : ConstantLE B op) :
    ∀ word ∈ op.encode.toArray.toList, word ≤ B := by
  have hr (register : Register) : register.word ≤ B := (register_word_le register).trans (by omega)
  have hregion (region : Region) : region.word ≤ B := (region_word_le region).trans (by omega)
  have hp (primitive : PackingPrimitive) : primitive.word ≤ B := (primitive_word_le primitive).trans (by omega)
  cases op with
  | base op =>
    cases op with
    | base instruction =>
      cases instruction with
      | constant target value => exact fiveWords_le B 0 target.word value 0 0 (by omega) (hr _) hc (by omega) (by omega)
      | add target left right => exact fiveWords_le B 1 target.word left.word right.word 0 (by omega) (hr _) (hr _) (hr _) (by omega)
      | minimum target left right => exact fiveWords_le B 2 target.word left.word right.word 0 (by omega) (hr _) (hr _) (hr _) (by omega)
      | select target condition whenTrue whenFalse => exact fiveWords_le B 3 target.word condition.word whenTrue.word whenFalse.word (by omega) (hr _) (hr _) (hr _) (hr _)
      | loadROM region target pointer => exact fiveWords_le B 4 region.word target.word pointer.word 0 (by omega) (hregion _) (hr _) (hr _) (by omega)
      | loadHeap target pointer => exact fiveWords_le B 5 target.word pointer.word 0 0 (by omega) (hr _) (hr _) (by omega) (by omega)
      | storeHeap pointer source => exact fiveWords_le B 6 pointer.word source.word 0 0 (by omega) (hr _) (hr _) (by omega) (by omega)
    | subtract target left right => exact fiveWords_le B 8 target.word left.word right.word 0 (by omega) (hr _) (hr _) (hr _) (by omega)
  | arithmetic primitive target left right => exact fiveWords_le B primitive.word target.word left.word right.word 0 (hp _) (hr _) (hr _) (hr _) (by omega)
  | jumpIfZero condition target => exact fiveWords_le B 15 condition.word target.word 0 0 (by omega) (hr _) (hr _) (by omega) (by omega)

theorem packingCode_fit (B bits : Nat) (hB : 15 ≤ B) (hb : Fits bits B) (program : List PackingOp)
    (hc : ConstantsLE B program) : WordsFit bits (packingCode program) := by
  intro word hw
  simp only [packingCode, List.mem_append] at hw
  rcases hw with hw | hw
  · obtain ⟨op, hop, hw⟩ := List.mem_flatMap.mp hw
    exact lt_of_le_of_lt (op_words_le B hB op (hc op hop) word hw) hb
  · have hh : word ≤ 7 := by
      change word ∈ [7,0,0,0,0] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> omega
    exact lt_of_le_of_lt (by omega) hb

theorem ConstantsLE.append (B : Nat) (left right : List PackingOp) (hl : ConstantsLE B left) (hr : ConstantsLE B right) :
    ConstantsLE B (left ++ right) := by
  intro op hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hl op hm
  · exact hr op hm

theorem expression_constants (expression : Expr) (rom : PhysicalROM) (environment : Nat → Nat)
    (B heapWords stack : Nat) (hstack : stack + expression.size ≤ B)
    (hc : ExprChecked rom environment B heapWords expression) : ConstantsLE B (expression.compile stack) := by
  induction expression generalizing stack with
  | constant value =>
    intro op hm
    simp only [Expr.compile, List.mem_singleton] at hm
    subst op
    exact hc
  | cell address =>
    intro op hm
    simp only [Expr.compile, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact hc.2.1
    · trivial
  | input address =>
    intro op hm
    simp only [Expr.compile, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact hc.2.1
    · trivial
  | binary operation left right ihl ihr =>
    change stack + (left.size + right.size + 1) ≤ B at hstack
    have h1 := ihl stack (by omega) hc.1
    have h2 : ConstantsLE B (spill stack) := by
      intro op hm
      simp only [spill, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · change stack ≤ B; omega
      · trivial
    have h3 := ihr (stack + 1) (by omega) hc.2.1
    have h4 : ConstantsLE B (finish stack operation) := by
      intro op hm
      simp only [finish, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · change stack ≤ B; omega
      · trivial
      · cases operation <;> trivial
    exact ConstantsLE.append _ _ _ h1 (ConstantsLE.append _ _ _ h2 (ConstantsLE.append _ _ _ h3 h4))

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035y
