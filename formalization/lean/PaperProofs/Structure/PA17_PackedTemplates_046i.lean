module
public import PaperProofs.Structure.PA17_PackedTemplates_046f
public import PaperProofs.Structure.PA17_PackedTemplates_046h
public import PaperProofs.Structure.PA17_QueryTemplates_044i

/-! Concrete all-subexpression certificates for all three physical source
templates. The same original factor32 accommodates the degree-four layout
arithmetic, while the fullword mask is checked separately and exactly. -/
@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace PaperProofs.Structure.LaminarTree.PA17PackedTemplates046

open IndexedRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d PA17UniformGenerator035o
open PA17ProgramTemplates041
local instance pa17OfNat046i (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add046i : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance pa17Mul046i : HMul Expr Expr Expr := ⟨.binary .multiply⟩

def numericScope : Finset Nat := {1, 2, 16, 17, 18, 19, 20, 21}
def queryNumericScope : Finset Nat := numericScope.erase 20
def numericSmallBounds : List Expr := PA17QueryTemplates044i.smallBounds ++ [nDim + 1, 2 * (qDim + 2)]
def NumericSmall (expression : Expr) : Prop := expression ∈ numericSmallBounds
def numericScale (N q t : Nat) : Nat := 32 * (N + q + t + 8)
def numericBound (N q t : Nat) : Nat := 4096 * numericScale N q t ^ 4

local instance pa17SmallDec046i (expression : Expr) : Decidable (NumericSmall expression) :=
  inferInstanceAs (Decidable (expression ∈ numericSmallBounds))

@[instance_reducible] def expressionProfileDec (scope : Finset Nat) (expression : Expr) :
    Decidable (ExpressionProfile scope expression) := by
  letI := PA17QueryTemplates044i.goodDec expression
  letI := PA17QueryTemplates044g.exprBelowDec 64 expression
  letI := PA17QueryTemplates044g.exprInputsDec 3 expression
  unfold ExpressionProfile
  infer_instance

@[instance_reducible] def profileDec (scope : Finset Nat) (smallBound : Expr → Prop)
    [DecidablePred smallBound] : (template : Template) → Decidable (Profile scope smallBound template)
  | .empty => isTrue True.intro
  | .word expression => expressionProfileDec scope expression
  | .append left right => by
    letI := profileDec scope smallBound left
    letI := profileDec scope smallBound right
    change Decidable (Profile scope smallBound left ∧ Profile scope smallBound right)
    infer_instance
  | .repeat counter count body => by
    letI := expressionProfileDec scope count
    letI := profileDec scope smallBound body
    change Decidable (ExpressionProfile scope count ∧ counter ≠ 1 ∧ counter ≠ 2 ∧
      (counter ∈ scope → smallBound count) ∧ Profile scope smallBound body)
    infer_instance

attribute [local instance] profileDec

theorem full_profile : Profile numericScope NumericSmall full := by decide
theorem query_profile : Profile queryNumericScope NumericSmall query := by decide
theorem rolling_profile : Profile numericScope NumericSmall rolling := by decide

theorem numericSmall_le (expression : Expr) (hs : NumericSmall expression)
    (N q t : Nat) (environment : Nat → Nat) :
    expression.eval (dimensionROM N q t) environment ≤ numericScale N q t := by
  rcases List.mem_append.mp hs with hs | hs
  · exact (PA17QueryTemplates044i.smallBound_le expression hs N q t environment).trans (by
      dsimp [PA17QueryTemplates044i.scale, numericScale]; omega)
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl
    · change N + 1 ≤ 32 * (N + q + t + 8)
      omega
    · change 2 * (q + 2) ≤ 32 * (N + q + t + 8)
      omega

theorem numericBound_fits (N q t : Nat) (hq : 0 < q) (ht : t ≤ N + q + 1) :
    Fits (indexWidth 32 N q) (numericBound N q t) := by
  apply fits_indexWidth_of_lt_power
  let base := N + q + 2
  have hb : 3 ≤ base := by dsimp [base]; omega
  have hs : numericScale N q t ≤ 128 * base := by dsimp [numericScale, base]; omega
  have hp := Nat.pow_le_pow_left hs 4
  have he : 4096 * (128 * base) ^ 4 = 1099511627776 * base ^ 4 := by ring
  have hlarge : 1099511627776 < base ^ 28 :=
    lt_of_lt_of_le (by decide : 1099511627776 < 3 ^ 28) (Nat.pow_le_pow_left hb 28)
  have hpositive : 0 < base ^ 4 := pow_pos (by omega) _
  calc
    numericBound N q t ≤ 1099511627776 * base ^ 4 := by dsimp [numericBound]; nlinarith
    _ < base ^ 4 * base ^ 28 := by nlinarith
    _ = base ^ 32 := by rw [← pow_add]

theorem profile_checked (scope : Finset Nat) (h1 : 1 ∈ scope) (h2 : 2 ∈ scope)
    (template : Template) (hp : Profile scope NumericSmall template)
    (N q t heapWords : Nat) (hq : 0 < q) (ht : t ≤ N + q + 1) (hh : 64 ≤ heapWords)
    (environment : Nat → Nat) (he : ∀ address ∈ scope, environment address ≤ numericScale N q t)
    (hm : MaskEnvironment (indexWidth 32 N q) environment) :
    TemplateChecked (dimensionROM N q t) (2 ^ indexWidth 32 N q - 1) heapWords environment template := by
  have hu : 1 ≤ numericScale N q t := by dsimp [numericScale]; omega
  have hfit := numericBound_fits N q t hq ht
  change numericBound N q t < 2 ^ indexWidth 32 N q at hfit
  have hpow : 1 ≤ numericScale N q t ^ 4 := Nat.one_le_pow _ _ hu
  have hbudget : numericBound N q t ≤ 2 ^ indexWidth 32 N q - 1 := by omega
  have hB : 64 ≤ 2 ^ indexWidth 32 N q - 1 := by dsimp [numericBound] at hbudget; omega
  apply profile_template_checked scope NumericSmall template hp _ (numericScale N q t)
    (indexWidth 32 N q) (2 ^ indexWidth 32 N q - 1) heapWords h1 h2
    hu hB hh hbudget le_rfl (PA17PackingBounds043.bits_pos N q)
  · simp [dimensionROM]
  · intro address ha
    interval_cases address <;> simp [dimensionROM, PhysicalROM.semantic, PhysicalROM.words, numericScale] <;> omega
  · intro expression hs env _
    exact numericSmall_le expression hs N q t env
  · exact he
  · exact hm

theorem full_checked (N q t heapWords : Nat) (hq : 0 < q) (ht : t ≤ N + q + 1) (hh : 64 ≤ heapWords)
    (environment : Nat → Nat) (he : ∀ address ∈ numericScope, environment address ≤ numericScale N q t)
    (hm : MaskEnvironment (indexWidth 32 N q) environment) :
    TemplateChecked (dimensionROM N q t) (2 ^ indexWidth 32 N q - 1) heapWords environment full :=
  profile_checked numericScope (by decide) (by decide) full full_profile N q t heapWords hq ht hh environment he hm

theorem query_checked (N q t heapWords : Nat) (hq : 0 < q) (ht : t ≤ N + q + 1) (hh : 64 ≤ heapWords)
    (environment : Nat → Nat) (he : ∀ address ∈ numericScope, environment address ≤ numericScale N q t)
    (hm : MaskEnvironment (indexWidth 32 N q) environment) :
    TemplateChecked (dimensionROM N q t) (2 ^ indexWidth 32 N q - 1) heapWords environment query :=
  profile_checked queryNumericScope (by decide) (by decide) query query_profile N q t heapWords hq ht hh environment
    (fun address ha => he address (Finset.mem_of_mem_erase ha)) hm

theorem rolling_checked (N q t heapWords : Nat) (hq : 0 < q) (ht : t ≤ N + q + 1) (hh : 64 ≤ heapWords)
    (environment : Nat → Nat) (he : ∀ address ∈ numericScope, environment address ≤ numericScale N q t)
    (hm : MaskEnvironment (indexWidth 32 N q) environment) :
    TemplateChecked (dimensionROM N q t) (2 ^ indexWidth 32 N q - 1) heapWords environment rolling :=
  profile_checked numericScope (by decide) (by decide) rolling rolling_profile N q t heapWords hq ht hh environment he hm

end PaperProofs.Structure.LaminarTree.PA17PackedTemplates046
