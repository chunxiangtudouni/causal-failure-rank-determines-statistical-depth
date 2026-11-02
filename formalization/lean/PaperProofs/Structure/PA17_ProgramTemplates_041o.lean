module
public import PaperProofs.Structure.PA17_ProgramTemplates_041n
public import PaperProofs.Structure.PA17_QueryTemplates_044k
public import PaperProofs.Structure.PA17_WordBounds_023

/-! All-subexpression numeric certificates for the actual full and rolling
templates, including stage/parity/seed counters and the length expressions. -/
@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041

open IndexedRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d
  PA17UniformGenerator035o PA17QueryTemplates044i PA17QueryTemplates044k
local instance pa17OfNat041o (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add041o : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance pa17Mul041o : HMul Expr Expr Expr := ⟨.binary .multiply⟩

def builderBounds : List Expr := smallBounds ++ [nDim + 1, 2 * (qDim + 2)]
def BuilderSmallBound (expression : Expr) : Prop := expression ∈ builderBounds
def builderScope : Finset Nat := {16, 17, 18, 19, 20, 21}
def builderScale (N q size : Nat) : Nat := 2 * (N + q + size + 8)
def builderBound (N q size : Nat) : Nat := 1048576 * builderScale N q size ^ 3

local instance pa17BuilderDec041o (expression : Expr) : Decidable (BuilderSmallBound expression) :=
  inferInstanceAs (Decidable (expression ∈ builderBounds))
attribute [local instance] profileWithDec

theorem builderSmallBound_le (expression : Expr) (he : BuilderSmallBound expression)
    (N q size : Nat) (environment : Nat → Nat) :
    expression.eval (dimensionROM N q size) environment ≤ builderScale N q size := by
  rcases List.mem_append.mp he with hs | hs
  · exact (smallBound_le expression hs N q size environment).trans (by dsimp [scale, builderScale]; omega)
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl
    all_goals change _ ≤ 2 * (N + q + size + 8)
    · change N + 1 ≤ _
      omega
    · change 2 * (q + 2) ≤ _
      omega

theorem full_profile : ProfileWith builderScope BuilderSmallBound wrappedFull.codeTemplate := by decide
theorem rolling_profile : ProfileWith builderScope BuilderSmallBound wrappedRolling.codeTemplate := by decide

theorem builderProfile_checked (template : Template) (hp : ProfileWith builderScope BuilderSmallBound template)
    (N q size heapWords : Nat) (hh : 64 ≤ heapWords) (environment : Nat → Nat)
    (he : ∀ address ∈ builderScope, environment address ≤ builderScale N q size) :
    TemplateChecked (dimensionROM N q size) (builderBound N q size) heapWords environment template := by
  have hu : 1 ≤ builderScale N q size := by dsimp [builderScale]; omega
  have hpow : 1 ≤ builderScale N q size ^ 3 := Nat.one_le_pow _ _ hu
  apply profileWith_template_checked builderScope BuilderSmallBound template hp _
    (builderScale N q size) (builderBound N q size) heapWords hu (by dsimp [builderBound]; omega) hh le_rfl
  · simp [dimensionROM]
  · intro address ha
    interval_cases address <;> simp [dimensionROM, PhysicalROM.semantic, PhysicalROM.words, builderScale] <;> omega
  · intro expression hs env _
    exact builderSmallBound_le expression hs N q size env
  · exact he

theorem full_template_checked (N q size heapWords : Nat) (hh : 64 ≤ heapWords) (environment : Nat → Nat)
    (he : ∀ address ∈ builderScope, environment address ≤ builderScale N q size) :
    TemplateChecked (dimensionROM N q size) (builderBound N q size) heapWords environment wrappedFull.codeTemplate :=
  builderProfile_checked _ full_profile N q size heapWords hh environment he

theorem rolling_template_checked (N q size heapWords : Nat) (hh : 64 ≤ heapWords) (environment : Nat → Nat)
    (he : ∀ address ∈ builderScope, environment address ≤ builderScale N q size) :
    TemplateChecked (dimensionROM N q size) (builderBound N q size) heapWords environment wrappedRolling.codeTemplate :=
  builderProfile_checked _ rolling_profile N q size heapWords hh environment he

theorem builderBound_fits (N q size : Nat) (hq : 0 < q) (ht : size ≤ N + q + 1) :
    Fits (indexWidth 32 N q) (builderBound N q size) := by
  apply fits_indexWidth_of_lt_power
  let base := N + q + 2
  have hb : 3 ≤ base := by dsimp [base]; omega
  have hs : builderScale N q size ≤ 8 * base := by dsimp [builderScale, base]; omega
  have hp := Nat.pow_le_pow_left hs 3
  have he : 1048576 * (8 * base) ^ 3 = 536870912 * base ^ 3 := by ring
  have hlarge : 536870912 < base ^ 29 :=
    lt_of_lt_of_le (by decide : 536870912 < 3 ^ 29) (Nat.pow_le_pow_left hb 29)
  have hpositive : 0 < base ^ 3 := pow_pos (by omega) _
  calc
    builderBound N q size ≤ 536870912 * base ^ 3 := by dsimp [builderBound]; nlinarith
    _ < base ^ 3 * base ^ 29 := by nlinarith
    _ = base ^ 32 := by rw [← pow_add]

end PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041
