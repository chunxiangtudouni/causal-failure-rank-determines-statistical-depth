module
public import PaperProofs.Structure.PA17_PackedTemplates_046f
public import PaperProofs.Structure.PA17_QueryTemplates_044l

/-! All six real code templates have productive actual loops. This connects
the fixed compiler's syntax-derived clock to emitted-code length. -/
@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace PaperProofs.Structure.LaminarTree.PA17PackedTemplates046

open AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d PA17UniformGenerator035n
  PA17ProgramTemplates041 PA17QueryTemplates044l
local instance pa17OfNat046j (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add046j : HAdd Expr Expr Expr := ⟨.binary .add⟩

def positive (expression : Expr) : Bool := decide (expression = tDim ∨ expression = qDim + 1)
attribute [local instance] shapeDec

theorem logicalFull_shape : ProductiveShape positive wrappedFull.haltingTemplate := by decide
theorem logicalQuery_shape : ProductiveShape positive PA17QueryTemplates044f.wrappedQuery.haltingTemplate := by decide
theorem logicalRolling_shape : ProductiveShape positive wrappedRolling.haltingTemplate := by decide
theorem physicalFull_shape : ProductiveShape positive full := by decide
theorem physicalQuery_shape : ProductiveShape positive query := by decide
theorem physicalRolling_shape : ProductiveShape positive rolling := by decide

theorem positive_eval (N q t : Nat) (ht : 0 < t) :
    ∀ expression, positive expression = true → ∀ environment : Nat → Nat,
      0 < expression.eval (dimensionROM N q t) environment := by
  intro expression he environment
  have heq : expression = tDim ∨ expression = qDim + 1 := of_decide_eq_true he
  rcases heq with rfl | rfl
  · exact ht
  · exact Nat.succ_pos q

theorem logicalFull_productive (N q t : Nat) (ht : 0 < t) (environment : Nat → Nat) :
    Productive (dimensionROM N q t) environment wrappedFull.haltingTemplate :=
  shape_productive positive _ logicalFull_shape _ (positive_eval N q t ht) environment

theorem logicalQuery_productive (N q t : Nat) (ht : 0 < t) (environment : Nat → Nat) :
    Productive (dimensionROM N q t) environment PA17QueryTemplates044f.wrappedQuery.haltingTemplate :=
  shape_productive positive _ logicalQuery_shape _ (positive_eval N q t ht) environment

theorem logicalRolling_productive (N q t : Nat) (ht : 0 < t) (environment : Nat → Nat) :
    Productive (dimensionROM N q t) environment wrappedRolling.haltingTemplate :=
  shape_productive positive _ logicalRolling_shape _ (positive_eval N q t ht) environment

theorem physicalFull_productive (N q t : Nat) (ht : 0 < t) (environment : Nat → Nat) :
    Productive (dimensionROM N q t) environment full :=
  shape_productive positive _ physicalFull_shape _ (positive_eval N q t ht) environment

theorem physicalQuery_productive (N q t : Nat) (ht : 0 < t) (environment : Nat → Nat) :
    Productive (dimensionROM N q t) environment query :=
  shape_productive positive _ physicalQuery_shape _ (positive_eval N q t ht) environment

theorem physicalRolling_productive (N q t : Nat) (ht : 0 < t) (environment : Nat → Nat) :
    Productive (dimensionROM N q t) environment rolling :=
  shape_productive positive _ physicalRolling_shape _ (positive_eval N q t ht) environment

end PaperProofs.Structure.LaminarTree.PA17PackedTemplates046
