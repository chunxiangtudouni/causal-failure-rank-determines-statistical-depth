module
public import PaperProofs.Structure.PA17_PackedTemplates_046a
public import PaperProofs.Structure.PA17_UniformGenerator_035j

/-! The actual mask emitter is finite-word safe at every subexpression.
Its proof explicitly checks the shift before the later subtraction. -/
@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA17PackedTemplates046

open IndexedRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035j
local instance pa17OfNat046g (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add046g : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance pa17Sub046g : HSub Expr Expr Expr := ⟨.binary .subtract⟩
local instance pa17Mul046g : HMul Expr Expr Expr := ⟨.binary .multiply⟩

theorem safeMask_checked (width : Expr) (rom : PhysicalROM) (environment : Nat → Nat)
    (bits B heapWords : Nat) (hw : ExprChecked rom environment B heapWords width)
    (hpositive : 0 < width.eval rom environment) (hwidth : width.eval rom environment ≤ bits)
    (hsmall : 2 ≤ B) (hmax : 2 ^ bits - 1 ≤ B) :
    ExprChecked rom environment B heapWords (safeMask width) := by
  let value := width.eval rom environment
  have hvalue : value ≤ B := checked_value width rom environment B heapWords hw
  have hv : 0 < value := hpositive
  have hvb : value ≤ bits := hwidth
  have hpow : 2 ^ (value - 1) < 2 ^ bits := Nat.pow_lt_pow_right (by decide) (by omega)
  have hshift : Nat.shiftLeft 1 (value - 1) ≤ B := by
    rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul]
    omega
  have hfinal : (safeMask width).eval rom environment ≤ B := by
    rw [safeMask_eval width rom environment hpositive]
    exact (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) hwidth) 1).trans hmax
  have hfinal' : (Nat.shiftLeft 1 (value - 1) - 1) * 2 + 1 ≤ B := hfinal
  have hone : ExprChecked rom environment B heapWords (1 : Expr) := by change 1 ≤ B; omega
  have htwo : ExprChecked rom environment B heapWords (2 : Expr) := hsmall
  have hpred : ExprChecked rom environment B heapWords (width - 1) :=
    ⟨hw, hone, by change value - 1 ≤ B; omega⟩
  have hshiftChecked : ExprChecked rom environment B heapWords (.binary .shiftLeft 1 (width - 1)) :=
    ⟨hone, hpred, hshift⟩
  have hsub : ExprChecked rom environment B heapWords ((.binary .shiftLeft 1 (width - 1)) - 1) :=
    ⟨hshiftChecked, hone, by change Nat.shiftLeft 1 (value - 1) - 1 ≤ B; omega⟩
  have hproduct : ExprChecked rom environment B heapWords (((.binary .shiftLeft 1 (width - 1)) - 1) * 2) :=
    ⟨hsub, htwo, by change (Nat.shiftLeft 1 (value - 1) - 1) * 2 ≤ B; omega⟩
  exact ⟨hproduct, hone, hfinal⟩

end PaperProofs.Structure.LaminarTree.PA17PackedTemplates046
