module
public import Structure.PA17_TM_RatArithmetic_MulFields_048b
public import Structure.PA17_TM_RatArithmetic_BankWalk_033b

/-! Sum the invariants of records ACTUALLY produced by native/cache calls.
The real producer must establish each gap/width bound. These conditional
internal metadata lemmas do not add original input qualifications. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulFields048

open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticParse002

theorem bank_sum_bounds (records : List RecordSpec) (gapBound widthBound : Nat)
    (hg : ∀ r∈records,r.gap≤gapBound) (hw : ∀ r∈records,r.digits.length≤widthBound) :
    totalGap records≤records.length*gapBound ∧ totalWidth records≤records.length*widthBound := by
  induction records with
  | nil => simp only [totalGap,totalWidth,List.length_nil,Nat.zero_mul,le_refl,and_self]
  | cons record later ih =>
    have hrg := hg record (by simp)
    have hrw := hw record (by simp)
    obtain ⟨hlg,hlw⟩ := ih (fun r hr => hg r (by simp [hr])) (fun r hr => hw r (by simp [hr]))
    simp only [totalGap,totalWidth,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem fixed_bank_bounds (j k : Nat) (records : List RecordSpec) (hj : records.length=j)
    (x y : Rat) (hg : ∀ r∈records,r.gap≤2*k*(fieldWidth x y)^2)
    (hw : ∀ r∈records,r.digits.length≤fieldWidth x y) :
    totalGap records≤2*j*k*(fieldWidth x y)^2 ∧ totalWidth records≤j*fieldWidth x y := by
  obtain ⟨hgap,hwidth⟩ := bank_sum_bounds records (2*k*(fieldWidth x y)^2) (fieldWidth x y) hg hw
  rw [hj] at hgap hwidth
  constructor
  · calc
      _ ≤ j*(2*k*(fieldWidth x y)^2) := hgap
      _ = _ := by ring
  · exact hwidth

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMulFields048
