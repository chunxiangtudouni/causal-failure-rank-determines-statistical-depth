module
public import RootB234_Quota_Code001
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.Quota

def firstDifference (e b n : Nat) (d : Rat) : Rat := d*(n : Rat)-2*((e : Rat)+b)
def secondDifference (e m n : Nat) (d : Rat) : Rat := (d*d)*(n : Rat)-(e : Rat)*(8*((m : Rat)*m))
def Successful (e b m n : Nat) (d : Rat) : Prop :=
  0≤firstDifference e b n d ∧ 0≤secondDifference e m n d

/-- Both actual sign tests accept equality. The Nat ceiling already
handles nonpositive thresholds, including the all-zero input. -/
theorem successful_iff (e b m n : Nat) (d : Rat) (positive : 0<d) :
    Successful e b m n d ↔ quota e b m d≤n := by
  have square : 0<d^2 := sq_pos_of_pos positive
  rw [quota,Nat.ceil_le,target,max_le_iff,div_le_iff₀ positive,div_le_iff₀ square]
  unfold Successful firstDifference secondDifference
  constructor
  · rintro ⟨first,second⟩
    constructor <;> nlinarith
  · rintro ⟨first,second⟩
    constructor <;> nlinarith

theorem successful_quota (e b m : Nat) (d : Rat) (positive : 0<d) :
    Successful e b m (quota e b m d) d :=
  (successful_iff e b m _ d positive).2 (Nat.le_refl _)

theorem unsuccessful_before (e b m n : Nat) (d : Rat) (positive : 0<d) (before : n<quota e b m d) :
    ¬Successful e b m n d := by
  rw [successful_iff e b m n d positive]
  omega

theorem first_success_exact (e b m n : Nat) (d : Rat) (positive : 0<d)
    (success : Successful e b m n d) (first : ∀ k<n,¬Successful e b m k d) :
    n=quota e b m d := by
  have lower:=(successful_iff e b m n d positive).1 success
  by_contra different
  exact first _ (by omega) (successful_quota e b m d positive)

theorem quota_zero (d : Rat) : quota 0 0 0 d=0 := by
  simp [quota,target]

end RootB234.Quota
