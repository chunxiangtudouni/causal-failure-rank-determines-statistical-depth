module

public import PaperProofs.Paid.CalibratedBackend

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Statistics PaperProofs.Paid

namespace PDROC

/-- The actual deterministic absorbing walk used by the original array
update, driven by the same finite review letters. -/
def endpointWalkState (level : ℕ) (tape : ℕ → Fin 2) :
    ℕ → PaperProofs.Paid.Parameters.WalkCell level
  | 0 => ⟨level, by omega⟩
  | n + 1 => PaperProofs.Paid.Parameters.walkMove level
      (endpointWalkState level tape n) (tape n)

@[simp] theorem endpointWalkState_zero (level : ℕ) (tape : ℕ → Fin 2) :
    (endpointWalkState level tape 0).val = level := rfl

theorem endpointWalkState_succ (level : ℕ) (tape : ℕ → Fin 2) (n : ℕ) :
    endpointWalkState level tape (n + 1) = PaperProofs.Paid.Parameters.walkMove level
      (endpointWalkState level tape n) (tape n) := rfl

theorem endpointWalkState_prefix (level n : ℕ) (tape tape' : ℕ → Fin 2)
    (hprefix : ∀ k < n, tape k = tape' k) :
    endpointWalkState level tape n = endpointWalkState level tape' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [endpointWalkState_succ, endpointWalkState_succ,
      ih (fun k hk => hprefix k (by omega)), hprefix n (by omega)]

theorem endpointWalkState_succ_of_boundary (level : ℕ) (tape : ℕ → Fin 2) (n : ℕ)
    (hboundary : (endpointWalkState level tape n).val = 0 ∨
      (endpointWalkState level tape n).val = 2 * level) :
    endpointWalkState level tape (n + 1) = endpointWalkState level tape n := by
  simp only [endpointWalkState_succ, PaperProofs.Paid.Parameters.walkMove, hboundary, ↓reduceDIte]

theorem endpointWalkState_succ_val_of_interior (level : ℕ) (tape : ℕ → Fin 2) (n : ℕ)
    (hzero : (endpointWalkState level tape n).val ≠ 0)
    (htop : (endpointWalkState level tape n).val ≠ 2 * level) :
    ((endpointWalkState level tape (n + 1)).val : ℤ) =
      ((endpointWalkState level tape n).val : ℤ) + if (tape n).val = 1 then 1 else -1 := by
  have hboundary : ¬ ((endpointWalkState level tape n).val = 0 ∨
      (endpointWalkState level tape n).val = 2 * level) := fun h => h.elim hzero htop
  rw [endpointWalkState_succ]
  unfold PaperProofs.Paid.Parameters.walkMove
  split_ifs <;> simp_all only <;> omega

end PDROC
