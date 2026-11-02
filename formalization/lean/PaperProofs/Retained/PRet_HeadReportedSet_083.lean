module

public import PaperProofs.Retained.PRet_ActualReportedErrors_048
public import PaperProofs.Common.NativeHeadContinuation

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetHeadReportedSet083

open Common Common.Native PRetActualReportedErrors048

open scoped Classical

variable {I : Instance}

/-- The actual post-head old-H update is exactly empty or {head}, decoded
from its genuine early report. This is a public-state identity, independent
of any optimal continuation or physical repair success. -/
theorem prefix_reportedErrors_one {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting source seed truth tapes n s)
    (head : I.Stage) (hhead : head.val = 0) (hwritten : s.ledger.written head ≠ none) :
    reportedErrors I s.history 1 = if HeadCorrectStartup head (publicStartup s) then ∅ else {head} := by
  classical
  rw [prefix_reportedErrors input C hearly mode accounting source seed truth tapes hp 1]
  have hcorrect := headCorrectStartup_iff input C hearly mode accounting source seed truth tapes hp head hwritten
  by_cases hc : HeadCorrectStartup head (publicStartup s)
  · rw [ite_eq_left hc]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro stage hs
    have hpast : stage.val < 1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hs).2).2
    have heq : stage = head := Fin.ext (by omega)
    subst stage
    have hwrong := (mem_ordinaryMismatches s.ledger head).mp (Finset.mem_inter.mp hs).1
    have hright := hcorrect.mp hc
    rw [hwrong] at hright
    cases ht : s.ledger.truth head <;> simp only [ht, Bool.not_false, Bool.not_true, Option.some.injEq,
      Bool.true_eq_false, Bool.false_eq_true] at hright
  · rw [ite_eq_right hc]
    ext stage
    simp only [Finset.mem_inter, mem_ordinaryMismatches, pastStages, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hs
      apply Fin.ext
      omega
    · intro heq
      subst stage
      refine ⟨?_, by omega⟩
      have hn : s.ledger.written head ≠ some (s.ledger.truth head) := fun h => hc (hcorrect.mpr h)
      cases hw : s.ledger.written head with
      | none => exact False.elim (hwritten hw)
      | some bit =>
        have hne : bit ≠ s.ledger.truth head := by
          intro heq
          exact hn (hw.trans (congrArg some heq))
        have hbit : bit = !s.ledger.truth head := by
          revert hne
          cases bit <;> cases s.ledger.truth head <;> decide
        exact congrArg some hbit

end PaperProofs.Retained.PRetHeadReportedSet083
