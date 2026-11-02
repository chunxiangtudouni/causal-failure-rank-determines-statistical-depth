module

public import PaperProofs.Common.NativeProtocol

/-!
Pathwise costs and original-cap enforcement for actual protocol transitions.
No condition on eventual success is used, and missed correction obligations
do not delete any charge. Controller feasibility under a sufficient resource
certificate is a separate theorem, not assumed here.
-/

@[expose] public section

open scoped ENNReal BigOperators

namespace PaperProofs.Common.Native

variable {I : Instance}

@[simp] theorem record_actualBill (accounting : NormalAccounting I) (s : State I)
    (action : Action I) (responses : List (VisibleEvent I)) (L : Ledger I)
    (cursor : ℕ) (halted : Bool) (F : Fees I) :
    (record accounting s action responses L cursor halted).ledger.actualBill F =
      L.actualBill F := rfl

@[simp] theorem initial_actualBill (truth : I.Stage → Bool) (F : Fees I) :
    (initial truth).ledger.actualBill F = 0 := by
  simp [initial, Ledger.actualBill, Ledger.observationBill, Ledger.correctionBill]

@[simp] theorem reportedWrite_actualBill (C : Contract I) (s : State I)
    (i : I.Stage) (bit : Bool) (F : Fees I) :
    (reportedWriteLedger C s i bit).actualBill F = s.ledger.actualBill F := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

@[simp] theorem allocate_actualBill (s : State I) (h : MismatchHandle I)
    (r : I.Tool) (F : Fees I) :
    (allocateLedger s h r).actualBill F = s.ledger.actualBill F := rfl

@[simp] theorem advance_actualBill (s : State I) (i : I.Stage) (F : Fees I) :
    (advanceLedger s i).actualBill F = s.ledger.actualBill F := rfl

@[simp] theorem stop_actualBill (s : State I) (abandon : Bool) (F : Fees I) :
    (stopState s abandon).ledger.actualBill F = s.ledger.actualBill F := rfl

theorem execute_actualBill (s : State I) (h : MismatchHandle I) (r : I.Tool) (F : Fees I) :
    (executeLedger s h r).actualBill F =
      s.ledger.actualBill F + ENNReal.ofReal (F.correction h.stage r : ℝ) := by
  simp [executeLedger, Ledger.actualBill, Ledger.observationBill, Ledger.correctionBill, add_assoc]

theorem review_actualBill_mono (s : State I) (i : I.Stage) (F : Fees I) :
    s.ledger.actualBill F ≤ (reviewLedger s i).actualBill F := by
  have hcounts (j : I.Stage) : s.ledger.reviews j ≤ (reviewLedger s i).reviews j := by
    by_cases hji : j = i
    · subst j
      simp only [reviewLedger, Function.update_self]
      exact le_self_add
    · simp [reviewLedger, Function.update_of_ne hji]
  have hobs : s.ledger.observationBill F ≤ (reviewLedger s i).observationBill F := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_right (ENat.toENNReal_mono (hcounts j)) _
  exact add_le_add hobs le_rfl

/-- This includes steps on already-failed task paths. -/
theorem step_actualBill_mono (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s s' : State I} {action : Action I}
    (hstep : Step input C mode accounting tapes s action s') (F : Fees I) :
    s.ledger.actualBill F ≤ s'.ledger.actualBill F := by
  cases hstep with
  | review i _ _ _ => simpa only [record_actualBill] using review_actualBill_mono s i F
  | write => simpa only [record_actualBill, reportedWrite_actualBill] using (le_refl (s.ledger.actualBill F))
  | allocate => simpa only [record_actualBill, allocate_actualBill] using (le_refl (s.ledger.actualBill F))
  | execute h r _ _ _ _ _ _ _ _ =>
    simp only [record_actualBill, execute_actualBill]
    exact le_self_add
  | advance => simpa only [record_actualBill, advance_actualBill] using (le_refl (s.ledger.actualBill F))
  | stop => simpa only [stop_actualBill] using (le_refl (s.ledger.actualBill F))
  | abandon => simpa only [stop_actualBill] using (le_refl (s.ledger.actualBill F))

theorem initial_obeysCaps (truth : I.Stage → Bool) (C : Contract I) :
    (initial truth).ledger.obeysCaps C := by
  simp [initial, Ledger.obeysCaps, Ledger.totalCalls]

theorem stop_obeysCaps (s : State I) (C : Contract I) (abandon : Bool)
    (h : s.ledger.obeysCaps C) : (stopState s abandon).ledger.obeysCaps C := h

/-- Native quotas are enforced on every actual prefix, without a probability or
successful-path exception. This is distinct from proving a constructed controller
always has an enabled next action under its rational certificate. -/
theorem step_native_obeysCaps (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s s' : State I} {action : Action I} (hold : s.ledger.obeysCaps C)
    (hstep : Step input C .native accounting tapes s action s') : s'.ledger.obeysCaps C := by
  cases hstep with
  | review _ _ _ resources => simpa [withinResources] using resources
  | write _ _ _ _ resources => simpa [withinResources] using resources
  | allocate _ _ _ _ _ _ _ _ resources => simpa [withinResources] using resources
  | execute _ _ _ _ _ _ _ _ _ resources => simpa [withinResources] using resources
  | advance _ _ _ resources => simpa [withinResources] using resources
  | stop _ => exact stop_obeysCaps _ C false hold
  | abandon _ => exact stop_obeysCaps _ C true hold

theorem prefix_native_obeysCaps (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) {Seed : Type*} (policy : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I}
    (h : Prefix input C .native accounting policy seed truth tapes n s) : s.ledger.obeysCaps C := by
  induction h with
  | initial => exact initial_obeysCaps truth C
  | next _ step ih => exact step_native_obeysCaps input C accounting tapes ih step

end PaperProofs.Common.Native
