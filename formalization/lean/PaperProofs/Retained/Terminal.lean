module

public import PaperProofs.Retained.NativeMatching
public import Mathlib.Logic.Relation

set_option autoImplicit false
set_option warningAsError true

/-!
Finite actual uncapped terminal traces. These are state-level Step traces,
not a compiled visible-history Policy and not a native resource certificate.
The independently proved Native.Invariant is propagated at every Step.
-/

@[expose] public section

namespace PaperProofs.Retained

open Common
open scoped BigOperators ENNReal

variable {I : Instance}

def UncappedTrace (input : StatisticalInput I) (C : Contract I)
    (accounting : Native.NormalAccounting I) (tapes : Native.ReviewTapes input) :
    Native.State I → Native.State I → Prop :=
  Relation.ReflTransGen (fun s t => ∃ action, Native.Step input C .uncapped accounting tapes s action t)

private theorem pair_frame (input : StatisticalInput I) (C : Contract I)
    (accounting : Native.NormalAccounting I) (tapes : Native.ReviewTapes input)
    {s committed repaired : Native.State I} {h : MismatchHandle I} {r : I.Tool}
    (ha : Native.Step input C .uncapped accounting tapes s (.allocate h r) committed)
    (he : Native.Step input C .uncapped accounting tapes committed (.execute h r) repaired) :
    repaired.ledger.truth = s.ledger.truth ∧ repaired.ledger.written = s.ledger.written ∧
      repaired.ledger.commitments = s.ledger.commitments ++ [⟨h, r, s.clock⟩] := by
  cases ha
  cases he
  exact ⟨rfl, rfl, rfl⟩

def originalHandle (base : Native.State I) (i : I.Stage) : MismatchHandle I :=
  ⟨i, base.ledger.writeSerial i⟩

private theorem repair_finite (input : StatisticalInput I) (C : Contract I)
    (accounting : Native.NormalAccounting I) (tapes : Native.ReviewTapes input)
    (hallocation : C.allocation = .terminalBarrier) (hexecution : C.execution = .terminalBarrier)
    (base : Native.State I) (errors : Finset I.Stage)
    (assignment : {i : I.Stage // i ∈ errors} → I.Tool)
    (hinj : Function.Injective assignment)
    (hcompatible : ∀ i, assignment i ∈ I.eligible i.val)
    (remaining : Finset {i : I.Stage // i ∈ errors})
    (s : Native.State I) (hinvariant : Native.Invariant C s) (hactive : s.halted = false)
    (hhandles : ∀ i : {i : I.Stage // i ∈ errors}, Native.validHandle s (originalHandle base i.val))
    (htools : ∀ i ∈ remaining, ∀ a ∈ s.ledger.commitments, a.tool ≠ assignment i)
    (hstages : ∀ i ∈ remaining, ∀ a ∈ s.ledger.commitments, a.handle.stage ≠ i.val) :
    ∃ t, UncappedTrace input C accounting tapes s t ∧ Native.Invariant C t ∧ t.halted = false ∧
      t.ledger.truth = s.ledger.truth ∧ t.ledger.written = s.ledger.written ∧
      (∀ i ∈ remaining, i.val ∈ executedStages t.ledger) ∧
      executedStages s.ledger ⊆ executedStages t.ledger ∧
      t.ledger.executions.length = s.ledger.executions.length + remaining.card ∧
      t.ledger.actualBill input.fees = s.ledger.actualBill input.fees +
        ∑ i ∈ remaining, ENNReal.ofReal (input.fees.correction i.val (assignment i) : ℝ) := by
  classical
  induction remaining using Finset.induction_on generalizing s with
  | empty =>
    refine ⟨s, .refl, hinvariant, hactive, rfl, rfl, ?_, Finset.Subset.refl _, ?_, ?_⟩
    · intro i hi
      exact False.elim ((Finset.notMem_empty i) hi)
    · simp only [Finset.card_empty, Nat.add_zero]
    · simp only [Finset.sum_empty, add_zero]
  | @insert i remaining hnot ih =>
    obtain ⟨committed, repaired, ha, he, hactiveRepair, hhandleFrame, hexecutions, hfee⟩ :=
      exists_uncapped_correction_pair input C accounting tapes s (originalHandle base i.val) (assignment i)
        hactive hinvariant.wellFormed (hhandles i) (hcompatible i) hallocation hexecution
        (htools i (Finset.mem_insert_self _ _)) (hstages i (Finset.mem_insert_self _ _))
    have hinvariantCommit := Native.step_invariant input C .uncapped accounting tapes ha hinvariant
    have hinvariantRepair := Native.step_invariant input C .uncapped accounting tapes he hinvariantCommit
    have hframe := pair_frame input C accounting tapes ha he
    have hhandlesRepair (j : {i : I.Stage // i ∈ errors}) :
        Native.validHandle repaired (originalHandle base j.val) :=
      (hhandleFrame (originalHandle base j.val)).mpr (hhandles j)
    have htoolsRepair : ∀ j ∈ remaining, ∀ a ∈ repaired.ledger.commitments,
        a.tool ≠ assignment j := by
      intro j hj a ha'
      rw [hframe.2.2] at ha'
      rcases List.mem_append.mp ha' with hold | hnew
      · exact htools j (Finset.mem_insert_of_mem hj) a hold
      · have heq := List.mem_singleton.mp hnew
        subst a
        intro htool
        have hij : i = j := hinj htool
        subst j
        exact hnot hj
    have hstagesRepair : ∀ j ∈ remaining, ∀ a ∈ repaired.ledger.commitments,
        a.handle.stage ≠ j.val := by
      intro j hj a ha'
      rw [hframe.2.2] at ha'
      rcases List.mem_append.mp ha' with hold | hnew
      · exact hstages j (Finset.mem_insert_of_mem hj) a hold
      · have heq := List.mem_singleton.mp hnew
        subst a
        intro hstage
        have hij : i = j := Subtype.ext hstage
        subst j
        exact hnot hj
    have hpairMono : executedStages s.ledger ⊆ executedStages repaired.ledger := by
      intro stage hstage
      obtain ⟨e, heold, hestage⟩ := (mem_executedStages s.ledger stage).mp hstage
      apply (mem_executedStages repaired.ledger stage).mpr
      refine ⟨e, ?_, hestage⟩
      rw [hexecutions]
      exact List.mem_append.mpr (Or.inl heold)
    have hcurrent : i.val ∈ executedStages repaired.ledger := by
      apply (mem_executedStages repaired.ledger i.val).mpr
      refine ⟨⟨originalHandle base i.val, assignment i, s.clock + 1⟩, ?_, rfl⟩
      rw [hexecutions]
      exact List.mem_append.mpr (Or.inr (by simp))
    obtain ⟨t, htrace, hinvariantT, hactiveT, htruthT, hwrittenT, hcoveredT, hmonoT, hlengthT, hfeeT⟩ :=
      ih repaired hinvariantRepair hactiveRepair hhandlesRepair htoolsRepair hstagesRepair
    have hpairTrace : UncappedTrace input C accounting tapes s repaired :=
      (Relation.ReflTransGen.single ⟨.allocate (originalHandle base i.val) (assignment i), ha⟩).trans
        (Relation.ReflTransGen.single ⟨.execute (originalHandle base i.val) (assignment i), he⟩)
    refine ⟨t, hpairTrace.trans htrace, hinvariantT, hactiveT,
      htruthT.trans hframe.1, hwrittenT.trans hframe.2.1, ?_, hpairMono.trans hmonoT, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with hji | hmem
      · subst j
        exact hmonoT hcurrent
      · exact hcoveredT j hmem
    · rw [hlengthT, hexecutions, List.length_append, List.length_singleton,
        Finset.card_insert_of_notMem hnot]
      omega
    · rw [hfeeT, hfee, Finset.sum_insert hnot]
      ac_rfl

private theorem written_correct_or_mismatch (L : Ledger I) (hwritten : Native.allWritten L)
    (i : I.Stage) : L.written i = some (L.truth i) ∨ i ∈ ordinaryMismatches L := by
  cases hwrite : L.written i with
  | none => exact False.elim (hwritten i hwrite)
  | some bit =>
    cases bit <;> cases htruth : L.truth i <;>
      simp [hwrite, htruth, ordinaryMismatches]

/-- A clean, active, completely written retained state with reported genuine
error handles and a real matching has a finite actual uncapped completion.
The full invariant is used and propagated; no report-clock bound is assumed
separately. Costs on the preceding path are retained in the equality. -/
theorem terminal_matching_trace (input : StatisticalInput I) (C : Contract I)
    (accounting : Native.NormalAccounting I) (tapes : Native.ReviewTapes input)
    (s : Native.State I) (hallocation : C.allocation = .terminalBarrier)
    (hexecution : C.execution = .terminalBarrier) (hinvariant : Native.Invariant C s)
    (hactive : s.halted = false) (hwritten : Native.allWritten s.ledger)
    (hcommit : s.ledger.commitments = []) (hexecute : s.ledger.executions = [])
    (hreported : ∀ i ∈ ordinaryMismatches s.ledger, ∃ time, s.ledger.reportTime i = some time)
    (hmatchable : Matchable I (ordinaryMismatches s.ledger)) :
    ∃ assignment : Matching I (ordinaryMismatches s.ledger), ∃ finished,
      UncappedTrace input C accounting tapes s finished ∧ Native.Invariant C finished ∧
      finished.halted = true ∧ finished.ledger.success C ∧
      finished.ledger.executions.length = (ordinaryMismatches s.ledger).card ∧
      finished.ledger.actualBill input.fees = s.ledger.actualBill input.fees +
        ∑ i : {i : I.Stage // i ∈ ordinaryMismatches s.ledger},
          ENNReal.ofReal (input.fees.correction i.val (assignment.val i) : ℝ) := by
  classical
  let errors := ordinaryMismatches s.ledger
  obtain ⟨assignment⟩ := (matchable_iff_matching I errors).mp hmatchable
  have hhandles (i : {i : I.Stage // i ∈ errors}) : Native.validHandle s (originalHandle s i.val) := by
    refine ⟨(mem_ordinaryMismatches s.ledger i.val).mp i.property, rfl, ?_⟩
    exact hreported i.val i.property
  have htools : ∀ i ∈ (Finset.univ : Finset {i : I.Stage // i ∈ errors}),
      ∀ a ∈ s.ledger.commitments, a.tool ≠ assignment.val i := by
    intro i _ a ha
    rw [hcommit] at ha
    cases ha
  have hstages : ∀ i ∈ (Finset.univ : Finset {i : I.Stage // i ∈ errors}),
      ∀ a ∈ s.ledger.commitments, a.handle.stage ≠ i.val := by
    intro i _ a ha
    rw [hcommit] at ha
    cases ha
  obtain ⟨repaired, htrace, hinvariantRepair, hactiveRepair, htruthRepair, hwrittenRepair,
      hcovered, _, hcount, hfee⟩ :=
    repair_finite input C accounting tapes hallocation hexecution s errors assignment.val
      assignment.property.1 assignment.property.2 Finset.univ s hinvariant hactive hhandles htools hstages
  have hallwritten : Native.allWritten repaired.ledger := by
    intro i
    simpa only [hwrittenRepair] using hwritten i
  have hmismatches : ordinaryMismatches repaired.ledger = errors := by
    ext i
    simp only [errors, mem_ordinaryMismatches, hwrittenRepair, htruthRepair]
  have hcovered' (i : I.Stage) (hi : i ∈ ordinaryMismatches repaired.ledger) :
      i ∈ executedStages repaired.ledger := by
    have hi' : i ∈ errors := hmismatches ▸ hi
    exact hcovered ⟨i, hi'⟩ (Finset.mem_univ _)
  let finished := Native.stopState repaired false
  have hstop : Native.Step input C .uncapped accounting tapes repaired .stop finished :=
    Native.Step.stop repaired hactiveRepair
  have hinvariantFinished := Native.step_invariant input C .uncapped accounting tapes hstop hinvariantRepair
  have hsuccess : finished.ledger.success C := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · simp [finished, Native.stopState, hallwritten]
    · simp [Ledger.windowObligations, hallocation, hexecution]
    · intro i
      rcases written_correct_or_mismatch repaired.ledger hallwritten i with hcorrect | hmismatch
      · exact Or.inl hcorrect
      · exact Or.inr ((mem_executedStages repaired.ledger i).mp (hcovered' i hmismatch))
  have htraceFinished : UncappedTrace input C accounting tapes s finished :=
    htrace.trans (Relation.ReflTransGen.single ⟨.stop, hstop⟩)
  refine ⟨assignment, finished, htraceFinished, hinvariantFinished, rfl, hsuccess, ?_, ?_⟩
  · change repaired.ledger.executions.length = errors.card
    simpa only [hexecute, List.length_nil, Finset.card_univ, Fintype.card_coe, Nat.zero_add] using hcount
  · change repaired.ledger.actualBill input.fees = s.ledger.actualBill input.fees + _
    exact hfee

/-- The invariant hypothesis of the state-level construction is supplied by
an actual native Prefix. This still returns a finite Step trace; compiling
its choices into one visible-history Policy is a separate obligation. -/
theorem terminal_matching_trace_from_prefix (input : StatisticalInput I) (C : Contract I)
    (accounting : Native.NormalAccounting I) (tapes : Native.ReviewTapes input)
    {Seed : Type*} (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (mode : Native.ResourceMode) {n : ℕ} {s : Native.State I}
    (hp : Native.Prefix input C mode accounting policy seed truth tapes n s)
    (hallocation : C.allocation = .terminalBarrier) (hexecution : C.execution = .terminalBarrier)
    (hactive : s.halted = false) (hwritten : Native.allWritten s.ledger)
    (hcommit : s.ledger.commitments = []) (hexecute : s.ledger.executions = [])
    (hreported : ∀ i ∈ ordinaryMismatches s.ledger, ∃ time, s.ledger.reportTime i = some time)
    (hmatchable : Matchable I (ordinaryMismatches s.ledger)) :
    ∃ assignment : Matching I (ordinaryMismatches s.ledger), ∃ finished,
      UncappedTrace input C accounting tapes s finished ∧ Native.Invariant C finished ∧
      finished.halted = true ∧ finished.ledger.success C ∧
      finished.ledger.executions.length = (ordinaryMismatches s.ledger).card ∧
      finished.ledger.actualBill input.fees = s.ledger.actualBill input.fees +
        ∑ i : {i : I.Stage // i ∈ ordinaryMismatches s.ledger},
          ENNReal.ofReal (input.fees.correction i.val (assignment.val i) : ℝ) :=
  terminal_matching_trace input C accounting tapes s hallocation hexecution
    (Native.prefix_invariant input C mode accounting policy seed truth tapes hp)
    hactive hwritten hcommit hexecute hreported hmatchable

end PaperProofs.Retained
