module

public import PaperProofs.Retained.Controller

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetExactTerminal001

open Common Common.Native
open scoped ENNReal BigOperators

variable {I : Instance}

def executionPair (execution : Execution I) : I.Stage × I.Tool :=
  (execution.handle.stage, execution.tool)

def pairCharge (input : StatisticalInput I) (pair : I.Stage × I.Tool) : ℝ≥0∞ :=
  ENNReal.ofReal (input.fees.correction pair.1 pair.2 : ℝ)

/-- Replay a specified finite list of genuine correction pairs. Source write
serials are rebound to the actual destination writes. The theorem records
the exact stage/tool list, actual charges, and an actual Step trace; it does
not supply the measurable shadow policy required by the complete R02. -/
theorem replay_pairs (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    (hallocation : C.allocation = .terminalBarrier)
    (hexecution : C.execution = .terminalBarrier)
    (base : State I) (pairs : List (I.Stage × I.Tool))
    (hstage : (pairs.map Prod.fst).Nodup) (htool : (pairs.map Prod.snd).Nodup)
    (hcompatible : ∀ pair ∈ pairs, pair.2 ∈ I.eligible pair.1)
    (s : State I) (hinvariant : Invariant C s) (hactive : s.halted = false)
    (hhandles : ∀ pair ∈ pairs, validHandle s (originalHandle base pair.1))
    (hunused : ∀ pair ∈ pairs, ∀ a ∈ s.ledger.commitments, a.tool ≠ pair.2)
    (hunallocated : ∀ pair ∈ pairs, ∀ a ∈ s.ledger.commitments,
      a.handle.stage ≠ pair.1) :
    ∃ t : State I, UncappedTrace input C accounting tapes s t ∧
      Invariant C t ∧ t.halted = false ∧ t.cursor = s.cursor ∧
      t.ledger.truth = s.ledger.truth ∧ t.ledger.written = s.ledger.written ∧
      t.ledger.executions.map executionPair = s.ledger.executions.map executionPair ++ pairs ∧
      t.ledger.actualBill input.fees = s.ledger.actualBill input.fees +
        (pairs.map (pairCharge input)).sum := by
  induction pairs generalizing s with
  | nil =>
    exact ⟨s, .refl, hinvariant, hactive, rfl, rfl, rfl, by simp, by simp⟩
  | cons pair later ih =>
    have hstages := List.nodup_cons.mp (by simpa only [List.map_cons] using hstage)
    have htools := List.nodup_cons.mp (by simpa only [List.map_cons] using htool)
    obtain ⟨committed, repaired, ha, he, hactiveRepair, hhandleFrame, hexecutions, hfee⟩ :=
      exists_uncapped_correction_pair input C accounting tapes s (originalHandle base pair.1) pair.2
        hactive hinvariant.wellFormed (hhandles pair (by simp)) (hcompatible pair (by simp))
        hallocation hexecution (hunused pair (by simp)) (hunallocated pair (by simp))
    have hframe : repaired.ledger.truth = s.ledger.truth ∧
        repaired.ledger.written = s.ledger.written ∧
        repaired.ledger.commitments = s.ledger.commitments ++ [⟨originalHandle base pair.1, pair.2, s.clock⟩] ∧
        repaired.cursor = s.cursor := by
      cases ha
      cases he
      exact ⟨rfl, rfl, rfl, rfl⟩
    have hinvariantRepair := step_invariant input C .uncapped accounting tapes he
      (step_invariant input C .uncapped accounting tapes ha hinvariant)
    have hhandlesRepair : ∀ item ∈ later, validHandle repaired (originalHandle base item.1) := by
      intro item hitem
      exact (hhandleFrame _).mpr (hhandles item (by simp [hitem]))
    have hunusedRepair : ∀ item ∈ later, ∀ a ∈ repaired.ledger.commitments, a.tool ≠ item.2 := by
      intro item hitem a ha'
      rw [hframe.2.2.1] at ha'
      rcases List.mem_append.mp ha' with hold | hnew
      · exact hunused item (by simp [hitem]) a hold
      · have heq := List.mem_singleton.mp hnew
        subst a
        intro heq
        apply htools.1
        exact List.mem_map.mpr ⟨item, hitem, heq.symm⟩
    have hunallocatedRepair : ∀ item ∈ later, ∀ a ∈ repaired.ledger.commitments,
        a.handle.stage ≠ item.1 := by
      intro item hitem a ha'
      rw [hframe.2.2.1] at ha'
      rcases List.mem_append.mp ha' with hold | hnew
      · exact hunallocated item (by simp [hitem]) a hold
      · have heq := List.mem_singleton.mp hnew
        subst a
        intro heq
        apply hstages.1
        exact List.mem_map.mpr ⟨item, hitem, heq.symm⟩
    obtain ⟨t, htrace, hinvariantT, hactiveT, hcursorT, htruthT, hwrittenT, hpairsT, hfeeT⟩ :=
      ih hstages.2 htools.2 (fun item hi => hcompatible item (by simp [hi])) repaired
        hinvariantRepair hactiveRepair hhandlesRepair hunusedRepair hunallocatedRepair
    refine ⟨t, ?_, hinvariantT, hactiveT, hcursorT.trans hframe.2.2.2,
      htruthT.trans hframe.1, hwrittenT.trans hframe.2.1, ?_, ?_⟩
    · exact ((Relation.ReflTransGen.single ⟨_, ha⟩).trans
        (Relation.ReflTransGen.single ⟨_, he⟩)).trans htrace
    · rw [hpairsT, hexecutions, List.map_append, List.map_singleton]
      simp only [executionPair, originalHandle, List.append_assoc, List.singleton_append]
    · rw [hfeeT, hfee, List.map_cons, List.sum_cons]
      exact add_assoc _ _ _

end PaperProofs.Retained.PRetExactTerminal001
