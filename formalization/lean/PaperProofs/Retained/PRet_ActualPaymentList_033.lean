module

public import PaperProofs.Retained.PRet_ActualPaymentPair_032

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetActualPaymentList033

open Common Common.Native PRetExactTerminal001 PRetDelayedPolicy010 PRetInformationPackets006
open PRetActualPaymentPair032

variable {I : Instance}

/-- The actual delayed interpreter follows the full remaining ordered list
of original paid executions. Actual allocate/execute Steps and both public
guards are checked at every pair. This is a constructive continuation lemma,
not an assumed controller performance contract. -/
theorem follow_paid_tail {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (sample : Seed × input.World) (startup : Startup I)
    (hh : startup.halted = true) (hf : startup.finished = true) (hab : startup.abandoned = false)
    (base : State I) (tail : List (Execution I))
    (hstage : (tail.map (fun e => e.handle.stage)).Nodup)
    (htool : (tail.map (fun e => e.tool)).Nodup)
    (hcompatible : ∀ e ∈ tail, e.tool ∈ I.eligible e.handle.stage)
    (paid : List (Execution I)) (hsource : startup.executions = paid ++ tail)
    (n : ℕ) (s : State I)
    (hrun : run input C .uncapped accounting (rule accounting source) sample n = s)
    (hinvariant : Invariant C s) (hactive : s.halted = false) (hcursor : s.cursor = I.stageCount)
    (hshadow : shadow accounting source sample.1 s.history = some startup)
    (hpairs : s.ledger.executions.map executionPair = paid.map executionPair)
    (hhandles : ∀ e ∈ tail, validHandle s (originalHandle base e.handle.stage))
    (hunused : ∀ e ∈ tail, ∀ a ∈ s.ledger.commitments, a.tool ≠ e.tool)
    (hunallocated : ∀ e ∈ tail, ∀ a ∈ s.ledger.commitments, a.handle.stage ≠ e.handle.stage) :
    ∃ finalClock ≥ n, ∃ final : State I,
      run input C .uncapped accounting (rule accounting source) sample finalClock = final ∧
      final.halted = false ∧ final.cursor = s.cursor ∧
      final.ledger.truth = s.ledger.truth ∧ final.ledger.written = s.ledger.written ∧
      shadow accounting source sample.1 final.history = some startup ∧
      final.ledger.executions.map executionPair = startup.executions.map executionPair := by
  induction tail generalizing paid n s with
  | nil =>
    refine ⟨n, le_rfl, s, hrun, hactive, rfl, rfl, rfl, hshadow, ?_⟩
    rw [hsource, List.append_nil]
    exact hpairs
  | cons execution later ih =>
    have hstages := List.nodup_cons.mp (by simpa only [List.map_cons] using hstage)
    have htools := List.nodup_cons.mp (by simpa only [List.map_cons] using htool)
    obtain ⟨committed, repaired, ha, he, hactiveRepair, hhandleFrame, hexecutions, _⟩ :=
      exists_uncapped_correction_pair input C accounting (worldTapes input sample.2) s
        (originalHandle base execution.handle.stage) execution.tool hactive hinvariant.wellFormed
        (hhandles execution (by simp)) (hcompatible execution (by simp)) hretained.2.1 hretained.2.2
        (hunused execution (by simp)) (hunallocated execution (by simp))
    have hlength : s.ledger.executions.length = paid.length := by
      have hl := congrArg List.length hpairs
      simpa only [List.length_map] using hl
    have hindex : startup.executions[s.ledger.executions.length]? = some execution := by
      rw [hsource, hlength, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    obtain ⟨hnext, hshadowRepair⟩ := actual_payment_pair input C hretained accounting source sample n startup hh hf hab
      (by rw [hrun]; exact hshadow) (by rw [hrun]; exact hcursor) execution
      (originalHandle base execution.handle.stage) execution.tool (by rw [hrun]; exact hindex) rfl rfl committed repaired
      (by rw [hrun]; exact ha) he
    have hframe : repaired.ledger.truth = s.ledger.truth ∧ repaired.ledger.written = s.ledger.written ∧
        repaired.ledger.commitments = s.ledger.commitments ++
          [⟨originalHandle base execution.handle.stage, execution.tool, s.clock⟩] ∧ repaired.cursor = s.cursor := by
      cases ha
      cases he
      exact ⟨rfl, rfl, rfl, rfl⟩
    have hinvariantRepair := step_invariant input C .uncapped accounting (worldTapes input sample.2) he
      (step_invariant input C .uncapped accounting (worldTapes input sample.2) ha hinvariant)
    have hhandlesRepair : ∀ e ∈ later, validHandle repaired (originalHandle base e.handle.stage) := by
      intro e he'
      exact (hhandleFrame _).mpr (hhandles e (by simp [he']))
    have hunusedRepair : ∀ e ∈ later, ∀ a ∈ repaired.ledger.commitments, a.tool ≠ e.tool := by
      intro e he' a ha'
      rw [hframe.2.2.1] at ha'
      rcases List.mem_append.mp ha' with hold | hnew
      · exact hunused e (by simp [he']) a hold
      · have heq := List.mem_singleton.mp hnew
        subst a
        intro heq
        exact htools.1 (List.mem_map.mpr ⟨e, he', heq.symm⟩)
    have hunallocatedRepair : ∀ e ∈ later, ∀ a ∈ repaired.ledger.commitments, a.handle.stage ≠ e.handle.stage := by
      intro e he' a ha'
      rw [hframe.2.2.1] at ha'
      rcases List.mem_append.mp ha' with hold | hnew
      · exact hunallocated e (by simp [he']) a hold
      · have heq := List.mem_singleton.mp hnew
        subst a
        intro heq
        exact hstages.1 (List.mem_map.mpr ⟨e, he', heq.symm⟩)
    have hsource' : startup.executions = (paid ++ [execution]) ++ later := by
      simpa only [List.append_assoc, List.singleton_append] using hsource
    have hpairsRepair : repaired.ledger.executions.map executionPair = (paid ++ [execution]).map executionPair := by
      rw [hexecutions, List.map_append, hpairs, List.map_append]
      rfl
    obtain ⟨last, hlast, final, hrunFinal, hactiveFinal, hcursorFinal, htruthFinal, hwrittenFinal,
        hshadowFinal, hpairsFinal⟩ := ih hstages.2 htools.2 (fun e he' => hcompatible e (by simp [he']))
      (paid ++ [execution]) hsource' (n + 2) repaired hnext hinvariantRepair hactiveRepair
      (hframe.2.2.2.trans hcursor) hshadowRepair hpairsRepair hhandlesRepair hunusedRepair hunallocatedRepair
    exact ⟨last, by omega, final, hrunFinal, hactiveFinal, hcursorFinal.trans hframe.2.2.2,
      htruthFinal.trans hframe.1, hwrittenFinal.trans hframe.2.1, hshadowFinal, hpairsFinal⟩

end PaperProofs.Retained.PRetActualPaymentList033
