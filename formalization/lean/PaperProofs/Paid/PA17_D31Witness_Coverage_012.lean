module

public import PaperProofs.Paid.PA17_D31Witness_Completion_009
public import PaperProofs.Paid.PA17_D31Witness_FullError_010
public import PaperProofs.Paid.PA17_D31Witness_Incidence_011
public import PaperProofs.Common.NativeHeadContinuation

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Paid.PA17D31WitnessCoverage012

open Common Common.Native MeasureTheory PA17D31Witness001 PA17D31WitnessPolicy008
open PA17D31WitnessCompletion009 PA17D31WitnessIncidence011

theorem candidate_advance_reason (P : Parameters) (seed : Unit)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (hactive : historyHalted history = false) (hcursor : historyCursor history = stage.val)
    (hvalid : historyValidHandle history ⟨stage, historyWriteSerial history stage⟩)
    (ha : blindCandidate P seed history = .advance stage) :
    (historyCommitments history).any (fun pair => pair.1.stage == stage) = true ∨
      blindUnusedTool P history = none := by
  have hlt : historyCursor history < P.certificate.stages := by
    rw [hcursor]
    exact stage_lt_stages P stage
  have hstage : (⟨historyCursor history,
      by simpa [Parameters.sharedInstance, Instance.stageCount] using hlt⟩ : P.sharedInstance.Stage) = stage :=
    Fin.ext hcursor
  unfold blindCandidate at ha
  simp only [hactive, Bool.false_eq_true, ↓reduceIte, dite_eq_left hlt, hstage] at ha
  cases hw : historyWrite history stage with
  | none => simp only [hw] at ha; cases ha
  | some pair =>
    simp only [hw] at ha
    by_cases hcomm : (historyCommitments history).any (fun pair => pair.1.stage == stage) = true
    · exact Or.inl hcomm
    · right
      have hrepair : historyValidHandle history ⟨stage, historyWriteSerial history stage⟩ ∧
          ¬ (historyCommitments history).any (fun pair => pair.1.stage == stage) := ⟨hvalid, hcomm⟩
      rw [ite_eq_left hrepair] at ha
      cases ht : blindUnusedTool P history with
      | none => rfl
      | some tool => rw [ht] at ha; cases ha

theorem prefix_no_tool_length (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (seed : Unit) (truth : P.sharedInstance.Stage → Bool)
    (tapes : ReviewTapes (P.input fee hfee)) {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes n s)
    (hnone : blindUnusedTool P s.history = none) :
    P.tools ≤ s.ledger.commitments.length := by
  have hu := menuUnusedTool_none_all_used P s.history hnone
  have hc := List.toFinset_card_le ((historyCommitments s.history).map Prod.snd)
  change (historyUsed s.history).card ≤ ((historyCommitments s.history).map Prod.snd).length at hc
  rw [hu, Finset.card_univ, Fintype.card_fin, List.length_map,
    prefix_historyCommitments (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
      .native (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes hp,
    List.length_map] at hc
  exact hc

/-- After each advance, each error has either its own actual commitment or
the original K tools have all been used. This keeps failed paths intact. -/
theorem prefix_past_error_coverage (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (seed : Unit) (truth : P.sharedInstance.Stage → Bool)
    (tapes : ReviewTapes (P.input fee hfee)) {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes n s) :
    ∀ stage : P.sharedInstance.Stage, stage.val < s.cursor → s.ledger.truth stage = true →
      stage ∈ committedStages s.ledger ∨ P.tools ≤ s.ledger.commitments.length := by
  induction hp with
  | initial => intro stage h; exact (Nat.not_lt_zero _ h).elim
  | @next n s next hp hs ih =>
    have hm := nativeRule_nonbinding P fee hfee allocation seed truth tapes hp
    generalize ha : blindRule P seed s.history = action at hs
    cases hs with
    | review current live port resources =>
      exact (blindRule_ne_review P seed s.history current ha).elim
    | write current bit live port resources =>
      classical
      simp only [record, reportedWriteLedger, Parameters.retainedPaymentExampleContract, ↓reduceIte,
        writeLedger]
      exact ih
    | allocate handle tool active valid compatible unused unallocated window resources =>
      intro stage hstage htruth
      let fresh : Commitment P.sharedInstance := ⟨handle, tool, s.clock⟩
      rcases ih stage hstage htruth with hc | hfull
      · left
        change stage ∈ ((s.ledger.commitments ++ [fresh]).map (fun a => a.handle.stage)).toFinset
        obtain ⟨a, ha, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, List.mem_append.mpr (Or.inl ha), heq⟩)
      · right
        change P.tools ≤ (s.ledger.commitments ++ [fresh]).length
        simp only [List.length_append, List.length_singleton]
        omega
    | execute | stop | abandon => exact ih
    | advance current live written resources =>
      intro stage hstage htruth
      change stage.val < s.cursor + 1 at hstage
      change s.ledger.truth stage = true at htruth
      change stage ∈ committedStages s.ledger ∨ P.tools ≤ s.ledger.commitments.length
      by_cases hold : stage.val < s.cursor
      · exact ih stage hold htruth
      · have heq : stage = current := by apply Fin.ext; have hc := live.2; omega
        subst stage
        have hh := (prefix_historyHalted (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
          .native (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes hp).trans live.1
        have hc := (prefix_historyCursor (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
          .native (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes hp).trans live.2
        have hfalse := prefix_written_false (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
          .native (blindCallAccounting P.sharedInstance) (blindRule P) (blindRule_write_false P)
          seed truth tapes hp
        have hw : s.ledger.written current = some false := by
          cases hv : s.ledger.written current with
          | none => exact (written hv).elim
          | some bit => simp only [hfalse current bit hv]
        obtain ⟨time, ht⟩ := prefix_early_written_reported (P.input fee hfee)
          (P.retainedPaymentExampleContract allocation) rfl .native
          (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes hp current written
        have hhandle : validHandle s ⟨current, historyWriteSerial s.history current⟩ := by
          refine ⟨?_, ?_, time, ht⟩
          · simpa only [htruth, Bool.not_true] using hw
          · exact prefix_historyWriteSerial (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
              .native (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes hp current
        have hvalid := Retained.PRetRetainedGuard007.historyValidHandle_complete (P.input fee hfee)
          (P.retainedPaymentExampleContract allocation) rfl .native (blindCallAccounting P.sharedInstance)
          (blindRule P) seed truth tapes hp _ hhandle
        rcases candidate_advance_reason P seed s.history current hh hc hvalid (hm.symm.trans ha) with ha | hn
        · left
          obtain ⟨pair, hpHistory, heq⟩ := List.any_eq_true.mp ha
          rw [prefix_historyCommitments (P.input fee hfee) (P.retainedPaymentExampleContract allocation)
            .native (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes hp] at hpHistory
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hpHistory
          exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ha, by simpa only [beq_iff_eq] using heq⟩)
        · exact Or.inr (prefix_no_tool_length P fee hfee allocation seed truth tapes hp hn)

end PaperProofs.Paid.PA17D31WitnessCoverage012
