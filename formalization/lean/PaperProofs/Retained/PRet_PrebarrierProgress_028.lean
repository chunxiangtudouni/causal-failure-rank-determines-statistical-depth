module

public import PaperProofs.Retained.PRet_SourceSuccess_027
public import PaperProofs.Retained.PRet_PaymentPrefix_021
public import PaperProofs.Retained.PRet_PastWritten_015

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetPrebarrierProgress028

open Common Common.Native PRetInformationPackets006 PRetDelayedPolicy010
open PRetReplayInvariant016 PRetPaymentPrefix021 PRetSourceSuccess027 PRetPastWritten015

variable {I : Instance}

theorem catchUp_step {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {target : State I}
    (hp : Prefix input C .uncapped accounting source seed truth tapes n target)
    (ha : target.halted = false) (hbound : target.cursor < I.stageCount)
    (destination : ℕ) (action : Action I) (hle : target.cursor ≤ destination)
    (hwritten : ∀ stage : I.Stage, stage.val < destination → target.ledger.written stage ≠ none)
    (hnext : target.cursor = destination → ∃ next,
      Step input C .uncapped accounting tapes target action next ∧ next.halted = false) :
    ∃ next, Step input C .uncapped accounting tapes target (catchUp target.history destination action) next ∧
      next.halted = false := by
  have hc := prefix_historyCursor input C .uncapped accounting source seed truth tapes hp
  by_cases hlt : target.cursor < destination
  · let stage : I.Stage := ⟨target.cursor, hbound⟩
    have haction : catchUp target.history destination action = .advance stage := by
      simp only [catchUp, hc, hlt, hbound, ↓reduceIte, ↓reduceDIte]
      rfl
    refine ⟨record accounting target (.advance stage) [.advanced stage]
      (advanceLedger target stage) (target.cursor + 1) false, ?_, rfl⟩
    rw [haction]
    exact Step.advance target stage ⟨ha, rfl⟩ (hwritten stage hlt) (Or.inl rfl)
  · have heq : target.cursor = destination := by omega
    have haction : catchUp target.history destination action = action := by
      simp only [catchUp, hc, heq, Nat.lt_irrefl, ↓reduceIte]
    rw [haction]
    exact hnext heq

/-- If the original source is eventually successful, every actual delayed
prebarrier active state has a genuine nonhalting raw Step. In particular,
neither cursor catch-up nor a source stop may cause false prebarrier failure. -/
theorem prebarrier_raw_step {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (hsuccess : runSuccess input C mode accounting source sample)
    {n : ℕ} {target : State I}
    (hp : Prefix input C .uncapped accounting (rule accounting source) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n target)
    (hi : ReplayInvariant input C mode accounting source sample target)
    (ha : target.halted = false) (hbound : target.cursor < I.stageCount) :
    ∃ next, Step input C .uncapped accounting (worldTapes input sample.2)
      target (raw accounting source sample.1 target.history) next ∧ next.halted = false := by
  obtain ⟨packets, oldClock, hinfo, hreplay, _, hwritten, _⟩ := hi
  have hraw := raw_of_replay accounting source sample.1 target.history packets _ hinfo hreplay
  change raw accounting source sample.1 target.history =
    candidate (publicStartup (run input C mode accounting source sample oldClock))
      (source sample.1 (run input C mode accounting source sample oldClock).history) target.history at hraw
  rw [hraw]
  obtain ⟨sourceClock, _, hsourcePrefix⟩ := run_has_prefix input C mode accounting source hlegal sample oldClock
  by_cases hh : (run input C mode accounting source sample oldClock).halted = true
  · have hs := halted_source_success input C mode accounting source sample hsuccess oldClock hh
    have hall := success_allWritten C _ (run_ledgerWellFormed input C mode accounting source hlegal sample oldClock) hs
    have hc := prefix_historyCursor input C .uncapped accounting (rule accounting source) sample.1 _ _ hp
    let stage : I.Stage := ⟨target.cursor, hbound⟩
    have haction : candidate (publicStartup (run input C mode accounting source sample oldClock))
        (source sample.1 (run input C mode accounting source sample oldClock).history) target.history = .advance stage := by
      simp only [candidate, publicStartup, hh, hs.1, hs.2.1, Bool.false_eq_true, ↓reduceIte,
        catchUp, hc, hbound, ↓reduceDIte]
      rfl
    refine ⟨record accounting target (.advance stage) [.advanced stage]
      (advanceLedger target stage) (target.cursor + 1) false, ?_, rfl⟩
    rw [haction]
    exact Step.advance target stage ⟨ha, rfl⟩ (by rw [hwritten]; exact hall stage) (Or.inl rfl)
  · have hsourceActive := Bool.eq_false_iff.mpr hh
    obtain ⟨stage, hreview | ⟨bit, hwrite⟩⟩ :=
      active_replay_information input C mode accounting source hlegal sample packets oldClock hreplay hsourceActive
    · obtain ⟨sourceNext, hsourceStep⟩ := hlegal sample.1 _ _ sourceClock _ hsourcePrefix hsourceActive
      rw [hreview] at hsourceStep
      cases hsourceStep with
      | review _ live port resources =>
        have hle : target.cursor ≤ stage.val := by
          by_contra hnot
          have hw := prefix_past_written input C .uncapped accounting (rule accounting source) sample.1 _ _ hp stage (by omega)
          rw [hwritten, port] at hw
          exact hw rfl
        simp only [candidate, publicStartup, hsourceActive, Bool.false_eq_true, ↓reduceIte, hreview]
        apply catchUp_step input C accounting (rule accounting source) sample.1 _ _ hp ha hbound stage.val (.review stage) hle
        · intro before hbefore
          rw [hwritten]
          exact prefix_past_written input C mode accounting source sample.1 _ _ hsourcePrefix before (live.2 ▸ hbefore)
        · intro heq
          refine ⟨_, Step.review target stage ⟨ha, heq⟩ ?_ (Or.inl rfl), rfl⟩
          rw [hwritten]
          exact port
    · obtain ⟨sourceNext, hsourceStep⟩ := hlegal sample.1 _ _ sourceClock _ hsourcePrefix hsourceActive
      rw [hwrite] at hsourceStep
      cases hsourceStep with
      | write _ _ live port resources =>
        have hle : target.cursor ≤ stage.val := by
          by_contra hnot
          have hw := prefix_past_written input C .uncapped accounting (rule accounting source) sample.1 _ _ hp stage (by omega)
          rw [hwritten, port] at hw
          exact hw rfl
        simp only [candidate, publicStartup, hsourceActive, Bool.false_eq_true, ↓reduceIte, hwrite]
        apply catchUp_step input C accounting (rule accounting source) sample.1 _ _ hp ha hbound stage.val (.write stage bit) hle
        · intro before hbefore
          rw [hwritten]
          exact prefix_past_written input C mode accounting source sample.1 _ _ hsourcePrefix before (live.2 ▸ hbefore)
        · intro heq
          refine ⟨_, Step.write target stage bit ⟨ha, heq⟩ ?_ (Or.inl rfl), rfl⟩
          rw [hwritten]
          exact port

end PaperProofs.Retained.PRetPrebarrierProgress028
