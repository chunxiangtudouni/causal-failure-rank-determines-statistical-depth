module

public import PaperProofs.Retained.Controller
public import PaperProofs.Common.HistorySuffixReplay

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetPublicAdministrativeReplay005

open Common Common.Native MeasureTheory

variable {I : Instance}

def silentAction : Action I → Bool
  | .review _ | .write _ _ => false
  | _ => true

noncomputable def silentUpdate (accounting : NormalAccounting I) (startup : Startup I) : Action I → Startup I
  | .allocate handle tool => startup.allocatePublic accounting handle tool
  | .execute handle tool => startup.executePublic accounting handle tool
  | .advance stage => startup.advancePublic accounting stage
  | .stop => startup.stopPublic false
  | .abandon => startup.stopPublic true
  | _ => startup

/-- All internal source transitions consume public data only. The cache has
no hidden truth or unobserved tape field; neither is an argument here. -/
noncomputable def silentNext (accounting : NormalAccounting I)
    (startup : Startup I) (action : Action I) : Option (Startup I) :=
  if startup.halted then none else
    if silentAction action then some (silentUpdate accounting startup action) else none

theorem silentNext_some_iff (accounting : NormalAccounting I) (startup next : Startup I) (action : Action I) :
    silentNext accounting startup action = some next ↔ startup.halted = false ∧
      silentAction action = true ∧ next = silentUpdate accounting startup action := by
  cases hh : startup.halted <;> cases ha : silentAction action <;> simp [silentNext, hh, ha, eq_comm]

noncomputable def settle {Seed : Type*} (accounting : NormalAccounting I) (rule : PolicyRule I Seed) :
    ℕ → Seed → Startup I → Startup I × ℕ
  | 0, _, startup => (startup, 0)
  | fuel + 1, seed, startup =>
    match silentNext accounting startup (rule seed startup.history) with
    | none => (startup, 0)
    | some next => let result := settle accounting rule fuel seed next
                   (result.1, result.2 + 1)

theorem settle_count_le {Seed : Type*} (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (fuel : ℕ) (seed : Seed) (startup : Startup I) :
    (settle accounting rule fuel seed startup).2 ≤ fuel := by
  induction fuel generalizing startup with
  | zero => exact le_rfl
  | succ fuel ih =>
    simp only [settle]
    split
    · exact Nat.zero_le _
    · exact Nat.succ_le_succ (ih _)

def position (startup : Startup I) : ℕ :=
  startup.commitments.length + startup.executions.length + startup.cursor + if startup.halted then 1 else 0

theorem position_le_bound (startup : Startup I)
    (hcommit : startup.commitments.length ≤ I.toolCount)
    (hexecute : startup.executions.length ≤ I.toolCount)
    (hcursor : startup.cursor ≤ I.stageCount) : position startup ≤ I.stageCount + 2 * I.toolCount + 1 := by
  cases hh : startup.halted <;> simp [position, hh] <;> omega

theorem silentNext_position (accounting : NormalAccounting I) (startup next : Startup I) (action : Action I)
    (hn : silentNext accounting startup action = some next) : position next = position startup + 1 := by
  obtain ⟨hh, ha, rfl⟩ := (silentNext_some_iff accounting startup next action).mp hn
  cases action <;> simp_all [silentAction, silentUpdate, position, Startup.allocatePublic,
    Startup.executePublic, Startup.advancePublic, Startup.stopPublic] <;> omega

theorem settle_position {Seed : Type*} (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (fuel : ℕ) (seed : Seed) (startup : Startup I) :
    position (settle accounting rule fuel seed startup).1 =
      position startup + (settle accounting rule fuel seed startup).2 := by
  induction fuel generalizing startup with
  | zero => simp only [settle, Nat.add_zero]
  | succ fuel ih =>
    generalize hn : silentNext accounting startup (rule seed startup.history) = next
    cases next with
    | none => simp only [settle, hn, Nat.add_zero]
    | some next =>
      simp only [settle, hn]
      rw [ih, silentNext_position accounting startup next _ hn]
      omega

theorem settle_stops_of_count_lt {Seed : Type*} (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (fuel : ℕ) (seed : Seed) (startup : Startup I)
    (hcount : (settle accounting rule fuel seed startup).2 < fuel) :
    silentNext accounting (settle accounting rule fuel seed startup).1
      (rule seed (settle accounting rule fuel seed startup).1.history) = none := by
  induction fuel generalizing startup with
  | zero => exact (Nat.not_lt_zero _ hcount).elim
  | succ fuel ih =>
    generalize hn : silentNext accounting startup (rule seed startup.history) = next
    cases next with
    | none => simp only [settle, hn]
    | some next =>
      simp only [settle, hn] at hcount ⊢
      exact ih next (Nat.lt_of_succ_lt_succ hcount)

section Measurable

variable {Seed : Type*} [MeasurableSpace Seed]

theorem measurable_silentNext (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hrule : MeasurableRule rule) : Measurable (fun sample : Seed × Startup I =>
      silentNext accounting sample.2 (rule sample.1 sample.2.history)) := by
  have hh : Measurable (fun sample : Seed × Startup I => sample.2.history) :=
    (measurable_of_countable (fun startup : Startup I => startup.history)).comp measurable_snd
  have ha := hrule.comp (measurable_fst.prodMk hh)
  exact (measurable_of_countable (fun pair : Startup I × Action I =>
    silentNext accounting pair.1 pair.2)).comp (measurable_snd.prodMk ha)

theorem measurable_settle (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hrule : MeasurableRule rule) (fuel : ℕ) : Measurable (fun sample : Seed × Startup I =>
      settle accounting rule fuel sample.1 sample.2) := by
  induction fuel with
  | zero => exact measurable_snd.prodMk measurable_const
  | succ fuel ih =>
    let step : Seed × Startup I → Option (Startup I) := fun sample =>
      silentNext accounting sample.2 (rule sample.1 sample.2.history)
    have hs : Measurable step := measurable_silentNext accounting rule hrule
    let resumed : Seed × Startup I → Seed × Startup I := fun sample =>
      (sample.1, (step sample).getD sample.2)
    have hn : Measurable resumed := measurable_fst.prodMk
      ((measurable_of_countable (fun pair : Option (Startup I) × Startup I =>
        pair.1.getD pair.2)).comp (hs.prodMk measurable_snd))
    have htail : Measurable (fun sample =>
        ((settle accounting rule fuel (resumed sample).1 (resumed sample).2).1,
          (settle accounting rule fuel (resumed sample).1 (resumed sample).2).2 + 1)) :=
      (measurable_of_countable (fun result : Startup I × ℕ => (result.1, result.2 + 1))).comp (ih.comp hn)
    have hm : Measurable (fun sample : Seed × Startup I =>
        if step sample = none then (sample.2, 0) else
          ((settle accounting rule fuel (resumed sample).1 (resumed sample).2).1,
            (settle accounting rule fuel (resumed sample).1 (resumed sample).2).2 + 1)) :=
      Measurable.ite (hs (measurableSet_singleton none)) (measurable_snd.prodMk measurable_const) htail
    convert hm using 1
    funext sample
    cases hn' : step sample <;> simp [settle, resumed, step] at hn' ⊢
    · rw [hn']
    · rw [hn']
      rfl

end Measurable

theorem silentNext_actual {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World)
    (n : ℕ) (next : Startup I)
    (hn : silentNext accounting (publicStartup (run input C mode accounting rule sample n))
      (rule sample.1 (run input C mode accounting rule sample n).history) = some next) :
    next = publicStartup (run input C mode accounting rule sample (n + 1)) := by
  obtain ⟨ha, hsilent, hnext⟩ := (silentNext_some_iff accounting _ next _).mp hn
  obtain ⟨m, _, hp⟩ := run_has_prefix input C mode accounting rule hlegal sample n
  obtain ⟨s', hs⟩ := hlegal sample.1 _ _ m _ hp ha
  have hr := run_succ_of_step input C mode accounting rule sample n s' ha hs
  rw [hr, hnext]
  generalize haction : rule sample.1 (run input C mode accounting rule sample n).history = action at hs hsilent ⊢
  cases hs <;> simp_all [silentAction, silentUpdate, publicStartup_allocate,
    publicStartup_execute, publicStartup_advance, publicStartup_stop]

theorem settle_actual {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World) (fuel n : ℕ) :
    let result := settle accounting rule fuel sample.1 (publicStartup (run input C mode accounting rule sample n))
    result.1 = publicStartup (run input C mode accounting rule sample (n + result.2)) := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
    generalize hn : silentNext accounting (publicStartup (run input C mode accounting rule sample n))
      (rule sample.1 (publicStartup (run input C mode accounting rule sample n)).history) = next
    cases next with
    | none => simp only [settle, hn, Nat.add_zero]
    | some next =>
      have hnext := silentNext_actual input C mode accounting rule hlegal sample n next hn
      have ht := ih (n + 1)
      rw [← hnext] at ht
      simp only [settle, hn]
      rw [show n + ((settle accounting rule fuel sample.1 next).2 + 1) =
        (n + 1) + (settle accounting rule fuel sample.1 next).2 by omega]
      exact ht

/-- The public administrative closure always stops within the original
finite stage/tool budget, on every real path. Its source protocol need not
terminate and its expected bill may be infinite. -/
theorem settle_actual_stops {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting rule) (sample : Seed × input.World) (n : ℕ) :
    let result := settle accounting rule (I.stageCount + 2 * I.toolCount + 2) sample.1
      (publicStartup (run input C mode accounting rule sample n))
    silentNext accounting result.1 (rule sample.1 result.1.history) = none := by
  let fuel := I.stageCount + 2 * I.toolCount + 2
  let startup := publicStartup (run input C mode accounting rule sample n)
  let result := settle accounting rule fuel sample.1 startup
  have hactual : result.1 = publicStartup (run input C mode accounting rule sample (n + result.2)) :=
    settle_actual input C mode accounting rule hlegal sample fuel n
  have hposition := settle_position accounting rule fuel sample.1 startup
  change position result.1 = position startup + result.2 at hposition
  have hbound : position result.1 ≤ I.stageCount + 2 * I.toolCount + 1 := by
    rw [hactual]
    have hwf := run_ledgerWellFormed input C mode accounting rule hlegal sample (n + result.2)
    have hcommit := hwf.commitment_tools.length_le_card
    have hexecute := hwf.execution_tools.length_le_card
    simp only [List.length_map, Instance.Tool, Fintype.card_fin] at hcommit hexecute
    have hcursor := (run_cursorInvariant input C mode accounting rule hlegal sample (n + result.2)).bound
    exact position_le_bound _ hcommit hexecute hcursor
  have hcount : result.2 < fuel := by dsimp [fuel]; omega
  exact settle_stops_of_count_lt accounting rule fuel sample.1 startup hcount

theorem silentNext_information (accounting : NormalAccounting I) (startup next : Startup I) (action : Action I)
    (hn : silentNext accounting startup action = some next) :
    informationTrace next.history = informationTrace startup.history := by
  obtain ⟨_, ha, rfl⟩ := (silentNext_some_iff accounting startup next action).mp hn
  cases action <;> simp_all [silentAction, silentUpdate, informationTrace, informationEvent,
    Startup.allocatePublic, Startup.executePublic, Startup.advancePublic, Startup.stopPublic,
    List.filterMap_append, List.filterMap_cons, List.filterMap_nil]

theorem settle_information {Seed : Type*} (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (fuel : ℕ) (seed : Seed) (startup : Startup I) :
    informationTrace (settle accounting rule fuel seed startup).1.history = informationTrace startup.history := by
  induction fuel generalizing startup with
  | zero => rfl
  | succ fuel ih =>
    generalize hn : silentNext accounting startup (rule seed startup.history) = next
    cases next with
    | none => simp only [settle, hn]
    | some next =>
      simp only [settle, hn]
      exact (ih next).trans (silentNext_information accounting startup next _ hn)

end PaperProofs.Retained.PRetPublicAdministrativeReplay005
